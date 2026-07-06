#!/usr/bin/env python3
"""
Credit Check — for Wikimedia Commons photographers.

Find your photographs that are live on Wikipedia, spot the ones missing your
photographer category, review them in Markdown, and add the category to the
ones you pick. Works for any photographer, not one hard-coded person.

It scans your own uploads as candidates, and reaches past them: any file whose
*author/photographer field* credits you is found too, which includes cropped
derivatives re-uploaded by other people. It also tells apart photos you TOOK
from photos that merely DEPICT you, so a portrait of you by someone else never
lands in "Photographs by <you>".

WORKFLOW
    Run `credit-check` to start the guided command-line app, or use commands:
    1. scan     -> writes review.md
    2. review   -> pick photos in your browser, terminal, or editor
    3. plan     -> dry-run the checked edits
    4. commit   -> logs in and adds the right category to each photo you checked

CONFIG (flags override environment and local preferences)
    --username     / WIKI_USERNAME      your Commons account (the uploader name)
    --author       / WIKI_AUTHOR        your name as it appears in author fields
    --by-category  / WIKI_BY_CATEGORY   default: "Photographs by <author>"
    --of-category  / WIKI_OF_CATEGORY   subject category for photos that depict you
    --qid          / WIKI_QID           your Wikidata id (e.g. Q42) for depicts (P180)
    .credit-check.json / --review-format   markdown by default; set org locally

EXAMPLES
    export WIKI_USERNAME='Jaydixit'
    export WIKI_AUTHOR='Jay Dixit'
    credit-check                              # guided mode
    credit-check scan
    credit-check scan --of-category 'Jay Dixit' --qid Q12345
    credit-check review review.md             # pick photos in your browser
    credit-check review --terminal review.md  # keyboard-only terminal review
    credit-check plan review.md               # dry run: shows the plan
    credit-check commit review.md --go         # actually edits

    (Not installed? Run it directly: python3 credit_check.py scan)

CREDENTIALS (commit --go only)
    Make a bot password at https://commons.wikimedia.org/wiki/Special:BotPasswords
    with "Edit existing pages", then:
        export COMMONS_BOTUSER='Jaydixit@categorize'
        export COMMONS_BOTPASS='the-generated-password'

questionary and prompt_toolkit provide the installed command's interactive UI;
direct script mode falls back to plain prompts if they are unavailable.
"""

import argparse, getpass, html, http.cookiejar, http.server, json, os, re, shlex, sys, tempfile, threading, time, webbrowser
import urllib.parse, urllib.request, urllib.error

try:
    import questionary
    from prompt_toolkit import Application
    from prompt_toolkit.key_binding import KeyBindings
    from prompt_toolkit.layout import Layout
    from prompt_toolkit.layout.controls import FormattedTextControl
    from prompt_toolkit.layout.containers import Window
    from prompt_toolkit.styles import Style
except ImportError:
    questionary = None
    Application = None
    FormattedTextControl = None
    KeyBindings = None
    Layout = None
    Style = None
    Window = None

API = "https://commons.wikimedia.org/w/api.php"
UA = "credit-check/2.0 (Commons photographer self-categorization; run by file owner)"
TITLE_BATCH = 50
WEB_REVIEW_HOST = "127.0.0.1"


# ---------------------------------------------------------------- HTTP client

class Client:
    def __init__(self):
        self.jar = http.cookiejar.CookieJar()
        self.opener = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.jar))
        self.opener.addheaders = [("User-Agent", UA)]

    def _call(self, params, data=None, tries=6, retry_post=False):
        params = {**params, "format": "json"}
        url = API + "?" + urllib.parse.urlencode(params)
        body = urllib.parse.urlencode(data).encode() if data else None
        may_retry = (body is None) or retry_post
        for attempt in range(tries):
            try:
                with self.opener.open(url, data=body, timeout=60) as r:
                    return json.load(r)
            except urllib.error.HTTPError as e:
                if may_retry and e.code in (429, 503) and attempt < tries - 1:
                    wait = int(e.headers.get("Retry-After") or 0) or 2 ** attempt
                    print("  rate-limited, waiting %ss..." % wait, file=sys.stderr)
                    time.sleep(wait); continue
                raise
            except urllib.error.URLError:
                if may_retry and attempt < tries - 1:
                    time.sleep(2 ** attempt); continue
                raise

    def get(self, params):          return self._call(params)
    def post(self, params, data, retry_post=False):
        return self._call(params, data=data, retry_post=retry_post)


# ---------------------------------------------------------------- discovery

def discover_titles(cl, username, author, insource_user):
    """Union of uploads by `username` and files whose source names `author`."""
    reasons = {}
    def add(t, r): reasons.setdefault(t, set()).add(r)

    cont = {}
    while True:
        d = cl.get({"action": "query", "list": "allimages", "aiuser": username,
                    "aisort": "timestamp", "aidir": "descending", "ailimit": "500", **cont})
        for im in d.get("query", {}).get("allimages", []):
            add(im["title"], "upload")
        if "continue" in d: cont = d["continue"]; time.sleep(0.4)
        else: break

    queries = ['insource:"%s"' % author]
    if insource_user:
        queries.append('insource:"User:%s"' % username)
    for srsearch in queries:
        offset = 0
        while True:
            d = cl.get({"action": "query", "list": "search", "srsearch": srsearch,
                        "srnamespace": "6", "srlimit": "500", "sroffset": offset})
            for h in d.get("query", {}).get("search", []):
                add(h["title"], "credited")
            cont = d.get("continue", {})
            if "sroffset" in cont: offset = cont["sroffset"]; time.sleep(0.4)
            else: break
    return reasons


def fetch_details(cl, titles, by_cat, of_cat):
    """Per title: pageid, uploader, cats, in_by_cat, in_of_cat, wp uses, wikitext."""
    by_full = "Category:" + by_cat
    of_full = "Category:" + of_cat if of_cat else None
    info = {}
    titles = list(titles)
    for i in range(0, len(titles), TITLE_BATCH):
        batch = titles[i:i + TITLE_BATCH]
        base = {"action": "query", "titles": "|".join(batch),
                "prop": "categories|globalusage|imageinfo|revisions",
                "cllimit": "500", "clshow": "!hidden", "iiprop": "user",
                "rvprop": "content", "rvslots": "main",
                "guprop": "url|namespace", "gufilterlocal": "1", "gulimit": "500"}
        cont = {}
        while True:
            d = cl.get({**base, **cont})
            for _, p in d.get("query", {}).get("pages", {}).items():
                t = p["title"]
                rec = info.setdefault(t, {"pageid": p.get("pageid"), "uploader": None,
                                          "cats": set(), "in_by": False, "in_of": False,
                                          "wp": {}, "text": ""})
                ii = (p.get("imageinfo") or [{}])[0]
                if ii.get("user"): rec["uploader"] = ii["user"]
                rev = (p.get("revisions") or [{}])[0]
                content = (rev.get("slots", {}).get("main", {}) or {}).get("*", "")
                if content: rec["text"] = content
                for c in p.get("categories", []):
                    rec["cats"].add(c["title"])
                    if c["title"] == by_full: rec["in_by"] = True
                    if of_full and c["title"] == of_full: rec["in_of"] = True
                for u in p.get("globalusage", []):
                    if u.get("ns") == "0" and u["wiki"].endswith("wikipedia.org"):
                        rec["wp"][u["wiki"] + "|" + u["title"]] = {
                            "wiki": u["wiki"], "lang": u["wiki"].split(".")[0], "title": u["title"]}
            if "continue" in d: cont = d["continue"]
            else: break
        print("  detail %d/%d..." % (min(i + TITLE_BATCH, len(titles)), len(titles)),
              file=sys.stderr)
        time.sleep(0.5)
    return info


def fetch_depicts(cl, pageids, qid):
    """Return set of pageids whose SDC depicts (P180) includes qid."""
    hits = set()
    ids = ["M%d" % pid for pid in pageids if pid]
    for i in range(0, len(ids), TITLE_BATCH):
        batch = ids[i:i + TITLE_BATCH]
        d = cl.get({"action": "wbgetentities", "ids": "|".join(batch), "props": "claims"})
        for mid, ent in d.get("entities", {}).items():
            claims = ent.get("statements") or ent.get("claims") or {}
            for st in claims.get("P180", []):
                val = (((st.get("mainsnak") or {}).get("datavalue") or {}).get("value") or {})
                if val.get("id") == qid:
                    hits.add(int(mid[1:]))
        time.sleep(0.4)
    return hits


# ---------------------------------------------------------------- classify

AUTHOR_FIELD_RE = re.compile(
    r"[|\n]\s*(?:author|photographer|artist)\s*=\s*((?:\[\[[^\]]*\]\]|[^|\n}])*)",
    re.I)
CREDIT_AUTHOR_RE = re.compile(r"Credit line[^}]*?Author\s*=\s*([^|}]*)", re.I)

def author_context(text):
    parts = AUTHOR_FIELD_RE.findall(text)
    parts += CREDIT_AUTHOR_RE.findall(text)
    parts += re.findall(r"\{\{Creator:[^}]*\}\}", text, re.I)
    return "\n".join(parts)

def name_matches(text, name):
    return bool(name and re.search(r"(?<!\w)%s(?!\w)" % re.escape(name), text, re.I))

def is_by(text, username, author):
    """True only if the author/photographer field credits this person.

    Being the uploader is not sufficient: people upload press photos,
    screenshots, and portraits taken of them by others. Authorship comes from
    the credit fields. An uploaded file whose credit fields do not confirm the
    photographer falls through to ambiguous for a human.
    """
    actx = author_context(text)
    if username and re.search(r"User:\s*%s\b" % re.escape(username), actx, re.I):
        return True
    if name_matches(actx, author):
        return True
    return False

def name_as_subject(text, author):
    """Name appears in the file text but not in the author context (subject-ish)."""
    if not author: return False
    actx = author_context(text)
    return name_matches(text, author) and not name_matches(actx, author)

def route_record(rec, username, author, of_cat, depicts):
    """Return by/of/ambiguous for missing-category work, or None if already done."""
    if is_by(rec["text"], username, author):
        return "by" if not rec["in_by"] else None
    if of_cat and rec["pageid"] in depicts:
        return "of" if not rec["in_of"] else None
    return "ambiguous"


# ---------------------------------------------------------------- derivative tracing
# A crop re-uploaded by someone else usually keeps the author field (caught by is_by).
# But some crops strip the credit and only cite the source file, via:
#   |source=[[:File:Original.jpg]]
#   |other versions={{Extracted from|1=Original filename.jpg}}   (bare title, no File:)
# Tracing follows those source links to the original and inherits its authorship.

DERIV_TEMPLATE_RE = re.compile(
    r"\{\{\s*(?:extracted from|derived from|image extracted|retouched picture|based on)\s*\|([^}]*)\}\}",
    re.I)
FIELD_LINE_RE = re.compile(r"[|\n]\s*(?:source|other[ _]versions|original)\s*=\s*([^\n]*)", re.I)
FILELINK_RE = re.compile(r"\[\[\s*:?\s*(File:[^\]\|\n]+)", re.I)

def norm_title(name):
    name = (name or "").strip().lstrip(":").strip()
    if re.match(r"(?i)^file:", name):
        name = name.split(":", 1)[1]
    elif not re.search(r"\.\w{2,5}$", name):
        return None                      # not a bare filename either
    name = name.replace("_", " ").strip()
    if not name:
        return None
    return "File:" + name[0].upper() + name[1:]

def _param_value(blob):
    m = re.search(r"(?:1|file|image)\s*=\s*([^|]+)", blob, re.I)
    return m.group(1) if m else blob.split("|")[0]

def source_files(text, self_title=None):
    """Source File: titles this file derives from."""
    out = []
    for blob in DERIV_TEMPLATE_RE.findall(text):
        t = norm_title(_param_value(blob))
        if t: out.append(t)
    for fld in FIELD_LINE_RE.findall(text):
        for link in FILELINK_RE.findall(fld):
            t = norm_title(link)
            if t: out.append(t)
    seen = []
    for t in out:
        if t != self_title and t not in seen:
            seen.append(t)
    return seen

def fetch_source_details(cl, titles):
    """{requested_title: {uploader, text}} for source files (redirects followed)."""
    det = {}
    titles = list(titles)
    for i in range(0, len(titles), TITLE_BATCH):
        batch = titles[i:i + TITLE_BATCH]
        d = cl.get({"action": "query", "titles": "|".join(batch), "redirects": "1",
                    "prop": "imageinfo|revisions", "iiprop": "user",
                    "rvprop": "content", "rvslots": "main"})
        q = d.get("query", {})
        alias = {}
        for r in q.get("redirects", []): alias[r["from"]] = r["to"]
        for n in q.get("normalized", []): alias[n["from"]] = n["to"]
        by_title = {}
        for _, p in q.get("pages", {}).items():
            ii = (p.get("imageinfo") or [{}])[0]
            rev = (p.get("revisions") or [{}])[0]
            content = (rev.get("slots", {}).get("main", {}) or {}).get("*", "")
            by_title[p["title"]] = {"uploader": ii.get("user"), "text": content}
        for req in batch:
            resolved = alias.get(req, req)
            det[req] = by_title.get(resolved, {"uploader": None, "text": ""})
        time.sleep(0.4)
    return det

def trace_to_by(title, depth, det, username, author, path):
    """Return the source title (up the chain) that is by the photographer, or None."""
    if depth < 0: return None
    d = det.get(title)
    if not d: return None
    if is_by(d.get("text", ""), username, author):
        return title
    for s in source_files(d.get("text", ""), self_title=title):
        if s in path: continue
        hit = trace_to_by(s, depth - 1, det, username, author, path + [s])
        if hit: return hit
    return None

def resolve_derivatives(cl, amb_list, username, author, max_depth=2):
    """Promote ambiguous files whose source chain reaches a by-photographer original.
    Returns {title: source_title_that_proved_it}."""
    if not amb_list: return {}
    # gather source titles up to max_depth, breadth-first
    det = {t: {"uploader": rec["uploader"], "text": rec["text"]} for t, rec in amb_list.items()}
    frontier = set()
    for rec in amb_list.values():
        frontier |= set(source_files(rec["text"]))
    for _ in range(max_depth):
        need = [t for t in frontier if t not in det]
        if not need: break
        print("  tracing %d source file(s)..." % len(need), file=sys.stderr)
        det.update(fetch_source_details(cl, need))
        frontier = set()
        for t in need:
            d = det[t]
            if is_by(d.get("text", ""), username, author):
                continue   # chain terminates here; no need to follow its links
            frontier |= set(source_files(d.get("text", ""), self_title=t))
    promoted = {}
    for t in amb_list:
        hit = trace_to_by(t, max_depth, det, username, author, [t])
        if hit and hit != t:
            promoted[t] = hit
    return promoted


# ---------------------------------------------------------------- review output

def langs_line(wp):
    order = sorted({u["lang"] for u in wp.values()}, key=lambda l: (l != "en", l))
    head = ", ".join(order[:8])
    if len(order) > 8: head += ", +%d" % (len(order) - 8)
    return head

REVIEW_FORMAT_ENV = "CREDIT_CHECK_REVIEW_FORMAT"
PREFERENCE_FILE = ".credit-check.json"
REVIEW_FORMAT_ALIASES = {"md": "markdown", "markdown": "markdown",
                         "org": "org", "org-mode": "org", "orgmode": "org"}

def normalize_review_format(value):
    fmt = (value or "markdown").strip().lower()
    if fmt not in REVIEW_FORMAT_ALIASES:
        sys.exit("Invalid review format %r. Use markdown or org." % value)
    return REVIEW_FORMAT_ALIASES[fmt]

def default_review_path(review_format):
    return "review.org" if review_format == "org" else "review.md"

def local_preferences():
    try:
        with open(PREFERENCE_FILE, encoding="utf-8") as f:
            prefs = json.load(f)
    except FileNotFoundError:
        return {}
    except json.JSONDecodeError as e:
        sys.exit("Invalid %s: %s" % (PREFERENCE_FILE, e))
    if not isinstance(prefs, dict):
        sys.exit("Invalid %s: expected a JSON object." % PREFERENCE_FILE)
    return prefs

def preferred_review_format():
    prefs = local_preferences()
    return prefs.get("review_format") or prefs.get("review-format")

def preference_value(*names, default=None):
    prefs = local_preferences()
    for name in names:
        if name in prefs:
            return prefs[name]
    return default

def preference_bool(*names, default=False):
    val = preference_value(*names, default=default)
    if isinstance(val, bool):
        return val
    if isinstance(val, str):
        if val.strip().lower() in ("1", "true", "yes", "y", "on"):
            return True
        if val.strip().lower() in ("0", "false", "no", "n", "off"):
            return False
    return bool(val)

def preference_int(*names, default):
    val = preference_value(*names, default=default)
    try:
        return int(val)
    except (TypeError, ValueError):
        sys.exit("Invalid %s in %s: expected a number." % (names[0], PREFERENCE_FILE))

def save_local_preferences(updates):
    prefs = local_preferences()
    for key, value in updates.items():
        if value is None or value == "":
            prefs.pop(key, None)
        else:
            prefs[key] = value
    with open(PREFERENCE_FILE, "w", encoding="utf-8") as f:
        json.dump(prefs, f, indent=2, sort_keys=True)
        f.write("\n")

def identity_default(pref_name, env_name, default=None):
    return os.environ.get(env_name) or preference_value(pref_name, default=default)

def preferred_review_path(review_format):
    return preference_value("review_path", "out", default=default_review_path(review_format))

def scan_min_uses(args):
    if getattr(args, "min_uses", None) is not None:
        return args.min_uses
    return preference_int("min_uses", "minimum_wikipedia_uses", default=1)

def scan_english_only(args):
    if getattr(args, "english_only", None) is not None:
        return args.english_only
    return preference_bool("english_only", default=False)

def scan_insource_user(args):
    if getattr(args, "insource_user", None) is not None:
        return args.insource_user
    return preference_bool("insource_user", "match_user_page_source", default=True)

def scan_no_derivatives(args):
    if getattr(args, "no_derivatives", None) is not None:
        return args.no_derivatives
    return not preference_bool("trace_derivatives", "follow_crops", default=True)

def scan_depth(args):
    if getattr(args, "depth", None) is not None:
        return args.depth
    return preference_int("depth", "source_depth", default=2)

def infer_review_format(args):
    explicit = args.review_format or os.environ.get(REVIEW_FORMAT_ENV)
    if explicit:
        return normalize_review_format(explicit)
    if args.out:
        ext = os.path.splitext(args.out)[1].lower()
        if ext == ".org":
            return "org"
        if ext in (".md", ".markdown"):
            return "markdown"
    preferred = preferred_review_format()
    if preferred:
        return normalize_review_format(preferred)
    return "markdown"

def sort_review_items(d):
    return sorted(d.items(), key=lambda kv: (-len(kv[1]["wp"]), kv[0]))

def review_path_arg(path):
    return shlex.quote(path)

def markdown_item_block(title, rec):
    name = title[5:] if title.startswith("File:") else title
    url = "https://commons.wikimedia.org/wiki/" + urllib.parse.quote(title.replace(" ", "_"))
    cats = ", ".join(sorted(c.replace("Category:", "") for c in rec["cats"])) or "(none)"
    block = [
        "## [%d] %s" % (len(rec["wp"]), name),
        "",
        "- [ ] %s" % title,
        "  [open on Commons](%s) - uploader %s - %s"
        % (url, rec["uploader"] or "?", "/".join(sorted(rec["reason"]))),
        "  cats: %s" % cats,
        "  live: %s" % langs_line(rec["wp"]),
    ]
    if rec.get("derived_from"):
        block.append("  derived from: %s (credited to you)" % rec["derived_from"])
    block.append("")
    return block

def org_item_block(title, rec):
    name = title[5:] if title.startswith("File:") else title
    url = "https://commons.wikimedia.org/wiki/" + urllib.parse.quote(title.replace(" ", "_"))
    cats = ", ".join(sorted(c.replace("Category:", "") for c in rec["cats"])) or "(none)"
    block = [
        "** [%d] %s" % (len(rec["wp"]), name),
        "   - [ ] %s" % title,
        "     [[%s][open on Commons]] · uploader %s · %s"
        % (url, rec["uploader"] or "?", "/".join(sorted(rec["reason"]))),
        "     cats: %s" % cats,
        "     live: %s" % langs_line(rec["wp"]),
    ]
    if rec.get("derived_from"):
        block.append("     derived from: %s (credited to you)" % rec["derived_from"])
    block.append("")
    return block

def write_markdown(by_list, of_list, amb_list, meta, path):
    L = []
    include_by = meta.get("include_by", True)
    include_of = meta.get("include_of", True)
    include_ambiguous = meta.get("include_ambiguous", True)
    L.append("# Category review - %s" % meta["author"])
    L.append("")
    L.append("Pick photos in the browser:")
    L.append("")
    L.append("    credit-check review %s" % review_path_arg(path))
    L.append("")
    L.append("Or tick `[X]` manually next to the photos you want, then dry-run and commit:")
    L.append("")
    L.append("    credit-check plan %s" % review_path_arg(path))
    L.append("    credit-check commit %s --go" % review_path_arg(path))
    L.append("")
    L.append("Each `# Add to [Category:...]` heading sets the category for the photos under it.")
    L.append("Move a photo between sections to change where it goes. `[ ]` photos are skipped.")
    L.append("")

    if include_by:
        L.append("# Add to [Category:%s] - photos you took (%d)"
                 % (meta["by_category"], len(by_list)))
        L.append("")
        for t, rec in sort_review_items(by_list): L += markdown_item_block(t, rec)

    if include_of and meta["of_category"]:
        L.append("# Add to [Category:%s] - photos that depict you (%d)"
                 % (meta["of_category"], len(of_list)))
        L.append("")
        for t, rec in sort_review_items(of_list): L += markdown_item_block(t, rec)

    if include_ambiguous:
        L.append("# Ambiguous - authorship or category is unclear (%d)" % len(amb_list))
        L.append("Not added automatically. To add one, move it under a heading above and tick it.")
        L.append("")
        for t, rec in sort_review_items(amb_list): L += markdown_item_block(t, rec)

    open(path, "w", encoding="utf-8").write("\n".join(L))

def write_org(by_list, of_list, amb_list, meta, path):
    L = []
    include_by = meta.get("include_by", True)
    include_of = meta.get("include_of", True)
    include_ambiguous = meta.get("include_ambiguous", True)
    L.append("#+TITLE: Category review — %s" % meta["author"])
    L.append("#+STARTUP: content")
    L.append("")
    L.append("# Pick photos in the browser:")
    L.append("#   credit-check review %s" % review_path_arg(path))
    L.append("# Or tick [X] manually next to the photos you want, then dry-run and commit:")
    L.append("#   credit-check plan %s" % review_path_arg(path))
    L.append("#   credit-check commit %s --go" % review_path_arg(path))
    L.append("# Each '* Add to [[Category:...]]' heading sets the category for the photos under it.")
    L.append("# Move a photo between sections to change where it goes. [ ] photos are skipped.")
    L.append("")

    if include_by:
        L.append("* Add to [[Category:%s]] — photos you took (%d)" % (meta["by_category"], len(by_list)))
        L.append("")
        for t, rec in sort_review_items(by_list): L += org_item_block(t, rec)

    if include_of and meta["of_category"]:
        L.append("* Add to [[Category:%s]] — photos that depict you (%d)"
                 % (meta["of_category"], len(of_list)))
        L.append("")
        for t, rec in sort_review_items(of_list): L += org_item_block(t, rec)

    if include_ambiguous:
        L.append("* Ambiguous — authorship or category is unclear (%d)" % len(amb_list))
        L.append("# NOT added automatically. To add one, move it under a heading above and tick it.")
        L.append("")
        for t, rec in sort_review_items(amb_list): L += org_item_block(t, rec)

    open(path, "w", encoding="utf-8").write("\n".join(L))

def write_review(by_list, of_list, amb_list, meta, path, review_format):
    if review_format == "org":
        write_org(by_list, of_list, amb_list, meta, path)
    else:
        write_markdown(by_list, of_list, amb_list, meta, path)

# ---------------------------------------------------------------- review parse (commit)

ORG_HEAD_TARGET_RE = re.compile(r"^\*\s+Add to \[\[Category:(.+?)\]\]")
MD_HEAD_TARGET_RE = re.compile(r"^#\s+Add to\s+\[Category:([^\]\n]+)\](?:\([^)]*\))?")
ORG_SECTION_RE = re.compile(r"^\*\s+")
MD_SECTION_RE = re.compile(r"^#\s+")
CHECK_RE = re.compile(r"^\s*-\s*\[(.)\]\s*(File:.+?)\s*$")
CHECK_LINE_RE = re.compile(r"^(\s*-\s*)\[(.)\](\s*File:.+?)(\n?)$")
ITEM_HEAD_RE = re.compile(r"^\s*(?:##|\*\*)\s+\[(\d+)\]\s+(.+?)\s*$")

def parse_approved(path, warn=True):
    """Return list of (file_title, target_category) for ticked items under a target heading.
    Top-level category headings set/reset the target; item headings do not."""
    approved, target = [], None
    ext = os.path.splitext(path)[1].lower()
    allow_org = ext not in (".md", ".markdown")
    allow_md = ext != ".org"
    for line in open(path, encoding="utf-8"):
        mt = None
        if allow_org:
            mt = ORG_HEAD_TARGET_RE.match(line)
        if not mt and allow_md:
            mt = MD_HEAD_TARGET_RE.match(line)
        if mt: target = mt.group(1); continue
        if (allow_org and ORG_SECTION_RE.match(line)) or (allow_md and MD_SECTION_RE.match(line)):
            target = None; continue   # e.g. the Ambiguous section
        mc = CHECK_RE.match(line)
        if mc and mc.group(1).strip().lower() == "x":
            if target: approved.append((mc.group(2), target))
            elif warn:
                print("  (skipping ticked item with no target category): %s"
                      % mc.group(2), file=sys.stderr)
    return approved

def parse_review_items(path):
    """Return review checkbox items with line numbers and their active target category."""
    items, target = [], None
    item_label, item_uses = None, None
    ext = os.path.splitext(path)[1].lower()
    allow_org = ext not in (".md", ".markdown")
    allow_md = ext != ".org"
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    for i, line in enumerate(lines):
        mh = ITEM_HEAD_RE.match(line)
        if mh:
            item_uses = int(mh.group(1))
            item_label = mh.group(2).strip()
            continue

        mt = None
        if allow_org:
            mt = ORG_HEAD_TARGET_RE.match(line)
        if not mt and allow_md:
            mt = MD_HEAD_TARGET_RE.match(line)
        if mt:
            target = mt.group(1)
            item_label, item_uses = None, None
            continue
        if (allow_org and ORG_SECTION_RE.match(line)) or (allow_md and MD_SECTION_RE.match(line)):
            target = None
            item_label, item_uses = None, None
            continue

        mc = CHECK_RE.match(line)
        if mc:
            title = mc.group(2)
            items.append({
                "line": i,
                "title": title,
                "target": target,
                "checked": mc.group(1).strip().lower() == "x",
                "uses": item_uses,
                "label": item_label or (title[5:] if title.startswith("File:") else title),
            })
            item_label, item_uses = None, None
    return items

def set_review_approvals(path, items, selected_lines):
    """Rewrite checkbox marks only for review photos with a target category."""
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    for item in items:
        if not item["target"]:
            continue
        m = CHECK_LINE_RE.match(lines[item["line"]])
        if not m:
            raise ValueError("Review item line no longer matches checkbox syntax: %s" %
                             lines[item["line"]].rstrip())
        mark = "X" if item["line"] in selected_lines else " "
        lines[item["line"]] = "%s[%s]%s%s" % (m.group(1), mark, m.group(3), m.group(4))
    with open(path, "w", encoding="utf-8") as f:
        f.writelines(lines)

def review_item_title(item):
    uses = "[%d] " % item["uses"] if item["uses"] is not None else ""
    target = "Category:%s" % item["target"] if item["target"] else "Ambiguous"
    return "%s%s -> %s" % (uses, item["label"], target)

def review_page_size():
    return max(1, preference_int("review_page_size", "page_size", default=20))

def commons_file_url(title):
    return "https://commons.wikimedia.org/wiki/" + urllib.parse.quote(
        title.replace(" ", "_"))

def commons_file_name(title):
    return title[5:] if title.startswith("File:") else title

def commons_thumb_url(title, width=320):
    name = commons_file_name(title).replace(" ", "_")
    return "https://commons.wikimedia.org/wiki/Special:FilePath/%s?width=%d" % (
        urllib.parse.quote(name), width)

def review_gallery_html(items, heading):
    cards = []
    for item in items:
        title = item["title"]
        uses = "%s Wikipedia use%s" % (
            item["uses"], "" if item["uses"] == 1 else "s") if item["uses"] is not None else "Wikipedia use unknown"
        checked = "Selected" if item["checked"] else "Not selected"
        cards.append("""<article class="photo">
  <a class="thumb" href="{file_url}" target="_blank" rel="noreferrer">
    <img src="{thumb_url}" alt="">
  </a>
  <h2>{label}</h2>
  <p>{uses} · {checked}</p>
  <p>{target}</p>
  <a href="{file_url}" target="_blank" rel="noreferrer">Open on Commons</a>
</article>""".format(
            file_url=html.escape(commons_file_url(title), quote=True),
            thumb_url=html.escape(commons_thumb_url(title), quote=True),
            label=html.escape(item["label"]),
            uses=html.escape(uses),
            checked=html.escape(checked),
            target=html.escape("Category:%s" % item["target"] if item["target"] else "Ambiguous"),
        ))
    return """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{heading}</title>
<style>
body {{ margin: 0; font: 15px/1.4 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; color: #24211f; background: #fbfaf7; }}
header {{ position: sticky; top: 0; padding: 18px 24px; background: rgba(251, 250, 247, 0.96); border-bottom: 1px solid #ddd8cf; }}
h1 {{ margin: 0; font-size: 22px; }}
main {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(220px, 1fr)); gap: 18px; padding: 24px; }}
.photo {{ background: #fff; border: 1px solid #ddd8cf; border-radius: 8px; padding: 12px; }}
.thumb {{ display: block; aspect-ratio: 4 / 3; background: #f1eee8; overflow: hidden; border-radius: 6px; }}
img {{ width: 100%; height: 100%; object-fit: contain; display: block; }}
h2 {{ margin: 10px 0 6px; font-size: 15px; line-height: 1.25; overflow-wrap: anywhere; }}
p {{ margin: 4px 0; color: #5f5a52; }}
a {{ color: #075985; }}
</style>
</head>
<body>
<header><h1>{heading}</h1></header>
<main>
{cards}
</main>
</body>
</html>
""".format(heading=html.escape(heading), cards="\n".join(cards))

def open_review_gallery(items, heading, quiet=False):
    fd, path = tempfile.mkstemp(prefix="credit-check-gallery.", suffix=".html")
    os.close(fd)
    with open(path, "w", encoding="utf-8") as f:
        f.write(review_gallery_html(items, heading))
    url = "file://" + urllib.request.pathname2url(path)
    webbrowser.open_new_tab(url)
    if not quiet:
        print("Opened %s" % path)
    return path

def web_review_payload(items):
    payload = []
    for item in items:
        payload.append({
            "line": item["line"],
            "title": item["title"],
            "label": item["label"],
            "target": item["target"],
            "checked": item["checked"],
            "uses": item["uses"],
            "file_url": commons_file_url(item["title"]),
            "thumb_url": commons_thumb_url(item["title"], width=420),
        })
    return payload

class ReviewChangedError(Exception):
    pass

def review_items_signature(items):
    return [(item["line"], item["title"], item["target"], item["checked"])
            for item in items]

def web_review_html(review, approvable, ambiguous_count=0, initial_mode="all"):
    if initial_mode not in ("all", "selected", "unselected"):
        initial_mode = "all"
    items_json = json.dumps(web_review_payload(approvable), ensure_ascii=True).replace(
        "</", "<\\/")
    review_json = json.dumps(os.path.abspath(review), ensure_ascii=True).replace(
        "</", "<\\/")
    review_arg_json = json.dumps(review_path_arg(review), ensure_ascii=True).replace(
        "</", "<\\/")
    ambiguous_json = json.dumps(ambiguous_count)
    initial_mode_json = json.dumps(initial_mode)
    return """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Credit Check review</title>
<style>
:root {
  color-scheme: light;
  --bg: #f5f7fa;
  --panel: #ffffff;
  --panel-soft: #f9fbfd;
  --ink: #18212f;
  --muted: #5b6878;
  --faint: #778393;
  --line: #d7e0e8;
  --line-strong: #b7c7d6;
  --accent: #0b6f9f;
  --accent-soft: #e8f4fa;
  --accent-strong: #095d87;
  --selected: #14825f;
  --selected-soft: #edf9f4;
  --warn: #7a5900;
  --warn-soft: #fff8e7;
}
* { box-sizing: border-box; }
body {
  margin: 0;
  background: var(--bg);
  color: var(--ink);
  font: 15px/1.45 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
}
header {
  position: sticky;
  top: 0;
  z-index: 10;
  background: rgba(255, 255, 255, 0.97);
  border-bottom: 1px solid var(--line);
  box-shadow: 0 2px 16px rgba(20, 33, 47, 0.07);
}
.topbar,
main {
  max-width: 1480px;
  margin: 0 auto;
  padding-left: 24px;
  padding-right: 24px;
}
.topbar {
  display: grid;
  gap: 14px;
  padding-top: 18px;
  padding-bottom: 16px;
}
.header-main {
  display: flex;
  align-items: flex-start;
  justify-content: space-between;
  gap: 18px;
}
.title-block {
  min-width: 0;
}
.eyebrow {
  margin: 0 0 4px;
  color: var(--accent-strong);
  font-size: 12px;
  font-weight: 700;
  letter-spacing: 0.03em;
  text-transform: uppercase;
}
h1 {
  margin: 0;
  font-size: 24px;
  line-height: 1.18;
  letter-spacing: 0;
  overflow-wrap: anywhere;
}
.summary {
  margin-top: 6px;
  color: var(--muted);
  font-weight: 650;
}
.review-path {
  color: var(--faint);
  font-size: 13px;
  overflow-wrap: anywhere;
}
.save-actions {
  display: flex;
  align-items: center;
  justify-content: flex-end;
  gap: 10px;
  flex: 0 0 auto;
}
.toolbar-row {
  display: flex;
  align-items: center;
  gap: 10px;
  flex-wrap: wrap;
}
.primary-tools {
  padding-top: 2px;
}
.bulk-tools {
  padding-top: 2px;
}
input[type="search"],
button {
  min-height: 38px;
  border: 1px solid var(--line);
  border-radius: 7px;
  background: #fff;
  color: var(--ink);
  font: inherit;
}
input[type="search"] {
  flex: 1 1 360px;
  min-width: min(100%, 280px);
  padding: 8px 10px;
}
button {
  padding: 7px 12px;
  cursor: pointer;
}
button:hover,
button:focus-visible,
input[type="search"]:focus {
  border-color: var(--accent);
  outline: 2px solid rgba(11, 111, 159, 0.16);
  outline-offset: 1px;
}
button.primary {
  border-color: var(--accent);
  background: var(--accent);
  color: #fff;
  font-weight: 700;
}
button.primary:hover,
button.primary:focus-visible {
  background: var(--accent-strong);
}
button.secondary {
  color: var(--muted);
  background: var(--panel-soft);
}
button.ghost {
  color: var(--accent-strong);
  background: transparent;
}
.mode-tabs {
  display: inline-flex;
  align-items: center;
  gap: 4px;
  padding: 3px;
  background: var(--panel-soft);
  border: 1px solid var(--line);
  border-radius: 8px;
}
.mode-tabs button {
  min-height: 32px;
  border-color: transparent;
  background: transparent;
  color: var(--muted);
  font-size: 14px;
}
.mode-tabs button.active {
  color: var(--ink);
  background: #fff;
  border-color: var(--line);
  box-shadow: 0 1px 3px rgba(20, 33, 47, 0.08);
}
.status {
  min-height: 1.4em;
  color: var(--muted);
  font-size: 13px;
}
main {
  padding-top: 24px;
  padding-bottom: 32px;
}
.notice {
  display: none;
  margin-bottom: 18px;
  padding: 12px 14px;
  color: #4f5662;
  background: var(--warn-soft);
  border: 1px solid #ead7a3;
  border-radius: 8px;
}
.notice.show {
  display: block;
}
.preview-panel {
  display: grid;
  gap: 10px;
  margin-bottom: 18px;
  padding: 14px;
  background: var(--panel);
  border: 1px solid var(--line);
  border-radius: 8px;
}
.preview-panel[hidden] {
  display: none;
}
.preview-header {
  display: flex;
  justify-content: space-between;
  gap: 14px;
  align-items: flex-start;
}
.preview-header h2 {
  margin: 0;
  font-size: 17px;
  line-height: 1.25;
}
.preview-header p,
.next-command {
  margin: 4px 0 0;
  color: var(--muted);
}
.preview-edits {
  margin: 0;
  max-height: 260px;
  overflow: auto;
  padding: 12px;
  color: #1d2938;
  background: #f8fafc;
  border: 1px solid var(--line);
  border-radius: 7px;
  font: 13px/1.45 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
  white-space: pre-wrap;
}
.empty {
  display: none;
  padding: 28px;
  color: var(--muted);
  background: var(--panel);
  border: 1px solid var(--line);
  border-radius: 8px;
}
.empty.show {
  display: block;
}
.sections {
  display: grid;
  gap: 28px;
}
.section {
  display: grid;
  gap: 12px;
}
.section-heading {
  display: flex;
  align-items: baseline;
  justify-content: space-between;
  gap: 12px;
  padding-bottom: 4px;
  border-bottom: 1px solid var(--line);
}
.section-heading h2 {
  margin: 0;
  font-size: 17px;
  line-height: 1.25;
  letter-spacing: 0;
  overflow-wrap: anywhere;
}
.section-heading p {
  margin: 0;
  color: var(--muted);
  font-size: 13px;
  text-align: right;
}
.grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(230px, 1fr));
  gap: 16px;
}
.photo {
  position: relative;
  display: grid;
  gap: 10px;
  align-content: start;
  min-width: 0;
  min-height: 100%;
  padding: 12px;
  background: var(--panel);
  border: 1px solid var(--line);
  border-radius: 8px;
  box-shadow: 0 1px 3px rgba(20, 33, 47, 0.04);
}
.photo::before {
  content: "";
  position: absolute;
  inset: -1px auto -1px -1px;
  width: 4px;
  border-radius: 8px 0 0 8px;
  background: transparent;
}
.photo:hover,
.photo:focus-visible {
  border-color: var(--accent);
  outline: 2px solid rgba(11, 111, 159, 0.14);
  outline-offset: 1px;
}
.photo.selected {
  border-color: rgba(20, 130, 95, 0.7);
  background: var(--selected-soft);
}
.photo.selected::before {
  background: var(--selected);
}
.photo.selected .selected-badge {
  opacity: 1;
  transform: translateY(0);
}
.select-line {
  display: inline-flex;
  align-items: center;
  gap: 8px;
  color: var(--muted);
  font-size: 13px;
  font-weight: 700;
}
.select-line input {
  width: 18px;
  height: 18px;
  accent-color: var(--selected);
}
.thumb {
  position: relative;
  display: block;
  aspect-ratio: 4 / 3;
  background: linear-gradient(135deg, #eef3f7, #f8fafc);
  border: 1px solid var(--line);
  border-radius: 6px;
  overflow: hidden;
}
.thumb-placeholder {
  position: absolute;
  inset: 0;
  display: grid;
  place-items: center;
  padding: 12px;
  color: var(--faint);
  font-size: 13px;
  text-align: center;
}
.thumb img {
  position: relative;
  z-index: 1;
  display: block;
  width: 100%;
  height: 100%;
  object-fit: contain;
  background: #fff;
  opacity: 0;
  transition: opacity 120ms ease;
}
.thumb.image-loaded img {
  opacity: 1;
}
.thumb.image-missing img {
  display: none;
}
.selected-badge {
  position: absolute;
  z-index: 2;
  top: 8px;
  right: 8px;
  min-width: 26px;
  height: 26px;
  display: grid;
  place-items: center;
  border-radius: 999px;
  color: #fff;
  background: var(--selected);
  font-size: 15px;
  font-weight: 800;
  opacity: 0;
  transform: translateY(-2px);
  transition: opacity 120ms ease, transform 120ms ease;
}
.photo h3 {
  margin: 0;
  font-size: 15px;
  font-weight: 500;
  line-height: 1.25;
  letter-spacing: 0;
  overflow-wrap: anywhere;
}
.photo h3 a {
  color: var(--ink);
  text-decoration: none;
}
.photo h3 a:hover,
.photo h3 a:focus-visible {
  color: var(--accent-strong);
  text-decoration: none;
}
a {
  color: var(--accent);
}
.card-footer {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 10px;
}
.use-badge {
  display: inline-flex;
  align-items: center;
  min-height: 24px;
  padding: 2px 8px;
  border-radius: 999px;
  color: var(--accent-strong);
  background: var(--accent-soft);
  font-size: 12px;
  font-weight: 700;
}
.commons-link {
  font-size: 13px;
  white-space: nowrap;
}
.target {
  margin: 0;
  color: var(--warn);
  font-size: 13px;
  overflow-wrap: anywhere;
}
.keyboard-hint {
  color: var(--faint);
  font-size: 12px;
}
@media (max-width: 760px) {
  .topbar,
  main {
    padding-left: 14px;
    padding-right: 14px;
  }
  .header-main {
    display: grid;
  }
  .save-actions {
    justify-content: stretch;
  }
  .save-actions button,
  .toolbar-row button {
    flex: 1 1 150px;
  }
  .mode-tabs {
    flex: 1 1 100%;
  }
  .mode-tabs button {
    flex: 1 1 0;
  }
  h1 {
    font-size: 21px;
  }
  .section-heading {
    display: grid;
  }
  .section-heading p {
    text-align: left;
  }
}
</style>
</head>
<body>
<header>
  <div class="topbar">
    <div class="header-main">
      <div class="title-block">
        <p class="eyebrow">Credit Check</p>
        <h1 id="screen-title">Review photos</h1>
        <div class="summary" id="summary"></div>
      </div>
      <div class="save-actions">
        <button type="button" class="secondary" data-action="preview">Preview edits</button>
        <button type="button" class="primary" data-action="save-close">Save and close</button>
        <button type="button" class="ghost" data-action="save">Save</button>
      </div>
    </div>
    <div class="review-path" id="review-path"></div>
    <div class="toolbar-row primary-tools">
      <input id="search" type="search" autocomplete="off" placeholder="Filter by filename, category, or use count">
      <div class="mode-tabs" role="group" aria-label="Review mode">
        <button type="button" data-mode="all">All</button>
        <button type="button" data-mode="selected">Selected</button>
        <button type="button" data-mode="unselected">Still deciding</button>
      </div>
    </div>
    <div class="toolbar-row bulk-tools">
      <button type="button" class="secondary" data-action="select-visible">Select visible</button>
      <button type="button" class="secondary" data-action="clear-visible">Clear visible</button>
      <button type="button" class="secondary" data-action="select-all">Select all</button>
      <button type="button" class="secondary" data-action="clear-all">Clear all</button>
      <span class="keyboard-hint">Shortcuts: / search, Space select, o open, s save</span>
    </div>
    <div class="status" id="status" role="status" aria-live="polite"></div>
  </div>
</header>
<main>
  <section class="preview-panel" id="preview-panel" hidden>
    <div class="preview-header">
      <div>
        <h2>Preview edits</h2>
        <p id="preview-summary"></p>
      </div>
      <button type="button" class="ghost" data-action="hide-preview">Hide preview</button>
    </div>
    <pre class="preview-edits" id="preview-edits"></pre>
    <p class="next-command" id="next-command"></p>
  </section>
  <div class="notice" id="ambiguous-note"></div>
  <div class="empty" id="empty">No photos match this filter.</div>
  <div class="sections" id="sections" aria-label="Photos"></div>
</main>
<script>
window.CREDIT_CHECK_REVIEW = __REVIEW_JSON__;
window.CREDIT_CHECK_REVIEW_ARG = __REVIEW_ARG_JSON__;
window.CREDIT_CHECK_ITEMS = __ITEMS_JSON__;
window.CREDIT_CHECK_AMBIGUOUS_COUNT = __AMBIGUOUS_JSON__;
window.CREDIT_CHECK_INITIAL_MODE = __INITIAL_MODE_JSON__;

(() => {
  const reviewPath = window.CREDIT_CHECK_REVIEW;
  const reviewArg = window.CREDIT_CHECK_REVIEW_ARG;
  const ambiguousCount = window.CREDIT_CHECK_AMBIGUOUS_COUNT;
  const items = window.CREDIT_CHECK_ITEMS.map((item) => ({
    ...item,
    selected: Boolean(item.checked),
  }));
  const sections = document.getElementById("sections");
  const empty = document.getElementById("empty");
  const summary = document.getElementById("summary");
  const status = document.getElementById("status");
  const search = document.getElementById("search");
  const modeButtons = Array.from(document.querySelectorAll("[data-mode]"));
  const screenTitle = document.getElementById("screen-title");
  const ambiguousNote = document.getElementById("ambiguous-note");
  const previewPanel = document.getElementById("preview-panel");
  const previewSummary = document.getElementById("preview-summary");
  const previewEdits = document.getElementById("preview-edits");
  const nextCommand = document.getElementById("next-command");
  const targets = Array.from(new Set(items.map((item) => item.target)));
  const singleTarget = targets.length === 1;
  let currentMode = ["all", "selected", "unselected"].includes(window.CREDIT_CHECK_INITIAL_MODE)
    ? window.CREDIT_CHECK_INITIAL_MODE
    : "all";
  let lastFocusedLine = items.length ? items[0].line : null;

  document.getElementById("review-path").textContent = reviewPath;
  if (singleTarget) {
    screenTitle.textContent = `Review photos for Category:${targets[0]}`;
  } else {
    screenTitle.textContent = `Review photos for ${targets.length} categories`;
  }
  if (ambiguousCount > 0) {
    const noun = ambiguousCount === 1 ? "photo was" : "photos were";
    ambiguousNote.textContent = `${ambiguousCount} ambiguous ${noun} not shown here. Edit review.md to move them under a category before selecting them.`;
    ambiguousNote.classList.add("show");
  }

  function escapeHtml(value) {
    return String(value ?? "").replace(/[&<>"']/g, (char) => ({
      "&": "&amp;",
      "<": "&lt;",
      ">": "&gt;",
      '"': "&quot;",
      "'": "&#39;",
    }[char]));
  }

  function itemText(item) {
    return [item.label, item.title, item.target, item.uses].join(" ").toLowerCase();
  }

  function visibleItems() {
    const query = search.value.trim().toLowerCase();
    return items.filter((item) => {
      if (currentMode === "selected" && !item.selected) return false;
      if (currentMode === "unselected" && item.selected) return false;
      return !query || itemText(item).includes(query);
    });
  }

  function groupItems(list) {
    const groups = [];
    const seen = new Map();
    list.forEach((item) => {
      if (!seen.has(item.target)) {
        const group = { target: item.target, items: [] };
        seen.set(item.target, group);
        groups.push(group);
      }
      seen.get(item.target).items.push(item);
    });
    return groups;
  }

  function usesText(item) {
    if (item.uses === null || item.uses === undefined) return "Uses unknown";
    return `${item.uses} ${item.uses === 1 ? "use" : "uses"}`;
  }

  function cardHtml(item) {
    const selectedClass = item.selected ? " selected" : "";
    const checked = item.selected ? " checked" : "";
    const selectText = item.selected ? "Selected" : "Select";
    const targetLine = singleTarget ? "" : `<p class="target">Category:${escapeHtml(item.target)}</p>`;
    return `<article class="photo${selectedClass}" tabindex="0" data-line="${item.line}" data-file-url="${escapeHtml(item.file_url)}">
      <label class="select-line">
        <input type="checkbox" data-line="${item.line}"${checked}>
        <span>${selectText}</span>
      </label>
      <a class="thumb" href="${escapeHtml(item.file_url)}" target="_blank" rel="noreferrer">
        <span class="thumb-placeholder">Loading thumbnail</span>
        <span class="selected-badge" aria-hidden="true">&#10003;</span>
        <img src="${escapeHtml(item.thumb_url)}" loading="lazy" alt="">
      </a>
      <h3><a href="${escapeHtml(item.file_url)}" target="_blank" rel="noreferrer">${escapeHtml(item.label)}</a></h3>
      <div class="card-footer">
        <span class="use-badge">${escapeHtml(usesText(item))}</span>
        <a class="commons-link" href="${escapeHtml(item.file_url)}" target="_blank" rel="noreferrer">Open on Commons</a>
      </div>
      ${targetLine}
    </article>`;
  }

  function sectionHtml(group) {
    const title = singleTarget ? "Photos credited to you, missing this category" : `Category:${group.target}`;
    const count = `${group.items.length} ${group.items.length === 1 ? "photo" : "photos"}`;
    const selected = group.items.filter((item) => item.selected).length;
    return `<section class="section">
      <div class="section-heading">
        <h2>${escapeHtml(title)}</h2>
        <p>${selected} selected / ${count}</p>
      </div>
      <div class="grid">${group.items.map(cardHtml).join("")}</div>
    </section>`;
  }

  function updateSummary(visible) {
    const selected = items.filter((item) => item.selected).length;
    const showing = visible.length === items.length ? "" : ` · ${visible.length} showing`;
    summary.textContent = `${items.length} photos · ${selected} selected${showing}`;
  }

  function renderModeButtons() {
    modeButtons.forEach((button) => {
      const active = button.dataset.mode === currentMode;
      button.classList.toggle("active", active);
      button.setAttribute("aria-pressed", active ? "true" : "false");
    });
  }

  function selectedItems() {
    return items.filter((item) => item.selected);
  }

  function renderPreview() {
    const selected = selectedItems();
    if (!selected.length) {
      previewSummary.textContent = "No selected photos yet.";
      previewEdits.textContent = "Pick photos above, then preview the category edits here.";
      nextCommand.textContent = "";
      return;
    }
    previewSummary.textContent = `${selected.length} ${selected.length === 1 ? "edit" : "edits"} ready for Commons.`;
    previewEdits.textContent = selected.map((item) =>
      `+ [[Category:${item.target}]]  ->  ${item.title}`
    ).join("\\n");
    nextCommand.textContent = `After saving, run: credit-check commit ${reviewArg} --go`;
  }

  function showPreview(setStatus = true) {
    renderPreview();
    previewPanel.hidden = false;
    if (setStatus) {
      const count = selectedItems().length;
      status.textContent = count
        ? `Previewing ${count} selected photos.`
        : "No selected photos yet.";
    }
    previewPanel.scrollIntoView({ block: "nearest" });
  }

  function render() {
    const visible = visibleItems();
    renderModeButtons();
    updateSummary(visible);
    empty.classList.toggle("show", visible.length === 0);
    sections.innerHTML = groupItems(visible).map(sectionHtml).join("");
    if (!previewPanel.hidden) renderPreview();
  }

  function setSelection(lines, value) {
    const lineSet = new Set(lines);
    items.forEach((item) => {
      if (lineSet.has(item.line)) item.selected = value;
    });
    status.textContent = "";
    render();
  }

  function toggleLine(line) {
    const item = items.find((candidate) => candidate.line === line);
    if (!item) return;
    item.selected = !item.selected;
    lastFocusedLine = line;
    status.textContent = "";
    render();
    const card = document.querySelector(`.photo[data-line="${line}"]`);
    if (card) card.focus({ preventScroll: true });
  }

  function focusedLine() {
    const card = document.activeElement && document.activeElement.closest
      ? document.activeElement.closest(".photo")
      : null;
    if (card) return Number(card.dataset.line);
    if (lastFocusedLine !== null && visibleItems().some((item) => item.line === lastFocusedLine)) {
      return lastFocusedLine;
    }
    const visible = visibleItems();
    return visible.length ? visible[0].line : null;
  }

  function openLine(line) {
    const item = items.find((candidate) => candidate.line === line);
    if (item) window.open(item.file_url, "_blank", "noopener");
  }

  async function save(closeAfter) {
    status.textContent = "Saving...";
    const selectedLines = items.filter((item) => item.selected).map((item) => item.line);
    try {
      const response = await fetch("/save", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ selected_lines: selectedLines, close: closeAfter }),
      });
      const data = await response.json();
      if (!response.ok || !data.ok) {
        throw new Error(data.error || response.statusText);
      }
      status.textContent = `Saved ${data.selected} selected photos. Preview below, then run: credit-check commit ${reviewArg} --go`;
      showPreview(false);
    } catch (error) {
      status.textContent = `Save failed: ${error.message}`;
    }
  }

  sections.addEventListener("change", (event) => {
    const checkbox = event.target.closest('input[type="checkbox"][data-line]');
    if (!checkbox) return;
    toggleLine(Number(checkbox.dataset.line));
  });

  sections.addEventListener("click", (event) => {
    const card = event.target.closest(".photo");
    if (!card) return;
    lastFocusedLine = Number(card.dataset.line);
    if (event.target.closest("a, input, label")) return;
    toggleLine(Number(card.dataset.line));
  });

  sections.addEventListener("focusin", (event) => {
    const card = event.target.closest(".photo");
    if (card) lastFocusedLine = Number(card.dataset.line);
  });

  sections.addEventListener("keydown", (event) => {
    const card = event.target.closest(".photo");
    if (!card || (event.key !== " " && event.key !== "Enter")) return;
    if (event.target.closest("a, input")) return;
    event.preventDefault();
    toggleLine(Number(card.dataset.line));
  });

  sections.addEventListener("load", (event) => {
    if (event.target.tagName !== "IMG") return;
    event.target.closest(".thumb").classList.add("image-loaded");
  }, true);

  sections.addEventListener("error", (event) => {
    if (event.target.tagName !== "IMG") return;
    event.target.closest(".thumb").classList.add("image-missing");
  }, true);

  document.addEventListener("keydown", (event) => {
    const typing = event.target.matches("input, textarea, select");
    if (event.key === "/" && !typing) {
      event.preventDefault();
      search.focus();
      search.select();
      return;
    }
    if (typing) return;
    if (event.key === "s") {
      event.preventDefault();
      save(false);
    } else if (event.key === "o") {
      const line = focusedLine();
      if (line !== null) {
        event.preventDefault();
        openLine(line);
      }
    } else if (event.key === " ") {
      const line = focusedLine();
      if (line !== null && document.activeElement.closest(".photo")) {
        event.preventDefault();
        toggleLine(line);
      }
    }
  });

  document.querySelector('[data-action="select-visible"]').addEventListener("click", () => {
    setSelection(visibleItems().map((item) => item.line), true);
  });
  document.querySelector('[data-action="clear-visible"]').addEventListener("click", () => {
    setSelection(visibleItems().map((item) => item.line), false);
  });
  document.querySelector('[data-action="select-all"]').addEventListener("click", () => {
    setSelection(items.map((item) => item.line), true);
  });
  document.querySelector('[data-action="clear-all"]').addEventListener("click", () => {
    setSelection(items.map((item) => item.line), false);
  });
  document.querySelector('[data-action="preview"]').addEventListener("click", () => showPreview(true));
  document.querySelector('[data-action="hide-preview"]').addEventListener("click", () => {
    previewPanel.hidden = true;
  });
  document.querySelector('[data-action="save"]').addEventListener("click", () => save(false));
  document.querySelector('[data-action="save-close"]').addEventListener("click", () => save(true));
  search.addEventListener("input", render);
  modeButtons.forEach((button) => {
    button.addEventListener("click", () => {
      currentMode = button.dataset.mode;
      status.textContent = currentMode === "selected"
        ? "Showing only your selected photos."
        : currentMode === "unselected"
          ? "Showing photos you have not selected yet."
          : "";
      render();
    });
  });

  render();
})();
</script>
</body>
</html>
""".replace("__REVIEW_JSON__", review_json).replace(
        "__REVIEW_ARG_JSON__", review_arg_json).replace(
        "__ITEMS_JSON__", items_json).replace(
        "__AMBIGUOUS_JSON__", ambiguous_json).replace(
        "__INITIAL_MODE_JSON__", initial_mode_json)

class LocalReviewServer(http.server.ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True

def review_web_handler(review, items, approvable, ambiguous_count=0, initial_mode="all"):
    page = web_review_html(review, approvable, ambiguous_count, initial_mode).encode("utf-8")

    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, fmt, *args):
            return

        def send_bytes(self, status, body, content_type):
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def send_json(self, status, payload):
            body = json.dumps(payload).encode("utf-8")
            self.send_bytes(status, body, "application/json; charset=utf-8")

        def same_origin(self):
            origin = self.headers.get("Origin")
            host = self.headers.get("Host")
            if host != self.server.review_host:
                self.send_json(403, {"ok": False, "error": "Host not allowed"})
                return False
            if origin and origin != self.server.review_origin:
                self.send_json(403, {"ok": False, "error": "Origin not allowed"})
                return False
            return True

        def do_GET(self):
            path = urllib.parse.urlparse(self.path).path
            if path in ("/", "/review"):
                self.send_bytes(200, page, "text/html; charset=utf-8")
            elif path == "/health":
                self.send_json(200, {"ok": True})
            else:
                self.send_json(404, {"ok": False, "error": "Not found"})

        def do_POST(self):
            path = urllib.parse.urlparse(self.path).path
            if path != "/save":
                self.send_json(404, {"ok": False, "error": "Not found"})
                return
            if not self.same_origin():
                return

            try:
                length = int(self.headers.get("Content-Length", "0") or "0")
                if length > 200000:
                    raise ValueError("Request too large")
                raw = self.rfile.read(length).decode("utf-8")
                data = json.loads(raw or "{}")

                current_items = parse_review_items(review)
                if review_items_signature(current_items) != self.server.review_signature:
                    raise ReviewChangedError(
                        "%s changed on disk. Reload the browser page before saving." %
                        os.path.basename(review))
                current_approvable = [item for item in current_items if item["target"]]
                allowed_lines = {item["line"] for item in current_approvable}

                selected = set()
                for line in data.get("selected_lines", []):
                    line = int(line)
                    if line not in allowed_lines:
                        raise ValueError("Unknown review item line: %s" % line)
                    selected.add(line)
                set_review_approvals(review, current_items, selected)
                self.server.review_signature = review_items_signature(
                    parse_review_items(review))
                self.server.saved_count = len(selected)
                self.send_json(200, {"ok": True, "selected": len(selected)})
                if data.get("close"):
                    threading.Thread(target=self.server.shutdown, daemon=True).start()
            except ReviewChangedError as e:
                self.send_json(409, {"ok": False, "error": str(e)})
            except ValueError as e:
                self.send_json(409, {"ok": False, "error": str(e)})
            except Exception as e:
                self.send_json(400, {"ok": False, "error": str(e)})

    return Handler

def browser_review_should_fallback(no_open=False):
    if not sys.stdin.isatty() or not sys.stdout.isatty():
        return True
    if no_open:
        return False
    if sys.platform.startswith("linux") and not (
            os.environ.get("DISPLAY") or os.environ.get("WAYLAND_DISPLAY") or
            os.environ.get("BROWSER")):
        return True
    return False

def review_file_web(review, port=0, open_browser=True, fallback_on_open_failure=False,
                    initial_mode="all"):
    if not os.path.exists(review):
        print("No review file found: %s. Choose Find your photos on Wikipedia first." % review)
        return False

    items = parse_review_items(review)
    approvable = [item for item in items if item["target"]]
    ambiguous_count = len([item for item in items if not item["target"]])
    if not items:
        print("%s has no photos in it. Run Find your photos on Wikipedia again." % review)
        return True
    if not approvable:
        if ambiguous_count:
            print("%s only has ambiguous photos. Edit the review file to move any real matches under a category before selecting them." % review)
        else:
            print("No photos to review in %s." % review)
        return True

    server = LocalReviewServer(
        (WEB_REVIEW_HOST, port),
        review_web_handler(review, items, approvable, ambiguous_count, initial_mode),
    )
    server.review_host = "%s:%d" % (WEB_REVIEW_HOST, server.server_address[1])
    server.review_origin = "http://%s" % server.review_host
    server.review_signature = review_items_signature(items)
    server.saved_count = None
    url = server.review_origin + "/"

    print("Opening local browser review for %d photo(s)." % len(approvable))
    print("Review file: %s" % os.path.abspath(review))
    print("URL: %s" % url)
    print("Use Save and close in the browser, or press Ctrl-C here to stop.")

    if open_browser:
        try:
            opened = webbrowser.open_new_tab(url)
        except Exception:
            opened = False
        if not opened:
            server.server_close()
            if fallback_on_open_failure:
                print("Browser review could not open; using terminal review instead.")
                return None
            print("Could not open a browser automatically. Open this URL manually: %s" % url)

    try:
        server.serve_forever(poll_interval=0.2)
    except KeyboardInterrupt:
        print("")
        print("Browser review stopped.")
    finally:
        server.server_close()

    if server.saved_count is not None:
        print("%d photo(s) selected. Next: credit-check plan %s" %
              (server.saved_count, review_path_arg(review)))
    return True

def review_page_items(approvable, page, page_size):
    start = page * page_size
    return approvable[start:start + page_size]

def review_file_with_pages(review, items, approvable):
    if Application is None:
        review_unavailable_message(review)
        return True

    page_size = review_page_size()
    state = {
        "selected": {item["line"] for item in approvable if item["checked"]},
        "page": 0,
        "cursor": 0,
        "message": "",
    }
    page_count = max(1, (len(approvable) + page_size - 1) // page_size)

    def clamp_state():
        state["page"] = max(0, min(state["page"], page_count - 1))
        page_items = review_page_items(approvable, state["page"], page_size)
        state["cursor"] = max(0, min(state["cursor"], max(0, len(page_items) - 1)))
        return page_items

    def current_page_items():
        return clamp_state()

    def current_item():
        page_items = current_page_items()
        if not page_items:
            return None
        return page_items[state["cursor"]]

    def page_bounds(page_items):
        start = state["page"] * page_size + 1
        end = start + len(page_items) - 1
        return start, end

    def set_message(text):
        state["message"] = text

    def render_review_screen():
        page_items = current_page_items()
        start, end = page_bounds(page_items)
        lines = [
            ("class:title", "Pick photos to add\n"),
            ("class:meta", "Photos %d-%d of %d | page %d/%d | %d selected\n" %
             (start, end, len(approvable), state["page"] + 1, page_count,
              len(state["selected"]))),
            ("class:help", "Space toggle  arrows move  n/p pages  m/c page  a/u all  o open  g gallery  v all gallery  s save  q quit\n\n"),
        ]

        for idx, item in enumerate(page_items):
            is_cursor = idx == state["cursor"]
            is_selected = item["line"] in state["selected"]
            cursor = ">" if is_cursor else " "
            mark = "X" if is_selected else " "
            uses = "[%d]" % item["uses"] if item["uses"] is not None else "[?]"
            line = "%s [%s] %s %s -> Category:%s\n" % (
                cursor, mark, uses, item["label"], item["target"])
            if is_cursor:
                style = "class:cursor"
            elif is_selected:
                style = "class:selected"
            else:
                style = ""
            lines.append((style, line))

        if state["message"]:
            lines.append(("", "\n"))
            lines.append(("class:message", state["message"] + "\n"))
        return lines

    kb = KeyBindings()

    def invalidate(event):
        event.app.invalidate()

    @kb.add("down")
    @kb.add("j")
    def _(event):
        page_items = current_page_items()
        if state["cursor"] < len(page_items) - 1:
            state["cursor"] += 1
        elif state["page"] < page_count - 1:
            state["page"] += 1
            state["cursor"] = 0
        invalidate(event)

    @kb.add("up")
    @kb.add("k")
    def _(event):
        if state["cursor"] > 0:
            state["cursor"] -= 1
        elif state["page"] > 0:
            state["page"] -= 1
            state["cursor"] = len(current_page_items()) - 1
        invalidate(event)

    @kb.add("n")
    @kb.add("right")
    def _(event):
        if state["page"] < page_count - 1:
            state["page"] += 1
            state["cursor"] = 0
        invalidate(event)

    @kb.add("p")
    @kb.add("left")
    def _(event):
        if state["page"] > 0:
            state["page"] -= 1
            state["cursor"] = 0
        invalidate(event)

    @kb.add(" ")
    @kb.add("enter")
    def _(event):
        item = current_item()
        if not item:
            return
        if item["line"] in state["selected"]:
            state["selected"].remove(item["line"])
        else:
            state["selected"].add(item["line"])
        invalidate(event)

    @kb.add("m")
    def _(event):
        state["selected"].update(item["line"] for item in current_page_items())
        set_message("Selected this page.")
        invalidate(event)

    @kb.add("c")
    def _(event):
        state["selected"].difference_update(item["line"] for item in current_page_items())
        set_message("Cleared this page.")
        invalidate(event)

    @kb.add("a")
    def _(event):
        state["selected"] = {item["line"] for item in approvable}
        set_message("Selected all photos.")
        invalidate(event)

    @kb.add("u")
    def _(event):
        state["selected"] = set()
        set_message("Cleared all photos.")
        invalidate(event)

    @kb.add("o")
    def _(event):
        item = current_item()
        if item:
            webbrowser.open_new_tab(commons_file_url(item["title"]))
            set_message("Opened current photo on Commons.")
        invalidate(event)

    @kb.add("g")
    def _(event):
        page_items = current_page_items()
        start, end = page_bounds(page_items)
        path = open_review_gallery(page_items, "Credit Check photos %d-%d" %
                                   (start, end), quiet=True)
        set_message("Opened page contact sheet: %s" % path)
        invalidate(event)

    @kb.add("v")
    def _(event):
        path = open_review_gallery(approvable, "Credit Check review - all photos",
                                   quiet=True)
        set_message("Opened full contact sheet: %s" % path)
        invalidate(event)

    @kb.add("s")
    def _(event):
        set_review_approvals(review, items, state["selected"])
        event.app.exit(result="save")

    @kb.add("q")
    @kb.add("c-c")
    def _(event):
        event.app.exit(result="quit")

    control = FormattedTextControl(render_review_screen, focusable=True)
    layout = Layout(Window(content=control, always_hide_cursor=True, wrap_lines=False))
    style = Style.from_dict({
        "title": "bold",
        "meta": "ansicyan",
        "help": "ansiblue",
        "cursor": "reverse",
        "selected": "ansigreen",
        "message": "ansiyellow",
    })
    app = Application(layout=layout, key_bindings=kb, full_screen=True,
                      mouse_support=False, style=style)
    result = app.run()
    if result == "save":
        approved = parse_approved(review, warn=False)
        print("Updated %s." % review)
        print("%d photo(s) selected. Next: credit-check plan %s" %
              (len(approved), review_path_arg(review)))
    else:
        print("No changes saved.")
    return True


# ---------------------------------------------------------------- commands

def resolve(args, name, env, default=None, required=False):
    val = getattr(args, name, None) or os.environ.get(env) or default
    if required and not val:
        sys.exit("Missing --%s (or %s). See --help." % (name.replace("_", "-"), env))
    return val

def cmd_scan(args):
    username = resolve(args, "username", "WIKI_USERNAME", required=True)
    author = resolve(args, "author", "WIKI_AUTHOR", required=True)
    by_cat = resolve(args, "by_category", "WIKI_BY_CATEGORY",
                     default="Photographs by %s" % author)
    of_cat = resolve(args, "of_category", "WIKI_OF_CATEGORY")
    qid = resolve(args, "qid", "WIKI_QID")
    review_format = infer_review_format(args)
    out = args.out or default_review_path(review_format)
    min_uses = scan_min_uses(args)
    english_only = scan_english_only(args)
    insource_user = scan_insource_user(args)
    no_derivatives = scan_no_derivatives(args)
    depth = scan_depth(args)
    scan_mode = getattr(args, "scan_mode", "both")
    include_by = scan_mode in ("both", "by")
    include_of = scan_mode in ("both", "of")
    include_ambiguous = scan_mode != "of"

    cl = Client()
    print("Config: user=%s author=%s\n  by-cat=[[Category:%s]]%s"
          % (username, author, by_cat,
             ("  of-cat=[[Category:%s]]" % of_cat) if of_cat else ""), file=sys.stderr)
    print("Discovering files...", file=sys.stderr)
    reasons = discover_titles(cl, username, author, insource_user)
    print("  %d possible matches. Fetching usage, categories, wikitext..." % len(reasons),
          file=sys.stderr)
    info = fetch_details(cl, reasons.keys(), by_cat, of_cat)

    depicts = set()
    if qid and of_cat:
        print("  checking SDC depicts (P180=%s)..." % qid, file=sys.stderr)
        depicts = fetch_depicts(cl, [r["pageid"] for r in info.values()], qid)

    by_list, of_list, amb_list = {}, {}, {}
    for title, rec in info.items():
        rec["reason"] = reasons.get(title, set())
        wp = rec["wp"]
        if english_only:
            wp = {k: v for k, v in wp.items() if v["lang"] == "en"}; rec["wp"] = wp
        if len(wp) < min_uses:
            continue
        route = route_record(rec, username, author, of_cat, depicts)
        if route == "by" and include_by:
            by_list[title] = rec
        elif route == "of" and include_of:
            of_list[title] = rec
        elif route == "ambiguous" and include_ambiguous:
            amb_list[title] = rec

    # derivative tracing: a crop that dropped your credit but cites a source
    # file that IS yours gets promoted from ambiguous into the by-list.
    if include_by and not no_derivatives and amb_list:
        promoted = resolve_derivatives(cl, amb_list, username, author, depth)
        for title, src in promoted.items():
            rec = amb_list.pop(title)
            if rec["in_by"]:
                continue
            rec["reason"] = set(rec.get("reason", set())) | {"derivative"}
            rec["derived_from"] = src
            by_list[title] = rec
        if promoted:
            print("  promoted %d derivative crop(s) via source chain." % len(promoted),
                  file=sys.stderr)

    meta = {
        "author": author,
        "by_category": by_cat,
        "of_category": of_cat,
        "include_by": include_by,
        "include_of": include_of,
        "include_ambiguous": include_ambiguous,
    }
    write_review(by_list, of_list, amb_list, meta, out, review_format)
    print("\nWrote %s" % out, file=sys.stderr)
    if include_by:
        print("  by  (photos you took, missing [[Category:%s]]): %d photos, used %d times"
              % (by_cat, len(by_list), sum(len(r["wp"]) for r in by_list.values())),
              file=sys.stderr)
    if of_cat and include_of:
        print("  of  (photos that depict you, missing [[Category:%s]]): %d photos"
              % (of_cat, len(of_list)), file=sys.stderr)
    if include_ambiguous:
        print("  ambiguous (authorship or category unclear): %d photos" % len(amb_list),
              file=sys.stderr)
    if not by_list and not of_list and not amb_list:
        print("  no missing-category photos found. You may already be caught up.",
              file=sys.stderr)


def login(cl, botuser, botpass):
    tok = cl.get({"action": "query", "meta": "tokens", "type": "login"})
    lgtoken = tok["query"]["tokens"]["logintoken"]
    res = cl.post({"action": "login"},
                  {"lgname": botuser, "lgpassword": botpass, "lgtoken": lgtoken},
                  retry_post=True)
    if res.get("login", {}).get("result") != "Success":
        sys.exit("Login failed: %s" % res.get("login", {}).get("result", res))
    return cl.get({"action": "query", "meta": "tokens"})["query"]["tokens"]["csrftoken"]

def load_approved(review, warn=True):
    try:
        approved = parse_approved(review, warn=warn)
    except FileNotFoundError:
        if warn:
            print("Review file not found: %s. Run credit-check scan first." % review)
        return []
    if not approved and warn:
        print("You haven't selected any photos in %s yet. Open review and pick the photos you want first." % review)
    return approved

def approved_or_exit(review):
    approved = load_approved(review)
    if not approved:
        sys.exit(1)
    return approved

def print_plan(approved, review, next_command=None):
    print("%d photo(s) selected in %s." % (len(approved), review))
    print("Dry run. Planned edits:")
    for t, cat in approved:
        print("   + [[Category:%s]]  ->  %s" % (cat, t))
    if next_command:
        print("\nRun %s to make these edits." % next_command)

def commons_category_url(cat):
    return "https://commons.wikimedia.org/wiki/" + urllib.parse.quote(
        ("Category:" + cat).replace(" ", "_"), safe=":/()-,")

def remaining_unselected_count(review):
    try:
        items = parse_review_items(review)
    except OSError:
        return None
    return len([item for item in items if item["target"] and not item["checked"]])

def print_commit_done_summary(added, skipped, failed, review, approved):
    print("")
    print("Done.")
    print("  Added category to %d photo(s)." % added)
    print("  Already present: %d" % skipped)
    print("  Failed: %d" % failed)

    cats = []
    seen = set()
    for _title, cat in approved:
        if cat not in seen:
            seen.add(cat)
            cats.append(cat)
    if cats:
        print("")
        print("Category page%s:" % ("" if len(cats) == 1 else "s"))
        for cat in cats:
            print("  %s" % commons_category_url(cat))

    remaining = remaining_unselected_count(review)
    if failed:
        print("")
        print("Some photos failed. Check the messages above, then run credit-check plan %s before trying again." %
              review_path_arg(review))
    elif remaining:
        print("")
        print("%d unchecked photo(s) remain in %s. Run credit-check review %s when you want to keep going." %
              (remaining, review, review_path_arg(review)))
    else:
        print("")
        print("All selected photos are handled.")

def cmd_plan(args):
    approved = approved_or_exit(args.review)
    print_plan(approved, args.review,
               "credit-check commit %s --go" % review_path_arg(args.review))

def cmd_commit(args):
    approved = approved_or_exit(args.review)
    if not args.go:
        print_plan(approved, args.review,
                   "credit-check commit %s --go" % review_path_arg(args.review))
        return

    print("%d photo(s) selected in %s." % (len(approved), args.review))

    botuser = args.botuser or os.environ.get("COMMONS_BOTUSER") \
        or input("Bot username (e.g. Jaydixit@categorize): ").strip()
    botpass = args.botpass or os.environ.get("COMMONS_BOTPASS") \
        or getpass.getpass("Bot password: ")

    cl = Client()
    csrf = login(cl, botuser, botpass)
    print("Logged in. Editing with %ss throttle...\n" % args.throttle)

    added = skipped = failed = 0
    for t, cat in approved:
        full = "Category:" + cat
        d = cl.get({"action": "query", "titles": t, "prop": "categories",
                    "clcategories": full, "cllimit": "1"})
        page = next(iter(d["query"]["pages"].values()))
        if page.get("categories"):
            print("  = already in [[%s]], skip: %s" % (full, t)); skipped += 1; continue
        try:
            res = cl.post({"action": "edit"},
                          {"title": t, "appendtext": "\n[[%s]]\n" % full,
                           "summary": args.summary + " ([[%s]])" % full, "token": csrf,
                           "assert": "user", "nocreate": "1", "maxlag": "5"})
        except (urllib.error.HTTPError, urllib.error.URLError, OSError) as e:
            print("  ! failed (network): %s (%s)" % (t, e)); failed += 1
            time.sleep(args.throttle)
            continue
        if res.get("edit", {}).get("result") == "Success":
            print("  + %s  ->  %s" % (full, t)); added += 1
        else:
            print("  ! failed: %s -> %s" % (t, res)); failed += 1
        time.sleep(args.throttle)
    print_commit_done_summary(added, skipped, failed, args.review, approved)


# ---------------------------------------------------------------- self-checks

SMOKE_USERNAME = "CreditCheckSmokeUserDefinitelyAbsent20260704"
SMOKE_AUTHOR = "Credit Check Smoke Author Definitely Absent 20260704"

def sample_review_data():
    rec = {
        "uploader": "SomeoneElse",
        "cats": {"Category:Example people"},
        "reason": {"credited"},
        "wp": {"en.wikipedia.org|Example": {
            "wiki": "en.wikipedia.org", "lang": "en", "title": "Example"}},
    }
    meta = {"author": "Test Person", "by_category": "Photographs by Test Person",
            "of_category": None}
    return {"File:Example.jpg": rec}, {}, {"File:Ambiguous.jpg": rec.copy()}, meta

def sample_of_review_data():
    rec = {
        "uploader": "SomeoneElse",
        "cats": {"Category:Example people"},
        "reason": {"depicts"},
        "wp": {"en.wikipedia.org|Example": {
            "wiki": "en.wikipedia.org", "lang": "en", "title": "Example"}},
    }
    meta = {
        "author": "Test Person",
        "by_category": "Photographs by Test Person",
        "of_category": "Test Person",
        "include_by": False,
        "include_of": True,
        "include_ambiguous": False,
    }
    return {}, {"File:Portrait.jpg": rec}, {}, meta

def check_equal(name, got, expected):
    if got != expected:
        raise AssertionError("%s: got %r, expected %r" % (name, got, expected))

def check_retry_policy():
    class FailingOpener:
        def __init__(self):
            self.calls = 0

        def open(self, url, data=None, timeout=60):
            self.calls += 1
            raise urllib.error.URLError("simulated lost response")

    old_sleep = time.sleep
    time.sleep = lambda seconds: None
    try:
        cl = Client()
        cl.opener = FailingOpener()
        try:
            cl._call({"action": "edit"}, data={"title": "File:X.jpg"}, tries=3)
        except urllib.error.URLError:
            pass
        check_equal("edit POST attempts", cl.opener.calls, 1)

        cl.opener = FailingOpener()
        try:
            cl._call({"action": "login"}, data={"lgname": "User"}, tries=3,
                     retry_post=True)
        except urllib.error.URLError:
            pass
        check_equal("retryable POST attempts", cl.opener.calls, 3)
    finally:
        time.sleep = old_sleep

def write_and_parse_sample(review_format, suffix):
    by_list, of_list, amb_list, meta = sample_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "review" + suffix)
        write_review(by_list, of_list, amb_list, meta, path, review_format)
        text = open(path, encoding="utf-8").read()
        if review_path_arg(path) not in text:
            raise AssertionError("review command did not include the review path")
        text = text.replace("- [ ] File:Example.jpg", "- [X] File:Example.jpg")
        text = text.replace("- [ ] File:Ambiguous.jpg", "- [X] File:Ambiguous.jpg")
        open(path, "w", encoding="utf-8").write(text)
        got = parse_approved(path, warn=False)
        check_equal("selected items", got,
                    [("File:Example.jpg", "Photographs by Test Person")])

def write_toggle_sample(review_format, suffix):
    by_list, of_list, amb_list, meta = sample_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "review" + suffix)
        write_review(by_list, of_list, amb_list, meta, path, review_format)
        items = parse_review_items(path)
        approvable = [item for item in items if item["target"]]
        ambiguous = [item for item in items if not item["target"]]
        check_equal("target review photos", len(approvable), 1)
        check_equal("ambiguous review photos", len(ambiguous), 1)

        set_review_approvals(path, items, {approvable[0]["line"]})
        check_equal("selected after terminal toggle", parse_approved(path, warn=False),
                    [("File:Example.jpg", "Photographs by Test Person")])

        items = parse_review_items(path)
        set_review_approvals(path, items, set())
        check_equal("selected after terminal untoggle", parse_approved(path, warn=False), [])

def check_load_approved_nonexit():
    by_list, of_list, amb_list, meta = sample_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        missing = os.path.join(td, "missing.md")
        check_equal("missing review selections", load_approved(missing, warn=False), [])

        path = os.path.join(td, "review.md")
        write_review(by_list, of_list, amb_list, meta, path, "markdown")
        check_equal("empty review selections", load_approved(path, warn=False), [])

def check_guided_review_state():
    old_cwd = os.getcwd()
    old_env = {key: os.environ.pop(key, None) for key in (
        "WIKI_USERNAME", "WIKI_AUTHOR", "WIKI_BY_CATEGORY", "WIKI_QID",
        "CREDIT_CHECK_DEV")}
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            state = review_workflow_state()
            check_equal("guided no-review state", state["exists"], False)
            check_equal("guided setup state", state["setup_complete"], False)
            check_equal("guided no-review label", review_state_label(state),
                        "Set up Credit Check to start")

            save_local_preferences({"username": "TestUser", "author": "Test Person"})
            state = review_workflow_state()
            check_equal("guided setup complete", state["setup_complete"], True)
            check_equal("guided no-review after setup", review_state_label(state),
                        "No review yet")

            by_list, of_list, amb_list, meta = sample_review_data()
            write_review(by_list, of_list, amb_list, meta, "review.md", "markdown")
            state = review_workflow_state()
            check_equal("guided review exists", state["exists"], True)
            check_equal("guided review total", state["total"], 1)
            check_equal("guided review ambiguous", state["ambiguous"], 1)
            check_equal("guided review selected", state["selected"], 0)

            items = parse_review_items("review.md")
            approvable = [item for item in items if item["target"]]
            set_review_approvals("review.md", items, {approvable[0]["line"]})
            state = review_workflow_state()
            check_equal("guided selected state", state["selected"], 1)
    finally:
        os.chdir(old_cwd)
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value

def check_guided_menu_dispatch():
    for value in ("self_test", "smoke", "scan_by", "scan_of", "review",
                  "review_selected", "plan", "settings", "add", "quit"):
        check_equal("guided dispatch %s" % value,
                    interactive_choice_action(value), value)
    for value in ("q", "quit", "exit"):
        check_equal("guided quit shortcut %s" % value,
                    interactive_choice_action(value), "quit")
    for value in ("1", "2", "3", "3b", "4", "5", "6", "9", "of"):
        check_equal("legacy guided input ignored %s" % value,
                    interactive_choice_action(value), None)

def check_guided_menu_visibility():
    old_cwd = os.getcwd()
    old_env = {key: os.environ.pop(key, None) for key in (
        "WIKI_USERNAME", "WIKI_AUTHOR", "WIKI_BY_CATEGORY", "WIKI_QID",
        "CREDIT_CHECK_DEV")}
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            save_local_preferences({"username": "TestUser", "author": "Test Person"})
            state = review_workflow_state()
            values = [value for _label, value, _desc in interactive_menu_actions(state)]
            if "self_test" in values or "smoke" in values:
                raise AssertionError("developer checks leaked into the default menu")
            if "scan_of" in values:
                raise AssertionError("photos-of-you action showed without a QID")

            save_local_preferences({"qid": "Q12345"})
            values = [value for _label, value, _desc in interactive_menu_actions(state)]
            if "scan_of" not in values:
                raise AssertionError("photos-of-you action did not show with a QID")

            os.environ["CREDIT_CHECK_DEV"] = "1"
            values = [value for _label, value, _desc in interactive_menu_actions(state)]
            if "self_test" not in values or "smoke" not in values:
                raise AssertionError("developer checks did not show in dev mode")
    finally:
        os.chdir(old_cwd)
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value
            else:
                os.environ.pop(key, None)

def check_review_preferences():
    old_cwd = os.getcwd()
    old_env = os.environ.pop(REVIEW_FORMAT_ENV, None)
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            args = argparse.Namespace(review_format=None, out=None)
            check_equal("default review format preference", infer_review_format(args), "markdown")
            check_equal("default guided review path", existing_review_default(), "review.md")
            open("review.org", "w", encoding="utf-8").close()
            check_equal("existing org review default", existing_review_default(), "review.org")
            os.remove("review.org")
            check_equal("default user-page source search",
                        scan_insource_user(argparse.Namespace(insource_user=None)), True)

            with open(PREFERENCE_FILE, "w", encoding="utf-8") as f:
                json.dump({
                    "review_format": "org",
                    "min_uses": "3",
                    "english_only": True,
                    "match_user_page_source": False,
                    "source_depth": "4",
                    "review_page_size": 12,
                    "review_path": "custom-review.org",
                }, f)
            check_equal("local org review preference", infer_review_format(args), "org")
            check_equal("local min uses preference",
                        preference_int("min_uses", default=1), 3)
            check_equal("local english-only preference",
                        preference_bool("english_only", default=False), True)
            check_equal("local source-search opt-out",
                        scan_insource_user(argparse.Namespace(insource_user=None)), False)
            check_equal("explicit source-search opt-in",
                        scan_insource_user(argparse.Namespace(insource_user=True)), True)
            check_equal("explicit source-search opt-out",
                        scan_insource_user(argparse.Namespace(insource_user=False)), False)
            check_equal("local source-depth preference",
                        preference_int("depth", "source_depth", default=2), 4)
            check_equal("local page-size preference", review_page_size(), 12)
            check_equal("local review-path preference",
                        preferred_review_path("org"), "custom-review.org")
            check_equal("missing preferred review default",
                        existing_review_default(), "custom-review.org")
            open("review.md", "w", encoding="utf-8").close()
            check_equal("existing review beats missing preferred",
                        existing_review_default(), "review.md")
            open("custom-review.org", "w", encoding="utf-8").close()
            check_equal("existing preferred review wins",
                        existing_review_default(), "custom-review.org")
            save_local_preferences({"username": "SavedUser", "qid": ""})
            check_equal("local setting saved",
                        local_preferences().get("username"), "SavedUser")
            check_equal("empty local setting removed",
                        "qid" in local_preferences(), False)
            check_equal(
                "output extension beats local preference",
                infer_review_format(argparse.Namespace(review_format=None, out="review.md")),
                "markdown",
            )
    finally:
        os.chdir(old_cwd)
        if old_env is not None:
            os.environ[REVIEW_FORMAT_ENV] = old_env

def check_of_only_review_sections():
    by_list, of_list, amb_list, meta = sample_of_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "review.md")
        write_review(by_list, of_list, amb_list, meta, path, "markdown")
        text = open(path, encoding="utf-8").read()
        if "# Add to [Category:Photographs by Test Person]" in text:
            raise AssertionError("of-only review included the by-photo section")
        if "# Ambiguous" in text:
            raise AssertionError("of-only review included the ambiguous section")
        if "# Add to [Category:Test Person]" not in text:
            raise AssertionError("of-only review omitted the subject category section")

def check_review_gallery_html():
    item = {
        "title": "File:Example photo.jpg",
        "label": "Example photo.jpg",
        "uses": 2,
        "target": "Photographs by Test Person",
        "checked": True,
    }
    text = review_gallery_html([item], "Test gallery")
    for needle in (
            "Test gallery",
            "Example photo.jpg",
            "Special:FilePath/Example_photo.jpg?width=320",
            "Open on Commons",
            "Selected"):
        if needle not in text:
            raise AssertionError("gallery missing %r" % needle)

def check_web_review_html():
    item = {
        "line": 12,
        "title": "File:Example photo.jpg",
        "label": "Example photo.jpg",
        "uses": 2,
        "target": "Photographs by Test Person",
        "checked": False,
    }
    text = web_review_html("review.md", [item], ambiguous_count=2)
    for needle in (
            "Review photos for Category",
            "window.CREDIT_CHECK_ITEMS",
            "window.CREDIT_CHECK_REVIEW_ARG",
            "window.CREDIT_CHECK_AMBIGUOUS_COUNT = 2",
            "window.CREDIT_CHECK_INITIAL_MODE",
            "ambiguous ${noun} not shown here",
            "Photos credited to you, missing this category",
            "Special:FilePath/Example_photo.jpg?width=420",
            "Select visible",
            "data-mode=\"selected\"",
            "Preview edits",
            "credit-check commit ${reviewArg} --go",
            "Shortcuts: / search, Space select, o open, s save",
            "Save and close",
            'fetch("/save"'):
        if needle not in text:
            raise AssertionError("web review missing %r" % needle)

    selected_text = web_review_html("review.md", [item], initial_mode="selected")
    if 'window.CREDIT_CHECK_INITIAL_MODE = "selected"' not in selected_text:
        raise AssertionError("web review selected-only mode was not embedded")

def check_commit_summary_helpers():
    check_equal("category url",
                commons_category_url("Photographs by Test Person"),
                "https://commons.wikimedia.org/wiki/Category:Photographs_by_Test_Person")
    by_list, of_list, amb_list, meta = sample_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "review.md")
        write_review(by_list, of_list, amb_list, meta, path, "markdown")
        check_equal("remaining before selection", remaining_unselected_count(path), 1)
        items = parse_review_items(path)
        approvable = [item for item in items if item["target"]]
        set_review_approvals(path, items, {approvable[0]["line"]})
        check_equal("remaining after selection", remaining_unselected_count(path), 0)

def check_web_review_save():
    by_list, of_list, amb_list, meta = sample_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "review.md")
        write_review(by_list, of_list, amb_list, meta, path, "markdown")
        items = parse_review_items(path)
        approvable = [item for item in items if item["target"]]
        server = LocalReviewServer(
            (WEB_REVIEW_HOST, 0),
            review_web_handler(path, items, approvable),
        )
        server.review_origin = "http://%s:%d" % (
            WEB_REVIEW_HOST, server.server_address[1])
        server.review_host = "%s:%d" % (WEB_REVIEW_HOST, server.server_address[1])
        server.review_signature = review_items_signature(items)
        server.saved_count = None
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            body = json.dumps({
                "selected_lines": [approvable[0]["line"]],
                "close": True,
            }).encode("utf-8")
            req = urllib.request.Request(
                server.review_origin + "/save",
                data=body,
                headers={
                    "Content-Type": "application/json",
                    "Origin": server.review_origin,
                },
            )
            with urllib.request.urlopen(req, timeout=5) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            check_equal("web save response", data["ok"], True)
            thread.join(5)
            if thread.is_alive():
                raise AssertionError("web review server did not close")
            check_equal("web save selected count", server.saved_count, 1)
            check_equal("web save selected items", parse_approved(path, warn=False),
                        [("File:Example.jpg", "Photographs by Test Person")])
        finally:
            if thread.is_alive():
                server.shutdown()
                thread.join(5)
            server.server_close()

def check_web_review_stale_save():
    by_list, of_list, amb_list, meta = sample_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "review.md")
        write_review(by_list, of_list, amb_list, meta, path, "markdown")
        items = parse_review_items(path)
        approvable = [item for item in items if item["target"]]
        server = LocalReviewServer(
            (WEB_REVIEW_HOST, 0),
            review_web_handler(path, items, approvable),
        )
        server.review_origin = "http://%s:%d" % (
            WEB_REVIEW_HOST, server.server_address[1])
        server.review_host = "%s:%d" % (WEB_REVIEW_HOST, server.server_address[1])
        server.review_signature = review_items_signature(items)
        server.saved_count = None
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            set_review_approvals(path, items, {approvable[0]["line"]})
            body = json.dumps({
                "selected_lines": [],
                "close": True,
            }).encode("utf-8")
            req = urllib.request.Request(
                server.review_origin + "/save",
                data=body,
                headers={
                    "Content-Type": "application/json",
                    "Origin": server.review_origin,
                },
            )
            try:
                urllib.request.urlopen(req, timeout=5)
                raise AssertionError("stale browser save unexpectedly succeeded")
            except urllib.error.HTTPError as e:
                check_equal("stale save status", e.code, 409)
                data = json.loads(e.read().decode("utf-8"))
                if "changed on disk" not in data.get("error", ""):
                    raise AssertionError("stale save error was not friendly")
            check_equal("stale save did not rewrite selections",
                        parse_approved(path, warn=False),
                        [("File:Example.jpg", "Photographs by Test Person")])
        finally:
            server.shutdown()
            thread.join(5)
            server.server_close()

def check_scan_routing():
    rec = {
        "text": "{{Information\n|description=Test Person\n}}",
        "pageid": 123,
        "in_by": False,
        "in_of": False,
    }
    check_equal("depicts missing of-category",
                route_record(rec, "TestUser", "Test Person", "Test Person", {123}), "of")

    rec_done = dict(rec, in_of=True)
    check_equal("depicts already in of-category",
                route_record(rec_done, "TestUser", "Test Person", "Test Person", {123}), None)

    rec_by = dict(rec, text="{{Information\n|author=Test Person\n}}", in_by=False)
    check_equal("by missing category",
                route_record(rec_by, "TestUser", "Test Person", "Test Person", {123}), "by")

    rec_amb = dict(rec, pageid=456)
    check_equal("not by or depicts",
                route_record(rec_amb, "TestUser", "Test Person", "Test Person", {123}),
                "ambiguous")

def run_check(name, func, failures):
    try:
        func()
        print("ok - %s" % name)
    except Exception as e:
        failures.append((name, e))
        print("not ok - %s: %s" % (name, e))

def cmd_self_test(args):
    failures = []

    def formats():
        check_equal("md alias", normalize_review_format("md"), "markdown")
        check_equal("org alias", normalize_review_format("org-mode"), "org")
        check_equal("default path", default_review_path("markdown"), "review.md")

    def authorship():
        check_equal("photographer field",
                    is_by("{{Information\n|photographer=Test Person\n}}",
                          "TestUser", "Test Person"),
                    True)
        check_equal("author user link",
                    is_by("{{Information\n|author=[[User:TestUser|Test Person]]\n}}",
                          "TestUser", "Test Person"),
                    True)
        check_equal("author alias display name",
                    is_by("{{Information\n|author=[[User:SomeAlias|Test Person]]\n}}",
                          "TestUser", "Test Person"),
                    True)
        check_equal("author field does not swallow description",
                    is_by("{{Information\n|author=[[User:SomeAlias|Somebody Else]]\n"
                          "|description=Test Person\n}}",
                          "TestUser", "Test Person"),
                    False)
        check_equal("description only",
                    is_by("{{Information\n|description=Test Person\n}}",
                          "TestUser", "Test Person"),
                    False)
        check_equal("author substring is not enough",
                    is_by("{{Information\n|author=Ajay Dixitson\n}}",
                          "TestUser", "Jay Dixit"),
                    False)
        check_equal("subject word boundary positive",
                    name_as_subject("{{Information\n|description=Jay Dixit\n}}",
                                    "Jay Dixit"),
                    True)
        check_equal("subject substring is not enough",
                    name_as_subject("{{Information\n|description=Ajay Dixitson\n}}",
                                    "Jay Dixit"),
                    False)

    run_check("review format preferences", formats, failures)
    run_check("local review-format preference file", check_review_preferences, failures)
    run_check("HTTP POST retry policy", check_retry_policy, failures)
    run_check("authorship classification", authorship, failures)
    run_check("Markdown review write/parse", lambda: write_and_parse_sample("markdown", ".md"), failures)
    run_check("org review write/parse", lambda: write_and_parse_sample("org", ".org"), failures)
    run_check("of-you review sections", check_of_only_review_sections, failures)
    run_check("browser review gallery", check_review_gallery_html, failures)
    run_check("local browser review app", check_web_review_html, failures)
    run_check("local browser review save", check_web_review_save, failures)
    run_check("local browser stale-save guard", check_web_review_stale_save, failures)
    run_check("commit completion helpers", check_commit_summary_helpers, failures)
    run_check("Markdown terminal review toggle", lambda: write_toggle_sample("markdown", ".md"), failures)
    run_check("org terminal review toggle", lambda: write_toggle_sample("org", ".org"), failures)
    run_check("interactive selected-photo loading", check_load_approved_nonexit, failures)
    run_check("guided review state", check_guided_review_state, failures)
    run_check("guided menu dispatch", check_guided_menu_dispatch, failures)
    run_check("guided menu visibility", check_guided_menu_visibility, failures)
    run_check("scan routing classification", check_scan_routing, failures)

    if failures:
        sys.exit("%d self-test(s) failed." % len(failures))
    print("Self-test passed.")

def cmd_smoke(args):
    review_format = infer_review_format(args)
    temp_ctx = None
    temp_dir = None
    if args.out:
        out = args.out
    else:
        if args.keep:
            temp_dir = tempfile.mkdtemp(prefix="credit-check-smoke.")
        else:
            temp_ctx = tempfile.TemporaryDirectory(prefix="credit-check-smoke.")
            temp_dir = temp_ctx.name
        out = os.path.join(temp_dir, default_review_path(review_format))

    scan_args = argparse.Namespace(
        username=SMOKE_USERNAME, author=SMOKE_AUTHOR, by_category=None,
        of_category=None, qid=None, insource_user=False, no_derivatives=True,
        depth=0, english_only=False, min_uses=1, review_format=review_format,
        out=out, scan_mode="by")
    cmd_scan(scan_args)
    if not os.path.exists(out):
        sys.exit("Smoke test failed: expected review file was not written: %s" % out)
    if parse_approved(out):
        sys.exit("Smoke test failed: empty review unexpectedly had selected photos.")
    print("Smoke test passed: wrote %s" % out)

    if not args.keep and not args.out:
        temp_ctx.cleanup()
        print("Temporary smoke review removed. Use --keep or --out to inspect it.")


# ---------------------------------------------------------------- interactive app

PLAIN_PROMPTS_ENV = "CREDIT_CHECK_PLAIN"
PROMPT_MARKER = ""

def interactive_dev_mode():
    return preference_bool("dev_menu", default=False) or preference_bool(
        "dev", default=False) or os.environ.get("CREDIT_CHECK_DEV") in (
            "1", "true", "TRUE", "yes", "YES", "on", "ON")

def has_subject_scan_settings():
    return bool(identity_default("qid", "WIKI_QID"))

def fancy_prompts_available():
    return (questionary is not None
            and sys.stdin.isatty()
            and sys.stdout.isatty()
            and not os.environ.get(PLAIN_PROMPTS_ENV))

def ask_question(q):
    answer = q.ask()
    if answer is None:
        sys.exit(130)
    return answer

def prompt_text(label, default=None, required=False):
    if fancy_prompts_available():
        while True:
            val = ask_question(questionary.text(label, default=default or "",
                                               qmark=PROMPT_MARKER)).strip()
            if not val and default is not None:
                val = default
            if val or not required:
                return val or None
            print("Required.")

    while True:
        suffix = " [%s]" % default if default else ""
        val = input("%s%s: " % (label, suffix)).strip()
        if not val and default is not None:
            val = default
        if val or not required:
            return val or None
        print("Required.")

def prompt_yes_no(label, default=False):
    if fancy_prompts_available():
        return bool(ask_question(questionary.confirm(label, default=default,
                                                     qmark=PROMPT_MARKER)))

    suffix = " [Y/n]" if default else " [y/N]"
    while True:
        val = input(label + suffix + ": ").strip().lower()
        if not val:
            return default
        if val in ("y", "yes"):
            return True
        if val in ("n", "no"):
            return False
        print("Please answer y or n.")

def prompt_int(label, default):
    while True:
        val = prompt_text(label, str(default))
        try:
            return int(val)
        except ValueError:
            print("Please enter a number.")

def existing_review_default():
    preferred = preference_value("review_path", "out")
    candidates = []
    if preferred:
        candidates.append(preferred)
    candidates += ["review.md", "review.org"]
    seen = set()
    for path in candidates:
        if not path or path in seen:
            continue
        seen.add(path)
        if os.path.exists(path):
            return path
    if preferred:
        return preferred
    fmt = normalize_review_format(
        os.environ.get(REVIEW_FORMAT_ENV) or preferred_review_format() or "markdown")
    return default_review_path(fmt)

def setup_complete():
    return bool(identity_default("username", "WIKI_USERNAME")
                and identity_default("author", "WIKI_AUTHOR"))

def guided_review_path():
    review = existing_review_default()
    if not os.path.exists(review):
        print("No review file found. Choose Find your photos on Wikipedia first.")
        return None
    return review

def open_review_from_guided_flow(review, initial_mode="all"):
    if browser_review_should_fallback(False):
        print("Browser review is not available here; using terminal review instead.")
        return review_file_interactive(review)
    ok = review_file_web(review, fallback_on_open_failure=True, initial_mode=initial_mode)
    if ok is None:
        return review_file_interactive(review)
    return ok

def review_workflow_state():
    review = existing_review_default()
    state = {
        "review": review,
        "exists": os.path.exists(review),
        "total": 0,
        "selected": 0,
        "ambiguous": 0,
        "setup_complete": setup_complete(),
    }
    if not state["exists"]:
        return state
    try:
        items = parse_review_items(review)
        state["total"] = len([item for item in items if item["target"]])
        state["ambiguous"] = len([item for item in items if not item["target"]])
        state["selected"] = len(parse_approved(review, warn=False))
    except OSError:
        state["exists"] = False
    return state

def review_state_label(state):
    if not state["setup_complete"] and not state["exists"]:
        return "Set up Credit Check to start"
    if not state["exists"]:
        return "No review yet"
    prefix = "" if state["setup_complete"] else "Setup incomplete · "
    if state["total"] == 0:
        return "%s%s has no photos to review" % (prefix, state["review"])
    text = "%d photos found · %d selected" % (state["total"], state["selected"])
    if state["ambiguous"]:
        text += " · %d ambiguous" % state["ambiguous"]
    return prefix + text

def review_unavailable_message(review):
    if questionary is None or Application is None:
        print("Terminal review needs questionary and prompt_toolkit. The installed pipx "
              "command has them; otherwise tick [X] by editing %s." % review)
    elif not sys.stdin.isatty() or not sys.stdout.isatty():
        print("Terminal checkbox review needs an interactive terminal. Tick [X] by editing %s, "
              "or run credit-check review from a terminal." % review)
    else:
        print("Terminal checkbox review is disabled because %s is set. Tick [X] by editing %s."
              % (PLAIN_PROMPTS_ENV, review))

def review_file_interactive(review):
    if not os.path.exists(review):
        print("No review file found: %s. Choose Find your photos on Wikipedia first." % review)
        return False

    items = parse_review_items(review)
    approvable = [item for item in items if item["target"]]
    if not items:
        print("%s has no photos in it. Run Find your photos on Wikipedia again." % review)
        return True
    if not approvable:
        ambiguous_count = len([item for item in items if not item["target"]])
        if ambiguous_count:
            print("%s only has ambiguous photos. Edit the review file to move any real matches under a category before selecting them." % review)
        else:
            print("No photos to review in %s." % review)
        return True

    if not fancy_prompts_available():
        review_unavailable_message(review)
        return True

    return review_file_with_pages(review, items, approvable)

def cmd_review(args):
    review = args.review or existing_review_default()
    initial_mode = "selected" if getattr(args, "selected", False) else "all"
    if args.terminal:
        ok = review_file_interactive(review)
    elif browser_review_should_fallback(args.no_open):
        print("Browser review is not available here; using terminal review instead.")
        ok = review_file_interactive(review)
    else:
        ok = review_file_web(review, port=args.port, open_browser=not args.no_open,
                             fallback_on_open_failure=True, initial_mode=initial_mode)
        if ok is None:
            ok = review_file_interactive(review)
    if not ok:
        sys.exit(1)

def cmd_web(args):
    review = args.review or existing_review_default()
    initial_mode = "selected" if getattr(args, "selected", False) else "all"
    if not review_file_web(review, port=args.port, open_browser=not args.no_open,
                           initial_mode=initial_mode):
        sys.exit(1)

def interactive_scan(scan_mode="by"):
    username = prompt_text(
        "Commons username",
        identity_default("username", "WIKI_USERNAME"),
        required=True)
    author = prompt_text(
        "Your name as it's credited on Commons",
        identity_default("author", "WIKI_AUTHOR"),
        required=True)
    by_default = identity_default(
        "by_category", "WIKI_BY_CATEGORY", "Photographs by %s" % author)
    of_cat = qid = None

    if scan_mode == "of":
        by_cat = by_default
        of_cat = prompt_text(
            "Category for photos of you",
            identity_default("of_category", "WIKI_OF_CATEGORY", author),
            required=True)
        qid = prompt_text(
            "Your Wikidata ID (turns on 'photos of you' detection)",
            identity_default("qid", "WIKI_QID"),
            required=True)
    else:
        by_cat = prompt_text("Your photographer category", by_default, required=True)

    updates = {
        "username": username,
        "author": author,
        "by_category": by_cat,
    }
    if scan_mode == "of":
        updates.update({"of_category": of_cat, "qid": qid})
    save_local_preferences(updates)

    review_format = infer_review_format(argparse.Namespace(review_format=None, out=None))
    out = preferred_review_path(review_format)
    min_uses = preference_int("min_uses", "minimum_wikipedia_uses", default=1)
    english_only = preference_bool("english_only", default=False)
    insource_user = preference_bool("insource_user", "match_user_page_source", default=True)
    trace_derivatives = preference_bool("trace_derivatives", "follow_crops", default=True)
    depth = preference_int("depth", "source_depth", default=2)

    args = argparse.Namespace(
        username=username, author=author, by_category=by_cat, of_category=of_cat,
        qid=qid, insource_user=insource_user, no_derivatives=not trace_derivatives,
        depth=depth, english_only=english_only, min_uses=min_uses,
        review_format=review_format, out=out, scan_mode=scan_mode)
    cmd_scan(args)
    if sys.stdin.isatty():
        open_review_from_guided_flow(out)

def interactive_settings():
    username = prompt_text(
        "Commons username",
        identity_default("username", "WIKI_USERNAME"),
        required=True)
    author = prompt_text(
        "Your name as it's credited on Commons",
        identity_default("author", "WIKI_AUTHOR"),
        required=True)
    by_cat = prompt_text(
        "Your photographer category",
        identity_default("by_category", "WIKI_BY_CATEGORY",
                         "Photographs by %s" % author),
        required=True)
    print("")
    print("Optional: set your Wikidata ID to also find portraits of you taken by other people.")
    of_cat = prompt_text(
        "Category for photos of you",
        identity_default("of_category", "WIKI_OF_CATEGORY", author),
        required=False)
    qid = prompt_text(
        "Your Wikidata ID",
        identity_default("qid", "WIKI_QID"),
        required=False)
    save_local_preferences({
        "username": username,
        "author": author,
        "by_category": by_cat,
        "of_category": of_cat,
        "qid": qid,
    })
    print("Saved settings to %s." % PREFERENCE_FILE)

def interactive_review(initial_mode="all"):
    review = guided_review_path()
    if review:
        open_review_from_guided_flow(review, initial_mode=initial_mode)

def interactive_plan():
    review = guided_review_path()
    if not review:
        return
    approved = load_approved(review)
    if not approved:
        print("Opening review so you can pick photos first.")
        open_review_from_guided_flow(review)
        return
    print_plan(approved, review,
               "credit-check commit %s --go" % review_path_arg(review))

def interactive_preview_and_commit():
    review = guided_review_path()
    if not review:
        return
    approved = load_approved(review)
    if not approved:
        print("Opening review so you can pick photos first.")
        open_review_from_guided_flow(review)
        return
    print_plan(approved, review,
               "credit-check commit %s --go" % review_path_arg(review))
    print("")
    print("This will edit Commons file pages.")
    if not prompt_yes_no("Actually make these edits now?", False):
        print("No edits made.")
        return
    args = argparse.Namespace(review=review, go=True, summary=(
        "Add photographer/subject category (own work in use on Wikipedia)"),
        throttle=5.0, botuser=None, botpass=None)
    cmd_commit(args)

def interactive_commit():
    interactive_preview_and_commit()

def interactive_menu_actions(state):
    if not state["setup_complete"]:
        primary_value = "settings"
        primary_label = "Set up Credit Check"
        primary_desc = "Save your Commons account, credited name, and photographer category."
    elif not state["exists"]:
        primary_value = "scan_by"
        primary_label = "Find your photos on Wikipedia"
        primary_desc = "Search Commons for credited photos missing your category."
    elif state["selected"]:
        primary_value = "add"
        primary_label = "Add your selected photos to Commons"
        primary_desc = "Show the exact edits, then confirm before changing Commons."
    else:
        primary_value = "review"
        primary_label = "Review found photos"
        primary_desc = "Open the browser contact sheet and pick photos."
    actions = [(primary_label, primary_value, primary_desc)]
    if primary_value != "scan_by":
        actions.append((
            "Find your photos on Wikipedia",
            "scan_by",
            "Search Commons for credited photos missing your category.",
        ))
    elif state["exists"]:
        actions.append((
            "Find your photos again",
            "scan_by",
            "Run a fresh scan and replace the local review file.",
        ))
    if state["exists"] and primary_value != "review":
        actions.append((
            "Review found photos",
            "review",
            "Open a local browser contact sheet and save the photos you pick.",
        ))
    if state["selected"]:
        actions.append((
            "Review selected photos",
            "review_selected",
            "Open the browser contact sheet showing only what you picked.",
        ))
    if primary_value != "settings":
        actions.append((
            "Settings",
            "settings",
            "Save your name, Commons account, and categories for this folder.",
        ))
    if state["selected"]:
        actions.append((
            "Preview edits in the terminal",
            "plan",
            "Show exactly which Commons pages would change.",
        ))
    if has_subject_scan_settings():
        actions.append((
            "Find photos of you by other people",
            "scan_of",
            "Use your Wikidata ID to add portraits to your subject category.",
        ))
    if interactive_dev_mode():
        actions += [
            ("Run local tool checks", "self_test",
             "Verify parsing, review files, routing, and retry behavior."),
            ("Run a read-only Commons test", "smoke",
             "Confirm Commons access without editing anything."),
        ]
    actions.append(("Quit", "quit", ""))
    return actions

def interactive_menu_choice():
    state = review_workflow_state()
    state_label = review_state_label(state)
    actions = interactive_menu_actions(state)

    if fancy_prompts_available():
        print("")
        choices = [
            questionary.Separator(" "),
            questionary.Separator("  " + state_label),
            questionary.Separator(" "),
        ]
        for idx, (label, value, desc) in enumerate(actions):
            if idx and value in ("scan_of", "self_test", "quit"):
                choices.append(questionary.Separator(" "))
            choices.append(questionary.Choice(label, value=value, description=desc))
        choices.append(questionary.Separator(" "))
        return ask_question(questionary.select(
            "Choose an action",
            qmark=PROMPT_MARKER,
            choices=choices,
        ))

    print("")
    print("Credit Check status: %s" % state_label)
    print("")
    print("Choose an action")
    print("")
    for idx, (label, _value, _desc) in enumerate(actions, start=1):
        print("%d. %s" % (idx, label))
    print("")
    answer = prompt_text("Choose", "1")
    if answer and answer.isdigit():
        index = int(answer)
        if 1 <= index <= len(actions):
            return actions[index - 1][1]
    for label, value, _desc in actions:
        if answer == value or (answer and answer.lower() == label.lower()):
            return value
    return answer

def interactive_choice_action(choice):
    if choice in ("self_test", "smoke", "scan_by", "scan_of", "review",
                  "review_selected", "plan", "settings", "add", "quit"):
        return choice
    if str(choice).lower() in ("q", "quit", "exit"):
        return "quit"
    return None

def cmd_interactive(args):
    print("Credit Check")
    print("")
    print("Credit Check is a free tool from WikiPortraits that")
    print("searches Wikipedia to find articles that feature your")
    print("photos, then adds those photos (or a subset) to a")
    print("category page on Wikimedia Commons — using a category")
    print('name like "Photographs by Jay Dixit" — so you can easily')
    print("keep track of which Wikipedia articles use your photos.")
    if not setup_complete():
        print("")
        print("First step: save your Commons account and credited name.")
    while True:
        choice = interactive_menu_choice()
        action = interactive_choice_action(choice)
        if action == "self_test":
            cmd_self_test(argparse.Namespace())
        elif action == "smoke":
            cmd_smoke(argparse.Namespace(review_format=None, out=None, keep=False))
        elif action == "scan_by":
            interactive_scan()
        elif action == "scan_of":
            interactive_scan("of")
        elif action == "review":
            interactive_review()
        elif action == "review_selected":
            interactive_review(initial_mode="selected")
        elif action == "plan":
            interactive_plan()
        elif action == "settings":
            interactive_settings()
        elif action == "add":
            interactive_preview_and_commit()
        elif action == "quit":
            return
        else:
            print("Choose one of the listed actions.")


# ---------------------------------------------------------------- CLI

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.set_defaults(func=cmd_interactive)
    sub = ap.add_subparsers(dest="cmd")

    i = sub.add_parser("interactive", help="start the guided command-line app")
    i.set_defaults(func=cmd_interactive)

    s = sub.add_parser("scan", help="find your photos and write review.md")
    s.add_argument("--username"); s.add_argument("--author")
    s.add_argument("--by-category", dest="by_category")
    s.add_argument("--of-category", dest="of_category")
    s.add_argument("--qid")
    s.add_argument("--insource-user", dest="insource_user", action="store_true",
                   default=None,
                   help="also match files whose source contains User:<username> (default)")
    s.add_argument("--no-insource-user", dest="insource_user", action="store_false",
                   help="skip User:<username> source-text discovery")
    s.add_argument("--no-derivatives", action="store_true", default=None,
                   help="skip source-chain tracing of crops that dropped your credit")
    s.add_argument("--depth", type=int, default=None,
                   help="how many source hops to follow when tracing derivatives (default: 2)")
    s.add_argument("--english-only", action="store_true", default=None)
    s.add_argument("--min-uses", type=int, default=None)
    s.add_argument("--review-format", choices=["markdown", "md", "org"],
                   help="review format override (default markdown; %s can set org)" %
                   PREFERENCE_FILE)
    s.add_argument("--out")
    s.set_defaults(func=cmd_scan)

    r = sub.add_parser("review", help="pick photos from a review file in your browser")
    r.add_argument("review", nargs="?", help="review file (default: review.md or review.org)")
    r.add_argument("--terminal", action="store_true",
                   help="use the keyboard-only terminal reviewer instead of the browser")
    r.add_argument("--port", type=int, default=0,
                   help="local browser review port (default: choose a free port)")
    r.add_argument("--no-open", action="store_true",
                   help="print the local review URL instead of opening a browser")
    r.add_argument("--selected", action="store_true",
                   help="open the browser in selected-only review mode")
    r.set_defaults(func=cmd_review)

    w = sub.add_parser("web", help="open the local browser photo picker")
    w.add_argument("review", nargs="?", help="review file (default: review.md or review.org)")
    w.add_argument("--port", type=int, default=0,
                   help="local browser review port (default: choose a free port)")
    w.add_argument("--no-open", action="store_true",
                   help="print the local review URL instead of opening a browser")
    w.add_argument("--selected", action="store_true",
                   help="open the browser in selected-only review mode")
    w.set_defaults(func=cmd_web)

    p = sub.add_parser("plan", help="preview the edits for the photos you checked")
    p.add_argument("review")
    p.set_defaults(func=cmd_plan)

    c = sub.add_parser("commit", help="add your category to the photos you picked")
    c.add_argument("review")
    c.add_argument("--go", action="store_true", help="actually edit (default: dry run)")
    c.add_argument("--summary", default="Add photographer/subject category (own work in use on Wikipedia)")
    c.add_argument("--throttle", type=float, default=5.0)
    c.add_argument("--botuser"); c.add_argument("--botpass")
    c.set_defaults(func=cmd_commit)

    st = sub.add_parser("self-test", help="run local parser and review-format checks")
    st.set_defaults(func=cmd_self_test)

    sm = sub.add_parser("smoke", help="run a read-only Commons smoke test")
    sm.add_argument("--review-format", choices=["markdown", "md", "org"],
                    help="review file format for the smoke review (default markdown)")
    sm.add_argument("--out", help="write smoke review to this path")
    sm.add_argument("--keep", action="store_true",
                    help="keep the temporary smoke review file")
    sm.set_defaults(func=cmd_smoke)

    args = ap.parse_args()
    try:
        args.func(args)
    except BrokenPipeError:
        pass
    except KeyboardInterrupt:
        sys.exit(130)

if __name__ == "__main__":
    main()
