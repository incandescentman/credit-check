#!/usr/bin/env python3
"""
Credit Check — for Wikimedia Commons photographers.

Find your photographs that are live on Wikipedia, spot the ones missing your
photographer category, review them in Markdown, and add the category to the
ones you pick. Works for any photographer, not one hard-coded person.

It scans your own uploads as candidates, and reaches past them: any file whose
*author/photographer field* credits you is found too, which includes cropped
derivatives re-uploaded by other people. It also has an additional feature for
finding photos of you taken by other people, kept separate for your photos-of-you
category.

WORKFLOW
    Run `credit-check` to start the guided command-line app, or use commands:
    1. scan     -> writes review.md
    2. review   -> pick photos in your browser, terminal, or editor
    3. plan     -> preview the checked edits
    4. commit   -> logs in and adds the right category to each photo you checked

CONFIG (flags override environment and local preferences)
    --username     / WIKI_USERNAME      your Wikimedia Commons account (the uploader name)
    --author       / WIKI_AUTHOR        your name as it appears in author fields
    --by-category  / WIKI_BY_CATEGORY   default: "Photographs by <author>"
    --of-category  / WIKI_OF_CATEGORY   category for photos of you
    --qid          / WIKI_QID           your Wikidata id (e.g. Q42) for depicts (P180)
    .credit-check.json / --review-format   markdown by default; set org locally

EXAMPLES
    credit-check                              # guided mode
    credit-check scan --username 'Jaydixit' --author 'Jay Dixit'
    credit-check scan --of-category 'Jay Dixit' --qid Q12345
    credit-check review review.md             # pick photos in your browser
    credit-check review --terminal review.md  # keyboard-only terminal review
    credit-check plan review.md               # preview: shows what would change
    credit-check commit review.md --go         # actually edits

    (Not installed? Run it directly: python3 credit_check.py scan)

CREDENTIALS (commit --go only)
    Make a bot password at https://commons.wikimedia.org/wiki/Special:BotPasswords
    with "Edit existing pages". This is an app password for your own Wikimedia Commons
    account, not a separate uploader. A login like Jaydixit@categorize still
    edits as Jaydixit. If credentials are missing, Credit Check explains the
    steps and prompts for the generated username and password. Direct-command
    users can also pass --botuser/--botpass or set COMMONS_BOTUSER and
    COMMONS_BOTPASS.

questionary and prompt_toolkit provide the installed command's interactive UI;
direct script mode falls back to plain prompts if they are unavailable.
"""

import argparse, builtins, getpass, html, http.cookiejar, http.server, io, json, os, re, shlex, shutil, sys, tempfile, textwrap, threading, time, webbrowser
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
WIKIDATA_API = "https://www.wikidata.org/w/api.php"
__version__ = "1.1.10"
UA = ("credit-check/%s (https://github.com/incandescentman/credit-check; "
      "jay@wikiportraits.org)" % __version__)
TITLE_BATCH = 50
WEB_REVIEW_HOST = "127.0.0.1"
SAFE_API_RETRY_CODES = frozenset(("maxlag", "ratelimited", "readonly"))


# ---------------------------------------------------------------- HTTP client

class MediaWikiAPIError(Exception):
    def __init__(self, error, response=None):
        self.error = error or {}
        self.response = response or {}
        self.code = self.error.get("code") or "unknown"
        self.info = self.error.get("info") or "MediaWiki API error"
        super().__init__("%s: %s" % (self.code, self.info))


def api_retry_wait(error, attempt):
    values = [error.get("retry-after"), error.get("wait")]
    if error.get("code") == "maxlag":
        values.append(error.get("lag"))
    for value in values:
        try:
            return max(1, int(float(value)))
        except (TypeError, ValueError):
            pass
    return 2 ** attempt

class Client:
    def __init__(self, api=API):
        self.api = api
        self.jar = http.cookiejar.CookieJar()
        self.opener = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.jar))
        self.opener.addheaders = [("User-Agent", UA)]

    def _call(self, params, data=None, tries=6, retry_post=False,
              retry_api_errors=None, headers=None):
        params = {**params, "format": "json"}
        url = self.api + "?" + urllib.parse.urlencode(params)
        body = urllib.parse.urlencode(data).encode() if data else None
        may_retry = (body is None) or retry_post
        retry_api_errors = frozenset(
            SAFE_API_RETRY_CODES if retry_api_errors is None and may_retry
            else (retry_api_errors or ()))
        for attempt in range(tries):
            try:
                request = urllib.request.Request(
                    url, data=body, headers=headers or {})
                with self.opener.open(request, timeout=60) as r:
                    result = json.load(r)
                error = result.get("error")
                if error:
                    code = error.get("code")
                    if code in retry_api_errors and attempt < tries - 1:
                        wait = api_retry_wait(error, attempt)
                        print("  %s, waiting %ss..." % (code, wait), file=sys.stderr)
                        time.sleep(wait)
                        continue
                    raise MediaWikiAPIError(error, result)
                return result
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
    def post(self, params, data, retry_post=False, retry_api_errors=None):
        return self._call(params, data=data, retry_post=retry_post,
                          retry_api_errors=retry_api_errors)

    def read_post(self, params):
        """Send a read-only API request with long parameters in the POST body."""
        data = dict(params)
        action = data.pop("action")
        return self._call(
            {"action": action},
            data=data,
            retry_post=True,
            headers={"Promise-Non-Write-API-Action": "true"},
        )


# ---------------------------------------------------------------- Wikidata lookup

MANUAL_QID_CHOICE = "__manual_qid__"
SKIP_QID_CHOICE = "__skip_qid__"

def parse_wikidata_candidates(data):
    candidates = []
    for item in data.get("search", []):
        qid = item.get("id")
        if not qid:
            continue
        candidates.append({
            "id": qid,
            "label": item.get("label") or qid,
            "description": item.get("description") or "",
        })
    return candidates

def fetch_wikidata_candidates(name):
    cl = Client(WIKIDATA_API)
    data = cl.get({
        "action": "wbsearchentities",
        "search": name,
        "type": "item",
        "language": "en",
        "limit": "7",
    })
    return parse_wikidata_candidates(data)

def wikidata_candidate_label(candidate):
    label = candidate["label"]
    if candidate.get("description"):
        label += " — " + candidate["description"]
    return "%s (%s)" % (label, candidate["id"])

def normalize_qid_input(value):
    if not value:
        return None
    m = re.search(r"\b(Q\d+)\b", value.strip(), re.I)
    if m:
        return m.group(1).upper()
    return value.strip()


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


def clean_commons_description(value):
    if isinstance(value, dict):
        value = value.get("en") or next(
            (candidate for language, candidate in value.items()
             if language != "_type"), "")
    if not isinstance(value, str):
        return ""
    text = re.sub(r"<[^>]+>", " ", value)
    text = html.unescape(text).replace("\u200b", "")
    return re.sub(r"\s+", " ", text).strip()


def useful_commons_description(value):
    text = clean_commons_description(value)
    if not text:
        return ""
    boilerplate = (
        r"^(?:(?:this|this image)\s+is\s+)?(?:a\s+)?cropped\s+version\s+of\s+file:",
        r"^(?:a\s+)?crop\s+(?:of|from)\s+file:",
    )
    if any(re.match(pattern, text, re.I) for pattern in boilerplate):
        return ""
    return text


def fetch_english_captions(cl, pageids):
    """Return Commons MediaInfo English captions keyed by numeric file page ID."""
    captions = {}
    ids = ["M%d" % pageid for pageid in pageids if pageid]
    for i in range(0, len(ids), TITLE_BATCH):
        batch = ids[i:i + TITLE_BATCH]
        data = cl.get({
            "action": "wbgetentities",
            "ids": "|".join(batch),
            "props": "labels",
            "languages": "en",
        })
        for entity_id, entity in data.get("entities", {}).items():
            if not re.fullmatch(r"M\d+", entity_id):
                continue
            value = ((entity.get("labels") or {}).get("en") or {}).get("value")
            if value and value.strip():
                captions[int(entity_id[1:])] = re.sub(r"\s+", " ", value).strip()
        time.sleep(0.4)
    return captions


def fetch_details(cl, titles, by_cat, of_cat):
    """Per title: file metadata, categories, Wikipedia uses, and wikitext."""
    by_full = "Category:" + by_cat
    of_full = "Category:" + of_cat if of_cat else None
    info = {}
    titles = list(titles)
    for i in range(0, len(titles), TITLE_BATCH):
        batch = titles[i:i + TITLE_BATCH]
        base = {"action": "query", "titles": "|".join(batch),
                "prop": "categories|globalusage|imageinfo|revisions",
                "cllimit": "500", "clprop": "hidden",
                "iiprop": "user|extmetadata",
                "iiextmetadatafilter": "ImageDescription",
                "iiextmetadatalanguage": "en",
                "iiextmetadatamultilang": "0",
                "rvprop": "content", "rvslots": "main",
                "guprop": "url|namespace", "gufilterlocal": "1", "gulimit": "500"}
        cont = {}
        while True:
            d = cl.read_post({**base, **cont})
            for _, p in d.get("query", {}).get("pages", {}).items():
                t = p["title"]
                rec = info.setdefault(t, {"pageid": p.get("pageid"), "uploader": None,
                                          "cats": set(), "in_by": False, "in_of": False,
                                          "wp": {}, "wd": {}, "text": "", "description": "",
                                          "caption": ""})
                ii = (p.get("imageinfo") or [{}])[0]
                if ii.get("user"): rec["uploader"] = ii["user"]
                extmetadata = ii.get("extmetadata") or {}
                description = (extmetadata.get("ImageDescription") or {}).get("value")
                if description:
                    rec["description"] = useful_commons_description(description)
                rev = (p.get("revisions") or [{}])[0]
                content = (rev.get("slots", {}).get("main", {}) or {}).get("*", "")
                if content: rec["text"] = content
                for c in p.get("categories", []):
                    category = c["title"]
                    if "hidden" not in c:
                        rec["cats"].add(category)
                    if category == by_full: rec["in_by"] = True
                    if of_full and category == of_full: rec["in_of"] = True
                for u in p.get("globalusage", []):
                    if u.get("ns") == "0" and u["wiki"].endswith("wikipedia.org"):
                        rec["wp"][u["wiki"] + "|" + u["title"]] = {
                            "wiki": u["wiki"], "lang": u["wiki"].split(".")[0], "title": u["title"]}
                    elif (u.get("ns") == "0" and u.get("wiki") == "www.wikidata.org"
                          and re.fullmatch(r"Q\d+", u.get("title", ""))):
                        rec["wd"][u["title"]] = {
                            "id": u["title"],
                            "label": u["title"],
                            "url": "https://www.wikidata.org/wiki/%s" % u["title"],
                        }
            if "continue" in d: cont = d["continue"]
            else: break
        print("  detail %d/%d..." % (min(i + TITLE_BATCH, len(titles)), len(titles)),
              file=sys.stderr)
        time.sleep(0.5)
    return info


def fetch_wikidata_usage_labels(records):
    """Add English labels to Wikidata global-usage items in-place."""
    qids = sorted({qid for rec in records for qid in rec.get("wd", {})})
    if not qids:
        return 0
    cl = Client(WIKIDATA_API)
    for i in range(0, len(qids), TITLE_BATCH):
        batch = qids[i:i + TITLE_BATCH]
        data = cl.get({
            "action": "wbgetentities",
            "ids": "|".join(batch),
            "props": "labels",
            "languages": "en",
            "languagefallback": "1",
        })
        for qid, entity in data.get("entities", {}).items():
            labels = entity.get("labels") or {}
            label = (labels.get("en") or next(iter(labels.values()), {})).get("value")
            if not label:
                continue
            for rec in records:
                if qid in rec.get("wd", {}):
                    rec["wd"][qid]["label"] = label
        time.sleep(0.4)
    return len(qids)


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

def record_kind(rec, username, author, of_cat, depicts):
    """Return by/of/ambiguous based on credit or depicts evidence."""
    if is_by(rec["text"], username, author):
        return "by"
    if of_cat and rec["pageid"] in depicts:
        return "of"
    return "ambiguous"


def route_record(rec, username, author, of_cat, depicts):
    """Return by/of/ambiguous for missing-category work, or None if already done."""
    kind = record_kind(rec, username, author, of_cat, depicts)
    if kind == "by":
        return "by" if not rec["in_by"] else None
    if kind == "of":
        return "of" if not rec["in_of"] else None
    return kind


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
        d = cl.read_post({
            "action": "query", "titles": "|".join(batch), "redirects": "1",
            "prop": "imageinfo|revisions", "iiprop": "user",
            "rvprop": "content", "rvslots": "main",
        })
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

def sorted_wikipedia_uses(wp):
    return sorted(wp.values(), key=lambda use: (
        use.get("lang") != "en",
        use.get("lang") or "",
        wikipedia_article_title(use),
    ))


def wikipedia_reach_metrics(records):
    """Aggregate distinct photos, article pages, and Wikipedia editions."""
    records = list(records)
    article_keys = {
        key
        for rec in records
        for key in rec.get("all_wp", rec["wp"])
    }
    wikipedias = {
        use["wiki"]
        for rec in records
        for use in rec.get("all_wp", rec["wp"]).values()
    }
    return {
        "in_use_total": len(records),
        "article_total": len(article_keys),
        "wikipedia_total": len(wikipedias),
    }


def wikipedia_article_title(use):
    # MediaWiki commonly returns database-form titles with underscores. Keep
    # those in URLs, but present the article name the way Wikipedia does.
    return (use.get("title") or "Untitled article").replace("_", " ")

def wikipedia_article_url(use):
    wiki = use.get("wiki") or ""
    title = use.get("title") or ""
    return "https://%s/wiki/%s" % (
        wiki,
        urllib.parse.quote(title.replace(" ", "_"), safe="/:,-"),
    )

def review_link_label(value):
    return str(value).replace("\\", "\\\\").replace("]", "\\]")

def unescape_review_link_label(value):
    return re.sub(r"\\(.)", r"\1", value)

def markdown_use_line(use):
    return "  used in: [%s](%s)" % (
        review_link_label(wikipedia_article_title(use)),
        wikipedia_article_url(use),
    )

def org_use_line(use):
    label = wikipedia_article_title(use).replace("]", "\\]")
    return "     used in: [[%s][%s]]" % (wikipedia_article_url(use), label)

REVIEW_FORMAT_ENV = "CREDIT_CHECK_REVIEW_FORMAT"
PREFERENCE_FILE = ".credit-check.json"
ALL_PHOTOS_CACHE_FILE = ".credit-check-all-photos.json"
ALL_PHOTOS_CACHE_VERSION = 2
PHOTOGRAPHER_PREF_KEYS = (
    "username", "author", "by_category", "of_category", "qid",
)
REVIEW_FORMAT_ALIASES = {"md": "markdown", "markdown": "markdown",
                         "org": "org", "org-mode": "org", "orgmode": "org"}

def atomic_write_text(path, text):
    # Write beside the target so os.replace is atomic on the same filesystem.
    d = os.path.dirname(os.path.abspath(path)) or "."
    fd, tmp = tempfile.mkstemp(prefix=".credit-check-write.", dir=d)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise

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
    atomic_write_text(PREFERENCE_FILE, json.dumps(prefs, indent=2, sort_keys=True) + "\n")

def clear_photographer_preferences():
    save_local_preferences({key: None for key in PHOTOGRAPHER_PREF_KEYS})

def reset_review_paths():
    prefs = local_preferences()
    candidates = []
    for key in ("review_path", "out"):
        path = prefs.get(key)
        if path:
            candidates.append(path)
    candidates += ["review.md", "review.org"]
    paths = []
    seen = set()
    for path in candidates:
        if not path or path in seen:
            continue
        seen.add(path)
        paths.append(path)
    return paths

def clear_review_files():
    removed = []
    paths = reset_review_paths()
    cache_paths = {
        all_photos_cache_path(path)
        for path in paths
    }
    for path in paths + sorted(cache_paths):
        if not (os.path.exists(path) or os.path.islink(path)):
            continue
        if os.path.isdir(path) and not os.path.islink(path):
            continue
        os.unlink(path)
        removed.append(path)
    return removed

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

def all_photos_cache_path(review):
    return os.path.join(
        os.path.dirname(os.path.abspath(review)),
        ALL_PHOTOS_CACHE_FILE,
    )

def all_photos_item(title, rec, target, line):
    uses = sorted_wikipedia_uses(rec.get("all_wp", rec.get("wp", {})))
    return {
        "line": line,
        "title": title,
        "label": title[5:] if title.startswith("File:") else title,
        "target": target,
        "checked": False,
        "uses": len(uses),
        "articles": [
            {
                "wiki": use.get("wiki", ""),
                "lang": use.get("lang", ""),
                "title": wikipedia_article_title(use),
                "url": wikipedia_article_url(use),
            }
            for use in uses
        ],
        "wikidata_items": sorted(
            rec.get("wd", {}).values(),
            key=lambda item: (item.get("label", "").casefold(), item.get("id", "")),
        ),
        "caption": rec.get("caption", ""),
    }

def write_all_photos_cache(review, gallery_records, review_titles):
    ordered = sorted(
        gallery_records,
        key=lambda entry: (
            -len(entry[1].get("all_wp", entry[1].get("wp", {}))),
            entry[0],
        ),
    )
    payload = {
        "version": ALL_PHOTOS_CACHE_VERSION,
        "review_titles": sorted(review_titles),
        "items": [
            all_photos_item(title, rec, target, -(index + 1))
            for index, (title, rec, target) in enumerate(ordered)
        ],
    }
    atomic_write_text(
        all_photos_cache_path(review),
        json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
    )

def load_all_photos_cache(review, review_items):
    try:
        with open(all_photos_cache_path(review), encoding="utf-8") as f:
            payload = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return None
    if not isinstance(payload, dict) or payload.get("version") != ALL_PHOTOS_CACHE_VERSION:
        return None
    expected_titles = sorted(item["title"] for item in review_items)
    if payload.get("review_titles") != expected_titles:
        return None
    raw_items = payload.get("items")
    if not isinstance(raw_items, list):
        return None
    items = []
    for index, item in enumerate(raw_items):
        if not isinstance(item, dict) or not isinstance(item.get("title"), str):
            return None
        articles = item.get("articles", [])
        wikidata_items = item.get("wikidata_items", [])
        if not isinstance(articles, list) or not isinstance(wikidata_items, list):
            return None
        normalized = dict(item)
        normalized["line"] = -(index + 1)
        normalized["checked"] = False
        normalized["label"] = item.get("label") or commons_file_name(item["title"])
        normalized["uses"] = item.get("uses") if isinstance(item.get("uses"), int) else None
        normalized["articles"] = articles
        normalized["wikidata_items"] = wikidata_items
        normalized["caption"] = item.get("caption", "")
        items.append(normalized)
    return items

def markdown_item_block(title, rec):
    name = title[5:] if title.startswith("File:") else title
    url = "https://commons.wikimedia.org/wiki/" + urllib.parse.quote(title.replace(" ", "_"))
    cats = ", ".join(sorted(c.replace("Category:", "") for c in rec["cats"])) or "(none)"
    block = [
        "## [%d] %s" % (len(rec["wp"]), name),
        "",
        "- [ ] %s" % title,
        "  [open on Wikimedia Commons](%s) - uploader %s - %s"
        % (url, rec["uploader"] or "?", "/".join(sorted(rec["reason"]))),
        "  cats: %s" % cats,
        "  live: %s" % langs_line(rec["wp"]),
    ]
    if rec.get("caption"):
        block.append("  caption: %s" % rec["caption"])
    block.extend(markdown_use_line(use) for use in sorted_wikipedia_uses(rec["wp"]))
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
        "     [[%s][open on Wikimedia Commons]] · uploader %s · %s"
        % (url, rec["uploader"] or "?", "/".join(sorted(rec["reason"]))),
        "     cats: %s" % cats,
        "     live: %s" % langs_line(rec["wp"]),
    ]
    if rec.get("caption"):
        block.append("     caption: %s" % rec["caption"])
    block.extend(org_use_line(use) for use in sorted_wikipedia_uses(rec["wp"]))
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
    L.append("<!-- credit-check-metrics: %s -->" % json.dumps({
        "article_total": meta.get("article_total"),
        "in_use_total": meta.get("in_use_total"),
        "missing_category_total": meta.get("missing_category_total"),
        "wikipedia_total": meta.get("wikipedia_total"),
    }, sort_keys=True))
    L.append("")
    L.append("Pick photos in the browser:")
    L.append("")
    L.append("    credit-check review %s" % review_path_arg(path))
    L.append("")
    L.append("Or tick `[X]` manually next to the photos you want, then preview and commit:")
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
        L.append("# Add to [Category:%s] - photos of you (%d)"
                 % (meta["of_category"], len(of_list)))
        L.append("")
        for t, rec in sort_review_items(of_list): L += markdown_item_block(t, rec)

    if include_ambiguous:
        L.append("# Ambiguous - authorship or category is unclear (%d)" % len(amb_list))
        L.append("Not added automatically. To add one, move it under a heading above and tick it.")
        L.append("")
        for t, rec in sort_review_items(amb_list): L += markdown_item_block(t, rec)

    atomic_write_text(path, "\n".join(L))

def write_org(by_list, of_list, amb_list, meta, path):
    L = []
    include_by = meta.get("include_by", True)
    include_of = meta.get("include_of", True)
    include_ambiguous = meta.get("include_ambiguous", True)
    L.append("#+TITLE: Category review — %s" % meta["author"])
    L.append("#+STARTUP: content")
    L.append("#+CREDIT_CHECK_METRICS: %s" % json.dumps({
        "article_total": meta.get("article_total"),
        "in_use_total": meta.get("in_use_total"),
        "missing_category_total": meta.get("missing_category_total"),
        "wikipedia_total": meta.get("wikipedia_total"),
    }, sort_keys=True))
    L.append("")
    L.append("# Pick photos in the browser:")
    L.append("#   credit-check review %s" % review_path_arg(path))
    L.append("# Or tick [X] manually next to the photos you want, then preview and commit:")
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
        L.append("* Add to [[Category:%s]] — photos of you (%d)"
                 % (meta["of_category"], len(of_list)))
        L.append("")
        for t, rec in sort_review_items(of_list): L += org_item_block(t, rec)

    if include_ambiguous:
        L.append("* Ambiguous — authorship or category is unclear (%d)" % len(amb_list))
        L.append("# NOT added automatically. To add one, move it under a heading above and tick it.")
        L.append("")
        for t, rec in sort_review_items(amb_list): L += org_item_block(t, rec)

    atomic_write_text(path, "\n".join(L))

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
MD_USE_RE = re.compile(r"^\s+used in:\s+\[((?:\\.|[^]])*)\]\((https?://\S+)\)\s*$")
ORG_USE_RE = re.compile(r"^\s+used in:\s+\[\[(https?://[^]]+)\]\[((?:\\.|[^]])*)\]\]\s*$")
CAPTION_RE = re.compile(r"^\s+caption:\s*(.*?)\s*$", re.I)
REVIEW_METRICS_RE = re.compile(
    r"(?:credit-check-metrics:|#\+CREDIT_CHECK_METRICS:)\s*(\{.*\})",
    re.I,
)

def article_from_review_link(url, label):
    parsed = urllib.parse.urlparse(url)
    wiki = parsed.netloc
    title = unescape_review_link_label(label)
    lang = wiki.split(".", 1)[0] if wiki.endswith(".wikipedia.org") else ""
    return {"wiki": wiki, "lang": lang, "title": title, "url": url}

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
    current_item = None
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
            current_item = None
            continue

        mu = MD_USE_RE.match(line) if allow_md else None
        if not mu and allow_org:
            mu = ORG_USE_RE.match(line)
            if mu and current_item is not None:
                current_item["articles"].append(
                    article_from_review_link(mu.group(1), mu.group(2)))
                continue
        elif mu and current_item is not None:
            current_item["articles"].append(
                article_from_review_link(mu.group(2), mu.group(1)))
            continue

        caption_match = CAPTION_RE.match(line)
        if caption_match and current_item is not None:
            current_item["caption"] = caption_match.group(1).strip()
            continue

        mt = None
        if allow_org:
            mt = ORG_HEAD_TARGET_RE.match(line)
        if not mt and allow_md:
            mt = MD_HEAD_TARGET_RE.match(line)
        if mt:
            target = mt.group(1)
            item_label, item_uses = None, None
            current_item = None
            continue
        if (allow_org and ORG_SECTION_RE.match(line)) or (allow_md and MD_SECTION_RE.match(line)):
            target = None
            item_label, item_uses = None, None
            current_item = None
            continue

        mc = CHECK_RE.match(line)
        if mc:
            title = mc.group(2)
            current_item = {
                "line": i,
                "title": title,
                "target": target,
                "checked": mc.group(1).strip().lower() == "x",
                "uses": item_uses,
                "label": item_label or (title[5:] if title.startswith("File:") else title),
                "articles": [],
                "caption": "",
            }
            items.append(current_item)
            item_label, item_uses = None, None
    return items


def review_scan_metrics(path, fallback_missing=None):
    """Return scan-level in-use and missing-category photo totals from a review."""
    metrics = {
        "article_total": None,
        "in_use_total": None,
        "missing_category_total": fallback_missing,
        "wikipedia_total": None,
    }
    with open(path, encoding="utf-8") as f:
        for line in f:
            match = REVIEW_METRICS_RE.search(line)
            if not match:
                continue
            try:
                parsed = json.loads(match.group(1))
            except (TypeError, ValueError):
                break
            for key in metrics:
                value = parsed.get(key)
                if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
                    metrics[key] = value
            break
    return metrics

def review_section_context(path):
    """Infer what kind of scan produced a review from its generated headings."""
    ext = os.path.splitext(path)[1].lower()
    allow_org = ext not in (".md", ".markdown")
    allow_md = ext != ".org"
    context = {
        "has_by_section": False,
        "has_of_section": False,
        "has_ambiguous_section": False,
        "by_category": None,
        "of_category": None,
    }
    with open(path, encoding="utf-8") as f:
        for line in f:
            lower = line.lower()
            mt = None
            if allow_org:
                mt = ORG_HEAD_TARGET_RE.match(line)
            if not mt and allow_md:
                mt = MD_HEAD_TARGET_RE.match(line)
            if mt:
                category = mt.group(1)
                if "photos of you" in lower:
                    context["has_of_section"] = True
                    context["of_category"] = category
                elif "photos you took" in lower:
                    context["has_by_section"] = True
                    context["by_category"] = category
                continue
            if ((allow_org and ORG_SECTION_RE.match(line)) or
                    (allow_md and MD_SECTION_RE.match(line))):
                if "ambiguous" in lower:
                    context["has_ambiguous_section"] = True
    return context

def review_mode_from_context(context):
    if (context.get("has_of_section") and
            not context.get("has_by_section") and
            not context.get("has_ambiguous_section")):
        return "of"
    return "by"

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
    atomic_write_text(path, "".join(lines))

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
  <a href="{file_url}" target="_blank" rel="noreferrer">Open on Wikimedia Commons</a>
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
            "articles": item.get("articles", []),
            "wikidata_items": item.get("wikidata_items", []),
            "caption": item.get("caption", ""),
            "file_url": commons_file_url(item["title"]),
            "thumb_url": commons_thumb_url(item["title"], width=420),
        })
    return payload

class ReviewChangedError(Exception):
    pass

def review_items_signature(items):
    return [(item["line"], item["title"], item["target"], item["checked"],
             item.get("caption", ""),
             tuple((article.get("title"), article.get("url"))
                   for article in item.get("articles", [])))
            for item in items]

def web_review_html(review, approvable, ambiguous_count=0, initial_mode="all",
                    guided=False, scan_metrics=None, all_photos=None,
                    initial_scope="missing"):
    if initial_mode not in ("all", "selected", "unselected"):
        initial_mode = "all"
    if initial_scope not in ("missing", "all"):
        initial_scope = "missing"
    items_json = json.dumps(web_review_payload(approvable), ensure_ascii=True).replace(
        "</", "<\\/")
    all_photos_available = all_photos is not None
    all_photos_json = json.dumps(
        web_review_payload(all_photos or []), ensure_ascii=True).replace("</", "<\\/")
    all_photos_available_json = json.dumps(all_photos_available)
    review_json = json.dumps(os.path.abspath(review), ensure_ascii=True).replace(
        "</", "<\\/")
    review_arg_json = json.dumps(review_path_arg(review), ensure_ascii=True).replace(
        "</", "<\\/")
    ambiguous_json = json.dumps(ambiguous_count)
    metrics = {
        "article_total": None,
        "in_use_total": None,
        "missing_category_total": len(approvable),
        "wikipedia_total": None,
    }
    if scan_metrics:
        metrics.update(scan_metrics)
    metrics_json = json.dumps(metrics, ensure_ascii=True).replace("</", "<\\/")
    initial_mode_json = json.dumps(initial_mode)
    initial_scope_json = json.dumps(initial_scope)
    guided_json = json.dumps(bool(guided))
    return """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Credit Check — Your photos on Wikipedia</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Instrument+Sans:wght@400..800&amp;display=swap">
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
  font: 15px/1.45 "Instrument Sans", -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
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
.section-heading-meta {
  display: flex;
  align-items: center;
  justify-content: flex-end;
  gap: 10px;
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

/* Warm, task-first picker direction from the approved Credit Check mockup. */
:root {
  --bg: #f1f1ed;
  --panel: #ffffff;
  --panel-soft: #f7f7f3;
  --ink: #15171c;
  --muted: #5b6068;
  --faint: #858a91;
  --line: #e5e5df;
  --line-strong: #cecec5;
  --accent: #0e6b45;
  --accent-soft: #eaf2ec;
  --accent-strong: #0b5738;
  --selected: #0e6b45;
  --selected-soft: #f5faf6;
  --warn: #72540a;
  --warn-soft: #fff8e7;
}
body {
  min-height: 100vh;
  background:
    radial-gradient(1100px 560px at 82% -10%, #ffffff 0%, rgba(255, 255, 255, 0) 64%),
    linear-gradient(180deg, #f7f7f4 0%, var(--bg) 100%);
  color: var(--ink);
  -webkit-font-smoothing: antialiased;
}
.app-shell {
  width: min(1560px, calc(100% - 48px));
  margin: 0 auto;
  padding: 24px 0 40px;
}
.picker-shell {
  min-width: 0;
  overflow: clip;
  background: rgba(255, 255, 255, 0.98);
  border: 1px solid rgba(255, 255, 255, 0.8);
  border-radius: 22px;
  box-shadow: 0 22px 58px -32px rgba(21, 23, 28, 0.36), 0 2px 8px rgba(21, 23, 28, 0.05);
}
.picker-shell > .product-header {
  position: static;
  padding: 22px 24px 0;
  background: rgba(255, 255, 255, 0.96);
  border-bottom: 0;
  box-shadow: none;
}
.picker-workspace {
  display: grid;
  grid-template-columns: minmax(0, 1fr) 330px;
  align-items: stretch;
}
.picker-content {
  min-width: 0;
}
.picker-controls,
.picker-shell .picker-main {
  max-width: none;
  margin: 0;
  padding-left: 24px;
  padding-right: 24px;
}
.picker-controls {
  padding-top: 0;
  padding-bottom: 18px;
  border-bottom: 1px solid var(--line);
}
.picker-main {
  padding-top: 22px;
  padding-bottom: 28px;
}
.picker-identity {
  display: block;
  flex: 1 1 auto;
  min-width: 0;
}
.product-lockup {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 28px;
  flex-wrap: nowrap;
  padding-bottom: 20px;
  border-bottom: 1px solid var(--line);
}
.product-title {
  margin: 0;
  color: #171a17;
  font-size: 44px;
  font-weight: 800;
  line-height: 0.98;
  letter-spacing: -0.05em;
}
.product-credit {
  display: inline-flex;
  align-items: center;
  gap: 4px;
  color: var(--muted);
  font-size: 17px;
  font-weight: 600;
  line-height: 1;
  margin-left: auto;
}
.wikiportraits-link {
  display: inline-flex;
  align-items: center;
  gap: 7px;
  color: var(--accent-strong);
  font-weight: 750;
  text-decoration: none;
}
.wikiportraits-link:hover,
.wikiportraits-link:focus-visible {
  color: var(--accent);
  text-decoration: underline;
  text-underline-offset: 3px;
}
.wikiportraits-logo {
  display: block;
  width: 34px;
  height: 34px;
  object-fit: contain;
}
.title-row {
  display: flex;
  align-items: center;
  gap: 12px;
  flex-wrap: wrap;
}
.rail-kicker,
.used-label,
.target-card > p {
  color: var(--accent);
  font-size: 11px;
  font-weight: 750;
  letter-spacing: 0.12em;
  text-transform: uppercase;
}
.task-row {
  margin-top: 26px;
}
.task-title {
  margin: 0;
  font-size: 24px;
  font-weight: 700;
  line-height: 1.2;
  letter-spacing: -0.015em;
}
.scope-tabs {
  display: grid;
  grid-template-columns: repeat(3, minmax(0, 1fr));
  align-self: start;
  gap: 5px;
  width: 100%;
  margin: 0;
  padding: 5px;
  background: var(--panel-soft);
  border: 1px solid var(--line);
  border-radius: 13px;
}
.scope-tab {
  display: grid;
  grid-template-columns: 1fr;
  justify-items: center;
  align-items: center;
  gap: 3px;
  min-height: 88px;
  padding: 6px 8px;
  color: var(--ink);
  background: transparent;
  border: 1px solid transparent;
  border-radius: 9px;
  font-size: 14px;
  font-weight: 700;
  line-height: 1.25;
  text-align: center;
  transition: background-color 140ms ease, border-color 140ms ease, box-shadow 140ms ease;
}
.scope-tab-icon {
  display: grid;
  place-items: center;
  width: 36px;
  height: 36px;
  color: var(--muted);
  background: rgba(14, 107, 69, 0.06);
  border-radius: 7px;
}
.scope-tab-icon svg { width: 22px; height: 22px; }
.scope-tab-icon img {
  display: block;
  width: 22px;
  height: 22px;
  object-fit: contain;
}
.scope-tab-copy { display: grid; gap: 2px; min-width: 0; }
.scope-tab-title {
  font-size: 13px;
  font-weight: 750;
  line-height: 1.2;
}
.scope-tab-meta {
  color: var(--muted);
  font-size: 11px;
  font-weight: 550;
  line-height: 1.25;
}
.scope-tab:hover:not(:disabled),
.scope-tab:focus-visible:not(:disabled) {
  color: var(--ink);
  background: #fff;
  border-color: rgba(14, 107, 69, 0.28);
  box-shadow: 0 7px 18px -14px rgba(11, 87, 56, 0.72);
}
.scope-tab.active {
  color: var(--ink);
  background: #fff;
  border-color: rgba(14, 107, 69, 0.2);
  box-shadow: 0 5px 18px -14px rgba(11, 87, 56, 0.65);
}
.scope-tab.active .scope-tab-icon {
  color: #fff;
  background: var(--accent-strong);
}
.scope-tab[data-scope="wikidata"].active .scope-tab-icon {
  background: #fff;
  box-shadow: inset 0 0 0 1px rgba(14, 107, 69, 0.18);
}
.scope-tab.active .scope-tab-meta { color: var(--accent-strong); }
.scope-tab:disabled {
  cursor: not-allowed;
  opacity: 0.48;
}
.scope-panel { min-width: 0; }
.scope-description {
  margin: 8px 5px 0;
  color: var(--muted);
  font-size: 12px;
  line-height: 1.4;
}
.scan-metrics {
  width: min(100%, 540px);
  margin: 0;
  overflow: hidden;
  background:
    radial-gradient(circle at 50% -30%, rgba(143, 240, 191, 0.24), transparent 52%),
    linear-gradient(145deg, #fbfdfb 0%, var(--panel-soft) 100%);
  border: 1px solid rgba(14, 107, 69, 0.18);
  border-radius: 16px;
  box-shadow: 0 14px 34px -28px rgba(11, 87, 56, 0.7);
}
.reach-overview {
  display: grid;
  grid-template-columns: minmax(0, 540px) minmax(220px, 1fr);
  align-items: start;
  gap: 18px;
  margin-top: 14px;
}
.missing-category-statement {
  margin: 12px 0 0;
}
.reach-statement {
  padding: 12px 24px;
  color: var(--ink);
}
.wikidata-reach {
  display: grid;
  grid-template-columns: 32px minmax(0, 1fr);
  align-items: center;
  gap: 12px;
  width: 100%;
  padding: 13px 24px 15px;
  color: var(--muted);
  background: rgba(255, 255, 255, 0.42);
  border: 0;
  border-top: 1px solid rgba(14, 107, 69, 0.12);
  font: inherit;
  text-align: left;
}
.wikidata-reach-icon {
  display: grid;
  place-items: center;
  width: 32px;
  height: 32px;
  color: var(--accent-strong);
  background: rgba(14, 107, 69, 0.07);
  border-radius: 7px;
}
.wikidata-reach-icon svg,
.wikidata-reach-icon img {
  display: block;
  width: 21px;
  height: 21px;
  object-fit: contain;
}
.wikidata-reach-copy { display: grid; gap: 1px; }
.wikidata-reach-kicker {
  font-size: 10px;
  font-weight: 800;
  letter-spacing: 0.11em;
  text-transform: uppercase;
}
.wikidata-reach-line { font-size: 13px; line-height: 1.35; }
.wikidata-reach-line strong { color: var(--ink); font-weight: 750; }
.reach-row {
  display: grid;
  grid-template-columns: 46px max-content minmax(0, 1fr);
  align-items: center;
  gap: 17px;
  min-height: 92px;
}
.reach-row + .reach-row {
  border-top: 1px solid rgba(14, 107, 69, 0.12);
}
.reach-icon {
  display: grid;
  place-items: center;
  width: 44px;
  height: 44px;
  color: var(--accent-strong);
  background: rgba(14, 107, 69, 0.09);
  border: 1px solid rgba(14, 107, 69, 0.12);
  border-radius: 13px;
}
.reach-icon svg,
.reach-icon img {
  display: block;
  width: 26px;
  height: 26px;
  object-fit: contain;
}
.reach-row strong {
  color: var(--accent-strong);
  font-size: clamp(56px, 6vw, 74px);
  font-weight: 800;
  line-height: 0.86;
  letter-spacing: -0.06em;
  font-variant-numeric: tabular-nums;
}
.reach-label {
  color: var(--ink);
  font-size: 19px;
  font-weight: 700;
  line-height: 1.25;
}
.missing-category-statement strong {
  color: var(--accent-strong);
  font-weight: 800;
}
.missing-category-statement {
  padding: 0;
  color: var(--ink);
  font-size: 15px;
  font-weight: 650;
  line-height: 1.35;
  text-align: left;
}
.missing-category-statement strong {
  font-size: 20px;
  letter-spacing: -0.025em;
}
.scan-metrics-note {
  margin: 4px 0 0;
  padding: 0;
  color: var(--muted);
  font-size: 12px;
  line-height: 1.35;
  text-align: left;
}
.summary {
  display: inline-flex;
  align-items: center;
  min-height: 30px;
  margin: 0;
  padding: 5px 11px;
  color: #fff;
  background: var(--selected);
  border-radius: 999px;
  font-size: 13px;
  font-weight: 700;
}
.summary::before {
  content: "";
  width: 6px;
  height: 6px;
  margin-right: 7px;
  background: #8ff0bf;
  border-radius: 50%;
}
.result-count {
  margin: 0;
  color: var(--muted);
  font-size: 14px;
}
.review-counts {
  display: flex;
  align-items: center;
  gap: 10px;
  min-height: 30px;
  margin-top: 8px;
  flex-wrap: wrap;
}
.mobile-save-actions {
  display: none;
}
.app-shell.all-photos-view .mobile-save-actions,
.app-shell.all-photos-view .mode-tabs,
.app-shell.all-photos-view .bulk-tools,
.app-shell.all-photos-view .summary {
  visibility: hidden;
  pointer-events: none;
}
.all-photos-rail {
  display: none;
  padding: 2px 4px 0;
}
.all-photos-rail h2 {
  margin: 8px 0;
  font-size: 21px;
  line-height: 1.22;
  letter-spacing: -0.02em;
}
.all-photos-rail p:not(.rail-kicker) {
  margin: 0 0 12px;
  color: var(--muted);
  font-size: 14px;
}
.app-shell.all-photos-view .action-rail > :not(.all-photos-rail) {
  display: none;
}
.app-shell.all-photos-view .all-photos-rail {
  display: block;
}
.photo.read-only {
  cursor: default;
}
input[type="search"],
button {
  border-color: var(--line-strong);
  border-radius: 9px;
}
input[type="search"] {
  background: var(--panel-soft);
}
button.primary {
  border-color: var(--accent);
  background: var(--accent);
}
button.primary:hover,
button.primary:focus-visible {
  background: var(--accent-strong);
}
.mode-tabs {
  background: var(--panel-soft);
  border-color: var(--line);
  border-radius: 10px;
}
.bulk-tools {
  row-gap: 8px;
}
.sections {
  gap: 32px;
}
.section-heading {
  border-bottom: 0;
  padding-bottom: 2px;
}
.section-heading h2 {
  font-size: 20px;
  letter-spacing: -0.015em;
}
.grid {
  grid-template-columns: repeat(3, minmax(0, 1fr));
  gap: 28px 24px;
}
.photo {
  gap: 0;
  padding: 0;
  overflow: hidden;
  border-color: rgba(213, 211, 202, 0.78);
  border-radius: 20px;
  box-shadow:
    0 1px 2px rgba(21, 23, 28, 0.035),
    0 12px 32px -26px rgba(21, 23, 28, 0.3);
  transition: border-color 220ms ease, box-shadow 220ms ease;
}
.photo::before {
  display: none;
}
.photo:hover,
.photo:focus-visible {
  border-color: rgba(14, 107, 69, 0.58);
  outline: none;
  box-shadow:
    0 2px 5px rgba(21, 23, 28, 0.05),
    0 22px 46px -30px rgba(21, 23, 28, 0.42);
}
.photo.selected {
  border-color: transparent;
  background: var(--panel);
  box-shadow: 0 0 0 2px var(--selected), 0 14px 32px -22px rgba(14, 107, 69, 0.52);
}
.select-control {
  position: absolute;
  z-index: 3;
  top: 11px;
  left: 11px;
  display: grid;
  place-items: center;
  width: 30px;
  height: 30px;
  color: transparent;
  background: rgba(255, 255, 255, 0.96);
  border: 1px solid rgba(255, 255, 255, 0.9);
  border-radius: 50%;
  box-shadow: 0 2px 7px rgba(21, 23, 28, 0.18);
  backdrop-filter: blur(5px);
  cursor: pointer;
  transition: color 180ms ease, background 180ms ease, box-shadow 180ms ease;
}
.select-control:hover {
  box-shadow: 0 4px 12px rgba(21, 23, 28, 0.22);
}
.photo.selected .select-control {
  color: #fff;
  background: var(--selected);
  border-color: var(--selected);
}
.select-control input {
  position: absolute;
  width: 1px;
  height: 1px;
  opacity: 0;
  pointer-events: none;
}
.select-indicator {
  display: grid;
  place-items: center;
  width: 100%;
  height: 100%;
  border-radius: 50%;
  font-size: 15px;
  font-weight: 800;
  line-height: 1;
}
.select-control input:focus-visible + .select-indicator {
  outline: 3px solid rgba(14, 107, 69, 0.28);
  outline-offset: 3px;
}
.thumb {
  aspect-ratio: 4 / 5;
  border: 0;
  border-radius: 0;
  background: linear-gradient(145deg, #ecece7, #f7f7f4);
}
.thumb::before,
.thumb::after {
  content: "";
  position: absolute;
  z-index: 2;
  width: 18px;
  height: 18px;
  pointer-events: none;
  filter:
    drop-shadow(0 1px 1px rgba(5, 48, 31, 0.52))
    drop-shadow(0 0 2px rgba(255, 255, 255, 0.35));
}
.thumb::before {
  top: 12px;
  right: 12px;
  border-top: 1px solid rgba(88, 211, 148, 0.98);
  border-right: 1px solid rgba(88, 211, 148, 0.98);
}
.thumb::after {
  bottom: 12px;
  left: 12px;
  border-bottom: 1px solid rgba(88, 211, 148, 0.98);
  border-left: 1px solid rgba(88, 211, 148, 0.98);
}
.thumb img {
  object-fit: cover;
  object-position: 50% 20%;
  background: #f4f4f0;
}
.photo-image {
  position: relative;
  min-width: 0;
}
.photo-content {
  display: grid;
  gap: 7px;
  padding: 18px 18px 20px;
}
.photo-title {
  position: relative;
  display: flex;
  align-items: center;
  box-sizing: border-box;
  min-height: 144px;
  padding: 24px 22px 22px;
  background:
    radial-gradient(220px 130px at 100% 0%, rgba(14, 107, 69, 0.1), transparent 72%),
    linear-gradient(145deg, #fff 0%, #faf9f5 100%);
  border-bottom: 1px solid rgba(213, 211, 202, 0.72);
}
.photo-title::after {
  content: "";
  position: absolute;
  right: 22px;
  bottom: -1px;
  left: 22px;
  height: 1px;
  background: linear-gradient(90deg, rgba(14, 107, 69, 0.18), transparent 76%);
}
.photo-caption {
  display: -webkit-box;
  margin: 0;
  overflow: hidden;
  color: #20251f;
  font-family: "Instrument Sans", -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
  font-size: 28px;
  font-weight: 800;
  line-height: 1.02;
  letter-spacing: -0.045em;
  text-wrap: balance;
  overflow-wrap: anywhere;
  -webkit-box-orient: vertical;
  -webkit-line-clamp: 3;
}
.used-label {
  margin: 0 0 1px;
}
.article-preview-list,
.article-list {
  display: grid;
  gap: 8px;
  min-width: 0;
  margin: 0;
  padding: 0;
  list-style: none;
}
.article-preview-list li,
.article-list li {
  min-width: 0;
}
.article-preview-list a,
.article-list a {
  color: var(--ink);
  text-decoration: none;
}
.article-preview-list a {
  font-size: 16px;
  font-weight: 650;
  line-height: 1.32;
  letter-spacing: -0.01em;
}
.article-preview-list a:hover,
.article-preview-list a:focus-visible,
.article-list a:hover,
.article-list a:focus-visible {
  color: var(--accent-strong);
  text-decoration: underline;
  text-underline-offset: 2px;
}
.article-language {
  display: block;
  margin-top: 2px;
  color: var(--muted);
  font-size: 12px;
  line-height: 1.3;
}
.article-fallback {
  margin: 0;
  color: var(--muted);
  font-size: 13px;
}
.article-disclosure,
.wikidata-disclosure,
.photo-details,
.edit-receipt {
  min-width: 0;
}
.article-disclosure > summary,
.wikidata-disclosure > summary,
.photo-details > summary,
.edit-receipt > summary {
  color: var(--accent-strong);
  cursor: pointer;
  font-size: 13px;
  font-weight: 650;
}
.article-disclosure > summary:hover,
.article-disclosure > summary:focus-visible,
.wikidata-disclosure > summary:hover,
.wikidata-disclosure > summary:focus-visible,
.photo-details > summary:hover,
.photo-details > summary:focus-visible,
.edit-receipt > summary:hover,
.edit-receipt > summary:focus-visible {
  text-decoration: underline;
  text-underline-offset: 2px;
}
.wikidata-disclosure {
  margin-top: 10px;
  color: var(--muted);
}
.wikidata-disclosure > summary {
  color: var(--muted);
  font-weight: 600;
}
.wikidata-list {
  gap: 5px;
  max-height: 150px;
  margin: 7px 0 0;
  padding: 8px 4px 2px;
  overflow: auto;
  border-top: 1px solid var(--line);
  font-size: 13px;
}
.wikidata-list a {
  color: var(--muted);
  text-decoration: none;
}
.wikidata-list a:hover,
.wikidata-list a:focus-visible {
  color: var(--accent-strong);
  text-decoration: underline;
  text-underline-offset: 2px;
}
.wikidata-id { color: var(--faint); }
.article-list {
  gap: 5px;
  max-height: 180px;
  margin: 8px 0 2px;
  padding: 8px 4px 4px;
  overflow: auto;
  border-top: 1px solid var(--line);
  font-size: 13px;
}
.language-groups {
  display: grid;
  gap: 12px;
  max-height: 240px;
  margin-top: 8px;
  padding-top: 8px;
  overflow: auto;
  border-top: 1px solid var(--line);
}
.language-group h3 {
  margin: 0 0 5px;
  color: var(--muted);
  font-size: 11px;
  font-weight: 750;
  letter-spacing: 0.06em;
  line-height: 1.3;
  text-transform: uppercase;
}
.language-group .article-list {
  max-height: none;
  margin: 0;
  padding: 0;
  overflow: visible;
  border-top: 0;
}
.photo-details {
  margin-top: 7px;
  padding-top: 8px;
  border-top: 1px solid var(--line);
}
.technical-details {
  display: grid;
  gap: 7px;
  margin-top: 8px;
}
.file-name {
  margin: 0 !important;
  color: var(--faint);
  font-size: 12.5px !important;
  font-weight: 500 !important;
  line-height: 1.35 !important;
}
.card-footer {
  margin: 0;
  padding: 0;
  border: 0;
}
.commons-link {
  color: var(--accent-strong);
  font-weight: 650;
}
.target {
  margin-top: 4px;
  color: var(--muted);
}
.action-rail {
  position: static;
  display: grid;
  align-content: start;
  gap: 20px;
  min-width: 0;
  padding: 24px;
  background: linear-gradient(180deg, #fbfbf8 0%, #f7f7f2 100%);
  border-left: 1px solid var(--line);
}
.rail-intro,
.preview-panel {
  padding: 2px 4px 0;
  background: transparent;
  border: 0;
  border-radius: 0;
  box-shadow: none;
}
.rail-intro h2 {
  margin: 8px 0 8px;
  font-size: 21px;
  line-height: 1.22;
  letter-spacing: -0.02em;
}
.rail-intro > #rail-state-copy {
  margin: 0;
  color: var(--muted);
  font-size: 14px;
}
.selection-flow {
  display: grid;
  grid-template-columns: auto 18px minmax(0, 1fr);
  gap: 8px;
  align-items: center;
  margin-top: 16px;
  padding: 12px 0;
  color: var(--accent-strong);
  border-top: 1px solid var(--line-strong);
  border-bottom: 1px solid var(--line-strong);
  font-size: 13px;
}
.selection-flow[hidden] {
  display: none;
}
.selection-flow strong {
  font-size: 14px;
}
.selection-flow span:last-child {
  overflow-wrap: anywhere;
}
.target-card {
  display: block;
  padding: 20px;
  color: #fff;
  background: linear-gradient(135deg, #0f7049, #0a4f33);
  border-radius: 18px;
  box-shadow: 0 18px 38px -25px rgba(10, 79, 51, 0.7);
  text-decoration: none;
  transition: background 180ms ease, box-shadow 180ms ease;
}
.target-card[href]:hover,
.target-card[href]:focus-visible {
  color: #fff;
  background: linear-gradient(135deg, #118058, #075338);
  box-shadow: 0 20px 42px -23px rgba(10, 79, 51, 0.78);
  outline: 3px solid rgba(88, 211, 148, 0.32);
  outline-offset: 3px;
}
.target-card > p {
  margin: 0;
  color: #a9e9c8;
}
.target-card h2 {
  margin: 6px 0 8px;
  font-family: Georgia, "Times New Roman", serif;
  font-size: 23px;
  line-height: 1.16;
  overflow-wrap: anywhere;
}
.target-card span {
  display: block;
  color: rgba(255, 255, 255, 0.78);
  font-size: 13px;
  line-height: 1.4;
}
.target-card .target-card-action {
  display: none;
  margin-top: 14px;
  color: #fff;
  font-weight: 750;
}
.target-card[href] .target-card-action {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  white-space: nowrap;
}
.target-card .target-card-action [aria-hidden="true"] {
  display: inline;
}
.preview-panel {
  display: grid;
  gap: 10px;
  margin: 0;
  padding-top: 19px;
  border-top: 1px solid var(--line-strong);
}
.preview-panel .rail-kicker {
  margin: 0 0 6px;
}
.preview-header h2 {
  font-size: 18px;
}
.preview-edits {
  max-height: 210px;
  margin-top: 9px;
  padding: 11px;
  background: var(--panel-soft);
  border-color: var(--line);
  font-size: 12px;
}
.next-command {
  font-size: 13px;
}
.status {
  min-height: 20px;
  padding: 0 3px;
}
.rail-actions {
  display: grid;
  gap: 8px;
  padding-top: 2px;
}
.rail-done {
  width: 100%;
  min-height: 48px;
  font-weight: 750;
  box-shadow: 0 12px 28px -18px rgba(14, 107, 69, 0.75);
}
.article-dialog-trigger {
  justify-self: start;
  min-height: 0;
  padding: 0;
  color: var(--accent-strong);
  background: transparent;
  border: 0;
  border-radius: 0;
  font-size: 13px;
  font-weight: 650;
  line-height: 1.4;
  text-align: left;
}
.article-dialog-trigger:hover,
.article-dialog-trigger:focus-visible {
  color: var(--accent-strong);
  background: transparent;
}
.article-dialog-trigger:hover {
  outline: none;
}
.article-dialog-trigger:focus-visible {
  outline: 3px solid rgba(14, 107, 69, 0.22);
  outline-offset: 3px;
}
.article-more-count {
  color: var(--muted);
  font-weight: 600;
  white-space: nowrap;
}
.article-more-count::after {
  color: var(--faint);
  content: " ·";
}
.article-dialog-trigger:hover .article-dialog-action,
.article-dialog-trigger:focus-visible .article-dialog-action {
  text-decoration: underline;
  text-underline-offset: 2px;
}
.article-dialog {
  width: min(1180px, calc(100% - 32px));
  max-width: none;
  max-height: calc(100dvh - 32px);
  margin: auto;
  padding: 0;
  color: var(--ink);
  background: var(--panel);
  border: 1px solid rgba(255, 255, 255, 0.88);
  border-radius: 22px;
  box-shadow: 0 34px 90px -28px rgba(21, 23, 28, 0.62);
  overflow: auto;
}
.article-dialog::backdrop {
  background: rgba(24, 28, 26, 0.48);
  backdrop-filter: blur(3px);
}
.article-dialog-shell {
  min-height: 100%;
  padding: 26px 28px 30px;
}
.article-dialog-header {
  position: relative;
  display: grid;
  grid-template-columns: minmax(0, 1fr) auto;
  gap: 24px;
  align-items: start;
  padding-bottom: 24px;
  border-bottom: 1px solid var(--line);
}
.article-dialog-context {
  display: grid;
  grid-template-columns: 92px minmax(0, 1fr);
  gap: 18px;
  align-items: center;
}
.article-dialog-thumb {
  display: block;
  width: 92px;
  aspect-ratio: 4 / 5;
  object-fit: contain;
  background: linear-gradient(145deg, #ecece7, #f7f7f4);
  border-radius: 12px;
}
.article-dialog-copy .used-label {
  margin: 0 0 7px;
}
.article-dialog-copy h2 {
  margin: 0;
  font-size: clamp(24px, 3vw, 34px);
  line-height: 1.1;
  letter-spacing: -0.025em;
}
.article-dialog-copy p:last-child {
  margin: 9px 0 0;
  color: var(--muted);
  font-size: 14px;
}
.article-dialog-close {
  min-width: 74px;
  color: var(--muted);
  background: var(--panel-soft);
  border-color: var(--line-strong);
}
.article-dialog-list {
  columns: 5 190px;
  column-gap: 24px;
  margin: 0;
  padding: 26px 0 0;
  list-style: none;
}
.article-dialog-list li {
  position: relative;
  break-inside: avoid;
  margin: 0 0 12px;
  padding-left: 15px;
  font-size: 15px;
  font-weight: 500;
  line-height: 1.35;
}
.article-dialog-list li::before {
  position: absolute;
  top: 0.56em;
  left: 0;
  width: 5px;
  height: 5px;
  content: "";
  background: var(--accent);
  border-radius: 50%;
}
.article-dialog-list a {
  color: var(--ink);
  text-decoration: none;
}
.article-dialog-list a:hover,
.article-dialog-list a:focus-visible {
  color: var(--accent-strong);
  text-decoration: underline;
  text-underline-offset: 2px;
}

@media (max-width: 1120px) {
  .picker-workspace {
    grid-template-columns: minmax(0, 1fr) 300px;
  }
  .grid {
    grid-template-columns: repeat(2, minmax(0, 1fr));
    gap: 24px 20px;
  }
}
@media (max-width: 900px) {
  .app-shell {
    width: min(100% - 28px, 760px);
    padding-top: 14px;
  }
  .picker-workspace {
    grid-template-columns: 1fr;
  }
  .action-rail {
    position: static;
    grid-template-columns: 1fr 1fr;
    align-items: start;
    border-top: 1px solid var(--line);
    border-left: 0;
  }
  .rail-intro,
  .target-card {
    min-height: 100%;
  }
  .preview-panel,
  .rail-actions {
    grid-column: 1 / -1;
  }
  .mobile-save-actions {
    display: flex;
  }
  .reach-overview {
    grid-template-columns: 1fr;
  }
  .scope-tabs {
    width: min(100%, 540px);
  }
  .scope-panel,
  .scope-description {
    width: min(100%, 540px);
  }
}
@media (max-width: 620px) {
  .app-shell {
    width: 100%;
    padding: 0;
  }
  .picker-shell {
    border-radius: 0;
  }
  .picker-shell > .product-header,
  .picker-controls,
  .picker-shell .picker-main {
    padding-left: 14px;
    padding-right: 14px;
  }
  .picker-shell > .product-header {
    padding-top: 14px;
  }
  .header-main {
    display: grid;
    align-items: stretch;
  }
  .product-lockup {
    display: grid;
    gap: 7px;
  }
  .product-title {
    font-size: 39px;
  }
  .product-separator {
    display: none;
  }
  .product-credit {
    font-size: 15px;
    margin-left: 0;
  }
  .wikiportraits-logo {
    width: 28px;
    height: 28px;
  }
  .task-row {
    margin-top: 22px;
  }
  .task-title {
    font-size: 22px;
  }
  .reach-statement {
    padding: 8px 14px;
  }
  .reach-row {
    grid-template-columns: 34px max-content minmax(0, 1fr);
    gap: 10px;
    min-height: 74px;
  }
  .reach-icon {
    width: 34px;
    height: 34px;
    border-radius: 10px;
  }
  .reach-icon svg,
  .reach-icon img {
    width: 21px;
    height: 21px;
  }
  .reach-row strong {
    font-size: 46px;
  }
  .reach-label {
    font-size: 15px;
  }
  .mobile-save-actions {
    justify-content: flex-end;
  }
  .mobile-save-actions button {
    flex: 0 0 auto;
    min-width: 76px;
  }
  .grid {
    grid-template-columns: 1fr;
  }
  .action-rail {
    grid-template-columns: 1fr;
    padding: 0 14px 24px;
  }
  .preview-panel,
  .rail-actions {
    grid-column: auto;
  }
  .article-dialog {
    width: 100%;
    max-height: 100dvh;
    border: 0;
    border-radius: 0;
  }
  .article-dialog-shell {
    padding: 20px 18px 26px;
  }
  .article-dialog-header {
    gap: 14px;
  }
  .article-dialog-context {
    grid-template-columns: 70px minmax(0, 1fr);
    gap: 13px;
  }
  .article-dialog-thumb {
    width: 70px;
  }
  .article-dialog-copy h2 {
    font-size: 23px;
  }
  .article-dialog-close {
    min-width: 0;
    padding: 8px 10px;
  }
  .article-dialog-list {
    columns: 1;
    padding-top: 22px;
  }
}
</style>
</head>
<body>
<div class="app-shell">
  <section class="picker-shell" aria-labelledby="product-title screen-title">
    <header class="product-header">
      <div class="product-lockup">
        <h1 class="product-title" id="product-title">Credit Check</h1>
        <span class="product-credit">A free tool from <a class="wikiportraits-link" href="https://www.wikiportraits.org/" target="_blank" rel="noreferrer"><span>WikiPortraits</span><img class="wikiportraits-logo" src="https://custom-images.strikinglycdn.com/res/hrscywv4p/image/upload/c_limit,fl_lossy,h_300,w_300,f_auto,q_auto/60063/415018_168019.png" alt=""></a></span>
      </div>
    </header>
    <div class="picker-workspace">
      <div class="picker-content">
        <section class="picker-controls" aria-labelledby="screen-title">
        <div class="header-main">
          <div class="picker-identity">
            <div class="title-block">
              <div class="title-row task-row">
                <h2 class="task-title" id="screen-title">Your photos on Wikipedia:</h2>
              </div>
              <div class="reach-overview">
                <div class="scan-metrics" aria-label="Your Wikipedia reach and category progress">
                  <div class="reach-statement" aria-live="polite">
                  <div class="reach-row">
                    <span class="reach-icon" aria-hidden="true"><svg xmlns="http://www.w3.org/2000/svg" class="icon icon-tabler icons-tabler-outline icon-tabler-camera" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M5 7h1a2 2 0 0 0 2 -2a1 1 0 0 1 1 -1h6a1 1 0 0 1 1 1a2 2 0 0 0 2 2h1a2 2 0 0 1 2 2v9a2 2 0 0 1 -2 2h-14a2 2 0 0 1 -2 -2v-9a2 2 0 0 1 2 -2" /><path d="M9 13a3 3 0 1 0 6 0a3 3 0 0 0 -6 0" /></svg></span>
                    <strong id="in-use-count">—</strong>
                    <span class="reach-label" id="photo-noun">photos</span>
                  </div>
                  <div class="reach-row">
                    <span class="reach-icon" aria-hidden="true"><img src="https://commons.wikimedia.org/wiki/Special:Redirect/file/Wikipedia%27s_W.svg" alt=""></span>
                    <strong id="article-count">—</strong>
                    <span class="reach-label" id="article-noun">articles</span>
                  </div>
                  <div class="reach-row">
                    <span class="reach-icon" aria-hidden="true"><svg xmlns="http://www.w3.org/2000/svg" class="icon icon-tabler icons-tabler-outline icon-tabler-world" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M3 12a9 9 0 1 0 18 0a9 9 0 0 0 -18 0" /><path d="M3.6 9h16.8" /><path d="M3.6 15h16.8" /><path d="M11.5 3a17 17 0 0 0 0 18" /><path d="M12.5 3a17 17 0 0 1 0 18" /></svg></span>
                    <strong id="wikipedia-count">—</strong>
                    <span class="reach-label" id="wikipedia-noun">Wikipedia language editions</span>
                  </div>
                  </div>
                  <div class="wikidata-reach" id="wikidata-reach" hidden>
                    <span class="wikidata-reach-icon" aria-hidden="true"><img src="https://commons.wikimedia.org/wiki/Special:Redirect/file/Notification-icon-Wikidata-logo.svg" alt=""></span>
                    <span class="wikidata-reach-copy">
                      <span class="wikidata-reach-kicker">Beyond Wikipedia</span>
                      <span class="wikidata-reach-line"><strong id="wikidata-photo-count">— photos</strong> are used on <strong id="wikidata-item-count">— Wikidata items</strong></span>
                    </span>
                  </div>
                </div>
                <div class="scope-panel">
                <div class="scope-tabs" role="tablist" aria-label="Your photo views">
                  <button type="button" class="scope-tab active" id="missing-scope-tab" data-scope="missing" role="tab" aria-selected="true" aria-controls="sections"><span class="scope-tab-icon" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M20 13l-7 7-9-9V4h7l3 3"/><circle cx="8.5" cy="8.5" r="1.5"/><path d="M18 3v6M15 6h6"/></svg></span><span class="scope-tab-copy"><span class="scope-tab-title">Photos to add</span><span class="scope-tab-meta" id="missing-scope-label">— photos</span></span></button>
                  <button type="button" class="scope-tab" id="all-scope-tab" data-scope="all" role="tab" aria-selected="false" aria-controls="sections"><span class="scope-tab-icon" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="3" width="7" height="7" rx="1"/><rect x="14" y="3" width="7" height="7" rx="1"/><rect x="3" y="14" width="7" height="7" rx="1"/><rect x="14" y="14" width="7" height="7" rx="1"/></svg></span><span class="scope-tab-copy"><span class="scope-tab-title">All your photos</span><span class="scope-tab-meta" id="all-scope-label">— on Wikipedia</span></span></button>
                  <button type="button" class="scope-tab" id="wikidata-scope-tab" data-scope="wikidata" role="tab" aria-selected="false" aria-controls="sections"><span class="scope-tab-icon" aria-hidden="true"><img src="https://commons.wikimedia.org/wiki/Special:Redirect/file/Notification-icon-Wikidata-logo.svg" alt=""></span><span class="scope-tab-copy"><span class="scope-tab-title">On Wikidata</span><span class="scope-tab-meta" id="wikidata-scope-label">— photos · — items</span></span></button>
                </div>
                <p class="scope-description" id="scope-description">Choose photos to add to your photographer category on Wikimedia Commons.</p>
                </div>
              </div>
              <p class="missing-category-statement"><strong id="missing-category-count">—</strong> of your <span id="missing-photo-noun">photos</span> <span id="missing-verb">are</span> still missing your Wikimedia Commons category</p>
              <p class="scan-metrics-note" id="scan-metrics-note">Distinct article pages across all Wikipedia language editions. Each photo counts once.</p>
              <div class="review-counts">
                <p class="result-count" id="result-count"></p>
                <div class="summary" id="summary"></div>
              </div>
            </div>
          </div>
          <div class="save-actions mobile-save-actions">
            <button type="button" class="primary" data-action="done">Exit</button>
          </div>
        </div>
        <div class="toolbar-row primary-tools">
          <input id="search" type="search" autocomplete="off" aria-label="Filter photos" placeholder="Filter by filename, article, category, or number of Wikipedia articles">
          <div class="mode-tabs" role="group" aria-label="Review mode">
            <button type="button" data-mode="all">All</button>
            <button type="button" data-mode="selected">Selected</button>
            <button type="button" data-mode="unselected">Not selected yet</button>
          </div>
        </div>
        <div class="toolbar-row bulk-tools">
          <button type="button" class="secondary" data-action="select-visible">Select shown</button>
          <button type="button" class="secondary" data-action="clear-visible">Unselect shown</button>
          <button type="button" class="secondary" data-action="select-all">Select all</button>
          <button type="button" class="secondary" data-action="clear-all">Unselect all</button>
          <span class="keyboard-hint">Shortcuts: / search, Space select, o open</span>
        </div>
        </section>
        <main class="picker-main">
          <div class="notice" id="ambiguous-note"></div>
          <div class="empty" id="empty">No photos match this view.</div>
          <div class="sections" id="sections" aria-label="Photos"></div>
        </main>
      </div>
      <aside class="action-rail" aria-label="Selection and next step">
        <div class="rail-intro">
          <p class="rail-kicker">Your selection</p>
          <h2 id="rail-state-title">Choose the photos you want to gather under your name.</h2>
          <p id="rail-state-copy">Your choices save automatically. Nothing changes on Wikimedia Commons until you confirm the edits.</p>
          <div class="selection-flow" id="selection-flow" hidden>
            <strong id="rail-selected-count"></strong>
            <span aria-hidden="true">→</span>
            <span id="rail-flow-target"></span>
          </div>
        </div>
        <a class="target-card" id="target-card" target="_blank" rel="noreferrer">
          <p>Your photographer category</p>
          <h2 id="target-summary"></h2>
          <span class="target-card-action">Open on Wikimedia Commons <span aria-hidden="true">↗</span></span>
        </a>
        <section class="preview-panel" id="preview-panel">
          <div class="preview-header">
            <div>
              <p class="rail-kicker">Ready when you are</p>
              <h2>Wikimedia Commons edits</h2>
              <p id="preview-summary"></p>
            </div>
          </div>
          <details class="edit-receipt" id="edit-receipt" hidden>
            <summary>Review exact Wikimedia Commons edits</summary>
            <pre class="preview-edits" id="preview-edits"></pre>
          </details>
          <p class="next-command" id="next-command"></p>
        </section>
        <div class="rail-actions">
          <div class="status" id="status" role="status" aria-live="polite"></div>
          <button type="button" class="primary rail-done" data-action="done">Exit</button>
        </div>
        <section class="all-photos-rail" aria-label="About this gallery">
          <p class="rail-kicker" id="gallery-rail-kicker">All your photos</p>
          <h2 id="gallery-rail-title">Your complete Wikipedia gallery.</h2>
          <p id="gallery-rail-description">This read-only view contains all <strong id="all-rail-photo-count">—</strong> photos from this scan, including photos already in your photographer category.</p>
          <p id="gallery-rail-guidance">Switch to the missing-category tab to choose photos to add.</p>
        </section>
      </aside>
    </div>
  </section>
</div>
<dialog class="article-dialog" id="article-dialog" aria-labelledby="article-dialog-title" aria-describedby="article-dialog-description">
  <div class="article-dialog-shell">
    <header class="article-dialog-header">
      <div class="article-dialog-context">
        <img class="article-dialog-thumb" id="article-dialog-thumb" alt="">
        <div class="article-dialog-copy">
          <p class="used-label">Your photo appears in:</p>
          <h2 id="article-dialog-title" tabindex="-1"></h2>
          <p id="article-dialog-description" hidden></p>
        </div>
      </div>
      <form method="dialog">
        <button type="submit" class="article-dialog-close">Close</button>
      </form>
    </header>
    <ul class="article-dialog-list" id="article-dialog-list"></ul>
  </div>
</dialog>
<script>
window.CREDIT_CHECK_REVIEW = __REVIEW_JSON__;
window.CREDIT_CHECK_REVIEW_ARG = __REVIEW_ARG_JSON__;
window.CREDIT_CHECK_ITEMS = __ITEMS_JSON__;
window.CREDIT_CHECK_ALL_PHOTOS = __ALL_PHOTOS_JSON__;
window.CREDIT_CHECK_ALL_PHOTOS_AVAILABLE = __ALL_PHOTOS_AVAILABLE_JSON__;
window.CREDIT_CHECK_AMBIGUOUS_COUNT = __AMBIGUOUS_JSON__;
window.CREDIT_CHECK_METRICS = __METRICS_JSON__;
window.CREDIT_CHECK_INITIAL_MODE = __INITIAL_MODE_JSON__;
window.CREDIT_CHECK_INITIAL_SCOPE = __INITIAL_SCOPE_JSON__;
window.CREDIT_CHECK_GUIDED = __GUIDED_JSON__;

(() => {
  const reviewArg = window.CREDIT_CHECK_REVIEW_ARG;
  const ambiguousCount = window.CREDIT_CHECK_AMBIGUOUS_COUNT;
  const scanMetrics = window.CREDIT_CHECK_METRICS;
  const guidedMode = Boolean(window.CREDIT_CHECK_GUIDED);
  const items = window.CREDIT_CHECK_ITEMS.map((item) => ({
    ...item,
    selected: Boolean(item.checked),
  }));
  const allPhotosAvailable = Boolean(window.CREDIT_CHECK_ALL_PHOTOS_AVAILABLE);
  const allPhotos = window.CREDIT_CHECK_ALL_PHOTOS.map((item) => ({
    ...item,
    selected: false,
  }));
  const appShell = document.querySelector(".app-shell");
  const sections = document.getElementById("sections");
  const empty = document.getElementById("empty");
  const summary = document.getElementById("summary");
  const resultCount = document.getElementById("result-count");
  const status = document.getElementById("status");
  const search = document.getElementById("search");
  const modeButtons = Array.from(document.querySelectorAll("[data-mode]"));
  const scopeButtons = Array.from(document.querySelectorAll("[data-scope]"));
  const missingScopeTab = document.getElementById("missing-scope-tab");
  const allScopeTab = document.getElementById("all-scope-tab");
  const missingScopeText = document.getElementById("missing-scope-label");
  const allScopeText = document.getElementById("all-scope-label");
  const wikidataScopeText = document.getElementById("wikidata-scope-label");
  const scopeDescription = document.getElementById("scope-description");
  const screenTitle = document.getElementById("screen-title");
  const inUseCount = document.getElementById("in-use-count");
  const articleCount = document.getElementById("article-count");
  const wikipediaCount = document.getElementById("wikipedia-count");
  const wikidataReach = document.getElementById("wikidata-reach");
  const wikidataPhotoCount = document.getElementById("wikidata-photo-count");
  const wikidataItemCount = document.getElementById("wikidata-item-count");
  const missingCategoryCount = document.getElementById("missing-category-count");
  const photoNoun = document.getElementById("photo-noun");
  const articleNoun = document.getElementById("article-noun");
  const wikipediaNoun = document.getElementById("wikipedia-noun");
  const missingPhotoNoun = document.getElementById("missing-photo-noun");
  const missingVerb = document.getElementById("missing-verb");
  const scanMetricsNote = document.getElementById("scan-metrics-note");
  const ambiguousNote = document.getElementById("ambiguous-note");
  const previewSummary = document.getElementById("preview-summary");
  const previewEdits = document.getElementById("preview-edits");
  const editReceipt = document.getElementById("edit-receipt");
  const nextCommand = document.getElementById("next-command");
  const targetSummary = document.getElementById("target-summary");
  const targetCard = document.getElementById("target-card");
  const railStateTitle = document.getElementById("rail-state-title");
  const railStateCopy = document.getElementById("rail-state-copy");
  const selectionFlow = document.getElementById("selection-flow");
  const railSelectedCount = document.getElementById("rail-selected-count");
  const railFlowTarget = document.getElementById("rail-flow-target");
  const allRailPhotoCount = document.getElementById("all-rail-photo-count");
  const galleryRailKicker = document.getElementById("gallery-rail-kicker");
  const galleryRailTitle = document.getElementById("gallery-rail-title");
  const galleryRailDescription = document.getElementById("gallery-rail-description");
  const galleryRailGuidance = document.getElementById("gallery-rail-guidance");
  const doneButtons = Array.from(document.querySelectorAll('[data-action="done"]'));
  const articleDialog = document.getElementById("article-dialog");
  const articleDialogTitle = document.getElementById("article-dialog-title");
  const articleDialogThumb = document.getElementById("article-dialog-thumb");
  const articleDialogDescription = document.getElementById("article-dialog-description");
  const articleDialogList = document.getElementById("article-dialog-list");
  const targets = Array.from(new Set(items.map((item) => item.target)));
  const singleTarget = targets.length === 1;
  const ENGLISH_ARTICLE_LIMIT = 5;
  const wikipediaLanguageNames = {
    "als": "Alemannic",
    "bat-smg": "Samogitian",
    "be-tarask": "Belarusian (Taraškievica)",
    "cbk-zam": "Chavacano",
    "fiu-vro": "Võro",
    "map-bms": "Banyumasan",
    "nds-nl": "Dutch Low Saxon",
    "roa-rup": "Aromanian",
    "roa-tara": "Tarantino",
    "simple": "Simple English",
    "zh-classical": "Classical Chinese",
    "zh-min-nan": "Min Nan Chinese",
    "zh-yue": "Cantonese",
  };
  const languageDisplayNames = typeof Intl.DisplayNames === "function"
    ? new Intl.DisplayNames(["en"], { type: "language" })
    : null;
  let currentMode = ["all", "selected", "unselected"].includes(window.CREDIT_CHECK_INITIAL_MODE)
    ? window.CREDIT_CHECK_INITIAL_MODE
    : "all";
  let currentScope = window.CREDIT_CHECK_INITIAL_SCOPE === "all" && allPhotosAvailable
    ? "all"
    : (items.length ? "missing" : (allPhotosAvailable ? "all" : "missing"));
  let lastFocusedLine = items.length ? items[0].line : null;
  let saveTimer = null;
  let pendingSave = false;
  let selectionRevision = 0;
  let articleDialogOpener = null;

  screenTitle.textContent = "Your photos on Wikipedia:";
  const metricValues = [
    scanMetrics.in_use_total,
    scanMetrics.article_total,
    scanMetrics.wikipedia_total,
  ];
  const hasReachMetrics = metricValues.every((value) => Number.isInteger(value));
  if (hasReachMetrics) {
    inUseCount.textContent = scanMetrics.in_use_total.toLocaleString("en-US");
    articleCount.textContent = scanMetrics.article_total.toLocaleString("en-US");
    wikipediaCount.textContent = scanMetrics.wikipedia_total.toLocaleString("en-US");
    photoNoun.textContent = scanMetrics.in_use_total === 1 ? "photo" : "photos";
    articleNoun.textContent = scanMetrics.article_total === 1 ? "article" : "articles";
    wikipediaNoun.textContent = scanMetrics.wikipedia_total === 1
      ? "Wikipedia language edition"
      : "Wikipedia language editions";
  } else {
    scanMetricsNote.textContent = "Scan again to calculate your complete Wikipedia reach.";
  }
  const wikidataPhotos = allPhotos.filter((item) => (item.wikidata_items || []).length > 0);
  const wikidataItemIds = new Set(
    wikidataPhotos.flatMap((item) => item.wikidata_items.map((entry) => entry.id))
  );
  if (wikidataPhotos.length) {
    wikidataReach.hidden = false;
    wikidataPhotoCount.textContent = `${wikidataPhotos.length.toLocaleString("en-US")} ${wikidataPhotos.length === 1 ? "photo" : "photos"}`;
    wikidataItemCount.textContent = `${wikidataItemIds.size.toLocaleString("en-US")} Wikidata ${wikidataItemIds.size === 1 ? "item" : "items"}`;
  }
  const missingTotal = Number.isInteger(scanMetrics.missing_category_total)
    ? scanMetrics.missing_category_total
    : items.length;
  missingCategoryCount.textContent = missingTotal.toLocaleString("en-US");
  missingPhotoNoun.textContent = missingTotal === 1 ? "photo" : "photos";
  missingVerb.textContent = missingTotal === 1 ? "is" : "are";
  const missingScopeLabel = `${missingTotal.toLocaleString("en-US")} ${missingTotal === 1 ? "photo" : "photos"}`;
  const allPhotosTotal = Number.isInteger(scanMetrics.in_use_total)
    ? scanMetrics.in_use_total
    : allPhotos.length;
  allRailPhotoCount.textContent = allPhotosTotal.toLocaleString("en-US");
  const allScopeLabel = `${allPhotosTotal.toLocaleString("en-US")} on Wikipedia`;
  const wikidataScopeLabel = `${wikidataPhotos.length.toLocaleString("en-US")} ${wikidataPhotos.length === 1 ? "photo" : "photos"} · ${wikidataItemIds.size.toLocaleString("en-US")} ${wikidataItemIds.size === 1 ? "item" : "items"}`;
  allScopeTab.disabled = !allPhotosAvailable;
  document.getElementById("wikidata-scope-tab").disabled = !wikidataPhotos.length;
  if (!allPhotosAvailable) {
    allScopeTab.title = "Scan again to create your complete all-photos gallery.";
  }
  const photographerPrefix = "Photographs by ";
  if (singleTarget && targets[0].startsWith(photographerPrefix)) {
    targetSummary.append(
      document.createTextNode(photographerPrefix.trim()),
      document.createElement("br"),
      document.createTextNode(targets[0].slice(photographerPrefix.length))
    );
  } else {
    targetSummary.textContent = singleTarget
      ? targets[0]
      : `${targets.length} Wikimedia Commons categories`;
  }
  function commonsCategoryUrl(category) {
    const path = `Category:${category}`.replace(/ /g, "_");
    return `https://commons.wikimedia.org/wiki/${encodeURIComponent(path)
      .replace(/%3A/g, ":")
      .replace(/%2F/g, "/")}`;
  }
  if (singleTarget) {
    targetCard.href = commonsCategoryUrl(targets[0]);
    targetCard.setAttribute(
      "aria-label",
      `Open Category:${targets[0]} on Wikimedia Commons`
    );
  }
  if (ambiguousCount > 0) {
    const noun = ambiguousCount === 1 ? "photo needs" : "photos need";
    const pron = ambiguousCount === 1 ? "it" : "they";
    ambiguousNote.textContent = `${ambiguousCount} ${noun} a category before ${pron} can appear here.`;
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
    const articleTitles = (item.articles || []).map((article) => article.title);
    const wikidataText = (item.wikidata_items || []).flatMap((entry) => [entry.label, entry.id]);
    return [item.caption, item.label, item.title, item.target, item.uses, ...articleTitles, ...wikidataText]
      .join(" ")
      .toLowerCase();
  }

  function filenamePhotoTitle(label) {
    return String(label || "")
      .replace(/\\.[^.]+$/, "")
      .replace(/\\s*\\((?:cropped[^)]*)\\)\\s*$/i, "")
      .replace(/^\\d{4}-\\d{2}-\\d{2}\\s+/, "")
      .replace(/\\s+\\d+\\s*$/, "")
      .replace(/[-_]+/g, " ")
      .replace(/\\s+/g, " ")
      .trim();
  }

  function currentItems() {
    return currentScope === "missing" ? items : allPhotos;
  }

  function visibleItems() {
    const query = search.value.trim().toLowerCase();
    return currentItems().filter((item) => {
      if (currentScope === "missing" && currentMode === "selected" && !item.selected) return false;
      if (currentScope === "missing" && currentMode === "unselected" && item.selected) return false;
      if (currentScope === "wikidata" && !(item.wikidata_items || []).length) return false;
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
    if (item.uses === null || item.uses === undefined) return "Wikipedia use unknown";
    return `${item.uses} Wikipedia ${item.uses === 1 ? "page" : "pages"}`;
  }

  function articleLanguage(article) {
    if (article.lang) return article.lang.toLowerCase();
    return (article.wiki || "").split(".", 1)[0].toLowerCase();
  }

  function languageName(code) {
    if (!code) return "Unknown language";
    if (wikipediaLanguageNames[code]) return wikipediaLanguageNames[code];
    if (languageDisplayNames) {
      try {
        const name = languageDisplayNames.of(code);
        if (name && name.toLowerCase() !== code.toLowerCase()) return name;
      } catch (error) {
        // Some Wikimedia language codes predate or extend BCP 47.
      }
    }
    return code.toUpperCase();
  }

  function articleListHtml(articles, showLanguage = false, preview = false) {
    return `<ul class="${preview ? "article-preview-list" : "article-list"}">${articles.map((article) => {
      const language = showLanguage
        ? `<span class="article-language">${escapeHtml(languageName(articleLanguage(article)))} Wikipedia</span>`
        : "";
      return `<li><a href="${escapeHtml(article.url)}" target="_blank" rel="noreferrer">${escapeHtml(article.title)}</a>${language}</li>`;
    }).join("")}</ul>`;
  }

  function articleDialogListHtml(articles) {
    return articles.map((article) =>
      `<li><a href="${escapeHtml(article.url)}" target="_blank" rel="noreferrer">${escapeHtml(article.title)}</a></li>`
    ).join("");
  }

  function groupedArticleHtml(articles) {
    const groups = new Map();
    articles.forEach((article) => {
      const language = articleLanguage(article);
      if (!groups.has(language)) groups.set(language, []);
      groups.get(language).push(article);
    });
    return Array.from(groups.entries())
      .sort(([left], [right]) => languageName(left).localeCompare(languageName(right)))
      .map(([language, languageArticles]) => `<section class="language-group">
        <h3>${escapeHtml(languageName(language))} Wikipedia (${languageArticles.length})</h3>
        ${articleListHtml(languageArticles)}
      </section>`)
      .join("");
  }

  function moreWikipediaPages(pageCount, languageCount, otherLanguages = false) {
    const pageWord = pageCount === 1 ? "page" : "pages";
    const languageWord = languageCount === 1 ? "language" : "languages";
    const preposition = languageCount === 1 ? "in" : "across";
    return `${pageCount} more Wikipedia ${pageWord} ${preposition} ${languageCount} ${otherLanguages ? "other " : ""}${languageWord}`;
  }

  function articleHtml(item) {
    const articles = item.articles || [];
    if (!articles.length) {
      return `<p class="article-fallback">${escapeHtml(usesText(item))}</p>`;
    }
    const englishArticles = articles.filter((article) => articleLanguage(article) === "en");
    const otherArticles = articles.filter((article) => articleLanguage(article) !== "en");

    if (!englishArticles.length) {
      const primary = articles[0];
      const remaining = articles.slice(1);
      const remainingLanguages = new Set(remaining.map(articleLanguage)).size;
      const more = remaining.length
        ? `<details class="article-disclosure other-language-disclosure">
            <summary>Plus ${escapeHtml(moreWikipediaPages(remaining.length, remainingLanguages))}</summary>
            <div class="language-groups">${groupedArticleHtml(remaining)}</div>
          </details>`
        : "";
      return `${articleListHtml([primary], true, true)}${more}`;
    }

    const visibleEnglish = englishArticles.slice(0, ENGLISH_ARTICLE_LIMIT);
    const hiddenEnglishCount = englishArticles.length - visibleEnglish.length;
    const otherLanguages = new Set(otherArticles.map(articleLanguage)).size;
    const allEnglish = hiddenEnglishCount > 0
      ? `<button type="button" class="article-dialog-trigger" data-article-dialog-line="${item.line}" aria-haspopup="dialog"><span class="article-more-count">+ ${hiddenEnglishCount} more</span> <span class="article-dialog-action">View all ${englishArticles.length} English-language Wikipedia articles</span></button>`
      : "";
    const moreLanguages = otherArticles.length
      ? `<details class="article-disclosure other-language-disclosure">
          <summary>Plus ${escapeHtml(moreWikipediaPages(otherArticles.length, otherLanguages, true))}</summary>
          <div class="language-groups">${groupedArticleHtml(otherArticles)}</div>
        </details>`
      : "";
    return `${articleListHtml(visibleEnglish, false, true)}${allEnglish}${moreLanguages}`;
  }

  function wikidataHtml(item) {
    const wikidataItems = item.wikidata_items || [];
    if (!wikidataItems.length) return "";
    const noun = wikidataItems.length === 1 ? "item" : "items";
    const rows = wikidataItems.map((entry) => {
      const label = entry.label || entry.id;
      const id = label === entry.id ? "" : ` <span class="wikidata-id">(${escapeHtml(entry.id)})</span>`;
      return `<li><a href="${escapeHtml(entry.url)}" target="_blank" rel="noreferrer">${escapeHtml(label)}${id}</a></li>`;
    }).join("");
    return `<details class="wikidata-disclosure">
      <summary>Also used on Wikidata · ${wikidataItems.length} ${noun}</summary>
      <ul class="article-list wikidata-list">${rows}</ul>
    </details>`;
  }

  function openArticleDialog(line, opener) {
    const item = currentItems().find((candidate) => candidate.line === line);
    if (!item) return;
    const englishArticles = (item.articles || []).filter(
      (article) => articleLanguage(article) === "en"
    );
    if (!englishArticles.length) return;
    articleDialogOpener = opener;
    articleDialogTitle.textContent = `${englishArticles.length} English-language Wikipedia ${englishArticles.length === 1 ? "article" : "articles"}`;
    articleDialogThumb.src = item.thumb_url;
    const caption = String(item.caption || "").trim();
    articleDialogDescription.textContent = caption;
    articleDialogDescription.hidden = !caption;
    articleDialogList.innerHTML = articleDialogListHtml(englishArticles);
    articleDialog.showModal();
    articleDialogTitle.focus({ preventScroll: true });
  }

  function cardHtml(item) {
    const readOnly = currentScope !== "missing";
    const selectedClass = !readOnly && item.selected ? " selected" : "";
    const checked = item.selected ? " checked" : "";
    const targetLine = singleTarget ? "" : `<p class="target">Category:${escapeHtml(item.target)}</p>`;
    const selectionLabel = item.selected ? `Unselect ${item.label}` : `Select ${item.label}`;
    const caption = String(item.caption || "").trim();
    const photoTitle = caption || filenamePhotoTitle(item.label);
    const captionLine = photoTitle
      ? `<div class="photo-title"><p class="photo-caption" title="${escapeHtml(photoTitle)}">${escapeHtml(photoTitle)}</p></div>`
      : "";
    const selectionControl = readOnly ? "" : `<label class="select-control" title="${escapeHtml(selectionLabel)}">
          <input type="checkbox" data-line="${item.line}" aria-label="${escapeHtml(selectionLabel)}"${checked}>
          <span class="select-indicator" aria-hidden="true">✓</span>
        </label>`;
    return `<article class="photo${selectedClass}${readOnly ? " read-only" : ""}"${readOnly ? "" : ' tabindex="0"'} data-line="${item.line}" data-file-url="${escapeHtml(item.file_url)}">
      ${captionLine}
      <div class="photo-image">
        ${selectionControl}
        <a class="thumb" href="${escapeHtml(item.file_url)}" target="_blank" rel="noreferrer">
          <span class="thumb-placeholder">Loading thumbnail</span>
          <img src="${escapeHtml(item.thumb_url)}" loading="lazy" alt="">
        </a>
      </div>
      <div class="photo-content">
        <p class="used-label">Your photo appears in:</p>
        ${articleHtml(item)}
        ${wikidataHtml(item)}
        <details class="photo-details">
          <summary>Photo details</summary>
          <div class="technical-details">
            <h3 class="file-name">${escapeHtml(item.label)}</h3>
            <div class="card-footer">
              <a class="commons-link" href="${escapeHtml(item.file_url)}" target="_blank" rel="noreferrer">Open on Wikimedia Commons ↗</a>
            </div>
            ${targetLine}
          </div>
        </details>
      </div>
    </article>`;
  }

  function sectionHtml(group) {
    const readOnly = currentScope !== "missing";
    const title = currentScope === "wikidata"
      ? "Your photos used on Wikidata"
      : readOnly
      ? "All your photos on Wikipedia"
      : singleTarget ? "Choose photos to add" : `Category:${group.target}`;
    const count = currentScope === "wikidata"
      ? `${wikidataPhotos.length.toLocaleString("en-US")} ${wikidataPhotos.length === 1 ? "photo" : "photos"} across ${wikidataItemIds.size.toLocaleString("en-US")} Wikidata ${wikidataItemIds.size === 1 ? "item" : "items"}`
      : `${group.items.length} ${group.items.length === 1 ? "photo" : "photos"}`;
    const selected = group.items.filter((item) => item.selected).length;
    return `<section class="section" data-target="${escapeHtml(group.target)}">
      <div class="section-heading">
        <h2>${escapeHtml(title)}</h2>
        <div class="section-heading-meta">
          <p>${readOnly ? count : `${selected} selected / ${count}`}</p>
        </div>
      </div>
      <div class="grid">${group.items.map(cardHtml).join("")}</div>
    </section>`;
  }

  function updateSummary(visible) {
    if (currentScope !== "missing") {
      const scopeTotal = currentScope === "wikidata" ? wikidataPhotos.length : allPhotos.length;
      resultCount.textContent = visible.length === scopeTotal
        ? `${scopeTotal} ${scopeTotal === 1 ? "photo" : "photos"} in this gallery`
        : `${visible.length} of ${scopeTotal} photos showing`;
      return;
    }
    const selected = items.filter((item) => item.selected).length;
    summary.textContent = `${selected} selected`;
    resultCount.textContent = visible.length === items.length
      ? `${items.length} photos ready to review below`
      : `${visible.length} of ${items.length} photos showing`;
  }

  function renderModeButtons() {
    modeButtons.forEach((button) => {
      const active = button.dataset.mode === currentMode;
      button.classList.toggle("active", active);
      button.setAttribute("aria-pressed", active ? "true" : "false");
    });
  }

  function renderScopeButtons() {
    missingScopeText.textContent = missingScopeLabel;
    allScopeText.textContent = allScopeLabel;
    wikidataScopeText.textContent = wikidataScopeLabel;
    scopeButtons.forEach((button) => {
      const active = button.dataset.scope === currentScope;
      button.classList.toggle("active", active);
      button.setAttribute("aria-selected", active ? "true" : "false");
    });
    scopeDescription.textContent = currentScope === "all"
      ? "Browse every photo from this scan, including photos already in your category."
      : currentScope === "wikidata"
        ? "See which of your photos are used on Wikidata items."
        : "Choose photos to add to your photographer category on Wikimedia Commons.";
    appShell.classList.toggle("all-photos-view", currentScope !== "missing");
    ambiguousNote.hidden = currentScope !== "missing";
    if (currentScope === "wikidata") {
      galleryRailKicker.textContent = "Wikidata view";
      galleryRailTitle.textContent = "Your Wikidata photo gallery.";
      galleryRailDescription.textContent = `${wikidataPhotos.length} photos used across ${wikidataItemIds.size} Wikidata items.`;
      galleryRailGuidance.textContent = "Choose All Wikipedia photos above to return to the complete gallery.";
    } else {
      galleryRailKicker.textContent = "All your photos";
      galleryRailTitle.textContent = "Your complete Wikipedia gallery.";
      galleryRailDescription.innerHTML = `This read-only view contains all <strong>${allPhotosTotal.toLocaleString("en-US")}</strong> photos from this scan, including photos already in your photographer category.`;
      galleryRailGuidance.textContent = "Switch to the missing-category tab to choose photos to add.";
    }
  }

  function selectedItems() {
    return items.filter((item) => item.selected);
  }

  function selectedLines() {
    return selectedItems().map((item) => item.line);
  }

  function savePayload(closeAfter) {
    return {
      selected_lines: selectedLines(),
      close: Boolean(closeAfter),
      revision: selectionRevision,
    };
  }

  function nextStepText() {
    if (guidedMode) {
      return "Click Exit below, then choose Add selected photos to your photographer category page on Wikimedia Commons from the menu.";
    }
    return `Next: credit-check commit ${reviewArg} --go`;
  }

  function renderPreview() {
    const selected = selectedItems();
    if (!selected.length) {
      railStateTitle.textContent = "Choose the photos you want to gather under your name.";
      railStateCopy.textContent = "Your choices save automatically. Nothing changes on Wikimedia Commons until you confirm the edits.";
      selectionFlow.hidden = true;
      previewSummary.textContent = "No photos selected yet.";
      previewEdits.textContent = "";
      editReceipt.hidden = true;
      nextCommand.textContent = "";
      doneButtons.forEach((button) => { button.textContent = "Exit"; });
      return;
    }
    const selectedTargets = Array.from(new Set(selected.map((item) => item.target)));
    const photoNoun = selected.length === 1 ? "photo" : "photos";
    railStateTitle.textContent = `${selected.length} ${photoNoun} selected`;
    railStateCopy.textContent = "Your choices are saved. Review the exact edits below, or keep choosing photos.";
    railSelectedCount.textContent = `${selected.length} ${photoNoun}`;
    railFlowTarget.textContent = selectedTargets.length === 1
      ? selectedTargets[0]
      : `${selectedTargets.length} Wikimedia Commons categories`;
    selectionFlow.hidden = false;
    previewSummary.textContent = `${selected.length} ${selected.length === 1 ? "category edit" : "category edits"} ready for Wikimedia Commons.`;
    previewEdits.textContent = selected.map((item) =>
      `+ [[Category:${item.target}]]  ->  ${item.title}`
    ).join("\\n");
    editReceipt.hidden = false;
    nextCommand.textContent = nextStepText();
    doneButtons.forEach((button) => { button.textContent = "Exit"; });
  }

  function syncThumbnailState(image, failed = false) {
    const thumb = image.closest(".thumb");
    if (!thumb) return;
    const placeholder = thumb.querySelector(".thumb-placeholder");
    const loaded = !failed && image.naturalWidth > 0;
    const missing = failed || (image.complete && image.naturalWidth === 0);
    thumb.classList.toggle("image-loaded", loaded);
    thumb.classList.toggle("image-missing", missing);
    if (!placeholder) return;
    placeholder.hidden = loaded;
    placeholder.textContent = missing
      ? "Thumbnail unavailable — open on Wikimedia Commons"
      : "Loading thumbnail";
  }

  function reconcileThumbnails() {
    const images = Array.from(sections.querySelectorAll(".thumb img"));
    images.slice(0, 6).forEach((image) => {
      image.loading = "eager";
      image.fetchPriority = "high";
    });
    images.forEach((image) => {
      if (image.complete) syncThumbnailState(image);
    });
  }

  function render() {
    const visible = visibleItems();
    renderScopeButtons();
    renderModeButtons();
    updateSummary(visible);
    empty.classList.toggle("show", visible.length === 0);
    const groups = currentScope !== "missing"
      ? [{ target: "", items: visible }]
      : groupItems(visible);
    sections.innerHTML = groups.map(sectionHtml).join("");
    reconcileThumbnails();
    renderPreview();
  }

  function syncCard(card, item) {
    if (!card || !item) return;
    card.classList.toggle("selected", item.selected);
    const checkbox = card.querySelector('input[type="checkbox"]');
    const selectionLabel = item.selected ? `Unselect ${item.label}` : `Select ${item.label}`;
    if (checkbox) {
      checkbox.checked = item.selected;
      checkbox.setAttribute("aria-label", selectionLabel);
    }
    const label = card.querySelector(".select-control");
    if (label) label.title = selectionLabel;
  }

  function updateSectionCounts() {
    const visible = visibleItems();
    sections.querySelectorAll(".section").forEach((section) => {
      const group = visible.filter((item) => item.target === section.dataset.target);
      const selected = group.filter((item) => item.selected).length;
      const noun = group.length === 1 ? "photo" : "photos";
      const count = section.querySelector(".section-heading p");
      if (count) count.textContent = `${selected} selected / ${group.length} ${noun}`;
    });
  }

  function refreshSelectionUi(line = null) {
    if (currentMode !== "all") {
      render();
      return;
    }
    if (line === null) {
      sections.querySelectorAll(".photo[data-line]").forEach((card) => {
        const item = items.find((candidate) => candidate.line === Number(card.dataset.line));
        syncCard(card, item);
      });
    } else {
      const item = items.find((candidate) => candidate.line === line);
      syncCard(document.querySelector(`.photo[data-line="${line}"]`), item);
    }
    const visible = visibleItems();
    updateSummary(visible);
    updateSectionCounts();
    renderPreview();
  }

  function setSelection(lines, value) {
    const lineSet = new Set(lines);
    let changed = false;
    items.forEach((item) => {
      if (lineSet.has(item.line) && item.selected !== value) {
        item.selected = value;
        changed = true;
      }
    });
    if (changed) {
      refreshSelectionUi();
      selectionRevision += 1;
      scheduleSave();
    }
  }

  function toggleLine(line) {
    const item = items.find((candidate) => candidate.line === line);
    if (!item) return;
    item.selected = !item.selected;
    selectionRevision += 1;
    lastFocusedLine = line;
    refreshSelectionUi(line);
    scheduleSave();
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
    const item = currentItems().find((candidate) => candidate.line === line);
    if (item) window.open(item.file_url, "_blank", "noopener");
  }

  function scheduleSave() {
    pendingSave = true;
    status.textContent = "Saving...";
    if (saveTimer) {
      clearTimeout(saveTimer);
    }
    saveTimer = setTimeout(() => {
      saveTimer = null;
      save(false);
    }, 500);
  }

  function flushPendingSaveBeacon() {
    if (!pendingSave && !saveTimer) return;
    if (saveTimer) {
      clearTimeout(saveTimer);
      saveTimer = null;
    }
    pendingSave = false;
    const body = JSON.stringify(savePayload(false));
    if (navigator.sendBeacon) {
      navigator.sendBeacon("/save", new Blob([body], { type: "application/json" }));
      return;
    }
    fetch("/save", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body,
      keepalive: true,
    }).catch(() => {});
  }

  function saveErrorMessage(error) {
    const message = error && error.message ? error.message : String(error);
    if (message.toLowerCase().includes("changed on disk")) {
      return "Review changed on disk - reload the page.";
    }
    return `Save failed: ${message}`;
  }

  async function save(closeAfter) {
    if (saveTimer) {
      clearTimeout(saveTimer);
      saveTimer = null;
    }
    pendingSave = true;
    status.textContent = "Saving...";
    try {
      const response = await fetch("/save", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(savePayload(closeAfter)),
      });
      const data = await response.json();
      if (!response.ok || !data.ok) {
        throw new Error(data.error || response.statusText);
      }
      pendingSave = false;
      renderPreview();
      if (closeAfter) {
        status.textContent = "Saved. Closing this tab...";
        setTimeout(() => {
          window.close();
          setTimeout(() => {
            status.textContent = "Saved. You can now close this tab.";
          }, 400);
        }, 50);
        return true;
      }
      status.textContent = "Saved";
      return true;
    } catch (error) {
      pendingSave = false;
      status.textContent = saveErrorMessage(error);
      return false;
    }
  }

  sections.addEventListener("change", (event) => {
    const checkbox = event.target.closest('input[type="checkbox"][data-line]');
    if (!checkbox) return;
    toggleLine(Number(checkbox.dataset.line));
  });

  sections.addEventListener("click", (event) => {
    const articleTrigger = event.target.closest("[data-article-dialog-line]");
    if (articleTrigger) {
      openArticleDialog(Number(articleTrigger.dataset.articleDialogLine), articleTrigger);
      return;
    }
    const card = event.target.closest(".photo");
    if (!card) return;
    lastFocusedLine = Number(card.dataset.line);
    if (currentScope !== "missing") return;
    if (event.target.closest("a, button, input, label, summary, details")) return;
    toggleLine(Number(card.dataset.line));
  });

  sections.addEventListener("focusin", (event) => {
    const card = event.target.closest(".photo");
    if (card) lastFocusedLine = Number(card.dataset.line);
  });

  sections.addEventListener("keydown", (event) => {
    if (currentScope !== "missing") return;
    const card = event.target.closest(".photo");
    if (!card || (event.key !== " " && event.key !== "Enter")) return;
    if (event.target.closest("a, button, input, summary, details")) return;
    event.preventDefault();
    toggleLine(Number(card.dataset.line));
  });

  sections.addEventListener("load", (event) => {
    if (event.target.tagName !== "IMG") return;
    syncThumbnailState(event.target);
  }, true);

  sections.addEventListener("error", (event) => {
    if (event.target.tagName !== "IMG") return;
    syncThumbnailState(event.target, true);
  }, true);

  document.addEventListener("keydown", (event) => {
    if (articleDialog.open) return;
    const typing = event.target.matches("input, textarea, select");
    const interactive = event.target.closest("a, button, input, label, summary, details");
    if (event.key === "/" && !typing) {
      event.preventDefault();
      search.focus();
      search.select();
      return;
    }
    if (typing || interactive) return;
    if (event.key === "o") {
      const line = focusedLine();
      if (line !== null) {
        event.preventDefault();
        openLine(line);
      }
    } else if (event.key === " ") {
      if (currentScope !== "missing") return;
      const line = focusedLine();
      if (line !== null && document.activeElement.closest(".photo")) {
        event.preventDefault();
        toggleLine(line);
      }
    }
  });

  articleDialog.addEventListener("click", (event) => {
    if (event.target === articleDialog) articleDialog.close();
  });
  articleDialog.addEventListener("close", () => {
    const opener = articleDialogOpener;
    articleDialogOpener = null;
    articleDialogThumb.removeAttribute("src");
    articleDialogDescription.textContent = "";
    articleDialogDescription.hidden = true;
    articleDialogList.innerHTML = "";
    if (opener && opener.isConnected) opener.focus({ preventScroll: true });
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
  doneButtons.forEach((button) => {
    button.addEventListener("click", () => save(true));
  });
  search.addEventListener("input", render);
  modeButtons.forEach((button) => {
    button.addEventListener("click", () => {
      currentMode = button.dataset.mode;
      status.textContent = currentMode === "selected"
        ? "Showing only photos you selected."
        : currentMode === "unselected"
          ? "Showing photos you have not selected yet."
          : "";
      render();
    });
  });
  scopeButtons.forEach((button) => {
    button.addEventListener("click", () => {
      if (button.disabled || button.dataset.scope === currentScope) return;
      currentScope = button.dataset.scope;
      currentMode = "all";
      lastFocusedLine = currentItems().length ? currentItems()[0].line : null;
      status.textContent = currentScope === "all"
        ? "Showing all your photos on Wikipedia."
        : currentScope === "wikidata"
          ? `Showing ${wikidataPhotos.length} photos used on Wikidata.`
          : "Showing photos missing your Wikimedia Commons category.";
      render();
    });
  });
  window.addEventListener("beforeunload", flushPendingSaveBeacon);
  window.addEventListener("pagehide", flushPendingSaveBeacon);

  render();
})();
</script>
</body>
</html>
""".replace("__REVIEW_JSON__", review_json).replace(
        "__REVIEW_ARG_JSON__", review_arg_json).replace(
        "__ITEMS_JSON__", items_json).replace(
        "__ALL_PHOTOS_JSON__", all_photos_json).replace(
        "__ALL_PHOTOS_AVAILABLE_JSON__", all_photos_available_json).replace(
        "__AMBIGUOUS_JSON__", ambiguous_json).replace(
        "__METRICS_JSON__", metrics_json).replace(
        "__INITIAL_MODE_JSON__", initial_mode_json).replace(
        "__INITIAL_SCOPE_JSON__", initial_scope_json).replace(
        "__GUIDED_JSON__", guided_json)

class LocalReviewServer(http.server.ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True

def review_web_handler(review, items, approvable, ambiguous_count=0, initial_mode="all",
                       guided=False, scan_metrics=None, all_photos=None,
                       initial_scope="missing"):
    page = web_review_html(review, approvable, ambiguous_count, initial_mode,
                           guided=guided, scan_metrics=scan_metrics,
                           all_photos=all_photos,
                           initial_scope=initial_scope).encode("utf-8")

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

                close_after = bool(data.get("close"))
                with self.server.review_lock:
                    revision = data.get("revision")
                    if revision is not None:
                        revision = int(revision)
                        if revision < self.server.review_client_revision:
                            current_items = parse_review_items(review)
                            selected_count = len([
                                item for item in current_items
                                if item["target"] and item["checked"]
                            ])
                            self.server.saved_count = selected_count
                            self.send_json(200, {
                                "ok": True,
                                "selected": selected_count,
                                "stale": True,
                            })
                            if close_after:
                                threading.Thread(
                                    target=self.server.shutdown, daemon=True).start()
                            return

                    current_items = parse_review_items(review)
                    if review_items_signature(current_items) != self.server.review_signature:
                        raise ReviewChangedError(
                            "%s changed on disk. Reload the browser page before saving." %
                            os.path.basename(review))
                    current_approvable = [
                        item for item in current_items if item["target"]]
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
                    if revision is not None:
                        self.server.review_client_revision = revision
                    self.server.saved_count = len(selected)
                    self.send_json(200, {"ok": True, "selected": len(selected)})
                    if close_after:
                        threading.Thread(
                            target=self.server.shutdown, daemon=True).start()
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

def missing_review_message(guided=False):
    if guided:
        return "No photos found yet. Choose Find your photos on Wikipedia first."
    return "Review file not found. Run credit-check scan first."

def photo_count_text(count):
    return "%d photo" % count if count == 1 else "%d photos" % count

def empty_review_message(guided=False, review_mode="by"):
    if review_mode == "of":
        return ("Credit Check didn't find any photos of you. You need to put the "
                "camera down and step in front of the lens once in a while!")
    if guided:
        return "You're all caught up. Choose Scan again for new photos when you want to check again."
    return "Your review is empty. Run credit-check scan again."

def guided_review_open_message(approvable_count, ambiguous_count):
    return "Opening the photo picker in your browser for %s." % (
        photo_count_text(approvable_count))

def no_approvable_review_message(ambiguous_count, guided=False):
    if ambiguous_count:
        if guided:
            return ("Credit Check found photos, but couldn't tell which category "
                    "to use for them, so there are no photos to choose yet.")
        return ("Credit Check found only ambiguous photos. Assign a category in "
                "the review file before selecting them.")
    return "No photos to choose right now." if guided else "No photos to review."

def review_file_web(review, port=0, open_browser=True, fallback_on_open_failure=False,
                    initial_mode="all", guided=False, initial_scope="missing"):
    if not os.path.exists(review):
        print(missing_review_message(guided))
        return False

    items = parse_review_items(review)
    approvable = [item for item in items if item["target"]]
    ambiguous_count = len([item for item in items if not item["target"]])
    scan_metrics = review_scan_metrics(review, fallback_missing=len(approvable))
    all_photos = load_all_photos_cache(review, items)
    if all_photos is not None:
        cached_by_title = {item["title"]: item for item in all_photos}
        for item in items:
            cached = cached_by_title.get(item["title"])
            if cached:
                item["wikidata_items"] = cached.get("wikidata_items", [])
    if (all_photos is None and
            scan_metrics.get("in_use_total") == len(approvable)):
        all_photos = [dict(item, checked=False) for item in approvable]
    if not items and not all_photos:
        print(empty_review_message(guided, review_mode_from_context(
            review_section_context(review))))
        return True
    if not approvable and not all_photos:
        print(no_approvable_review_message(ambiguous_count, guided))
        return True

    server = LocalReviewServer(
        (WEB_REVIEW_HOST, port),
        review_web_handler(review, items, approvable, ambiguous_count, initial_mode,
                           guided=guided, scan_metrics=scan_metrics,
                           all_photos=all_photos,
                           initial_scope=initial_scope),
    )
    server.review_host = "%s:%d" % (WEB_REVIEW_HOST, server.server_address[1])
    server.review_origin = "http://%s" % server.review_host
    server.review_signature = review_items_signature(items)
    server.review_lock = threading.Lock()
    server.review_client_revision = -1
    server.saved_count = None
    url = server.review_origin + "/"

    if guided and initial_scope == "all" and all_photos is not None:
        print("Opening your complete Wikipedia photo gallery in your browser.")
    elif guided and approvable:
        print(guided_review_open_message(len(approvable), ambiguous_count))
    elif guided:
        print("Opening your complete Wikipedia photo gallery in your browser.")
    else:
        if approvable:
            print("Opening photo picker in your browser for %d photo(s)." % len(approvable))
        else:
            print("Opening your complete Wikipedia photo gallery in your browser.")
        print("Review file: %s" % os.path.abspath(review))
    if guided:
        print("If the browser doesn't open, use this URL: %s" % url)
        print("Use Exit in the browser when you're finished.")
    else:
        print("URL: %s" % url)
        print("Use Exit in the browser, or press Ctrl-C here to stop.")

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
        if guided:
            print("%d photo(s) selected. Next: choose Add selected photos to your photographer category page on Wikimedia Commons." %
                  server.saved_count)
        else:
            print("%d photo(s) selected. Next: credit-check commit %s --go" %
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
            set_message("Opened current photo on Wikimedia Commons.")
        invalidate(event)

    @kb.add("g")
    def _(event):
        page_items = current_page_items()
        start, end = page_bounds(page_items)
        path = open_review_gallery(page_items, "Credit Check photos %d-%d" %
                                   (start, end), quiet=True)
        set_message("Opened read-only page gallery: %s" % path)
        invalidate(event)

    @kb.add("v")
    def _(event):
        path = open_review_gallery(approvable, "Credit Check review - all photos",
                                   quiet=True)
        set_message("Opened read-only full gallery: %s" % path)
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
    candidate_count = len(reasons)
    if candidate_count == 0:
        if getattr(args, "guided", False):
            if scan_mode == "of":
                print(empty_review_message(review_mode="of"))
            else:
                print("Credit Check couldn't find any Wikimedia Commons photos credited to you. "
                      "Double-check your Wikimedia Commons username and credited name in Settings.")
        else:
            print("  found no files for user %s - check your Wikimedia Commons username in Settings."
                  % username, file=sys.stderr)
        return False
    print("  %d possible matches. Fetching usage, categories, wikitext..." % candidate_count,
          file=sys.stderr)
    info = fetch_details(cl, reasons.keys(), by_cat, of_cat)
    wikidata_total = sum(len(rec.get("wd", {})) for rec in info.values())
    if wikidata_total:
        print("  resolving %d Wikidata item use(s)..." % wikidata_total, file=sys.stderr)
        fetch_wikidata_usage_labels(info.values())

    depicts = set()
    if qid and of_cat:
        print("  checking SDC depicts (P180=%s)..." % qid, file=sys.stderr)
        depicts = fetch_depicts(cl, [r["pageid"] for r in info.values()], qid)

    by_list, of_list, amb_list = {}, {}, {}
    by_in_use, of_in_use, ambiguous_in_use = {}, {}, {}
    by_missing_category, of_missing_category = set(), set()
    for title, rec in info.items():
        rec["reason"] = reasons.get(title, set())
        all_wp = rec["wp"]
        if not all_wp:
            continue
        rec["all_wp"] = all_wp
        kind = record_kind(rec, username, author, of_cat, depicts)
        if kind == "by":
            by_in_use[title] = rec
            if not rec["in_by"]:
                by_missing_category.add(title)
        elif kind == "of":
            of_in_use[title] = rec
            if not rec["in_of"]:
                of_missing_category.add(title)
        else:
            ambiguous_in_use[title] = rec

        wp = all_wp
        if english_only:
            wp = {k: v for k, v in wp.items() if v["lang"] == "en"}
        rec["wp"] = wp
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
    if include_by and not no_derivatives and ambiguous_in_use:
        promoted = resolve_derivatives(cl, ambiguous_in_use, username, author, depth)
        for title, src in promoted.items():
            rec = ambiguous_in_use[title]
            amb_list.pop(title, None)
            by_in_use[title] = rec
            if not rec["in_by"]:
                by_missing_category.add(title)
            if rec["in_by"]:
                continue
            rec["reason"] = set(rec.get("reason", set())) | {"derivative"}
            rec["derived_from"] = src
            if len(rec["wp"]) >= min_uses:
                by_list[title] = rec
        if promoted:
            print("  promoted %d derivative crop(s) via source chain." % len(promoted),
                  file=sys.stderr)

    metric_records = []
    if include_by:
        metric_records.extend(by_in_use.values())
    if include_of:
        metric_records.extend(of_in_use.values())
    reach_metrics = wikipedia_reach_metrics(metric_records)
    missing_category_total = (
        (len(by_missing_category) if include_by else 0) +
        (len(of_missing_category) if include_of else 0)
    )

    review_records_by_title = {
        title: rec
        for review_list in (by_list, of_list, amb_list)
        for title, rec in review_list.items()
    }
    gallery_records = []
    if include_by:
        gallery_records.extend(
            (title, rec, by_cat)
            for title, rec in by_in_use.items()
        )
    if include_of and of_cat:
        gallery_records.extend(
            (title, rec, of_cat)
            for title, rec in of_in_use.items()
        )
    caption_records = {
        title: rec
        for title, rec, _target in gallery_records
    }
    caption_records.update(review_records_by_title)
    if caption_records:
        print("  fetching English photo captions...", file=sys.stderr)
        structured_captions = fetch_english_captions(
            cl, [rec.get("pageid") for rec in caption_records.values()])
        structured_count = 0
        fallback_count = 0
        for rec in caption_records.values():
            structured_caption = structured_captions.get(rec.get("pageid"), "")
            if structured_caption:
                structured_count += 1
            elif rec.get("description"):
                fallback_count += 1
            rec["caption"] = structured_caption or rec.get("description", "")
        print("  %d structured captions; %d useful description fallbacks."
              % (structured_count, fallback_count), file=sys.stderr)

    meta = {
        "author": author,
        "by_category": by_cat,
        "of_category": of_cat,
        "include_by": include_by,
        "include_of": include_of,
        "include_ambiguous": include_ambiguous,
        **reach_metrics,
        "missing_category_total": missing_category_total,
    }
    write_review(by_list, of_list, amb_list, meta, out, review_format)
    write_all_photos_cache(
        out,
        gallery_records,
        review_records_by_title.keys(),
    )
    if getattr(args, "guided", False):
        return True
    of_only_empty = include_of and not include_by and not include_ambiguous and not of_list
    if of_only_empty:
        print(empty_review_message(review_mode="of"), file=sys.stderr)
        return
    print("\nWrote %s" % out, file=sys.stderr)
    if include_by:
        print("  by  (photos you took, missing [[Category:%s]]): %d photos, used %d times"
              % (by_cat, len(by_list), sum(len(r["wp"]) for r in by_list.values())),
              file=sys.stderr)
    if of_cat and include_of:
        print("  of  (photos of you, missing [[Category:%s]]): %d photos"
              % (of_cat, len(of_list)), file=sys.stderr)
    if include_ambiguous:
        print("  ambiguous (authorship or category unclear): %d photos" % len(amb_list),
              file=sys.stderr)
    if not by_list and not of_list and not amb_list:
        print("  no missing-category photos found. You may already be caught up.",
              file=sys.stderr)
    return True


def login(cl, botuser, botpass):
    tok = cl.get({"action": "query", "meta": "tokens", "type": "login"})
    lgtoken = tok["query"]["tokens"]["logintoken"]
    res = cl.post({"action": "login"},
                  {"lgname": botuser, "lgpassword": botpass, "lgtoken": lgtoken},
                  retry_post=True)
    if res.get("login", {}).get("result") != "Success":
        sys.exit("Login failed: %s" % res.get("login", {}).get("result", res))
    return cl.get({"action": "query", "meta": "tokens"})["query"]["tokens"]["csrftoken"]

def load_approved(review, warn=True, guided=False):
    try:
        approved = parse_approved(review, warn=warn)
    except FileNotFoundError:
        if warn:
            if guided:
                print(missing_review_message(guided=True))
            else:
                print("Review file not found: %s. Run credit-check scan first." % review)
        return []
    if not approved and warn:
        if guided:
            print("You haven't selected any photos yet.")
        else:
            print("You haven't selected any photos in %s yet. Run credit-check review %s and choose the photos you want first." %
                  (review, review_path_arg(review)))
    return approved

def approved_or_exit(review):
    approved = load_approved(review)
    if not approved:
        sys.exit(1)
    return approved

def photo_count(n):
    return "%d photo%s" % (n, "" if n == 1 else "s")

def display_file_title(title):
    if title.startswith("File:"):
        return title[len("File:"):]
    return title

def grouped_approved(approved):
    groups = []
    by_category = {}
    for title, cat in approved:
        if cat not in by_category:
            by_category[cat] = []
            groups.append((cat, by_category[cat]))
        by_category[cat].append(title)
    return groups

def approved_categories(approved):
    return [cat for cat, _titles in grouped_approved(approved)]

def approved_category_urls(approved):
    return [(cat, commons_category_url(cat)) for cat in approved_categories(approved)]

def output_width():
    return max(72, min(shutil.get_terminal_size((100, 20)).columns, 120))

def print_wrapped_line(prefix, text, width=None):
    width = width or output_width()
    body_width = max(24, width - len(prefix))
    lines = textwrap.wrap(
        text, width=body_width, break_long_words=False,
        break_on_hyphens=False) or [""]
    print(prefix + lines[0])
    follow = " " * len(prefix)
    for line in lines[1:]:
        print(follow + line)

def print_category_preview(approved):
    for cat, titles in grouped_approved(approved):
        print("")
        print("Category:%s" % cat)
        number_width = len(str(len(titles)))
        for idx, title in enumerate(titles, start=1):
            print_wrapped_line("  %*d. " % (number_width, idx),
                               display_file_title(title))

def format_seconds(seconds):
    if seconds == int(seconds):
        seconds = int(seconds)
    if seconds == 1:
        return "1 second"
    return "%s seconds" % seconds

def progress_prefix(index, total, status):
    return "  %*d/%d  %-13s " % (len(str(total)), index, total, status)

def print_progress_line(index, total, status, title, detail=None):
    text = display_file_title(title)
    if detail:
        text += " (%s)" % detail
    print_wrapped_line(progress_prefix(index, total, status), text)

def print_plan(approved, review, next_command=None, guided=False):
    if guided:
        print("%s selected." % photo_count(len(approved)))
    else:
        print("%s selected in %s." % (photo_count(len(approved)), review))
    print("Preview - Wikimedia Commons edits (nothing is edited yet):")
    print_category_preview(approved)
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

def clear_review_selections(review):
    try:
        items = parse_review_items(review)
    except OSError:
        return False
    if not any(item["target"] and item["checked"] for item in items):
        return False
    set_review_approvals(review, items, set())
    return True

def guided_selection_clear_message():
    return "The selected photos are now unchecked, so you won't add them twice."

def print_commit_done_summary(added, skipped, failed, review, approved, guided=False):
    print("")
    if failed:
        print("Done, with a few problems to check.")
    elif added:
        print("Congratulations - your selected photos have been added to your Wikimedia Commons category.")
    elif skipped:
        print("Good news - your selected photos were already in your Wikimedia Commons category.")
    else:
        print("Done.")
    print("")
    print("  Added: %d" % added)
    print("  Already there: %d" % skipped)
    print("  Failed: %d" % failed)

    cat_urls = approved_category_urls(approved)
    if cat_urls:
        print("")
        if len(cat_urls) == 1:
            print("You can view your photos here:")
        else:
            print("You can view your category pages here:")
        for _cat, url in cat_urls:
            print("  %s" % url)

    remaining = remaining_unselected_count(review)
    if failed:
        print("")
        if guided:
            print("Some photos failed. Check the messages above, then choose Add selected photos to your photographer category page on Wikimedia Commons again when you're ready.")
        else:
            print("Some photos failed. Check the messages above, then run credit-check plan %s before trying again." %
                  review_path_arg(review))
    elif remaining:
        print("")
        if guided:
            print("%d unselected photos remain. Choose \"Choose photos to add\" when you want to keep going." %
                  remaining)
        else:
            print("%d photos you did not select remain. Run credit-check review %s when you want to keep going." %
                  (remaining, review_path_arg(review)))
    else:
        print("")
        print("All your selected photos are now categorized.")

def offer_open_category_pages(approved):
    cat_urls = approved_category_urls(approved)
    if not cat_urls:
        return
    if len(cat_urls) == 1:
        label = "Open this category page now?"
    else:
        label = "Open these category pages now?"
    if not prompt_yes_no(label, True):
        return
    for _cat, url in cat_urls:
        webbrowser.open(url)
    if len(cat_urls) == 1:
        print("Opened %s" % cat_urls[0][1])
    else:
        print("Opened %d category pages." % len(cat_urls))

def cmd_plan(args):
    approved = approved_or_exit(args.review)
    print_plan(approved, args.review,
               "credit-check commit %s --go" % review_path_arg(args.review))

BOT_PASSWORD_URL = "https://commons.wikimedia.org/wiki/Special:BotPasswords"

def bot_password_intro_lines():
    return [
        "Credit Check needs a Wikimedia Commons bot password before it can edit.",
        "",
        "A bot password is an app password for your own Wikimedia Commons account, not a separate uploader.",
        "A login like YourName@categorize still edits as YourName; the suffix just names this tool's credential.",
        "Credit Check only edits existing file pages to add categories. It does not upload files or change who uploaded them.",
        "",
        "To create one:",
        "  1. Go to %s" % BOT_PASSWORD_URL,
        "  2. Log in there with your normal Wikimedia Commons username and password.",
        "  3. Create a new bot password. Name it something like categorize.",
        "  4. Grant \"Edit existing pages\".",
        "  5. Copy the generated username, like YourName@categorize, and the generated password.",
        "  6. Come back here and paste them below.",
        "",
        "Do not use your main Wikimedia Commons password.",
        "",
    ]

def print_bot_password_intro():
    print("\n".join(bot_password_intro_lines()))

def default_bot_username():
    username = identity_default("username", "WIKI_USERNAME")
    if username:
        return "%s@categorize" % username
    return None

def prompt_secret_required(label):
    while True:
        value = getpass.getpass(label + ": ")
        if value:
            return value
        print("Required.")

def resolve_commit_credentials(args):
    botuser = args.botuser or os.environ.get("COMMONS_BOTUSER")
    botpass = args.botpass or os.environ.get("COMMONS_BOTPASS")

    if not botuser or not botpass:
        print_bot_password_intro()

    if not botuser:
        botuser = prompt_text(
            "Generated bot-password username",
            default_bot_username(),
            required=True)
    if not botpass:
        botpass = prompt_secret_required("Generated bot-password password")

    return botuser, botpass

def fetch_category_edit_state(cl, title, full_category):
    data = cl.get({
        "action": "query",
        "titles": title,
        "prop": "categories|revisions",
        "clcategories": full_category,
        "cllimit": "1",
        "rvprop": "ids|timestamp",
        "curtimestamp": "1",
    })
    pages = data.get("query", {}).get("pages", {})
    if not pages:
        raise ValueError("Wikimedia Commons returned no page data")
    page = next(iter(pages.values()))
    if "missing" in page or page.get("pageid") == -1:
        raise ValueError("file page does not exist")
    revisions = page.get("revisions") or []
    if not revisions or not revisions[0].get("revid"):
        raise ValueError("Wikimedia Commons returned no current revision")
    return {
        "category_present": bool(page.get("categories")),
        "revid": revisions[0]["revid"],
        "basetimestamp": revisions[0].get("timestamp"),
        "starttimestamp": data.get("curtimestamp"),
    }

def post_category_edit(cl, csrf, title, full_category, summary, state):
    edit_data = {
        "title": title,
        "appendtext": "\n[[%s]]\n" % full_category,
        "summary": summary + " ([[%s]])" % full_category,
        "token": csrf,
        "assert": "user",
        "nocreate": "1",
        "maxlag": "5",
        "baserevid": str(state["revid"]),
    }
    if state.get("basetimestamp"):
        edit_data["basetimestamp"] = state["basetimestamp"]
    if state.get("starttimestamp"):
        edit_data["starttimestamp"] = state["starttimestamp"]
    result = cl.post(
        {"action": "edit"},
        edit_data,
        retry_api_errors=SAFE_API_RETRY_CODES,
    )
    if result.get("edit", {}).get("result") != "Success":
        raise MediaWikiAPIError({
            "code": "edit-failed",
            "info": str(result),
        }, result)

def add_category_to_file(cl, csrf, title, full_category, summary):
    state = fetch_category_edit_state(cl, title, full_category)
    if state["category_present"]:
        return "already"
    try:
        post_category_edit(cl, csrf, title, full_category, summary, state)
        return "added"
    except MediaWikiAPIError as error:
        if error.code != "editconflict":
            raise

    # A page changed after the pre-check. Re-read it: if another edit added the
    # category, count that as already done; otherwise retry once against the new
    # revision. An unknown network outcome never reaches this branch.
    state = fetch_category_edit_state(cl, title, full_category)
    if state["category_present"]:
        return "already"
    post_category_edit(cl, csrf, title, full_category, summary, state)
    return "added"

def cmd_commit(args):
    approved = approved_or_exit(args.review)
    if not args.go:
        print_plan(approved, args.review,
                   "credit-check commit %s --go" % review_path_arg(args.review))
        return

    if getattr(args, "guided", False):
        if not getattr(args, "preview_shown", False):
            print("%s selected." % photo_count(len(approved)))
    else:
        print("%s selected in %s." % (photo_count(len(approved)), args.review))

    botuser, botpass = resolve_commit_credentials(args)

    cl = Client()
    csrf = login(cl, botuser, botpass)
    print("Logged in. Adding categories on Wikimedia Commons.")
    print("Pausing %s between edits." % format_seconds(args.throttle))

    added = skipped = failed = 0
    progress = 0
    total = len(approved)
    for cat, titles in grouped_approved(approved):
        full = "Category:" + cat
        print("")
        print(full)
        for t in titles:
            progress += 1
            try:
                result = add_category_to_file(
                    cl, csrf, t, full, args.summary)
            except MediaWikiAPIError as e:
                print_progress_line(progress, total, "Failed", t, "api: %s" % e)
                failed += 1
                time.sleep(args.throttle)
                continue
            except (urllib.error.HTTPError, urllib.error.URLError, OSError) as e:
                print_progress_line(progress, total, "Failed", t, "network: %s" % e)
                failed += 1
                time.sleep(args.throttle)
                continue
            except (KeyError, TypeError, ValueError) as e:
                print_progress_line(progress, total, "Failed", t, str(e))
                failed += 1
                time.sleep(args.throttle)
                continue
            if result == "added":
                print_progress_line(progress, total, "Added", t)
                added += 1
            else:
                print_progress_line(progress, total, "Already there", t)
                skipped += 1
            time.sleep(args.throttle)
    print_commit_done_summary(added, skipped, failed, args.review, approved,
                              guided=getattr(args, "guided", False))
    if getattr(args, "guided", False) and not failed and clear_review_selections(args.review):
        print(guided_selection_clear_message())
    if getattr(args, "guided", False) and not failed:
        offer_open_category_pages(approved)


# ---------------------------------------------------------------- self-checks

SMOKE_USERNAME = "CreditCheckSmokeUserDefinitelyAbsent20260704"
SMOKE_AUTHOR = "Credit Check Smoke Author Definitely Absent 20260704"

def sample_review_data():
    rec = {
        "uploader": "SomeoneElse",
        "cats": {"Category:Example people"},
        "reason": {"credited"},
        "caption": "Test Person at an example event.",
        "wp": {"en.wikipedia.org|Example": {
            "wiki": "en.wikipedia.org", "lang": "en", "title": "Example"}},
    }
    meta = {
        "author": "Test Person",
        "by_category": "Photographs by Test Person",
        "of_category": None,
        "in_use_total": 8,
        "article_total": 21,
        "wikipedia_total": 4,
        "missing_category_total": 1,
    }
    return {"File:Example.jpg": rec}, {}, {"File:Ambiguous.jpg": rec.copy()}, meta

def sample_of_review_data():
    rec = {
        "uploader": "SomeoneElse",
        "cats": {"Category:Example people"},
        "reason": {"depicts"},
        "caption": "A portrait of Test Person.",
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
        "in_use_total": 3,
        "article_total": 7,
        "wikipedia_total": 2,
        "missing_category_total": 1,
    }
    return {}, {"File:Portrait.jpg": rec}, {}, meta

def check_equal(name, got, expected):
    if got != expected:
        raise AssertionError("%s: got %r, expected %r" % (name, got, expected))

def check_photo_caption_metadata():
    check_equal("description html cleanup",
                clean_commons_description("<div>Test &amp; <b>caption</b></div>"),
                "Test & caption")
    check_equal("multilingual description cleanup",
                clean_commons_description({"_type": "text", "en": "English caption"}),
                "English caption")
    check_equal("crop boilerplate omitted",
                useful_commons_description(
                    "A cropped version of File:Example portrait.jpg"), "")
    check_equal("useful description retained",
                useful_commons_description("Test Person at an example event."),
                "Test Person at an example event.")

    class CaptionClient:
        def get(self, params):
            check_equal("caption API action", params["action"], "wbgetentities")
            check_equal("caption API languages", params["languages"], "en")
            return {
                "entities": {
                    "M123": {"labels": {"en": {"value": " Structured\ncaption "}}},
                    "M456": {"labels": {"fr": {"value": "Légende"}}},
                    "not-a-media-id": {"labels": {"en": {"value": "Ignore me"}}},
                }
            }

    old_sleep = time.sleep
    try:
        time.sleep = lambda seconds: None
        check_equal("English structured captions",
                    fetch_english_captions(CaptionClient(), [123, None, 456]),
                    {123: "Structured caption"})
    finally:
        time.sleep = old_sleep

def check_retry_policy():
    class FailingOpener:
        def __init__(self):
            self.calls = 0

        def open(self, url, data=None, timeout=60):
            self.calls += 1
            raise urllib.error.URLError("simulated lost response")

    class JSONResponse(io.BytesIO):
        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc, traceback):
            self.close()

    class SequenceOpener:
        def __init__(self, payloads):
            self.payloads = list(payloads)
            self.calls = 0

        def open(self, url, data=None, timeout=60):
            self.calls += 1
            payload = self.payloads.pop(0)
            return JSONResponse(json.dumps(payload).encode("utf-8"))

    class CapturingOpener:
        def __init__(self):
            self.requests = []

        def open(self, request, timeout=60):
            self.requests.append(request)
            return JSONResponse(b'{"query": {}}')

    old_sleep = time.sleep
    time.sleep = lambda seconds: None
    try:
        cl = Client()
        cl.opener = CapturingOpener()
        cl.read_post({
            "action": "query",
            "titles": "File:" + ("Long filename " * 100) + ".jpg",
            "prop": "imageinfo",
            "continue": "||",
        })
        request = cl.opener.requests[0]
        query = urllib.parse.parse_qs(urllib.parse.urlsplit(request.full_url).query)
        body = urllib.parse.parse_qs(request.data.decode("utf-8"))
        headers = {key.lower(): value for key, value in request.header_items()}
        check_equal("read POST URL parameters", query,
                    {"action": ["query"], "format": ["json"]})
        check_equal("read POST keeps titles in body", "titles" in body, True)
        check_equal("read POST keeps continuation in body", body["continue"], ["||"])
        check_equal("read POST promise header",
                    headers.get("promise-non-write-api-action"), "true")

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

        cl.opener = SequenceOpener([
            {"error": {"code": "maxlag", "info": "Waiting for replicas", "lag": 0}},
            {"edit": {"result": "Success"}},
        ])
        got = cl._call(
            {"action": "edit"},
            data={"title": "File:X.jpg"},
            tries=3,
            retry_api_errors=SAFE_API_RETRY_CODES,
        )
        check_equal("explicit safe API error retried", got["edit"]["result"], "Success")
        check_equal("safe API retry attempts", cl.opener.calls, 2)

        cl.opener = SequenceOpener([
            {"error": {"code": "badtoken", "info": "Invalid token"}},
        ])
        try:
            cl._call({"action": "edit"}, data={"title": "File:X.jpg"}, tries=3,
                     retry_api_errors=SAFE_API_RETRY_CODES)
            raise AssertionError("unsafe API error was retried or ignored")
        except MediaWikiAPIError as error:
            check_equal("API error code", error.code, "badtoken")
        check_equal("unsafe API error attempts", cl.opener.calls, 1)
    finally:
        time.sleep = old_sleep

def check_version_identity():
    if __version__ not in UA:
        raise AssertionError("User-Agent version does not match the app version")
    if "github.com/incandescentman/credit-check" not in UA:
        raise AssertionError("User-Agent is missing the project contact URL")
    manifest = os.path.join(os.path.dirname(os.path.abspath(__file__)), "pyproject.toml")
    if os.path.exists(manifest):
        text = open(manifest, encoding="utf-8").read()
        match = re.search(r'^version\s*=\s*"([^"]+)"', text, re.M)
        if not match:
            raise AssertionError("pyproject.toml has no project version")
        check_equal("source and package versions", __version__, match.group(1))

def check_commit_write_safety():
    def page_state(revid, category_present=False):
        page = {
            "pageid": 1,
            "title": "File:Example.jpg",
            "revisions": [{"revid": revid, "timestamp": "2026-07-13T12:00:00Z"}],
        }
        if category_present:
            page["categories"] = [{"title": "Category:Photographs by Test Person"}]
        return {
            "curtimestamp": "2026-07-13T12:00:01Z",
            "query": {"pages": {"1": page}},
        }

    class FakeClient:
        def __init__(self, gets, posts):
            self.gets = list(gets)
            self.posts = list(posts)
            self.post_calls = []

        def get(self, params):
            value = self.gets.pop(0)
            if isinstance(value, BaseException):
                raise value
            return value

        def post(self, params, data, retry_api_errors=None):
            self.post_calls.append((params, data, retry_api_errors))
            value = self.posts.pop(0)
            if isinstance(value, BaseException):
                raise value
            return value

    full = "Category:Photographs by Test Person"
    client = FakeClient([page_state(10)], [{"edit": {"result": "Success"}}])
    result = add_category_to_file(client, "token", "File:Example.jpg", full, "Summary")
    check_equal("guarded edit result", result, "added")
    check_equal("guarded edit base revision", client.post_calls[0][1]["baserevid"], "10")
    check_equal("guarded edit safe API retries", client.post_calls[0][2],
                SAFE_API_RETRY_CODES)

    client = FakeClient([page_state(10, category_present=True)], [])
    check_equal("already-present pre-check",
                add_category_to_file(client, "token", "File:Example.jpg", full, "Summary"),
                "already")
    check_equal("already-present did not edit", len(client.post_calls), 0)

    conflict = MediaWikiAPIError({"code": "editconflict", "info": "Changed"})
    client = FakeClient(
        [page_state(10), page_state(11)],
        [conflict, {"edit": {"result": "Success"}}],
    )
    check_equal("conflict re-check result",
                add_category_to_file(client, "token", "File:Example.jpg", full, "Summary"),
                "added")
    check_equal("conflict retry fresh revision", client.post_calls[1][1]["baserevid"], "11")

    client = FakeClient(
        [page_state(10), page_state(11, category_present=True)],
        [conflict],
    )
    check_equal("conflict resolved by another editor",
                add_category_to_file(client, "token", "File:Example.jpg", full, "Summary"),
                "already")
    check_equal("conflict-present did not retry edit", len(client.post_calls), 1)

    lost = urllib.error.URLError("simulated lost edit response")
    client = FakeClient([page_state(10)], [lost])
    try:
        add_category_to_file(client, "token", "File:Example.jpg", full, "Summary")
        raise AssertionError("lost edit response was ignored")
    except urllib.error.URLError:
        pass
    check_equal("unknown edit outcome not retried", len(client.post_calls), 1)

def check_atomic_write_text():
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "sample.txt")
        atomic_write_text(path, "hello\n")
        check_equal("atomic write content", open(path, encoding="utf-8").read(), "hello\n")
        leftovers = [name for name in os.listdir(td)
                     if name.startswith(".credit-check-write.")]
        check_equal("atomic write temp leftovers", leftovers, [])

        old_replace = os.replace
        atomic_write_text(path, "old\n")
        try:
            def failing_replace(src, dst):
                raise KeyboardInterrupt()

            os.replace = failing_replace
            try:
                atomic_write_text(path, "new\n")
                raise AssertionError("atomic write failure did not re-raise")
            except KeyboardInterrupt:
                pass
        finally:
            os.replace = old_replace
        check_equal("atomic write preserved target",
                    open(path, encoding="utf-8").read(), "old\n")
        leftovers = [name for name in os.listdir(td)
                     if name.startswith(".credit-check-write.")]
        check_equal("atomic write failure temp cleanup", leftovers, [])

        by_list, of_list, amb_list, meta = sample_review_data()
        review = os.path.join(td, "review.md")
        write_review(by_list, of_list, amb_list, meta, review, "markdown")
        items = parse_review_items(review)
        approvable = [item for item in items if item["target"]]
        set_review_approvals(review, items, {approvable[0]["line"]})
        check_equal("atomic review round trip",
                    parse_approved(review, warn=False),
                    [("File:Example.jpg", "Photographs by Test Person")])

def write_and_parse_sample(review_format, suffix):
    by_list, of_list, amb_list, meta = sample_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "review" + suffix)
        write_review(by_list, of_list, amb_list, meta, path, review_format)
        text = open(path, encoding="utf-8").read()
        if review_path_arg(path) not in text:
            raise AssertionError("review command did not include the review path")
        check_equal("review scan metrics", review_scan_metrics(path), {
            "article_total": 21,
            "in_use_total": 8,
            "missing_category_total": 1,
            "wikipedia_total": 4,
        })
        parsed_items = parse_review_items(path)
        parsed_example = next(item for item in parsed_items
                              if item["title"] == "File:Example.jpg")
        check_equal("review article title", parsed_example["articles"][0]["title"],
                    "Example")
        check_equal("review article url", parsed_example["articles"][0]["url"],
                    "https://en.wikipedia.org/wiki/Example")
        check_equal("review caption", parsed_example["caption"],
                    "Test Person at an example event.")
        captionless_text = re.sub(r"^\s+caption:.*\n", "", text, flags=re.M)
        atomic_write_text(path, captionless_text)
        captionless_example = next(item for item in parse_review_items(path)
                                   if item["title"] == "File:Example.jpg")
        check_equal("legacy review without caption", captionless_example["caption"], "")
        legacy_text = re.sub(
            r"^(?:<!-- credit-check-metrics:.*-->|#\+CREDIT_CHECK_METRICS:.*)\n",
            "", text, flags=re.M | re.I)
        atomic_write_text(path, legacy_text)
        check_equal("legacy review metric fallback", review_scan_metrics(path, 1), {
            "article_total": None,
            "in_use_total": None,
            "missing_category_total": 1,
            "wikipedia_total": None,
        })
        atomic_write_text(path, text)
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
                        "Ready to find your photos")

            by_list, of_list, amb_list, meta = sample_review_data()
            write_review({}, {}, {}, meta, "review.md", "markdown")
            state = review_workflow_state()
            check_equal("guided empty review total", state["total"], 0)
            check_equal("guided empty review label", review_state_label(state),
                        "You're all caught up — re-scan to check for new photos")

            write_review({}, {}, amb_list, meta, "review.md", "markdown")
            state = review_workflow_state()
            check_equal("guided ambiguous-only review total", state["total"], 0)
            check_equal("guided ambiguous-only label", review_state_label(state),
                        "Found some photos, but none had a clear category yet")

            _by_list, _of_list, _amb_list, of_meta = sample_of_review_data()
            write_review({}, {}, {}, of_meta, "review.md", "markdown")
            state = review_workflow_state()
            check_equal("guided empty of-review mode", state["review_mode"], "of")
            check_equal("guided empty of-review category",
                        state["of_category"], "Test Person")
            check_equal("guided empty of-review label", review_state_label(state),
                        "No new photos of you this time")

            write_review(by_list, of_list, amb_list, meta, "review.md", "markdown")
            categorized_rec = dict(next(iter(by_list.values())))
            write_all_photos_cache(
                "review.md",
                [
                    ("File:Example.jpg", next(iter(by_list.values())),
                     "Photographs by Test Person"),
                    ("File:Already categorized.jpg", categorized_rec,
                     "Photographs by Test Person"),
                ],
                {"File:Example.jpg", "File:Ambiguous.jpg"},
            )
            state = review_workflow_state()
            check_equal("guided review exists", state["exists"], True)
            check_equal("guided review total", state["total"], 1)
            check_equal("guided all-photos total", state["all_photos_total"], 2)
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
            else:
                os.environ.pop(key, None)

def check_guided_menu_dispatch():
    for value in ("self_test", "smoke", "scan_by", "scan_of", "review",
                  "view_all", "settings", "start_over", "add", "quit"):
        check_equal("guided dispatch %s" % value,
                    interactive_choice_action(value), value)
    for value in ("q", "quit", "exit"):
        check_equal("guided quit shortcut %s" % value,
                    interactive_choice_action(value), "quit")
    for value in ("1", "2", "3", "3b", "4", "5", "6", "9", "of",
                  "plan", "review_selected"):
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
            state = review_workflow_state()
            values = [value for _label, value, _desc in interactive_menu_actions(state)]
            if "scan_of" not in values:
                raise AssertionError("photos-of-you action did not show before setup")

            save_local_preferences({"username": "TestUser", "author": "Test Person"})
            state = review_workflow_state()
            actions = interactive_menu_actions(state)
            values = [value for _label, value, _desc in actions]
            if "self_test" in values or "smoke" in values:
                raise AssertionError("developer checks leaked into the default menu")
            if "scan_of" not in values:
                raise AssertionError("photos-of-you action did not show without a QID")
            labels = {value: label for label, value, _desc in actions}
            check_equal("photos-of-you guided label", labels.get("scan_of"),
                        "Find photos *of* you")
            check_equal("start-over guided label", labels.get("start_over"),
                        "Start over with a different photographer")

            zero = {"setup_complete": True, "exists": True, "total": 0,
                    "selected": 0, "ambiguous": 0, "review": "review.md",
                    "all_photos_total": 8}
            zero_values = [value for _label, value, _desc in interactive_menu_actions(zero)]
            if zero_values[0] != "scan_by":
                raise AssertionError("empty review should lead with a scan, not review")
            if "review" in zero_values:
                raise AssertionError("empty review must not offer photo review")
            if "view_all" not in zero_values:
                raise AssertionError("complete gallery did not appear after a caught-up scan")

            no_gallery = dict(zero, all_photos_total=0)
            no_gallery_values = [
                value for _label, value, _desc in interactive_menu_actions(no_gallery)]
            if "view_all" in no_gallery_values:
                raise AssertionError("all-photo gallery appeared without preserved scan data")

            selected = {"setup_complete": True, "exists": True, "total": 2,
                        "selected": 1, "ambiguous": 0, "review": "review.md",
                        "all_photos_total": 8}
            selected_actions = interactive_menu_actions(selected)
            selected_labels = [label for label, _value, _desc in selected_actions]
            selected_values = [value for _label, value, _desc in selected_actions]
            check_equal("selected menu primary label", selected_labels[0],
                        "Add selected photos to your photographer category page on Wikimedia Commons")
            if "plan" in selected_values:
                raise AssertionError("selected menu must not offer terminal preview")
            if "review_selected" in selected_values:
                raise AssertionError("selected menu must not offer selected-only review")

            os.environ["CREDIT_CHECK_DEV"] = "1"
            values = [value for _label, value, _desc in interactive_menu_actions(state)]
            if "self_test" not in values or "smoke" not in values:
                raise AssertionError("developer checks did not show in dev mode")
    finally:
        os.chdir(old_cwd)
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value

def check_guided_menu_copy_matrix():
    old_env = {key: os.environ.pop(key, None) for key in (
        "CREDIT_CHECK_DEV", "CREDIT_CHECK_DEV_MENU")}
    try:
        photos_of_you = (
            "Find photos *of* you",
            "scan_of",
            "Find portraits of you taken by other people and add them to your category for photos of you.",
        )
        quit_action = ("Quit", "quit", "")
        settings = (
            "Settings",
            "settings",
            "Save your name, Wikimedia Commons account, and category for photos you took.",
        )
        start_over = (
            "Start over with a different photographer",
            "start_over",
            "Clear saved details and search for a new set of photos.",
        )
        setup = (
            "Set up Credit Check",
            "settings",
            "Save your Wikimedia Commons account, credited name, and category.",
        )
        find = (
            "Find your photos on Wikipedia",
            "scan_by",
            "Find photos credited to you that Wikipedia is using but that aren't in your photographer category yet.",
        )
        scan_again = (
            "Scan again for new photos",
            "scan_by",
            "Search again for new photos you've uploaded or that are newly used on Wikipedia. Replaces the photos found so far.",
        )
        caught_up_scan = (
            "Scan again for new photos",
            "scan_by",
            "Look for new photos of yours now used on Wikipedia.",
        )
        search_of_again = (
            "Search for photos of you again",
            "scan_of",
            "Look again for portraits of you taken by other people.",
        )
        choose = (
            "Choose photos to add",
            "review",
            "Open the browser photo picker and choose photos.",
        )
        add = (
            "Add selected photos to your photographer category page on Wikimedia Commons",
            "add",
            "Preview the Wikimedia Commons edits, then add them.",
        )
        view_all = (
            "View all your photos",
            "view_all",
            "Open a read-only gallery of every photo from the latest scan that appears on Wikipedia.",
        )
        cases = [
            ("setup needed",
             {"setup_complete": False, "exists": False, "total": 0,
              "selected": 0, "ambiguous": 0, "review": "review.md"},
             [setup, find, photos_of_you, quit_action]),
            ("ready to scan",
             {"setup_complete": True, "exists": False, "total": 0,
              "selected": 0, "ambiguous": 0, "review": "review.md"},
             [find, settings, start_over, photos_of_you, quit_action]),
            ("caught up",
             {"setup_complete": True, "exists": True, "total": 0,
              "selected": 0, "ambiguous": 0, "review": "review.md",
              "review_mode": "by", "of_category": None,
              "all_photos_total": 8},
             [caught_up_scan, view_all, settings, start_over, photos_of_you, quit_action]),
            ("no photos of you",
             {"setup_complete": True, "exists": True, "total": 0,
              "selected": 0, "ambiguous": 0, "review": "review.md",
              "review_mode": "of", "of_category": "Test Person",
              "all_photos_total": 3},
             [search_of_again, scan_again, view_all, settings, start_over, quit_action]),
            ("choose photos",
             {"setup_complete": True, "exists": True, "total": 2,
              "selected": 0, "ambiguous": 1, "review": "review.md",
              "all_photos_total": 8},
             [choose, scan_again, view_all, settings, start_over, photos_of_you, quit_action]),
            ("selected photos",
             {"setup_complete": True, "exists": True, "total": 2,
              "selected": 1, "ambiguous": 0, "review": "review.md",
              "all_photos_total": 8},
             [add, scan_again, choose, view_all, settings, start_over, photos_of_you, quit_action]),
            ("setup incomplete with photos",
             {"setup_complete": False, "exists": True, "total": 2,
              "selected": 0, "ambiguous": 0, "review": "review.md",
              "all_photos_total": 8},
             [setup, scan_again, choose, view_all, start_over, photos_of_you, quit_action]),
        ]
        for name, state, expected in cases:
            check_equal("guided menu copy matrix %s" % name,
                        interactive_menu_actions(state), expected)
    finally:
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value
            else:
                os.environ.pop(key, None)

def check_guided_copy_messages():
    check_equal("guided missing-results message",
                missing_review_message(guided=True),
                "No photos found yet. Choose Find your photos on Wikipedia first.")
    check_equal("guided empty-results message",
                empty_review_message(guided=True),
                "You're all caught up. Choose Scan again for new photos when you want to check again.")
    check_equal("guided empty photos-of-you message",
                empty_review_message(guided=True, review_mode="of"),
                "Credit Check didn't find any photos of you. You need to put the camera down and step in front of the lens once in a while!")
    check_equal("guided review-open message",
                guided_review_open_message(54, 13),
                "Opening the photo picker in your browser for 54 photos.")
    check_equal("guided ambiguous-results message",
                no_approvable_review_message(1, guided=True),
                "Credit Check found photos, but couldn't tell which category to use for them, so there are no photos to choose yet.")
    check_equal("guided no-double-add message",
                guided_selection_clear_message(),
                "The selected photos are now unchecked, so you won't add them twice.")
    intro = "\n".join(bot_password_intro_lines())
    if "not a separate uploader" not in intro:
        raise AssertionError("bot password intro lost account ownership explanation")
    if "still edits as YourName" not in intro:
        raise AssertionError("bot password intro lost edit attribution explanation")
    if "Do not use your main Wikimedia Commons password." not in intro:
        raise AssertionError("bot password intro lost main-password warning")
    if "Log in there with your normal Wikimedia Commons username and password." not in intro:
        raise AssertionError("bot password intro lost Wikimedia Commons login step")
    if "Come back here and paste them below." not in intro:
        raise AssertionError("bot password intro lost return-to-tool step")

    old_stdout = sys.stdout
    old_prompt_yes_no = globals()["prompt_yes_no"]
    old_cwd = os.getcwd()
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            by_list, of_list, amb_list, meta = sample_review_data()

            sys.stdout = io.StringIO()
            review_file_web("missing.md", open_browser=False, guided=True)
            check_equal("guided web missing output", sys.stdout.getvalue().strip(),
                        missing_review_message(guided=True))

            write_review({}, {}, {}, meta, "review.md", "markdown")
            sys.stdout = io.StringIO()
            review_file_interactive("review.md", guided=True)
            check_equal("guided terminal empty output",
                        sys.stdout.getvalue().strip(),
                        empty_review_message(guided=True))

            _by_list, _of_list, _amb_list, of_meta = sample_of_review_data()
            write_review({}, {}, {}, of_meta, "review.md", "markdown")
            sys.stdout = io.StringIO()
            review_file_web("review.md", open_browser=False, guided=True)
            check_equal("guided web photos-of-you empty output",
                        sys.stdout.getvalue().strip(),
                        empty_review_message(guided=True, review_mode="of"))

            write_review({}, {}, amb_list, meta, "review.md", "markdown")
            sys.stdout = io.StringIO()
            review_file_web("review.md", open_browser=False, guided=True)
            check_equal("guided web ambiguous output",
                        sys.stdout.getvalue().strip(),
                        no_approvable_review_message(1, guided=True))

            write_review(by_list, of_list, amb_list, meta, "review.md", "markdown")
            items = parse_review_items("review.md")
            approvable = [item for item in items if item["target"]]
            set_review_approvals("review.md", items, {approvable[0]["line"]})
            prompts = []

            def no_confirm(label, default=False):
                prompts.append((label, default))
                return False

            globals()["prompt_yes_no"] = no_confirm
            sys.stdout = io.StringIO()
            interactive_preview_and_commit()
            output = sys.stdout.getvalue()
            if "This will add categories on Wikimedia Commons." not in output:
                raise AssertionError("guided add confirmation intro missing")
            if "selected in review.md" in output:
                raise AssertionError("guided add preview leaked the review filename")
            check_equal("guided add confirmation prompt", prompts,
                        [("Add these categories now?", False)])
    finally:
        sys.stdout = old_stdout
        globals()["prompt_yes_no"] = old_prompt_yes_no
        os.chdir(old_cwd)

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

def check_interactive_settings_core_only():
    old_cwd = os.getcwd()
    old_env = {key: os.environ.pop(key, None) for key in (
        "WIKI_USERNAME", "WIKI_AUTHOR", "WIKI_BY_CATEGORY", "WIKI_OF_CATEGORY",
        "WIKI_QID")}
    old_prompt = globals()["prompt_text"]
    old_stdout = sys.stdout
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            save_local_preferences({
                "username": "OldUser",
                "author": "Old Author",
                "by_category": "Old Category",
                "of_category": "Existing Subject",
                "qid": "Q999",
            })
            prompts = []
            answers = {
                "Wikimedia Commons username": "NewUser",
                "Your name as it's credited on Wikimedia Commons": "New Author",
                "Wikimedia Commons category for photos you took": "Photographs by New Author",
            }

            def fake_prompt(label, default=None, required=False):
                prompts.append((label, default, required))
                return answers[label]

            globals()["prompt_text"] = fake_prompt
            sys.stdout = io.StringIO()
            interactive_settings()
            prefs = local_preferences()
            check_equal("settings prompts", [p[0] for p in prompts], [
                "Wikimedia Commons username",
                "Your name as it's credited on Wikimedia Commons",
                "Wikimedia Commons category for photos you took",
            ])
            check_equal("settings saved username", prefs.get("username"), "NewUser")
            check_equal("settings saved author", prefs.get("author"), "New Author")
            check_equal("settings saved by category", prefs.get("by_category"),
                        "Photographs by New Author")
            check_equal("settings preserved of-category",
                        prefs.get("of_category"), "Existing Subject")
            check_equal("settings preserved qid", prefs.get("qid"), "Q999")
    finally:
        sys.stdout = old_stdout
        globals()["prompt_text"] = old_prompt
        os.chdir(old_cwd)
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value
            else:
                os.environ.pop(key, None)

def check_interactive_start_over():
    old_cwd = os.getcwd()
    old_env = {key: os.environ.pop(key, None) for key in (
        "WIKI_USERNAME", "WIKI_AUTHOR", "WIKI_BY_CATEGORY", "WIKI_OF_CATEGORY",
        "WIKI_QID")}
    old_prompt = globals()["prompt_text"]
    old_confirm = globals()["prompt_yes_no"]
    old_cmd_scan = globals()["cmd_scan"]
    old_stdout = sys.stdout
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            os.environ["WIKI_USERNAME"] = "EnvUser"
            os.environ["WIKI_AUTHOR"] = "Env Author"
            os.environ["WIKI_BY_CATEGORY"] = "Env Category"
            save_local_preferences({
                "username": "OldUser",
                "author": "Old Author",
                "by_category": "Old Category",
                "of_category": "Old Subject",
                "qid": "Q999",
                "review_path": "custom-review.md",
                "review_page_size": 12,
            })
            for path in ("custom-review.md", "review.md", "review.org",
                         ALL_PHOTOS_CACHE_FILE):
                atomic_write_text(path, "old review\n")
            prompts = []
            confirmations = []
            scan_calls = []
            answers = {
                "Wikimedia Commons username": "NewUser",
                "Your name as it's credited on Wikimedia Commons": "New Author",
                "Wikimedia Commons category for photos you took": "Photographs by New Author",
            }

            def fake_confirm(label, default=False):
                confirmations.append((label, default))
                return True

            def fake_prompt(label, default=None, required=False):
                prompts.append((label, default, required))
                return answers[label]

            globals()["prompt_yes_no"] = fake_confirm
            globals()["prompt_text"] = fake_prompt
            globals()["cmd_scan"] = lambda args: scan_calls.append(args)
            sys.stdout = io.StringIO()
            interactive_start_over()
            output = sys.stdout.getvalue()
            prefs = local_preferences()
            check_equal("start-over confirmation default", confirmations, [(
                "Start over with a different photographer? This clears saved details "
                "and the photos found so far.",
                False,
            )])
            check_equal("start-over prompts", [p[0] for p in prompts], [
                "Wikimedia Commons username",
                "Your name as it's credited on Wikimedia Commons",
                "Wikimedia Commons category for photos you took",
            ])
            check_equal("start-over saved username", prefs.get("username"), "NewUser")
            check_equal("start-over saved author", prefs.get("author"), "New Author")
            check_equal("start-over saved by category", prefs.get("by_category"),
                        "Photographs by New Author")
            check_equal("start-over cleared of-category", "of_category" in prefs, False)
            check_equal("start-over cleared qid", "qid" in prefs, False)
            check_equal("start-over preserved review path",
                        prefs.get("review_path"), "custom-review.md")
            check_equal("start-over preserved page size",
                        prefs.get("review_page_size"), 12)
            for path in ("custom-review.md", "review.md", "review.org",
                         ALL_PHOTOS_CACHE_FILE):
                check_equal("start-over removed %s" % path, os.path.exists(path), False)
            check_equal("start-over scan calls", len(scan_calls), 1)
            args = scan_calls[0]
            check_equal("start-over scan username", args.username, "NewUser")
            check_equal("start-over scan author", args.author, "New Author")
            check_equal("start-over scan category", args.by_category,
                        "Photographs by New Author")
            if "Cleared saved details and the photos found so far." not in output:
                raise AssertionError("missing start-over cleared message")

        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            save_local_preferences({"username": "OldUser", "author": "Old Author"})
            atomic_write_text("review.md", "old review\n")
            globals()["prompt_yes_no"] = lambda label, default=False: False

            def should_not_prompt(*args, **kwargs):
                raise AssertionError("cancelled start-over prompted for new details")

            globals()["prompt_text"] = should_not_prompt
            globals()["cmd_scan"] = lambda args: (_ for _ in ()).throw(
                AssertionError("cancelled start-over scanned"))
            sys.stdout = io.StringIO()
            interactive_start_over()
            prefs = local_preferences()
            check_equal("cancelled start-over kept username",
                        prefs.get("username"), "OldUser")
            check_equal("cancelled start-over kept review",
                        open("review.md", encoding="utf-8").read(), "old review\n")
    finally:
        sys.stdout = old_stdout
        globals()["prompt_text"] = old_prompt
        globals()["prompt_yes_no"] = old_confirm
        globals()["cmd_scan"] = old_cmd_scan
        os.chdir(old_cwd)
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value
            else:
                os.environ.pop(key, None)

def check_interactive_by_scan_identity_prompts():
    old_cwd = os.getcwd()
    old_env = {key: os.environ.pop(key, None) for key in (
        "WIKI_USERNAME", "WIKI_AUTHOR", "WIKI_BY_CATEGORY", "WIKI_OF_CATEGORY",
        "WIKI_QID", REVIEW_FORMAT_ENV)}
    old_prompt = globals()["prompt_text"]
    old_cmd_scan = globals()["cmd_scan"]
    old_open_review = globals()["open_review_from_guided_flow"]
    old_stdout = sys.stdout
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            save_local_preferences({
                "username": "SavedUser",
                "author": "Saved Author",
                "by_category": "Saved By Category",
            })
            scan_calls = []
            prompts = []

            def fake_cmd_scan(args):
                scan_calls.append(args)

            def fake_prompt(label, default=None, required=False):
                prompts.append((label, default, required))
                raise AssertionError("unexpected prompt: %s" % label)

            globals()["cmd_scan"] = fake_cmd_scan
            globals()["open_review_from_guided_flow"] = lambda out: None
            globals()["prompt_text"] = fake_prompt
            sys.stdout = io.StringIO()
            interactive_scan("by")
            check_equal("saved by-scan prompt count", prompts, [])
            check_equal("saved by-scan calls", len(scan_calls), 1)
            args = scan_calls[0]
            check_equal("saved by-scan username", args.username, "SavedUser")
            check_equal("saved by-scan author", args.author, "Saved Author")
            check_equal("saved by-scan category", args.by_category, "Saved By Category")

        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            scan_calls = []
            prompts = []
            answers = {
                "Wikimedia Commons username": "PromptedUser",
                "Your name as it's credited on Wikimedia Commons": "Prompted Author",
            }

            def fake_prompt_missing(label, default=None, required=False):
                prompts.append((label, default, required))
                return answers[label]

            globals()["cmd_scan"] = lambda args: scan_calls.append(args)
            globals()["prompt_text"] = fake_prompt_missing
            sys.stdout = io.StringIO()
            interactive_scan("by")
            check_equal("missing identity prompts", [p[0] for p in prompts], [
                "Wikimedia Commons username",
                "Your name as it's credited on Wikimedia Commons",
            ])
            check_equal("missing by-scan calls", len(scan_calls), 1)
            args = scan_calls[0]
            check_equal("missing by-scan username", args.username, "PromptedUser")
            check_equal("missing by-scan author", args.author, "Prompted Author")
            check_equal("missing by-scan default category",
                        args.by_category, "Photographs by Prompted Author")
    finally:
        sys.stdout = old_stdout
        globals()["prompt_text"] = old_prompt
        globals()["cmd_scan"] = old_cmd_scan
        globals()["open_review_from_guided_flow"] = old_open_review
        os.chdir(old_cwd)
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value
            else:
                os.environ.pop(key, None)

def check_wikidata_candidate_parser():
    sample = {
        "search": [
            {"id": "Q12345", "label": "Jay Dixit",
             "description": "writer and editor"},
            {"id": "Q67890", "label": "Jay Dixit",
             "description": "cricketer"},
            {"label": "No id", "description": "ignored"},
        ],
    }
    check_equal("wikidata candidate parser", parse_wikidata_candidates(sample), [
        {"id": "Q12345", "label": "Jay Dixit", "description": "writer and editor"},
        {"id": "Q67890", "label": "Jay Dixit", "description": "cricketer"},
    ])
    check_equal("empty wikidata candidates",
                parse_wikidata_candidates({"search": []}), [])
    check_equal("wikidata candidate label",
                wikidata_candidate_label(parse_wikidata_candidates(sample)[0]),
                "Jay Dixit — writer and editor (Q12345)")
    check_equal("wikidata url qid normalization",
                normalize_qid_input("https://www.wikidata.org/wiki/q12345"), "Q12345")

def check_interactive_wikidata_lookup_paths():
    old_prompt = globals()["prompt_text"]
    old_stdout = sys.stdout
    old_cwd = os.getcwd()
    old_env = os.environ.pop("WIKI_QID", None)
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            candidate_prompts = []

            def prompt_candidate(label, default=None, required=False):
                candidate_prompts.append((label, default, required))
                return "2"

            globals()["prompt_text"] = prompt_candidate
            sys.stdout = io.StringIO()
            qid = interactive_wikidata_qid("Jay Dixit", fetcher=lambda name: [
                {"id": "Q12345", "label": "Jay Dixit", "description": "writer"},
                {"id": "Q67890", "label": "Jay Dixit", "description": "cricketer"},
            ])
            check_equal("candidate selected qid", qid, "Q67890")
            check_equal("candidate selection prompt", [p[0] for p in candidate_prompts],
                        ["Choose"])

            manual_prompts = []
            manual_answers = iter(["2", "https://www.wikidata.org/wiki/Q12345"])

            def prompt_manual(label, default=None, required=False):
                manual_prompts.append((label, default, required))
                return next(manual_answers)

            globals()["prompt_text"] = prompt_manual
            sys.stdout = io.StringIO()
            qid = interactive_wikidata_qid("Jay Dixit", fetcher=lambda name: [
                {"id": "Q67890", "label": "Jay Dixit", "description": "cricketer"},
            ])
            check_equal("manual fallback qid", qid, "Q12345")
            check_equal("manual fallback prompts", [p[0] for p in manual_prompts], [
                "Choose",
                "Your Q-number is in your wikidata.org page URL, like Q12345.",
            ])

            no_result_prompts = []
            no_result_answers = iter(["1", "q99999"])

            def prompt_no_result(label, default=None, required=False):
                no_result_prompts.append((label, default, required))
                return next(no_result_answers)

            globals()["prompt_text"] = prompt_no_result
            sys.stdout = io.StringIO()
            qid = interactive_wikidata_qid("Missing Person", fetcher=lambda name: [])
            no_result_output = sys.stdout.getvalue()
            check_equal("no-result manual qid", qid, "Q99999")
            if "No Wikidata item found for 'Missing Person'" not in no_result_output:
                raise AssertionError("missing no-result Wikidata message")
            check_equal("no-result manual prompts", [p[0] for p in no_result_prompts], [
                "Choose",
                "Your Q-number is in your wikidata.org page URL, like Q12345.",
            ])

            error_prompts = []

            def prompt_error(label, default=None, required=False):
                error_prompts.append((label, default, required))
                return "2"

            def failing_fetcher(name):
                raise urllib.error.URLError("simulated outage")

            globals()["prompt_text"] = prompt_error
            sys.stdout = io.StringIO()
            qid = interactive_wikidata_qid("Offline Person", fetcher=failing_fetcher)
            error_output = sys.stdout.getvalue()
            check_equal("error skip qid", qid, None)
            if "Couldn't reach Wikidata" not in error_output:
                raise AssertionError("missing Wikidata error message")
            check_equal("error skip prompts", [p[0] for p in error_prompts], ["Choose"])
    finally:
        sys.stdout = old_stdout
        globals()["prompt_text"] = old_prompt
        os.chdir(old_cwd)
        if old_env is not None:
            os.environ["WIKI_QID"] = old_env

def check_interactive_of_scan_onboarding():
    old_cwd = os.getcwd()
    old_env = {key: os.environ.pop(key, None) for key in (
        "WIKI_USERNAME", "WIKI_AUTHOR", "WIKI_BY_CATEGORY", "WIKI_OF_CATEGORY",
        "WIKI_QID", REVIEW_FORMAT_ENV)}
    old_prompt = globals()["prompt_text"]
    old_cmd_scan = globals()["cmd_scan"]
    old_open_review = globals()["open_review_from_guided_flow"]
    old_fetch = globals()["fetch_wikidata_candidates"]
    old_stdout = sys.stdout
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            save_local_preferences({
                "username": "SavedUser",
                "author": "Saved Author",
                "by_category": "Saved By Category",
            })
            scan_calls = []
            opened = []

            def fake_cmd_scan(args):
                scan_calls.append(args)

            globals()["cmd_scan"] = fake_cmd_scan
            globals()["open_review_from_guided_flow"] = lambda out: opened.append(out)
            globals()["fetch_wikidata_candidates"] = lambda name: []

            no_qid_prompts = []
            no_qid_answers = {
                "Wikimedia Commons category for photos of you": "Saved Author",
                "Choose": "2",
            }

            def fake_prompt_no_qid(label, default=None, required=False):
                no_qid_prompts.append((label, default, required))
                return no_qid_answers[label]

            globals()["prompt_text"] = fake_prompt_no_qid
            sys.stdout = io.StringIO()
            interactive_scan("of")
            no_qid_output = sys.stdout.getvalue()
            check_equal("of scan skipped without qid", len(scan_calls), 0)
            if "Without a Wikidata ID" not in no_qid_output:
                raise AssertionError("missing graceful no-QID message")
            prefs = local_preferences()
            if "qid" in prefs or "of_category" in prefs:
                raise AssertionError("blank of-scan saved portrait settings")
            check_equal("of scan prompts without qid", [p[0] for p in no_qid_prompts], [
                "Wikimedia Commons category for photos of you",
                "Choose",
            ])
            check_equal("of-category default without qid", no_qid_prompts[0][1],
                        "Saved Author")
            if "No Wikidata item found for 'Saved Author'" not in no_qid_output:
                raise AssertionError("missing no-results message in of-scan")

            with_qid_prompts = []
            with_qid_answers = {
                "Wikimedia Commons category for photos of you": "Portrait Category",
                "Choose": "1",
            }

            def fake_prompt_with_qid(label, default=None, required=False):
                with_qid_prompts.append((label, default, required))
                return with_qid_answers[label]

            globals()["prompt_text"] = fake_prompt_with_qid
            globals()["fetch_wikidata_candidates"] = lambda name: [
                {"id": "Q12345", "label": "Saved Author", "description": "writer"},
            ]
            sys.stdout = io.StringIO()
            interactive_scan("of")
            check_equal("of scan proceeded with qid", len(scan_calls), 1)
            args = scan_calls[0]
            check_equal("of scan mode", args.scan_mode, "of")
            check_equal("of scan username", args.username, "SavedUser")
            check_equal("of scan author", args.author, "Saved Author")
            check_equal("of scan by category", args.by_category, "Saved By Category")
            check_equal("of scan category", args.of_category, "Portrait Category")
            check_equal("of scan qid", args.qid, "Q12345")
            prefs = local_preferences()
            check_equal("of scan preserved username", prefs.get("username"), "SavedUser")
            check_equal("of scan preserved author", prefs.get("author"), "Saved Author")
            check_equal("of scan preserved by category",
                        prefs.get("by_category"), "Saved By Category")
            check_equal("of scan saved of category",
                        prefs.get("of_category"), "Portrait Category")
            check_equal("of scan saved qid", prefs.get("qid"), "Q12345")
            check_equal("of scan prompts with qid", [p[0] for p in with_qid_prompts], [
                "Wikimedia Commons category for photos of you",
                "Choose",
            ])
    finally:
        sys.stdout = old_stdout
        globals()["prompt_text"] = old_prompt
        globals()["cmd_scan"] = old_cmd_scan
        globals()["open_review_from_guided_flow"] = old_open_review
        globals()["fetch_wikidata_candidates"] = old_fetch
        os.chdir(old_cwd)
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value
            else:
                os.environ.pop(key, None)

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
            raise AssertionError("of-only review omitted the photos-of-you category section")

def check_review_gallery_html():
    item = {
        "title": "File:Example photo.jpg",
        "label": "Example photo.jpg",
        "uses": 9,
        "target": "Photographs by Test Person",
        "checked": True,
    }
    text = review_gallery_html([item], "Test gallery")
    for needle in (
            "Test gallery",
            "Example photo.jpg",
            "Special:FilePath/Example_photo.jpg?width=320",
            "Open on Wikimedia Commons",
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
        "caption": "Test Person at an example event.",
        "articles": [
            {"title": "Example article", "url": "https://en.wikipedia.org/wiki/Example_article",
             "wiki": "en.wikipedia.org", "lang": "en"},
            {"title": "Another article", "url": "https://en.wikipedia.org/wiki/Another_article",
             "wiki": "en.wikipedia.org", "lang": "en"},
            {"title": "Third article", "url": "https://en.wikipedia.org/wiki/Third_article",
             "wiki": "en.wikipedia.org", "lang": "en"},
            {"title": "Fourth article", "url": "https://en.wikipedia.org/wiki/Fourth_article",
             "wiki": "en.wikipedia.org", "lang": "en"},
            {"title": "Fifth article", "url": "https://en.wikipedia.org/wiki/Fifth_article",
             "wiki": "en.wikipedia.org", "lang": "en"},
            {"title": "Sixth article", "url": "https://en.wikipedia.org/wiki/Sixth_article",
             "wiki": "en.wikipedia.org", "lang": "en"},
            {"title": "Seventh article", "url": "https://en.wikipedia.org/wiki/Seventh_article",
             "wiki": "en.wikipedia.org", "lang": "en"},
            {"title": "Artículo de ejemplo", "url": "https://es.wikipedia.org/wiki/Art%C3%ADculo_de_ejemplo",
             "wiki": "es.wikipedia.org", "lang": "es"},
            {"title": "Beispielartikel", "url": "https://de.wikipedia.org/wiki/Beispielartikel",
             "wiki": "de.wikipedia.org", "lang": "de"},
        ],
        "wikidata_items": [
            {"id": "Q123", "label": "Example person",
             "url": "https://www.wikidata.org/wiki/Q123"},
            {"id": "Q456", "label": "Example event",
             "url": "https://www.wikidata.org/wiki/Q456"},
        ],
    }
    scan_metrics = {
        "in_use_total": 8,
        "article_total": 21,
        "wikipedia_total": 4,
        "missing_category_total": 1,
    }
    categorized_item = dict(
        item,
        line=-1,
        title="File:Already categorized.jpg",
        label="Already categorized.jpg",
        checked=False,
    )
    text = web_review_html(
        "review.md", [item], ambiguous_count=2, scan_metrics=scan_metrics,
        all_photos=[item, categorized_item])
    for needle in (
            "Your photos on Wikipedia:",
            "Credit Check — Your photos on Wikipedia",
            '<h1 class="product-title" id="product-title">Credit Check</h1>',
            "A free tool from <a class=\"wikiportraits-link\"",
            "font-size: 17px",
            "width: 34px",
            "margin-top: 22px",
            "https://www.wikiportraits.org/",
            "wikiportraits-logo",
            "Your selection",
            "Your photographer category",
            "target-card",
            'id="target-card"',
            "Open on Wikimedia Commons",
            "white-space: nowrap",
            "commonsCategoryUrl",
            'const photographerPrefix = "Photographs by ";',
            'document.createElement("br")',
            "targetCard.href = commonsCategoryUrl(targets[0])",
            "action-rail",
            "selection-flow",
            "window.CREDIT_CHECK_ITEMS",
            "window.CREDIT_CHECK_ALL_PHOTOS",
            "window.CREDIT_CHECK_ALL_PHOTOS_AVAILABLE = true",
            "Already categorized.jpg",
            "window.CREDIT_CHECK_REVIEW_ARG",
            "window.CREDIT_CHECK_AMBIGUOUS_COUNT = 2",
            'window.CREDIT_CHECK_METRICS = {"article_total": 21, "in_use_total": 8, "missing_category_total": 1, "wikipedia_total": 4}',
            "window.CREDIT_CHECK_INITIAL_MODE",
            'window.CREDIT_CHECK_INITIAL_SCOPE = "missing"',
            "window.CREDIT_CHECK_GUIDED",
            "Your Wikipedia reach and category progress",
            'data-scope="missing"',
            'data-scope="all"',
            'data-scope="wikidata"',
            "Photos to add",
            "All your photos",
            "On Wikidata",
            "${allPhotosTotal.toLocaleString(\"en-US\")} on Wikipedia",
            ".scope-tab-icon {",
            ".scope-tab-title {",
            ".scope-tab-meta {",
            "scope-description",
            "Choose photos to add to your photographer category on Wikimedia Commons.",
            "Browse every photo from this scan, including photos already in your category.",
            "See which of your photos are used on Wikidata items.",
            "all-photos-view",
            '${readOnly ? " read-only" : ""}',
            ".picker-workspace {",
            ".app-shell.all-photos-view .action-rail > :not(.all-photos-rail)",
            ".picker-shell > .product-header {\n  position: static;",
            "Your complete Wikipedia gallery.",
            "Your Wikidata photo gallery.",
            'id="all-rail-photo-count"',
            "including photos already in your photographer category",
            "reach-row",
            "wikidata-reach",
            "Beyond Wikipedia",
            "wikidataPhotos.length",
            "wikidataItemIds.size",
            "Showing ${wikidataPhotos.length} photos used on Wikidata.",
            "icon-tabler-camera",
            "Wikipedia%27s_W.svg",
            "Notification-icon-Wikidata-logo.svg",
            "icon-tabler-world",
            'stroke-width="2"',
            'class="reach-label" id="photo-noun">photos</span>',
            'class="reach-label" id="article-noun">articles</span>',
            'class="reach-label" id="wikipedia-noun">Wikipedia language editions</span>',
            "of your",
            "photos</span> <span id=\"missing-verb\">are</span> still missing your Wikimedia Commons category",
            "Distinct article pages across all Wikipedia language editions. Each photo counts once.",
            "photos ready to review below",
            "a category before",
            "Choose photos to add",
            "Your photo appears in:",
            "Also used on Wikidata · ${wikidataItems.length} ${noun}",
            "wikidata-disclosure",
            "Example person",
            "https://www.wikidata.org/wiki/Q123",
            "photo-caption",
            "photo-title",
            "photo-image",
            "grid-template-columns: repeat(3, minmax(0, 1fr))",
            "family=Instrument+Sans:wght@400..800&amp;display=swap",
            'font: 15px/1.45 "Instrument Sans"',
            "min-height: 144px",
            "font-size: 28px",
            "font-weight: 800",
            "letter-spacing: -0.045em",
            "-webkit-line-clamp: 3",
            "object-fit: cover",
            "object-position: 50% 20%",
            ".thumb::before",
            ".thumb::after",
            "border-top: 1px solid rgba(88, 211, 148, 0.98)",
            "captionLine",
            "filenamePhotoTitle",
            "photoTitle",
            '${captionLine}\n      <div class="photo-image">',
            "return [item.caption, item.label",
            "Example article",
            "ENGLISH_ARTICLE_LIMIT = 5",
            "View all ${englishArticles.length} English-language Wikipedia articles",
            "+ ${hiddenEnglishCount} more",
            "article-more-count",
            "article-dialog-action",
            "Plus ${escapeHtml(moreWikipediaPages",
            "article-disclosure",
            'id="article-dialog"',
            'aria-haspopup="dialog"',
            "article-dialog-list",
            "columns: 5 190px",
            "articleDialog.showModal()",
            'articleDialog.addEventListener("close"',
            "Test Person at an example event.",
            "articleDialogDescription",
            "item.caption",
            "language-groups",
            "Photo details",
            "select-control",
            "syncThumbnailState",
            "reconcileThumbnails",
            "Thumbnail unavailable — open on Wikimedia Commons",
            'image.loading = "eager"',
            "Filter by filename, article, category",
            "Special:FilePath/Example_photo.jpg?width=420",
            "Select shown",
            "data-mode=\"selected\"",
            "Wikimedia Commons edits",
            "Review exact Wikimedia Commons edits",
            "Your choices are saved. Review the exact edits below",
            "credit-check commit ${reviewArg} --go",
            "Shortcuts: / search, Space select, o open",
            'data-action="done"',
            "Exit",
            "scheduleSave",
            "selectionRevision",
            "Saving...",
            "Saved",
            "navigator.sendBeacon",
            "beforeunload",
            'fetch("/save"',
            "window.close()",
            "You can now close this tab"):
        if needle not in text:
            raise AssertionError("web review missing %r" % needle)
    if 'data-action="preview"' in text or 'data-action="hide-preview"' in text:
        raise AssertionError("web review should show Wikimedia Commons edits live without preview buttons")
    if "Also used in" in text:
        raise AssertionError("web review should distinguish English articles from other-language pages")
    if "Plus ${extraEnglish.length} more English-language Wikipedia" in text:
        raise AssertionError("web review should offer one complete English article list")
    if "together in one place" in text:
        raise AssertionError("web review should keep the article dialog description concise")
    if "Every English-language Wikipedia article using this photo." in text:
        raise AssertionError("web review should show photo metadata instead of generic dialog copy")
    if 'data-action="save"' in text or 'data-action="save-close"' in text:
        raise AssertionError("web review should rely on auto-save plus Exit controls")
    if text.count('data-action="done">Exit</button>') != 2:
        raise AssertionError("web review should offer desktop and mobile Exit controls")
    deleted_category_copy = (
        "One place to keep " +
        "track of the Wikipedia articles " +
        "using your photos."
    )
    if deleted_category_copy in text:
        raise AssertionError("web review should omit the deleted category-card sentence")
    if "After saving" in text or "Then run:" in text or "review-path" in text:
        raise AssertionError("web review should not surface old save/path hints")

    selected_text = web_review_html("review.md", [item], initial_mode="selected")
    if 'window.CREDIT_CHECK_INITIAL_MODE = "selected"' not in selected_text:
        raise AssertionError("web review selected-only mode was not embedded")
    all_scope_text = web_review_html(
        "review.md", [item], all_photos=[item, categorized_item],
        initial_scope="all")
    if 'window.CREDIT_CHECK_INITIAL_SCOPE = "all"' not in all_scope_text:
        raise AssertionError("web review all-photo scope was not embedded")
    guided_text = web_review_html("review.md", [item], guided=True)
    if "Click Exit below, then choose Add selected photos to your photographer category page on Wikimedia Commons from the menu." not in guided_text:
        raise AssertionError("guided web review next step was not embedded")

def check_commit_summary_helpers():
    check_equal("category url",
                commons_category_url("Photographs by Test Person"),
                "https://commons.wikimedia.org/wiki/Category:Photographs_by_Test_Person")
    approved = [
        ("File:Alpha photo.jpg", "Photographs by Test Person"),
        ("File:Beta portrait.jpg", "Photographs by Test Person"),
    ]
    old_stdout = sys.stdout
    old_prompt_yes_no = globals()["prompt_yes_no"]
    old_browser_open = webbrowser.open
    try:
        sys.stdout = io.StringIO()
        print_plan(approved, "review.md", guided=True)
        plan_output = sys.stdout.getvalue()
        if "Preview - Wikimedia Commons edits (nothing is edited yet):" not in plan_output:
            raise AssertionError("commit preview title missing")
        if "Category:Photographs by Test Person" not in plan_output:
            raise AssertionError("commit preview category header missing")
        if "Alpha photo.jpg" not in plan_output or "File:Alpha" in plan_output:
            raise AssertionError("commit preview did not clean file titles")
        if "[[Category:" in plan_output or " -> " in plan_output:
            raise AssertionError("commit preview kept old wiki-link arrow layout")

        sys.stdout = io.StringIO()
        print_progress_line(1, 12, "Already there", "File:Alpha photo.jpg")
        progress_output = sys.stdout.getvalue()
        if "1/12" not in progress_output or "Already there" not in progress_output:
            raise AssertionError("commit progress status missing")
        if "File:Alpha" in progress_output:
            raise AssertionError("commit progress did not clean file titles")

        sys.stdout = io.StringIO()
        print_commit_done_summary(2, 1, 0, "missing-review.md", approved, guided=True)
        done_output = sys.stdout.getvalue()
        for needle in (
                "Congratulations - your selected photos have been added",
                "You can view your photos here:",
                "https://commons.wikimedia.org/wiki/Category:Photographs_by_Test_Person",
                "Added: 2",
                "Already there: 1",
                "Failed: 0"):
            if needle not in done_output:
                raise AssertionError("commit success output missing %r" % needle)

        prompts = []
        opened = []

        def yes_open(label, default=False):
            prompts.append((label, default))
            return True

        globals()["prompt_yes_no"] = yes_open
        webbrowser.open = lambda url: opened.append(url)
        sys.stdout = io.StringIO()
        offer_open_category_pages(approved)
        check_equal("open category prompt", prompts,
                    [("Open this category page now?", True)])
        check_equal("opened category url", opened,
                    ["https://commons.wikimedia.org/wiki/Category:Photographs_by_Test_Person"])
    finally:
        sys.stdout = old_stdout
        globals()["prompt_yes_no"] = old_prompt_yes_no
        webbrowser.open = old_browser_open

    by_list, of_list, amb_list, meta = sample_review_data()
    with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
        path = os.path.join(td, "review.md")
        write_review(by_list, of_list, amb_list, meta, path, "markdown")
        check_equal("remaining before selection", remaining_unselected_count(path), 1)
        items = parse_review_items(path)
        approvable = [item for item in items if item["target"]]
        set_review_approvals(path, items, {approvable[0]["line"]})
        check_equal("remaining after selection", remaining_unselected_count(path), 0)
        check_equal("clear selected review checkboxes", clear_review_selections(path), True)
        check_equal("selected cleared after guided add",
                    parse_approved(path, warn=False), [])
        check_equal("clearing unselected review is a no-op",
                    clear_review_selections(path), False)

def check_commit_credential_prompts():
    old_cwd = os.getcwd()
    old_env = {key: os.environ.get(key) for key in (
        "COMMONS_BOTUSER", "COMMONS_BOTPASS", "WIKI_USERNAME", PLAIN_PROMPTS_ENV)}
    old_input = builtins.input
    old_getpass = getpass.getpass
    old_stdout = sys.stdout
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            for key in ("COMMONS_BOTUSER", "COMMONS_BOTPASS", "WIKI_USERNAME"):
                os.environ.pop(key, None)
            os.environ[PLAIN_PROMPTS_ENV] = "1"

            save_local_preferences({"username": "SavedUser"})
            prompts = []

            def accept_default(prompt):
                prompts.append(prompt)
                return ""

            builtins.input = accept_default
            getpass.getpass = lambda prompt: "generated-secret"
            sys.stdout = io.StringIO()
            botuser, botpass = resolve_commit_credentials(
                argparse.Namespace(botuser=None, botpass=None))
            check_equal("bot username accepts default", botuser,
                        "SavedUser@categorize")
            check_equal("bot password prompt result", botpass, "generated-secret")
            if "Generated bot-password username [SavedUser@categorize]" not in prompts[0]:
                raise AssertionError("bot username prompt did not show saved default")

            save_local_preferences({"username": None})
            answers = iter(["", "TypedUser@categorize"])

            def blank_then_value(prompt):
                prompts.append(prompt)
                return next(answers)

            builtins.input = blank_then_value
            sys.stdout = io.StringIO()
            botuser, _botpass = resolve_commit_credentials(
                argparse.Namespace(botuser=None, botpass="secret"))
            check_equal("bot username blank without default loops", botuser,
                        "TypedUser@categorize")
    finally:
        sys.stdout = old_stdout
        builtins.input = old_input
        getpass.getpass = old_getpass
        for key, value in old_env.items():
            if value is not None:
                os.environ[key] = value
            else:
                os.environ.pop(key, None)
        os.chdir(old_cwd)

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
        server.review_lock = threading.Lock()
        server.review_client_revision = -1
        server.saved_count = None
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            body = json.dumps({
                "selected_lines": [approvable[0]["line"]],
                "close": False,
            }).encode("utf-8")
            req = urllib.request.Request(
                server.review_origin + "/save",
                data=body,
                headers={"Content-Type": "application/json"},
            )
            with urllib.request.urlopen(req, timeout=5) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            check_equal("web save without origin response", data["ok"], True)
            check_equal("web save without origin selections",
                        parse_approved(path, warn=False),
                        [("File:Example.jpg", "Photographs by Test Person")])

            body = json.dumps({
                "selected_lines": [approvable[0]["line"]],
                "close": False,
                "revision": 2,
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
            check_equal("web save revision response", data["ok"], True)

            body = json.dumps({
                "selected_lines": [],
                "close": False,
                "revision": 1,
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
            check_equal("stale browser revision ignored", data.get("stale"), True)
            check_equal("stale browser revision kept selections",
                        parse_approved(path, warn=False),
                        [("File:Example.jpg", "Photographs by Test Person")])

            body = json.dumps({
                "selected_lines": [approvable[0]["line"]],
                "close": True,
                "revision": 3,
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
        server.review_lock = threading.Lock()
        server.review_client_revision = -1
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

def check_hidden_category_scan():
    class FakeClient:
        def __init__(self):
            self.calls = []

        def read_post(self, params):
            self.calls.append(dict(params))
            return {
                "query": {
                    "pages": {
                        "123": {
                            "pageid": 123,
                            "title": "File:Hidden target.jpg",
                            "categories": [
                                {"title": "Category:Visible context"},
                                {"title": "Category:Unrelated hidden", "hidden": ""},
                                {"title": "Category:Photographs by Test Person", "hidden": ""},
                                {"title": "Category:Test Person", "hidden": ""},
                            ],
                        },
                    },
                },
            }

    old_stderr = sys.stderr
    try:
        sys.stderr = io.StringIO()
        client = FakeClient()
        details = fetch_details(
            client,
            ["File:Hidden target.jpg"],
            "Photographs by Test Person",
            "Test Person",
        )
    finally:
        sys.stderr = old_stderr

    check_equal("hidden-category request count", len(client.calls), 1)
    request = client.calls[0]
    check_equal("hidden-category scan does not exclude hidden categories",
                "clshow" in request, False)
    check_equal("hidden-category scan requests visibility markers",
                request.get("clprop"), "hidden")
    record = details["File:Hidden target.jpg"]
    check_equal("hidden photographer category detected", record["in_by"], True)
    check_equal("hidden subject category detected", record["in_of"], True)
    check_equal("unrelated hidden categories stay out of review context",
                record["cats"], {"Category:Visible context"})


def check_scan_routing():
    first_photo = {
        "wp": {
            "en.wikipedia.org|Shared_article": {
                "wiki": "en.wikipedia.org", "lang": "en", "title": "Shared_article"},
            "es.wikipedia.org|Otro_artículo": {
                "wiki": "es.wikipedia.org", "lang": "es", "title": "Otro_artículo"},
        },
    }
    second_photo = {
        "wp": {
            "en.wikipedia.org|Shared_article": {
                "wiki": "en.wikipedia.org", "lang": "en", "title": "Shared_article"},
            "de.wikipedia.org|Beispiel": {
                "wiki": "de.wikipedia.org", "lang": "de", "title": "Beispiel"},
        },
    }
    check_equal("distinct Wikipedia reach totals",
                wikipedia_reach_metrics([first_photo, second_photo]), {
                    "in_use_total": 2,
                    "article_total": 3,
                    "wikipedia_total": 3,
                })

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


def check_scan_reach_totals():
    old_cwd = os.getcwd()
    old_discover = globals()["discover_titles"]
    old_fetch_details = globals()["fetch_details"]
    old_fetch_captions = globals()["fetch_english_captions"]
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)

            def fake_discover(cl, username, author, insource_user):
                return {
                    "File:Missing.jpg": {"credited"},
                    "File:Categorized.jpg": {"credited"},
                    "File:Unused.jpg": {"credited"},
                }

            def record(pageid, in_by, wp):
                return {
                    "pageid": pageid,
                    "uploader": "TestUser",
                    "cats": set(),
                    "in_by": in_by,
                    "in_of": False,
                    "wp": wp,
                    "text": "{{Information\n|author=Test Person\n}}",
                    "description": "",
                    "caption": "",
                }

            def fake_details(cl, titles, by_cat, of_cat):
                return {
                    "File:Missing.jpg": record(1, False, {
                        "en.wikipedia.org|Shared_article": {
                            "wiki": "en.wikipedia.org", "lang": "en",
                            "title": "Shared_article"},
                        "es.wikipedia.org|Otro_artículo": {
                            "wiki": "es.wikipedia.org", "lang": "es",
                            "title": "Otro_artículo"},
                    }),
                    "File:Categorized.jpg": record(2, True, {
                        "en.wikipedia.org|Shared_article": {
                            "wiki": "en.wikipedia.org", "lang": "en",
                            "title": "Shared_article"},
                        "de.wikipedia.org|Beispiel": {
                            "wiki": "de.wikipedia.org", "lang": "de",
                            "title": "Beispiel"},
                    }),
                    "File:Unused.jpg": record(3, False, {}),
                }

            globals()["discover_titles"] = fake_discover
            globals()["fetch_details"] = fake_details
            globals()["fetch_english_captions"] = lambda cl, pageids: {}
            args = argparse.Namespace(
                username="TestUser", author="Test Person", by_category=None,
                of_category=None, qid=None, insource_user=False, no_derivatives=True,
                depth=0, english_only=False, min_uses=1, review_format="markdown",
                out="review.md", scan_mode="by", guided=True)
            check_equal("reach scan wrote review", cmd_scan(args), True)
            check_equal("reach scan totals include categorized photos",
                        review_scan_metrics("review.md"), {
                            "article_total": 3,
                            "in_use_total": 2,
                            "missing_category_total": 1,
                            "wikipedia_total": 3,
                        })
            items = parse_review_items("review.md")
            check_equal("reach scan grid excludes categorized photos", len(items), 1)
            check_equal("reach scan missing photo title", items[0]["title"],
                        "File:Missing.jpg")
            gallery_items = load_all_photos_cache("review.md", items)
            check_equal("reach gallery includes all in-use photos",
                        len(gallery_items), 2)
            check_equal("reach gallery includes categorized photo",
                        {item["title"] for item in gallery_items}, {
                            "File:Missing.jpg",
                            "File:Categorized.jpg",
                        })
            check_equal("reach gallery keeps all article uses",
                        sum(item["uses"] for item in gallery_items), 4)
    finally:
        globals()["discover_titles"] = old_discover
        globals()["fetch_details"] = old_fetch_details
        globals()["fetch_english_captions"] = old_fetch_captions
        os.chdir(old_cwd)


def check_zero_candidate_scan_no_review():
    old_cwd = os.getcwd()
    old_discover = globals()["discover_titles"]
    old_fetch_details = globals()["fetch_details"]
    old_write_review = globals()["write_review"]
    old_stderr = sys.stderr
    try:
        with tempfile.TemporaryDirectory(prefix="credit-check-self-test.") as td:
            os.chdir(td)
            save_local_preferences({"username": "WrongUser", "author": "Wrong Author"})

            def no_titles(cl, username, author, insource_user):
                return {}

            def should_not_fetch(*args, **kwargs):
                raise AssertionError("zero-candidate scan fetched details")

            def should_not_write(*args, **kwargs):
                raise AssertionError("zero-candidate scan wrote a review")

            globals()["discover_titles"] = no_titles
            globals()["fetch_details"] = should_not_fetch
            globals()["write_review"] = should_not_write
            sys.stderr = io.StringIO()
            args = argparse.Namespace(
                username="WrongUser", author="Wrong Author", by_category=None,
                of_category=None, qid=None, insource_user=False, no_derivatives=True,
                depth=0, english_only=False, min_uses=1, review_format="markdown",
                out="review.md", scan_mode="by")
            cmd_scan(args)
            output = sys.stderr.getvalue()
            if "found no files for user WrongUser" not in output:
                raise AssertionError("missing zero-candidate scan warning")
            if os.path.exists("review.md"):
                raise AssertionError("zero-candidate scan created a review file")
            check_equal("zero-candidate no-review label",
                        review_state_label(review_workflow_state()),
                        "Ready to find your photos")

            atomic_write_text("review.md", "existing review\n")
            sys.stderr = io.StringIO()
            cmd_scan(args)
            check_equal("zero-candidate existing review preserved",
                        open("review.md", encoding="utf-8").read(),
                        "existing review\n")
    finally:
        sys.stderr = old_stderr
        globals()["discover_titles"] = old_discover
        globals()["fetch_details"] = old_fetch_details
        globals()["write_review"] = old_write_review
        os.chdir(old_cwd)

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
    run_check("version and User-Agent identity", check_version_identity, failures)
    run_check("conflict-safe category writes", check_commit_write_safety, failures)
    run_check("atomic text writes", check_atomic_write_text, failures)
    run_check("photo caption metadata", check_photo_caption_metadata, failures)
    run_check("authorship classification", authorship, failures)
    run_check("Markdown review write/parse", lambda: write_and_parse_sample("markdown", ".md"), failures)
    run_check("org review write/parse", lambda: write_and_parse_sample("org", ".org"), failures)
    run_check("of-you review sections", check_of_only_review_sections, failures)
    run_check("browser review gallery", check_review_gallery_html, failures)
    run_check("local browser review app", check_web_review_html, failures)
    run_check("local browser review save", check_web_review_save, failures)
    run_check("local browser stale-save guard", check_web_review_stale_save, failures)
    run_check("commit completion helpers", check_commit_summary_helpers, failures)
    run_check("commit credential prompts", check_commit_credential_prompts, failures)
    run_check("Markdown terminal review toggle", lambda: write_toggle_sample("markdown", ".md"), failures)
    run_check("org terminal review toggle", lambda: write_toggle_sample("org", ".org"), failures)
    run_check("interactive selected-photo loading", check_load_approved_nonexit, failures)
    run_check("guided review state", check_guided_review_state, failures)
    run_check("guided menu dispatch", check_guided_menu_dispatch, failures)
    run_check("guided menu visibility", check_guided_menu_visibility, failures)
    run_check("guided menu copy matrix", check_guided_menu_copy_matrix, failures)
    run_check("guided copy messages", check_guided_copy_messages, failures)
    run_check("interactive settings core fields", check_interactive_settings_core_only, failures)
    run_check("interactive start-over reset", check_interactive_start_over, failures)
    run_check("interactive by-scan identity prompts", check_interactive_by_scan_identity_prompts, failures)
    run_check("Wikidata candidate parsing", check_wikidata_candidate_parser, failures)
    run_check("interactive Wikidata lookup paths", check_interactive_wikidata_lookup_paths, failures)
    run_check("interactive photos-of-you onboarding", check_interactive_of_scan_onboarding, failures)
    run_check("hidden-category scan detection", check_hidden_category_scan, failures)
    run_check("scan routing classification", check_scan_routing, failures)
    run_check("scan Wikipedia reach totals", check_scan_reach_totals, failures)
    run_check("zero-candidate scan guard", check_zero_candidate_scan_no_review, failures)

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
        print("Smoke test passed: no candidate files found, so no review was written.")
    else:
        if parse_approved(out):
            sys.exit("Smoke test failed: empty review unexpectedly had selected photos.")
        print("Smoke test passed: wrote %s" % out)

    if not args.keep and not args.out:
        temp_ctx.cleanup()
        print("Temporary smoke files removed. Use --keep or --out to inspect them.")


# ---------------------------------------------------------------- interactive app

PLAIN_PROMPTS_ENV = "CREDIT_CHECK_PLAIN"
PROMPT_MARKER = ""

def interactive_dev_mode():
    return preference_bool("dev_menu", default=False) or preference_bool(
        "dev", default=False) or os.environ.get("CREDIT_CHECK_DEV") in (
            "1", "true", "TRUE", "yes", "YES", "on", "ON")

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

def prompt_select(label, choices, default_index=0):
    if fancy_prompts_available():
        return ask_question(questionary.select(
            label,
            qmark=PROMPT_MARKER,
            choices=[
                questionary.Choice(text, value=value, description=desc)
                for text, value, desc in choices
            ],
        ))

    while True:
        print(label)
        for idx, (text, _value, _desc) in enumerate(choices, start=1):
            print("  %d. %s" % (idx, text))
        default = str(default_index + 1) if 0 <= default_index < len(choices) else "1"
        answer = prompt_text("Choose", default)
        if answer and answer.isdigit():
            idx = int(answer)
            if 1 <= idx <= len(choices):
                return choices[idx - 1][1]
        for text, value, _desc in choices:
            if answer == value or (answer and answer.lower() == text.lower()):
                return value
        print("Choose one of the listed options.")

def prompt_manual_qid():
    qid = prompt_text(
        "Your Q-number is in your wikidata.org page URL, like Q12345.",
        required=False)
    return normalize_qid_input(qid)

def prompt_wikidata_choice(candidates):
    choices = [
        (wikidata_candidate_label(candidate), candidate["id"], candidate.get("description", ""))
        for candidate in candidates
    ]
    choices.append(("None of these / enter a Q-number myself", MANUAL_QID_CHOICE, ""))
    choices.append(("Skip — don't set up photos of you", SKIP_QID_CHOICE, ""))
    choice = prompt_select("Which of these is you?", choices)
    if choice == MANUAL_QID_CHOICE:
        return prompt_manual_qid()
    if choice == SKIP_QID_CHOICE:
        return None
    return choice

def prompt_manual_or_skip_qid():
    choice = prompt_select("Which of these is you?", [
        ("None of these / enter a Q-number myself", MANUAL_QID_CHOICE, ""),
        ("Skip — don't set up photos of you", SKIP_QID_CHOICE, ""),
    ])
    if choice == MANUAL_QID_CHOICE:
        return prompt_manual_qid()
    return None

def interactive_wikidata_qid(author, fetcher=None):
    existing_qid = identity_default("qid", "WIKI_QID")
    if existing_qid:
        return existing_qid
    print("Looking you up on Wikidata…")
    if fetcher is None:
        fetcher = fetch_wikidata_candidates
    try:
        candidates = fetcher(author)
    except Exception:
        print("Couldn't reach Wikidata to look you up; enter your Q-number manually or skip.")
        return prompt_manual_or_skip_qid()
    if not candidates:
        print("No Wikidata item found for '%s' — you may not have one." % author)
        return prompt_manual_or_skip_qid()
    return prompt_wikidata_choice(candidates)

def print_no_wikidata_message():
    print("Without a Wikidata ID, Credit Check can't identify photos of you, "
          "so there's nothing to scan yet. Once you have your Q-number, "
          "choose this again.")

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
        print(missing_review_message(guided=True))
        return None
    return review

def open_review_from_guided_flow(review, initial_mode="all", initial_scope="missing"):
    if browser_review_should_fallback(False):
        print("Browser review is not available here; using terminal review instead.")
        return review_file_interactive(review, guided=True)
    ok = review_file_web(review, fallback_on_open_failure=True,
                         initial_mode=initial_mode, guided=True,
                         initial_scope=initial_scope)
    if ok is None:
        return review_file_interactive(review, guided=True)
    return ok

def review_workflow_state():
    review = existing_review_default()
    state = {
        "review": review,
        "exists": os.path.exists(review),
        "total": 0,
        "selected": 0,
        "ambiguous": 0,
        "all_photos_total": 0,
        "setup_complete": setup_complete(),
        "review_mode": "by",
        "of_category": None,
    }
    if not state["exists"]:
        return state
    try:
        context = review_section_context(review)
        state["review_mode"] = review_mode_from_context(context)
        state["of_category"] = context.get("of_category")
        items = parse_review_items(review)
        state["total"] = len([item for item in items if item["target"]])
        state["ambiguous"] = len([item for item in items if not item["target"]])
        state["selected"] = len(parse_approved(review, warn=False))
        all_photos = load_all_photos_cache(review, items)
        if all_photos is not None:
            state["all_photos_total"] = len(all_photos)
        else:
            metrics = review_scan_metrics(review, fallback_missing=state["total"])
            if metrics.get("in_use_total") == state["total"]:
                state["all_photos_total"] = state["total"]
    except OSError:
        state["exists"] = False
    return state

def review_state_label(state):
    if not state["setup_complete"] and not state["exists"]:
        return "Set up Credit Check to start"
    if not state["exists"]:
        return "Ready to find your photos"
    prefix = "" if state["setup_complete"] else "Setup incomplete · "
    if state["total"] == 0 and state["ambiguous"]:
        return "%sFound some photos, but none had a clear category yet" % prefix
    if state["total"] == 0:
        if state.get("review_mode") == "of":
            return "%sNo new photos of you this time" % prefix
        return "%sYou're all caught up — re-scan to check for new photos" % prefix
    text = "%d photos found · %d selected" % (state["total"], state["selected"])
    if state["ambiguous"]:
        text += " · %d ambiguous" % state["ambiguous"]
    return prefix + text

def review_unavailable_message(review, guided=False):
    if guided:
        if questionary is None or Application is None:
            print("The terminal photo picker needs questionary and prompt_toolkit. The installed Credit Check command has them.")
        elif not sys.stdin.isatty() or not sys.stdout.isatty():
            print("The terminal photo picker needs an interactive terminal.")
        else:
            print("The terminal photo picker is disabled because %s is set." %
                  PLAIN_PROMPTS_ENV)
        return
    if questionary is None or Application is None:
        print("Terminal review needs questionary and prompt_toolkit. The installed pipx "
              "command has them; otherwise tick [X] by editing %s." % review)
    elif not sys.stdin.isatty() or not sys.stdout.isatty():
        print("Terminal checkbox review needs an interactive terminal. Tick [X] by editing %s, "
              "or run credit-check review from a terminal." % review)
    else:
        print("Terminal checkbox review is disabled because %s is set. Tick [X] by editing %s."
              % (PLAIN_PROMPTS_ENV, review))

def review_file_interactive(review, guided=False):
    if not os.path.exists(review):
        print(missing_review_message(guided))
        return False

    items = parse_review_items(review)
    approvable = [item for item in items if item["target"]]
    ambiguous_count = len([item for item in items if not item["target"]])
    if not items:
        print(empty_review_message(guided, review_mode_from_context(
            review_section_context(review))))
        return True
    if not approvable:
        print(no_approvable_review_message(ambiguous_count, guided))
        return True

    if not fancy_prompts_available():
        review_unavailable_message(review, guided=guided)
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
    if scan_mode == "of":
        print("This finds portraits of you that other people shot and uploaded.")
        print("")

    username = identity_default("username", "WIKI_USERNAME")
    if not username:
        username = prompt_text("Wikimedia Commons username", required=True)
    author = identity_default("author", "WIKI_AUTHOR")
    if not author:
        author = prompt_text("Your name as it's credited on Wikimedia Commons", required=True)
    by_default = identity_default(
        "by_category", "WIKI_BY_CATEGORY", "Photographs by %s" % author)
    of_cat = qid = None

    if scan_mode == "of":
        by_cat = by_default
        of_cat = prompt_text(
            "Wikimedia Commons category for photos of you",
            identity_default("of_category", "WIKI_OF_CATEGORY", author),
            required=True)
        qid = interactive_wikidata_qid(author)
        if not qid:
            print_no_wikidata_message()
            return
    else:
        by_cat = by_default

    if scan_mode == "of":
        updates = {"of_category": of_cat, "qid": qid}
    else:
        updates = {
            "username": username,
            "author": author,
            "by_category": by_cat,
        }
    save_local_preferences(updates)

    run_guided_scan(username, author, by_cat, of_cat, qid, scan_mode)

def run_guided_scan(username, author, by_cat, of_cat=None, qid=None, scan_mode="by"):
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
        review_format=review_format, out=out, scan_mode=scan_mode, guided=True)
    wrote_review = cmd_scan(args)
    if wrote_review and sys.stdin.isatty():
        open_review_from_guided_flow(out)

def prompt_photographer_settings():
    username = prompt_text(
        "Wikimedia Commons username",
        identity_default("username", "WIKI_USERNAME"),
        required=True)
    author = prompt_text(
        "Your name as it's credited on Wikimedia Commons",
        identity_default("author", "WIKI_AUTHOR"),
        required=True)
    by_cat = prompt_text(
        "Wikimedia Commons category for photos you took",
        identity_default("by_category", "WIKI_BY_CATEGORY",
                         "Photographs by %s" % author),
        required=True)
    return {
        "username": username,
        "author": author,
        "by_category": by_cat,
    }

def interactive_settings():
    settings = prompt_photographer_settings()
    save_local_preferences(settings)
    print("Settings saved.")

def interactive_start_over():
    if not prompt_yes_no(
            "Start over with a different photographer? This clears saved details "
            "and the photos found so far.",
            False):
        print("Keeping the current photographer.")
        return
    clear_photographer_preferences()
    removed = clear_review_files()
    settings = prompt_photographer_settings()
    save_local_preferences({
        "username": settings["username"],
        "author": settings["author"],
        "by_category": settings["by_category"],
    })
    if removed:
        print("Cleared saved details and the photos found so far.")
    else:
        print("Cleared saved details.")
    run_guided_scan(settings["username"], settings["author"],
                    settings["by_category"], scan_mode="by")

def interactive_review(initial_mode="all", initial_scope="missing"):
    review = guided_review_path()
    if review:
        open_review_from_guided_flow(
            review, initial_mode=initial_mode, initial_scope=initial_scope)

def interactive_preview_and_commit():
    review = guided_review_path()
    if not review:
        return
    approved = load_approved(review, warn=False)
    if not approved:
        print("Opening the photo picker so you can choose photos first.")
        open_review_from_guided_flow(review)
        return
    print_plan(approved, review, guided=True)
    print("")
    print("This will add categories on Wikimedia Commons.")
    if not prompt_yes_no("Add these categories now?", False):
        print("No edits made.")
        return
    args = argparse.Namespace(review=review, go=True, summary=(
        "Add photographer or photos-of-you category"),
        throttle=5.0, botuser=None, botpass=None, guided=True,
        preview_shown=True)
    cmd_commit(args)

def interactive_commit():
    interactive_preview_and_commit()

def interactive_menu_actions(state):
    if not state["setup_complete"]:
        primary_value = "settings"
        primary_label = "Set up Credit Check"
        primary_desc = "Save your Wikimedia Commons account, credited name, and category."
    elif not state["exists"]:
        primary_value = "scan_by"
        primary_label = "Find your photos on Wikipedia"
        primary_desc = "Find photos credited to you that Wikipedia is using but that aren't in your photographer category yet."
    elif state["total"] == 0:
        if state.get("review_mode") == "of":
            primary_value = "scan_of"
            primary_label = "Search for photos of you again"
            primary_desc = "Look again for portraits of you taken by other people."
        else:
            primary_value = "scan_by"
            primary_label = "Scan again for new photos"
            primary_desc = "Look for new photos of yours now used on Wikipedia."
    elif state["selected"]:
        primary_value = "add"
        primary_label = "Add selected photos to your photographer category page on Wikimedia Commons"
        primary_desc = "Preview the Wikimedia Commons edits, then add them."
    else:
        primary_value = "review"
        primary_label = "Choose photos to add"
        primary_desc = "Open the browser photo picker and choose photos."
    actions = [(primary_label, primary_value, primary_desc)]
    if primary_value != "scan_by":
        if state["exists"]:
            actions.append((
                "Scan again for new photos",
                "scan_by",
                "Search again for new photos you've uploaded or that are newly "
                "used on Wikipedia. Replaces the photos found so far.",
            ))
        else:
            actions.append((
                "Find your photos on Wikipedia",
                "scan_by",
                "Find photos credited to you that Wikipedia is using but that aren't in your photographer category yet.",
            ))
    if state["total"] > 0 and primary_value != "review":
        actions.append((
            "Choose photos to add",
            "review",
            "Open the browser photo picker and choose photos.",
        ))
    if state.get("all_photos_total", 0) > 0:
        actions.append((
            "View all your photos",
            "view_all",
            "Open a read-only gallery of every photo from the latest scan that appears on Wikipedia.",
        ))
    if primary_value != "settings":
        actions.append((
            "Settings",
            "settings",
            "Save your name, Wikimedia Commons account, and category for photos you took.",
        ))
    if state["setup_complete"] or state["exists"]:
        actions.append((
            "Start over with a different photographer",
            "start_over",
            "Clear saved details and search for a new set of photos.",
        ))
    if primary_value != "scan_of":
        actions.append((
            "Find photos *of* you",
            "scan_of",
            "Find portraits of you taken by other people and add them to your category for photos of you.",
        ))
    if interactive_dev_mode():
        actions += [
            ("Run local tool checks", "self_test",
             "Verify parsing, review files, routing, and retry behavior."),
            ("Run a read-only Wikimedia Commons test", "smoke",
             "Confirm Wikimedia Commons access without editing anything."),
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
    if choice in ("self_test", "smoke", "scan_by", "scan_of", "review", "view_all",
                  "settings", "start_over", "add", "quit"):
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
        print("First step: save your Wikimedia Commons account and credited name.")
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
        elif action == "view_all":
            interactive_review(initial_scope="all")
        elif action == "settings":
            interactive_settings()
        elif action == "start_over":
            interactive_start_over()
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
    ap.add_argument("--version", action="version",
                    version="credit-check %s" % __version__)
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

    c = sub.add_parser("commit", help="add your photographer category to the photos you picked")
    c.add_argument("review")
    c.add_argument("--go", action="store_true",
                   help="actually edit (default: preview only)")
    c.add_argument("--summary", default="Add photographer or photos-of-you category")
    c.add_argument("--throttle", type=float, default=5.0,
                   help="seconds to pause between edits (default: 5)")
    c.add_argument("--botuser"); c.add_argument("--botpass")
    c.set_defaults(func=cmd_commit)

    st = sub.add_parser("self-test", help="run local parser and review-format checks")
    st.set_defaults(func=cmd_self_test)

    sm = sub.add_parser("smoke", help="run a read-only Wikimedia Commons smoke test")
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
