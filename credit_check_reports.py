"""Append-only scan history and printable reach reports for Credit Check.

This module is intentionally independent of the CLI.  Callers pass the
canonical ``all_photos_item`` dictionaries and the already-computed reach
metrics; this module never scans Wikimedia or edits review/cache files.
"""

from __future__ import annotations

import csv
import datetime as _datetime
import hashlib
import html
import io
import json
import os
from pathlib import Path
import tempfile
from urllib.parse import quote, urlparse
import uuid


SNAPSHOT_VERSION = 1
HISTORY_DIRECTORY = ".credit-check-history"
_SECRET_WORDS = ("password", "passwd", "secret", "token", "credential", "api_key", "apikey")
_METRIC_KEYS = (
    "in_use_total", "article_total", "wikipedia_total", "views_status", "views_last_month",
    "views_window_end", "views_window_months", "views_window_total",
    "views_by_month", "views_top_photos", "views_articles_counted",
    "views_articles_requested", "views_articles_no_data", "views_articles_failed",
    "views_articles_deferred", "views_mainpage_policy", "views_articles_excluded",
    "views_mainpage_lookup_failed", "views_excluded_photos",
    "image_requests_status", "image_requests_window_end", "image_requests_window_months",
    "image_requests_last_month", "image_requests_window_total", "image_requests_by_month",
    "image_requests_files_requested", "image_requests_files_counted", "image_requests_files_no_data",
    "image_requests_files_complete", "image_requests_files_last_month", "image_requests_files_failed",
    "image_requests_files_deferred", "image_requests_referer", "image_requests_agent",
    "image_requests_by_month_coverage", "image_requests_photos",
)


def _json_copy(value, label):
    try:
        return json.loads(json.dumps(value, ensure_ascii=False, sort_keys=True))
    except (TypeError, ValueError) as error:
        raise TypeError("%s must contain only JSON values" % label) from error


def _mapping(value, label):
    if not isinstance(value, dict):
        raise TypeError("%s must be a dictionary" % label)
    return value


def _clean_public_mapping(value, label):
    value = _json_copy(_mapping(value, label), label)
    def inspect(node, location):
        if isinstance(node, dict):
            for key, child in node.items():
                lowered = str(key).casefold().replace("-", "_")
                if any(word in lowered for word in _SECRET_WORDS):
                    raise ValueError("%s must not contain credentials or secrets (%s)" % (label, location + str(key)))
                inspect(child, location + str(key) + ".")
        elif isinstance(node, list):
            for index, child in enumerate(node):
                inspect(child, "%s%d." % (location, index))
    inspect(value, "")
    return value


def _fingerprint(value):
    encoded = json.dumps(value, ensure_ascii=False, sort_keys=True,
                         separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _utc_timestamp(value, *, allow_none=False):
    if value is None:
        if allow_none:
            return None
        value = _datetime.datetime.now(_datetime.timezone.utc)
    elif isinstance(value, str):
        try:
            value = _datetime.datetime.fromisoformat(value.replace("Z", "+00:00"))
        except ValueError as error:
            raise ValueError("scanned_at must be an ISO 8601 timestamp") from error
    if not isinstance(value, _datetime.datetime):
        raise TypeError("scanned_at must be a datetime or ISO 8601 string")
    if value.tzinfo is None:
        raise ValueError("scanned_at must include a timezone")
    return value.astimezone(_datetime.timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z")


def _article(article):
    article = _mapping(article, "article")
    wiki = article.get("wiki")
    title = article.get("title")
    if not isinstance(wiki, str) or not wiki or not isinstance(title, str) or not title:
        raise ValueError("every article needs non-empty wiki and title strings")
    url = article.get("url", "")
    if not isinstance(url, str):
        raise TypeError("article url must be a string")
    if url and urlparse(url).scheme not in ("http", "https"):
        raise ValueError("article links must use http or https")
    lang = article.get("lang", "")
    if not isinstance(lang, str):
        raise TypeError("article lang must be a string")
    return {"wiki": wiki, "lang": lang, "title": title, "url": url}


def _item(item):
    item = _mapping(item, "item")
    title = item.get("title")
    if not isinstance(title, str) or not title:
        raise ValueError("every photo needs a non-empty title")
    raw_articles = item.get("articles", [])
    if not isinstance(raw_articles, list):
        raise TypeError("photo articles must be a list")
    articles = sorted((_article(article) for article in raw_articles),
                      key=lambda a: (a["wiki"], a["title"], a["url"]))
    if len({(a["wiki"], a["title"]) for a in articles}) != len(articles):
        raise ValueError("a photo cannot contain duplicate Wikipedia placements")
    result = {
        "title": title,
        "label": item.get("label", title[5:] if title.startswith("File:") else title),
        "target": item.get("target", ""),
        "caption": item.get("caption", ""),
        "articles": articles,
        "wikidata_items": _json_copy(item.get("wikidata_items", []), "wikidata_items"),
        "uses": len(articles),
    }
    for key in ("label", "target", "caption"):
        if not isinstance(result[key], str):
            raise TypeError("photo %s must be a string" % key)
    return result


def _derived_metrics(items):
    pages = {(a["wiki"], a["title"]) for item in items for a in item["articles"]}
    wikis = {a["wiki"] for item in items for a in item["articles"]}
    return {"in_use_total": len(items), "article_total": len(pages),
            "wikipedia_total": len(wikis), "placement_total": sum(len(i["articles"]) for i in items)}


def make_snapshot(identity, scan_options, items, metrics, scanned_at=None):
    """Return a validated, canonical snapshot without writing it."""
    identity = _clean_public_mapping(identity, "identity")
    scan_options = _clean_public_mapping(scan_options, "scan_options")
    if not isinstance(items, list):
        items = list(items)
    clean_items = sorted((_item(item) for item in items), key=lambda item: item["title"].casefold())
    if len({item["title"] for item in clean_items}) != len(clean_items):
        raise ValueError("photo titles must be unique")
    supplied = _json_copy(_mapping(metrics, "metrics"), "metrics")
    clean_metrics = {key: supplied[key] for key in _METRIC_KEYS if key in supplied}
    derived = _derived_metrics(clean_items)
    for key in ("in_use_total", "article_total", "wikipedia_total"):
        if key in clean_metrics and clean_metrics[key] != derived[key]:
            raise ValueError("metrics.%s does not match the supplied photos" % key)
        clean_metrics[key] = derived[key]
    clean_metrics["placement_total"] = derived["placement_total"]
    scanned = _utc_timestamp(scanned_at, allow_none=True)
    scope = {"identity": identity, "scan_options": scan_options}
    return {
        "version": SNAPSHOT_VERSION,
        "snapshot_id": str(uuid.uuid4()),
        "scanned_at": scanned,
        "generated_at": _utc_timestamp(None),
        "scope_fingerprint": _fingerprint(scope),
        "identity": identity,
        "scan_options": scan_options,
        "metrics": clean_metrics,
        "items": clean_items,
    }


def _validate_snapshot(snapshot):
    snapshot = _json_copy(_mapping(snapshot, "snapshot"), "snapshot")
    if snapshot.get("version") != SNAPSHOT_VERSION:
        raise ValueError("unsupported snapshot version")
    required = ("snapshot_id", "scanned_at", "scope_fingerprint", "identity", "scan_options", "metrics", "items")
    if any(key not in snapshot for key in required):
        raise ValueError("snapshot is missing required fields")
    allowed = set(required) | {"version", "generated_at", "metadata", "comparison"}
    unknown = set(snapshot) - allowed
    if unknown:
        raise ValueError("snapshot has unsupported fields: %s" % ", ".join(sorted(unknown)))
    if snapshot["scope_fingerprint"] != _fingerprint({"identity": snapshot["identity"], "scan_options": snapshot["scan_options"]}):
        raise ValueError("snapshot scope fingerprint is invalid")
    rebuilt = make_snapshot(snapshot["identity"], snapshot["scan_options"], snapshot["items"], snapshot["metrics"], snapshot["scanned_at"])
    rebuilt["snapshot_id"] = snapshot["snapshot_id"]
    rebuilt["generated_at"] = _utc_timestamp(snapshot.get("generated_at"))
    if "metadata" in snapshot:
        rebuilt["metadata"] = _clean_public_mapping(snapshot["metadata"], "metadata")
    if "comparison" in snapshot:
        comparison = _json_copy(_mapping(snapshot["comparison"], "comparison"), "comparison")
        if comparison.get("current_snapshot_id") != rebuilt["snapshot_id"]:
            raise ValueError("saved comparison does not describe its snapshot")
        rebuilt["comparison"] = comparison
    return rebuilt


def _photo_record(item):
    filename = item["title"][5:] if item["title"].startswith("File:") else item["title"]
    return {"title": item["title"], "caption": item.get("caption", ""),
            "commons_url": "https://commons.wikimedia.org/wiki/File:" + quote(filename.replace(" ", "_"), safe="/:,-")}


def _placement_records(snapshot):
    return {(item["title"], a["wiki"], a["title"]): {
        "photo_title": item["title"], "article_wiki": a["wiki"],
        "article_title": a["title"], "article_url": a["url"],
    } for item in snapshot["items"] for a in item["articles"]}


def _multiples(snapshot):
    pages = {}
    for placement in _placement_records(snapshot).values():
        key = (placement["article_wiki"], placement["article_title"])
        pages.setdefault(key, []).append(placement["photo_title"])
    return [{"article_wiki": key[0], "article_title": key[1], "photo_titles": sorted(titles)}
            for key, titles in sorted(pages.items()) if len(titles) > 1]


def compare_snapshots(previous, current):
    """Compare snapshots from exactly the same identity and scan-option scope."""
    current = _validate_snapshot(current)
    if previous is None:
        return {"baseline": True, "previous_snapshot_id": None, "previous_scanned_at": None,
                "current_snapshot_id": current["snapshot_id"], "current_scanned_at": current["scanned_at"],
                "added_photos": [], "removed_photos": [], "added_placements": [], "removed_placements": [],
                "current_distinct_pages": current["metrics"]["article_total"],
                "current_placements": current["metrics"]["placement_total"],
                "pages_with_multiple_photos": _multiples(current)}
    previous = _validate_snapshot(previous)
    if previous["scope_fingerprint"] != current["scope_fingerprint"]:
        raise ValueError("snapshots have different identities or scan options")
    old_photos = {item["title"]: _photo_record(item) for item in previous["items"]}
    new_photos = {item["title"]: _photo_record(item) for item in current["items"]}
    old_places, new_places = _placement_records(previous), _placement_records(current)
    return {
        "baseline": False,
        "previous_snapshot_id": previous["snapshot_id"], "previous_scanned_at": previous["scanned_at"],
        "current_snapshot_id": current["snapshot_id"], "current_scanned_at": current["scanned_at"],
        "added_photos": [new_photos[k] for k in sorted(new_photos.keys() - old_photos.keys())],
        "removed_photos": [old_photos[k] for k in sorted(old_photos.keys() - new_photos.keys())],
        "added_placements": [new_places[k] for k in sorted(new_places.keys() - old_places.keys())],
        "removed_placements": [old_places[k] for k in sorted(old_places.keys() - new_places.keys())],
        "previous_distinct_pages": previous["metrics"]["article_total"],
        "current_distinct_pages": current["metrics"]["article_total"],
        "previous_placements": previous["metrics"]["placement_total"],
        "current_placements": current["metrics"]["placement_total"],
        "pages_with_multiple_photos": _multiples(current),
    }


def _history_dir(review_path):
    return Path(review_path).expanduser().resolve().parent / HISTORY_DIRECTORY


def _exclusive_text(path, text):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="") as output:
        output.write(text)
        output.flush()
        os.fsync(output.fileno())
    return path


def _snapshot_files(review_path):
    directory = _history_dir(review_path)
    return sorted(directory.glob("snapshot-*.json")) if directory.exists() else []


def load_snapshot(review_path, snapshot_id):
    """Load one archived snapshot by its complete UUID."""
    if not isinstance(snapshot_id, str) or not snapshot_id:
        raise ValueError("snapshot_id is required")
    matches = []
    for path in _snapshot_files(review_path):
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise ValueError("invalid archived snapshot: %s" % path) from error
        if payload.get("snapshot_id") == snapshot_id:
            matches.append((path, payload))
    if not matches:
        raise FileNotFoundError("snapshot not found: %s" % snapshot_id)
    if len(matches) > 1:
        raise ValueError("duplicate snapshot evidence for id: %s" % snapshot_id)
    return _validate_snapshot(matches[0][1])


def load_comparison(review_path, snapshot_id):
    """Load the comparison saved with an archived snapshot."""
    snapshot = load_snapshot(review_path, snapshot_id)
    if "comparison" not in snapshot:
        raise ValueError("snapshot has no saved comparison: %s" % snapshot_id)
    return snapshot["comparison"]


def load_latest_matching(review_path, identity, scan_options):
    """Load the newest valid snapshot with this exact public scope."""
    identity = _clean_public_mapping(identity, "identity")
    scan_options = _clean_public_mapping(scan_options, "scan_options")
    fingerprint = _fingerprint({"identity": identity, "scan_options": scan_options})
    matches = []
    for path in _snapshot_files(review_path):
        try:
            snapshot = _validate_snapshot(json.loads(path.read_text(encoding="utf-8")))
        except (OSError, json.JSONDecodeError, TypeError, ValueError) as error:
            raise ValueError("invalid archived snapshot: %s" % path) from error
        if snapshot["scope_fingerprint"] == fingerprint:
            matches.append(snapshot)
    return max(matches, key=lambda value: (value["generated_at"], value["snapshot_id"])) if matches else None


def archive_snapshot(review_path, snapshot, review_text=None):
    """Compare with the matching baseline, then append immutable evidence."""
    snapshot = _validate_snapshot(snapshot)
    previous = load_latest_matching(review_path, snapshot["identity"], snapshot["scan_options"])
    comparison = compare_snapshots(previous, snapshot)
    stamp = (snapshot["scanned_at"] or snapshot["generated_at"]).replace(":", "").replace("-", "")
    stem = "%s-%s" % (stamp, snapshot["snapshot_id"])
    snapshot_path = _history_dir(review_path) / ("snapshot-%s.json" % stem)
    archived_snapshot = dict(snapshot)
    archived_snapshot["comparison"] = comparison
    _exclusive_text(snapshot_path, json.dumps(archived_snapshot, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    review_archive_path = None
    if review_text is not None:
        if not isinstance(review_text, str):
            raise TypeError("review_text must be a string")
        suffix = Path(review_path).suffix or ".txt"
        review_archive_path = _history_dir(review_path) / ("review-%s%s" % (stem, suffix))
        try:
            _exclusive_text(review_archive_path, review_text)
        except Exception:
            # The snapshot remains valid evidence even if optional review archival fails.
            raise
    comparison.update({"snapshot_id": snapshot["snapshot_id"], "snapshot_path": str(snapshot_path),
                       "review_archive_path": str(review_archive_path) if review_archive_path else None})
    return comparison


def _e(value):
    return html.escape(str(value), quote=True)


def _safe_link(url, label):
    parsed = urlparse(url or "")
    if parsed.scheme not in ("http", "https"):
        return _e(label)
    return '<a href="%s">%s</a>' % (_e(url), _e(label))


def _number(value):
    return format(value, ",") if isinstance(value, int) and not isinstance(value, bool) else "—"


def _display_timestamp(value):
    if not value:
        return "Scan date not recorded"
    moment = _datetime.datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(_datetime.timezone.utc)
    return "%s %s at %s UTC" % (moment.day, moment.strftime("%B %Y"), moment.strftime("%H:%M"))


def render_reach_report(snapshot, comparison=None, title=None):
    """Render a self-contained, script-free HTML report suitable for printing."""
    snapshot = _validate_snapshot(snapshot)
    if comparison is not None and comparison.get("current_snapshot_id") != snapshot["snapshot_id"]:
        raise ValueError("comparison does not describe this snapshot")
    metrics = snapshot["metrics"]
    attribution = snapshot["identity"].get("author") or snapshot["identity"].get("credited_name") or snapshot["identity"].get("username") or snapshot["identity"].get("name") or "Photographer"
    report_title = title or "Wikipedia photo reach report"
    cards = "".join('<div class="metric"><strong>%s</strong><span>%s</span></div>' % pair for pair in (
        (_number(metrics["in_use_total"]), "photos used on Wikipedia"),
        (_number(metrics["article_total"]), "distinct Wikipedia articles"),
        (_number(metrics["wikipedia_total"]), "Wikipedia language editions"),
    ))
    image_requests = ""
    if "image_requests_status" in metrics:
        status = metrics.get("image_requests_status")
        counted = metrics.get("image_requests_files_counted", 0)
        requested = metrics.get("image_requests_files_requested", counted)
        complete = metrics.get("image_requests_files_complete", counted)
        last_month_counted = metrics.get("image_requests_files_last_month", counted)
        no_data = metrics.get("image_requests_files_no_data", 0)
        failed = metrics.get("image_requests_files_failed", 0)
        deferred = metrics.get("image_requests_files_deferred", 0)
        explanation = ('<p class="note">These are actual requests for your image files across all referring sites. '
                       'They count user-classified traffic, which excludes identified automated traffic, but may include preloads. '
                       'They are not unique people or verified visual impressions.</p>')
        availability = ('<p class="note">Photos measured: %s of %s. Complete histories: %s of %s. %s coverage: %s of %s. No data: %s. Failed requests: %s. Deferred files: %s. Missing months are omitted; displayed totals sum the measurements that are available.</p>' %
                        tuple(map(_e, (_number(counted), _number(requested), _number(complete), _number(requested),
                                       metrics.get("image_requests_window_end", "Last month"), _number(last_month_counted),
                                       _number(requested), _number(no_data), _number(failed), _number(deferred)))))
        if status == "unavailable":
            image_requests = ('<section><h2>Image requests unavailable</h2>'
                              '<p>Image-file requests could not be measured for this report. No request total is presented.</p>'
                              + explanation + availability + '</section>')
        else:
            qualifier = "Partial measurement · " if status == "partial" else ""
            request_cards = []
            if metrics.get("image_requests_last_month") is not None:
                request_cards.append('<div><strong>%s</strong><span>image requests in %s</span></div>' % (
                    _e(_number(metrics.get("image_requests_last_month"))),
                    _e(metrics.get("image_requests_window_end", "measurement month unavailable"))))
            if metrics.get("image_requests_window_total") is not None:
                request_cards.append('<div><strong>%s</strong><span>image requests across available measurements in the %s-month window</span></div>' % (
                    _e(_number(metrics.get("image_requests_window_total"))),
                    _e(metrics.get("image_requests_window_months", "—"))))
            totals = '<div class="viewgrid">%s</div>' % "".join(request_cards) if request_cards else '<p>No request total is available.</p>'
            image_requests = ('<section><h2>%sImage requests</h2>%s%s%s</section>' %
                              (_e(qualifier), totals, explanation, availability))
    views = ""
    if "views_last_month" in metrics:
        mainpage_policy = metrics.get("views_mainpage_policy")
        status = metrics.get("views_status", "complete")
        counted = metrics.get("views_articles_counted", 0)
        requested = metrics.get("views_articles_requested", counted)
        no_data = metrics.get("views_articles_no_data", 0)
        failed = metrics.get("views_articles_failed", 0)
        deferred = metrics.get("views_articles_deferred", 0)
        excluded = metrics.get("views_articles_excluded", 0)
        lookup_failed = metrics.get("views_mainpage_lookup_failed", [])
        if not isinstance(lookup_failed, list):
            lookup_failed = []
        explanation = ('<p class="note">These totals show views of Wikipedia articles that carried your photos when this scan ran. Your photos may not have been on those pages for the whole period. Article views do not measure how often someone saw your photos. Each article counts once in the overall total. Your Main Page placements stay listed but are excluded from view totals because a brief appearance can inflate them.</p>')
        lookup_note = ""
        if lookup_failed:
            lookup_note = (' Main Page lookup failed for %s Wikipedia %s (%s), so every article from %s was deferred.' % (
                _number(len(lookup_failed)), "project" if len(lookup_failed) == 1 else "projects",
                ", ".join(_e(project) for project in lookup_failed),
                "that project" if len(lookup_failed) == 1 else "those projects"))
        availability = ('<p class="note">Articles measured: %s of %s. Main Page articles excluded: %s. No pageview data: %s. Failed requests: %s. Deferred article views: %s.%s</p>' %
                        (tuple(map(_e, (_number(counted), _number(requested), _number(excluded),
                                        _number(no_data), _number(failed), _number(deferred)))) +
                         (lookup_note,)))
        if mainpage_policy != "exclude-v1":
            views = ('<section class="article-context"><h2>Article views need updating</h2>'
                     '<p>This report predates Main Page exclusion. Regenerate it with article views to calculate comparable totals.</p></section>')
        elif status == "excluded":
            views = ('<section class="article-context"><h2>Article views excluded</h2>'
                     '<p>All placements eligible for article-view measurement were Main Page placements. They remain listed below, but no article-view total is presented.</p>'
                     + explanation + availability + '</section>')
        elif status == "unavailable" or metrics.get("views_last_month") is None:
            views = ('<section class="article-context"><h2>Article views unavailable</h2>'
                     '<p>Wikipedia article pageviews could not be measured for this report. No pageview total is presented.</p>'
                     + explanation + availability + '</section>')
        else:
            qualifier = "Partial measurement · " if status == "partial" else ""
            views = ('<section class="article-context"><h2>%sArticle views</h2><div class="viewgrid"><div><strong>%s</strong><span>article views in %s</span></div>'
                     '<div><strong>%s</strong><span>article views across %s months</span></div></div>%s%s</section>') % (
                         _e(qualifier), _e(_number(metrics.get("views_last_month"))),
                         _e(metrics.get("views_window_end", "measurement month unavailable")),
                         _e(_number(metrics.get("views_window_total"))),
                         _e(metrics.get("views_window_months", "—")), explanation, availability)
    changes = ""
    if comparison:
        if comparison.get("baseline"):
            changes = '<section><h2>Changes since the previous matching scan</h2><p>This is the first snapshot for this photographer and these scan options.</p></section>'
        else:
            def change_list(records, kind):
                rows = []
                for record in records:
                    if kind == "photo":
                        rows.append("<li>%s</li>" % _safe_link(record.get("commons_url", ""), record.get("title", "Untitled photo")))
                    else:
                        article = _safe_link(record.get("article_url", ""), record.get("article_title", "Untitled article"))
                        photo_title = record.get("photo_title", "Untitled photo")
                        filename = photo_title[5:] if photo_title.startswith("File:") else photo_title
                        commons = "https://commons.wikimedia.org/wiki/File:" + quote(filename.replace(" ", "_"), safe="/:,-")
                        rows.append("<li>%s <small>%s · photo: %s</small></li>" % (
                            article, _e(record.get("article_wiki", "")), _safe_link(commons, photo_title)))
                return "".join(rows) or "<li>None</li>"
            detail_groups = (
                ("Added photos", comparison.get("added_photos", []), "photo"),
                ("Removed photos", comparison.get("removed_photos", []), "photo"),
                ("Added Wikipedia placements", comparison.get("added_placements", []), "placement"),
                ("Removed Wikipedia placements", comparison.get("removed_placements", []), "placement"),
            )
            change_details = "".join(
                '<details%s><summary>%s <b>%s</b></summary><ul>%s</ul></details>' % (
                    " open" if len(records) <= 8 else "", _e(label), _number(len(records)),
                    change_list(records, kind))
                for label, records, kind in detail_groups
            )
            changes = ('<section><h2>Changes since %s</h2><div class="changes">'
                       '<span><b>+%s</b> photos</span><span><b>−%s</b> photos</span>'
                       '<span><b>+%s</b> placements</span><span><b>−%s</b> placements</span></div>'
                       '<p class="note">A placement is one photo on one Wikipedia article. Distinct article totals count the page once when it carries several photos.</p><div class="change-details">%s</div></section>') % (tuple(map(_e, (
                           _display_timestamp(comparison.get("previous_scanned_at")), len(comparison.get("added_photos", [])),
                           len(comparison.get("removed_photos", [])), len(comparison.get("added_placements", [])),
                           len(comparison.get("removed_placements", []))))) + (change_details,))
    photo_sections = []
    request_photos = {}
    for photo in metrics.get("image_requests_photos", []):
        if isinstance(photo, dict) and isinstance(photo.get("title"), str):
            request_photos[photo["title"]] = photo
    excluded_photos = {}
    if metrics.get("views_mainpage_policy") == "exclude-v1":
        for photo in metrics.get("views_excluded_photos", []):
            if (isinstance(photo, dict) and isinstance(photo.get("title"), str)
                    and photo.get("views_status") == "excluded"):
                excluded_photos[photo["title"]] = photo
    for item in snapshot["items"]:
        filename = item["title"][5:] if item["title"].startswith("File:") else item["title"]
        commons = "https://commons.wikimedia.org/wiki/File:" + quote(filename.replace(" ", "_"), safe="/:,-")
        article_links = "".join("<li>%s <small>%s</small></li>" % (_safe_link(a["url"], a["title"]), _e(a["wiki"])) for a in item["articles"])
        caption = '<p class="caption">%s</p>' % _e(item["caption"]) if item.get("caption") else ""
        photo_views = ""
        if item["title"] in excluded_photos:
            photo_views = '<p class="note">Article views: excluded — only Main Page placements.</p>'
        photo_requests = ""
        request = request_photos.get(item["title"])
        if request:
            request_status = request.get("status")
            if request_status in ("complete", "partial"):
                parts = []
                if request.get("last_month") is not None:
                    parts.append('<b>%s image requests</b> in %s' % (
                        _e(_number(request.get("last_month"))), _e(metrics.get("image_requests_window_end", "—"))))
                if request.get("window_total") is not None:
                    parts.append('<b>%s image requests</b> across available measurements' %
                                 _e(_number(request.get("window_total"))))
                measured = request.get("months_counted")
                window = metrics.get("image_requests_window_months")
                if measured is not None and window is not None:
                    parts.append('%s of %s months measured' % (_e(_number(measured)), _e(_number(window))))
                photo_requests = '<p class="photo-requests">%s</p>' % " · ".join(parts)
            elif request_status == "no-data":
                photo_requests = '<p class="note">Image requests: no data returned.</p>'
            elif request_status == "failed":
                photo_requests = '<p class="note">Image requests: request failed.</p>'
            elif request_status == "deferred":
                photo_requests = '<p class="note">Image requests: deferred.</p>'
        photo_sections.append('<article><h3>%s</h3>%s<p>%s · %s placements</p>%s<ul>%s</ul></article>' % (
            _safe_link(commons, item["label"]), caption, _e(attribution),
            _number(len(item["articles"])), photo_requests + photo_views, article_links))
    scan_date = _display_timestamp(snapshot["scanned_at"])
    return """<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>%s</title><style>
:root{--paper:#f7f7f3;--white:#fff;--ink:#15171c;--muted:#5b6068;--line:#e5e5df;--green:#0b5738}*{box-sizing:border-box}body{margin:0;background:var(--paper);color:var(--ink);font:16px/1.5 system-ui,-apple-system,sans-serif}main{max-width:1080px;margin:auto;padding:56px 32px 80px}header{border-top:5px solid var(--green);padding-top:24px}h1{margin:.15em 0;font:400 clamp(38px,7vw,72px)/1.02 Georgia,serif;letter-spacing:-.03em}.eyebrow,h2{color:var(--green);font-size:12px;font-weight:800;letter-spacing:.14em;text-transform:uppercase}.byline,.note,.caption,small{color:var(--muted)}.metrics{display:grid;grid-template-columns:repeat(3,1fr);margin:40px 0;background:var(--white);border:1px solid var(--line)}.metric{padding:28px;border-top:2px solid var(--ink)}.metric+.metric{border-left:1px solid var(--line)}.metric strong,.viewgrid strong{display:block;color:var(--green);font:400 56px/1 Georgia,serif}.metric span,.viewgrid span{display:block;margin-top:10px;font-weight:700}section{margin:44px 0}.article-context{margin-top:32px;padding-top:28px;border-top:1px solid var(--line)}.article-context .viewgrid strong{font-size:42px}.viewgrid,.changes{display:grid;grid-template-columns:repeat(2,1fr);gap:16px}.viewgrid>div,.changes span{padding:20px;background:var(--white);border:1px solid var(--line)}.change-details{margin-top:18px}.change-details details{margin:8px 0;padding:12px 16px;background:var(--white);border:1px solid var(--line)}.change-details summary{cursor:pointer;font-weight:700}.change-details summary b{color:var(--green);float:right}article{break-inside:avoid;margin:0 0 18px;padding:22px;background:var(--white);border:1px solid var(--line)}article h3{margin:0;font:400 24px/1.25 Georgia,serif}a{color:var(--green);text-decoration-thickness:1px;text-underline-offset:3px}ul{columns:2;column-gap:32px;padding-left:22px}li{break-inside:avoid;margin:.35em 0}small{display:block}@media(max-width:700px){main{padding:32px 18px}.metrics,.viewgrid,.changes{grid-template-columns:1fr}.metric+.metric{border-left:0}.metric strong{font-size:46px}ul{columns:1}}@media print{body{background:#fff}main{max-width:none;padding:0}.metrics,article,.viewgrid>div,.changes span,.change-details details{background:#fff}details{display:block}details>summary{list-style:none}details>summary::marker{display:none}details:not([open])>*:not(summary){display:block}a{color:inherit;text-decoration:none}header{padding-top:14px}section{margin:28px 0}}
</style></head><body><main><header><div class="eyebrow">Credit Check · dated evidence</div><h1>%s</h1><p class="byline">Photographer: %s<br>%s</p></header><div class="metrics">%s</div>%s%s%s<section><h2>Photo and article evidence</h2>%s</section><footer class="note">Snapshot %s</footer></main></body></html>""" % (
        _e(report_title), _e(report_title), _e(attribution),
        "Scan completed: " + _e(scan_date) if snapshot["scanned_at"] else _e(scan_date),
        cards, image_requests, views, changes, "".join(photo_sections), _e(snapshot["snapshot_id"]),
    )


def write_reach_report(output_path, snapshot, comparison=None, title=None):
    """Write a new HTML report, refusing to overwrite an existing file."""
    return _exclusive_text(output_path, render_reach_report(snapshot, comparison, title))


def export_snapshot_json(output_path, snapshot, comparison=None):
    """Write a new machine-readable snapshot export."""
    snapshot = _validate_snapshot(snapshot)
    payload = {"snapshot": snapshot}
    if comparison is not None:
        if comparison.get("current_snapshot_id") != snapshot["snapshot_id"]:
            raise ValueError("comparison does not describe this snapshot")
        payload["comparison"] = _json_copy(comparison, "comparison")
    return _exclusive_text(output_path, json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n")


def export_placements_csv(output_path, snapshot):
    """Write one CSV row per photo-to-Wikipedia-page placement."""
    snapshot = _validate_snapshot(snapshot)
    stream = io.StringIO(newline="")
    fieldnames = ("photo_title", "article_wiki", "article_title", "article_url")
    has_image_requests = "image_requests_status" in snapshot["metrics"]
    if has_image_requests:
        fieldnames += ("image_requests_status", "image_requests_last_month", "image_requests_window_total",
                       "image_requests_months_counted", "image_requests_window_start", "image_requests_window_end",
                       "image_requests_window_months", "image_requests_referer", "image_requests_agent")
    writer = csv.DictWriter(stream, fieldnames=fieldnames)
    writer.writeheader()
    requests = {photo.get("title"): photo for photo in snapshot["metrics"].get("image_requests_photos", [])
                if isinstance(photo, dict) and isinstance(photo.get("title"), str)}
    months = snapshot["metrics"].get("image_requests_by_month", [])
    window_start = months[0][0] if months and isinstance(months[0], list) and months[0] else ""
    rows = []
    for placement in _placement_records(snapshot).values():
        request = requests.get(placement["photo_title"], {})
        row = dict(placement)
        if has_image_requests:
            row.update({
                "image_requests_status": request.get("status", ""),
                "image_requests_last_month": request.get("last_month") if request.get("last_month") is not None else "",
                "image_requests_window_total": request.get("window_total") if request.get("window_total") is not None else "",
                "image_requests_months_counted": request.get("months_counted", ""),
                "image_requests_window_start": window_start,
                "image_requests_window_end": snapshot["metrics"].get("image_requests_window_end", ""),
                "image_requests_window_months": snapshot["metrics"].get("image_requests_window_months", ""),
                "image_requests_referer": snapshot["metrics"].get("image_requests_referer", ""),
                "image_requests_agent": snapshot["metrics"].get("image_requests_agent", ""),
            })
        rows.append(row)
    writer.writerows(rows)
    return _exclusive_text(output_path, stream.getvalue())


def check_reports(cache_path):
    """Verify round trips and source counts against an actual all-photos cache."""
    cache_path = Path(cache_path)
    payload = json.loads(cache_path.read_text(encoding="utf-8"))
    items = payload.get("items")
    if not isinstance(items, list) or not items:
        raise ValueError("cache must contain a non-empty items list")
    pages = {(a["wiki"], a["title"]) for item in items for a in item.get("articles", [])}
    wikis = {a["wiki"] for item in items for a in item.get("articles", [])}
    metrics = {"in_use_total": len(items), "article_total": len(pages), "wikipedia_total": len(wikis)}
    first_title = items[0]["title"]
    second_title = items[1]["title"]
    metrics.update({
        "image_requests_status": "partial", "image_requests_window_end": "1999-12",
        "image_requests_window_months": 2, "image_requests_last_month": 123,
        "image_requests_window_total": 789, "image_requests_by_month": [["1999-11", 666], ["1999-12", 123]],
        "image_requests_by_month_coverage": [["1999-11", 2], ["1999-12", 1]],
        "image_requests_files_requested": len(items), "image_requests_files_counted": 2,
        "image_requests_files_complete": 1, "image_requests_files_last_month": 1,
        "image_requests_files_no_data": max(len(items) - 2, 0), "image_requests_files_failed": 0,
        "image_requests_files_deferred": 0, "image_requests_referer": "all-referers",
        "image_requests_agent": "user", "image_requests_photos": [
            {"title": first_title, "commons_url": "https://commons.wikimedia.org/wiki/" + quote(first_title),
             "status": "complete", "last_month": 123, "window_total": 456, "months_counted": 2},
            {"title": second_title, "commons_url": "https://commons.wikimedia.org/wiki/" + quote(second_title),
             "status": "partial", "last_month": None, "window_total": 333, "months_counted": 1},
        ],
        "views_status": "complete", "views_last_month": 12, "views_window_end": "1999-12",
        "views_window_months": 2, "views_window_total": 34, "views_by_month": [["1999-11", 22], ["1999-12", 12]],
        "views_top_photos": [], "views_articles_counted": len(pages), "views_articles_requested": len(pages),
        "views_articles_no_data": 0, "views_articles_failed": 0, "views_articles_deferred": 0,
        "views_mainpage_policy": "exclude-v1", "views_articles_excluded": 0,
        "views_mainpage_lookup_failed": [], "views_excluded_photos": [],
    })
    snapshot = make_snapshot({"credited_name": "Verification"}, {"source": "real-cache"}, items, metrics,
                             "2000-01-01T00:00:00Z")
    comparison = compare_snapshots(snapshot, snapshot)
    html_text = render_reach_report(snapshot, comparison)
    with tempfile.TemporaryDirectory(prefix="credit-check-reports-") as directory:
        json_path = export_snapshot_json(Path(directory) / "report.json", snapshot, comparison)
        csv_path = export_placements_csv(Path(directory) / "placements.csv", snapshot)
        legacy_snapshot = make_snapshot({"credited_name": "Verification"}, {"source": "legacy"}, items,
                                        {"in_use_total": len(items), "article_total": len(pages),
                                         "wikipedia_total": len(wikis)}, "2000-01-01T00:00:00Z")
        legacy_csv_path = export_placements_csv(Path(directory) / "legacy-placements.csv", legacy_snapshot)
        exported = json.loads(json_path.read_text(encoding="utf-8"))["snapshot"]
        csv_rows = list(csv.DictReader(csv_path.open(encoding="utf-8", newline="")))
        legacy_reader = csv.DictReader(legacy_csv_path.open(encoding="utf-8", newline=""))
        legacy_fields = legacy_reader.fieldnames
    checks = {
        "photos": len(snapshot["items"]), "placements": snapshot["metrics"]["placement_total"],
        "distinct_articles": snapshot["metrics"]["article_total"], "wikipedias": snapshot["metrics"]["wikipedia_total"],
        "json_round_trip": exported == snapshot, "csv_rows": len(csv_rows),
        "html_contains_all_photo_titles": all(_e(item["label"]) in html_text for item in snapshot["items"]),
        "html_has_no_script": "<script" not in html_text.casefold(),
        "html_has_image_requests_before_article_views": html_text.find("Image requests") < html_text.find("Article views"),
        "html_has_per_photo_image_requests": "123 image requests" in html_text and "1 of 2 months measured" in html_text,
        "html_has_coverage": "Photos measured: 2 of %s" % len(items) in html_text and "1999-12 coverage: 1 of %s" % len(items) in html_text,
        "csv_has_image_requests": any(row["image_requests_last_month"] == "123" and row["image_requests_months_counted"] == "2"
                                      and row["image_requests_window_start"] == "1999-11" and row["image_requests_referer"] == "all-referers"
                                      for row in csv_rows),
        "csv_preserves_legacy_fields": legacy_fields == ["photo_title", "article_wiki", "article_title", "article_url"],
    }
    if (checks["csv_rows"] != checks["placements"] or not checks["json_round_trip"]
            or not checks["html_contains_all_photo_titles"] or not checks["html_has_no_script"]
            or not checks["html_has_image_requests_before_article_views"]
            or not checks["html_has_per_photo_image_requests"] or not checks["html_has_coverage"]
            or not checks["csv_has_image_requests"] or not checks["csv_preserves_legacy_fields"]):
        raise AssertionError("report verification failed: %r" % checks)
    return checks
