#!/usr/bin/env python3
"""
gap_check.py — turn a list of people you've photographed into a ranked upload queue.

credit_check.py answers "where are my photos being used?"
This answers the opposite question: "which of my photos does Wikipedia still need?"

For each name it resolves the English Wikipedia article, looks at the lead image,
and scores how much a new free photograph would improve the article.

    P1  article exists, no lead image at all
    P2  lead image is low resolution (under ~1.2 MP)
    P3  lead image is old (uploaded 6+ years ago) or lacks Commons metadata
    P4  lead image is recent and decent — leave it alone
    --  no article, or a disambiguation page

Anything already credited to you is marked YOURS so it drops out of the queue.

Usage:
    python3 gap_check.py names.txt
    python3 gap_check.py --from-filenames ~/photos/tiff2025/
    python3 gap_check.py "Vanessa Kirby" "Jude Law"
"""

import argparse
import json
import os
import re
import sys
import time
import urllib.parse
from datetime import datetime, timezone

from credit_check import API as COMMONS, Client

EN = "https://en.wikipedia.org/w/api.php"

LOWRES_PIXELS = 1_200_000
STALE_YEARS = 6


def api(client, params, pause=0.4):
    """Use Credit Check's retrying, read-only POST client for batched queries."""
    result = client.read_post({**params, "formatversion": "2"})
    time.sleep(pause)
    return result


def norm(filename):
    """Commons titles use spaces, image URLs use underscores. Pick one."""
    return urllib.parse.unquote(filename).replace("_", " ")


def chunked(seq, n):
    for i in range(0, len(seq), n):
        yield seq[i : i + n]


def names_from_filenames(folder):
    """
    Pull people out of filenames like `vanessa-kirby_tiff_2024.jpg` or
    `jason-bateman-jude-law_tiff_2025.jpg`. Everything before the first
    underscore is the person or people, hyphen separated.
    """
    found = []
    for entry in sorted(os.listdir(folder)):
        if not entry.lower().endswith((".jpg", ".jpeg", ".png", ".webp", ".tif", ".tiff")):
            continue
        stem = os.path.splitext(entry)[0].split("_")[0]
        words = [w for w in stem.split("-") if w and not w.isdigit()]
        # Two people in one frame usually means four or more name words.
        if len(words) >= 4 and len(words) % 2 == 0:
            half = len(words) // 2
            people = [" ".join(words[:half]), " ".join(words[half:])]
        else:
            people = [" ".join(words)]
        for p in people:
            title = " ".join(w.capitalize() for w in p.split())
            if title and title not in found:
                found.append(title)
    return found


def lead_images(names):
    """Resolve each name to an article and its lead image, 40 at a time."""
    out = {}
    client = Client(EN)
    for batch in chunked(names, 40):
        data = api(
            client,
            {
                "action": "query",
                "titles": "|".join(batch),
                "prop": "pageimages|pageprops",
                "piprop": "name|original",
                "redirects": 1,
            },
        )
        q = data.get("query", {})
        # Map whatever we asked for back to whatever the wiki returned.
        alias = {n["from"]: n["to"] for n in q.get("normalized", [])}
        alias.update({r["from"]: r["to"] for r in q.get("redirects", [])})
        pages = {p.get("title"): p for p in q.get("pages", [])}
        for name in batch:
            resolved = alias.get(name, name)
            resolved = alias.get(resolved, resolved)
            page = pages.get(resolved, {})
            if page.get("missing"):
                out[name] = {"article": None}
                continue
            if "disambiguation" in page.get("pageprops", {}):
                out[name] = {"article": resolved, "disambig": True}
                continue
            pageimage = page.get("pageimage")
            out[name] = {
                "article": resolved,
                "file": norm(pageimage) if pageimage else None,
                "width": page.get("original", {}).get("width", 0),
                "height": page.get("original", {}).get("height", 0),
            }
    return out


def file_details(filenames):
    """Resolution, upload date and credit for each lead image, 40 at a time."""
    out = {}
    client = Client(COMMONS)
    for batch in chunked(filenames, 40):
        data = api(
            client,
            {
                "action": "query",
                "titles": "|".join("File:" + f for f in batch),
                "prop": "imageinfo",
                "iiprop": "extmetadata|timestamp",
            },
        )
        for page in data.get("query", {}).get("pages", []):
            title = norm(page.get("title", "")[len("File:") :])
            if page.get("missing"):
                out[title] = None
                continue
            info = (page.get("imageinfo") or [{}])[0]
            em = info.get("extmetadata", {})
            plain = lambda k: re.sub("<[^>]+>", "", em.get(k, {}).get("value", "")).strip()
            out[title] = {
                "artist": plain("Artist"),
                "license": plain("LicenseShortName"),
                "uploaded": info.get("timestamp", ""),
            }
    return out


def score(entry, detail, credit_names=()):
    if not entry.get("article"):
        return "--", "no English Wikipedia article"
    if entry.get("disambig"):
        return "--", "disambiguation page, check the real title"
    if not entry.get("file"):
        return "P1", "article has no lead image"

    if detail is None:
        return "P3", "lead image is not on Wikimedia Commons or has no Commons metadata"

    artist = detail["artist"].lower()
    aliases = [name.strip().lower() for name in credit_names if name and name.strip()]
    if any(alias in artist for alias in aliases):
        return "YOURS", "lead image is already yours"

    pixels = entry.get("width", 0) * entry.get("height", 0)
    if not pixels:
        return "P3", "lead image dimensions are unavailable"
    if pixels and pixels < LOWRES_PIXELS:
        return "P2", f"lead image is only {entry['width']}x{entry['height']}"

    if not detail.get("artist") or not detail.get("license"):
        return "P3", "lead image has incomplete Wikimedia Commons metadata"
    try:
        up = datetime.fromisoformat(detail.get("uploaded", "").replace("Z", "+00:00"))
        if up.tzinfo is None:
            raise ValueError("timestamp has no timezone")
    except (TypeError, ValueError):
        return "P3", "lead image upload date is unavailable"
    years = (datetime.now(timezone.utc) - up).days / 365.25
    if years >= STALE_YEARS:
        return "P3", f"lead image is {years:.0f} years old"

    return "P4", "lead image is recent and reasonable"


def run(names, from_filenames=None, json_output=False, credit_names=()):
    names = list(names)
    if from_filenames:
        names = names_from_filenames(from_filenames)
    elif len(names) == 1 and names[0].endswith(".txt"):
        with open(names[0]) as fh:
            names = [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]
    if not names:
        raise ValueError("give me some names, a .txt file, or --from-filenames")

    entries = lead_images(names)
    wanted = [e["file"] for e in entries.values() if e.get("file")]
    details = file_details(wanted) if wanted else {}

    rows = []
    for name in names:
        entry = entries.get(name, {"article": None})
        detail = details.get(entry.get("file") or "")
        band, why = score(entry, detail, credit_names)
        rows.append({"name": name, "priority": band, "reason": why,
                     "article": entry.get("article"), "file": entry.get("file")})

    order = {"P1": 0, "P2": 1, "P3": 2, "P4": 3, "YOURS": 4, "--": 5}
    rows.sort(key=lambda r: (order[r["priority"]], r["name"]))

    if json_output:
        print(json.dumps(rows, indent=2))
        return rows

    width = max(len(r["name"]) for r in rows) + 2
    current = None
    for r in rows:
        if r["priority"] != current:
            current = r["priority"]
            print(f"\n{current}")
        print(f"  {r['name']:<{width}} {r['reason']}")

    counts = {}
    for r in rows:
        counts[r["priority"]] = counts.get(r["priority"], 0) + 1
    print("\n" + "  ".join(f"{k}: {v}" for k, v in sorted(counts.items(), key=lambda kv: order[kv[0]])))
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("names", nargs="*", help="names, or a .txt file with one name per line")
    ap.add_argument("--from-filenames", metavar="DIR", help="read names out of a folder of photos")
    ap.add_argument("--json", action="store_true", help="emit JSON instead of a table")
    ap.add_argument("--credit", action="append", default=[],
                    help="name or Wikimedia Commons username that marks an image as yours")
    args = ap.parse_args()
    try:
        run(args.names, args.from_filenames, args.json, args.credit)
    except ValueError as error:
        ap.error(str(error))


if __name__ == "__main__":
    main()
