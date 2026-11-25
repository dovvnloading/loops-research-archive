#!/usr/bin/env python3
"""Keep scholarly URLs stable while replacing the old presentation layer."""
from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import shutil

from prepare_data import ROOT, is_archive_file, tracked_files

DIST = ROOT / "dist"
REDIRECT = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>LOOPS — Research Archive</title><meta http-equiv="refresh" content="0;url=./#archive">
<style>body{background:#090c0f;color:#e0e9e4;font:18px system-ui;padding:12vw}a{color:#a9e6c7}</style>
</head><body><main><h1>The archive has a new home.</h1><p><a href="./#archive">Open the LOOPS research engine</a></p></main></body></html>
"""
NOT_FOUND = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>LOOPS — Page not found</title><style>body{background:#090c0f;color:#e0e9e4;font:18px system-ui;padding:12vw}a{color:#a9e6c7}</style></head>
<body><main><p>LOOPS / 404</p><h1>Outside the known set.</h1><p>This research path was not found.</p><p><a href="https://dovvnloading.github.io/loops-research-archive/#archive">Open the research archive</a></p></main></body></html>
"""


def main() -> None:
    if not (DIST / "index.html").is_file():
        raise SystemExit("Build the Vite application before packaging the archive.")
    copied, total = 0, 0
    for name in tracked_files():
        if not is_archive_file(name):
            continue
        source = ROOT / name
        if not source.is_file() or source.is_symlink():
            continue
        target = DIST / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
        copied += 1
        total += source.stat().st_size
    for name in ("favicon.svg", "robots.txt", "sitemap.xml"):
        source = ROOT / name
        if source.is_file():
            shutil.copy2(source, DIST / name)
    for name in ("classic.html", "dossier.html", "template.html"):
        (DIST / name).write_text(REDIRECT)
    (DIST / "404.html").write_text(NOT_FOUND)
    (DIST / ".nojekyll").touch()
    manifest = json.loads((DIST / "data/manifest.json").read_text())
    (DIST / "health.json").write_text(json.dumps({
        "application": "loops-fractal-research-engine", "schema": 1,
        "data_sha256": manifest["input_sha256"], "source_commit": manifest["source_commit"],
        "entry_sha256": sha256((DIST / "index.html").read_bytes()).hexdigest(),
        "archive_files": copied, "mlc_status": "MLC remains open",
    }, indent=2) + "\n")
    print(f"Preserved {copied} scholarly URLs ({total / 1024 / 1024:.1f} MiB); legacy pages redirect to the new archive.")


if __name__ == "__main__":
    main()
