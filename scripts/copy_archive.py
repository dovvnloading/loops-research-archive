#!/usr/bin/env python3
"""Keep scholarly URLs stable while replacing the old presentation layer."""
from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import shutil

from prepare_data import ROOT, is_archive_file, tracked_files

DIST = ROOT / "dist"
# Standalone pages cannot load the bundled fonts, so they name the same families
# and fall back to system faces. Colours match src/design/tokens.css.
PAGE_STYLE = (
    ":root{color-scheme:dark}"
    "body{margin:0;min-height:100vh;display:grid;align-content:center;background:#0a0a09;color:#ebe7dc;"
    "font:15px/1.5 'Libre Franklin','Franklin Gothic Medium','Helvetica Neue',Arial,sans-serif}"
    "main{width:min(560px,calc(100% - 36px));margin:0 auto}"
    "h1{margin:0 0 8px;font:500 28px/1.15 'STIX Two Text',Cambria,'Times New Roman',serif}"
    "p{margin:0 0 12px;color:#b6b2a6}a{color:#ebe7dc}"
)
REDIRECT = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>LOOPS — Research archive</title><meta http-equiv="refresh" content="0;url=./#archive">
<style>{PAGE_STYLE}</style>
</head><body><main><h1>This page has moved</h1><p>The research archive is now part of the LOOPS application.</p><p><a href="./#archive">Open the research record</a></p></main></body></html>
"""
NOT_FOUND = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="robots" content="noindex">
<title>LOOPS — Page not found</title><style>{PAGE_STYLE}</style></head>
<body><main><h1>Page not found</h1><p>Nothing is published at this address. The research files are unchanged and remain in the archive.</p><p><a href="https://dovvnloading.github.io/loops-research-archive/#archive">Open the research record</a></p></main></body></html>
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
