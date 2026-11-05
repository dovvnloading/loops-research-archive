#!/usr/bin/env python3
"""Check README research-status provenance, internal links and SVG diagrams.

A README is not itself a mathematical proof. This simple offline
regression catches broken archive links, stale source-lock counts,
missing SVG accessibility text, and documentation headings/graphics
that silently disappear in a later edit.

Usage (standard library only):
    python code/verify_readme_integrity.py
"""
from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
README = ROOT / "README.md"
SVG_DIR = ROOT / "figs" / "readme"
EXPECTED_SVGS = ("ledger-status.svg", "two-scale-return.svg")
EXPECTED_COUNTS = {"imported": 34, "proved": 316, "open": 115}
EXPECTED_SOURCE_LOCK = "2026-07-27"

LINK = re.compile(r"!?\[[^\]]+\]\((\./[^)#]+)(?:#[^)]+)?\)")
LOCAL_ANCHOR = re.compile(r"\]\(#([a-zA-Z0-9_-]+)\)")
HEAD = re.compile(r"^#{2,6}\s+(.+?)\s*$", re.MULTILINE)


def heading_slug(title: str) -> str:
    """Enough of GitHub's heading slug for this deliberately plain README."""
    title = re.sub(r"<[^>]+>", "", title)
    title = re.sub(r"[^\w\s-]", "", title, flags=re.UNICODE)
    return re.sub(r"\s+", "-", title.strip().lower())


def check() -> None:
    text = README.read_text(encoding="utf-8")
    assert "# A Marked-Width Reduction of Mandelbrot Local Connectivity" in text
    assert "MLC remains open" in text
    assert "Paper 2's hypothesis H3" in text or "Paper 2's H3" in text
    assert EXPECTED_SOURCE_LOCK in text

    obligations = json.loads((ROOT / "ledger.json").read_text(encoding="utf-8"))
    rows = obligations["obligations"]
    counts = dict(Counter(row["status"] for row in rows))
    assert len(rows) == 465, "The status chart must be reviewed if ledger size changes"
    assert counts == EXPECTED_COUNTS, (
        "The source-locked status chart must be updated with provenance", counts
    )
    for key, count in EXPECTED_COUNTS.items():
        # Exact values occur in the accessible table as well as in the graphic.
        assert f"**{count}**" in text, (key, count)

    linked = [m.group(1) for m in LINK.finditer(text)]
    assert len(linked) >= 30, "Unusually few local evidence/source links"
    broken = sorted({
        p for p in linked if not (ROOT / p.removeprefix("./")).exists()
    })
    assert not broken, f"Broken local README links: {broken}"
    assert "&#" not in text

    slugs = {heading_slug(h) for h in HEAD.findall(text)}
    missing = sorted(set(LOCAL_ANCHOR.findall(text)) - slugs)
    assert not missing, f"README section navigation points to missing headings: {missing}"

    assert "'''mermaid" not in text
    assert "\x60\x60\x60mermaid" in text, "Research dependency diagram missing"
    ns = "{http://www.w3.org/2000/svg}"
    for name in EXPECTED_SVGS:
        svg = SVG_DIR / name
        assert f"./figs/readme/{name}" in text, f"README does not use {name}"
        root = ET.parse(svg).getroot()
        assert root.tag == ns + "svg", (name, root.tag)
        assert root.get("viewBox"), f"{name}: SVG requires scalable viewBox"
        assert root.find(ns + "title") is not None, f"{name}: missing accessible title"
        assert root.find(ns + "desc") is not None, f"{name}: missing accessible description"
        assert root.find(ns + "script") is None, f"{name}: script not allowed in static diagram"

    chart = (SVG_DIR / EXPECTED_SVGS[0]).read_text(encoding="utf-8")
    for count in EXPECTED_COUNTS.values():
        assert str(count) in chart
    assert "465" in chart and EXPECTED_SOURCE_LOCK in chart

    print(
        "PASS: README integrity: "
        f"{len(linked)} local links, {len(slugs)} headings, "
        f"{len(EXPECTED_SVGS)} accessible SVGs, "
        "one GitHub Mermaid diagram, source-locked 465-obligation ledger"
    )


if __name__ == "__main__":
    check()
