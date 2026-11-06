#!/usr/bin/env python3
"""Check README research provenance, internal links and exact original SVG figures.

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
import sys
from collections import Counter
from pathlib import Path
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
README = ROOT / "README.md"
SVG_DIR = ROOT / "figs" / "readme"
EXPECTED_SVGS = (
    "tip-ray-portrait.svg",
    "two-scale-angle-map.svg",
    "two-scale-return.svg",
    "complex-return-disks.svg",
)
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
    assert len(rows) == 465, "The source-locked ledger changed; review the README"
    assert counts == EXPECTED_COUNTS, (
        "The source-locked ledger counts must be updated with provenance", counts
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

    # Check that the picture describes the manifest, not a generic or
    # editorially invented drawing. The SVG source stores exact fractions.
    portrait = json.loads(
        (ROOT / "results" / "period27_tip_ray_portrait.json").read_text(encoding="utf-8")
    )
    chord_root = ET.parse(SVG_DIR / "tip-ray-portrait.svg").getroot()
    chord_rows = [
        el for el in chord_root.iter() if el.get("data-lower") is not None
    ]
    actual_chords = {
        int(el.attrib["data-phase"]): (el.attrib["data-lower"], el.attrib["data-upper"])
        for el in chord_rows
    }
    expected_chords = {
        int(entry["phase"]): (entry["lower"], entry["upper"])
        for entry in portrait["nine_landing_pairs"]
    }
    assert len(chord_rows) == 9 and actual_chords == expected_chords
    assert portrait["distinct_rational_angles"] == 18
    assert portrait["pairwise_chord_crossings"] == 0

    # The independently maintained finite verifier supplies the internal
    # angle values; this is not a new analytical proof of Levin's theorems.
    sys.path.insert(0, str(ROOT / "research" / "independent_audits"))
    from verify_tip_levin_transport import certify as certify_levin  # noqa: E402

    exact_map = certify_levin()
    map_root = ET.parse(SVG_DIR / "two-scale-angle-map.svg").getroot()
    actual_p3 = {
        el.attrib["data-ambient"]: el.attrib["data-period3"]
        for el in map_root.iter() if el.get("data-period3") is not None
    }
    actual_p9 = {
        el.attrib["data-ambient"]: el.attrib["data-period9"]
        for el in map_root.iter() if el.get("data-period9") is not None
    }
    assert actual_p3 == exact_map["period3_internal_angles"]
    assert actual_p9 == exact_map["period9_internal_angles"]
    assert (ROOT / "code" / "generate_readme_research_figures.mjs").is_file()

    print(
        "PASS: README integrity: "
        f"{len(linked)} local links, {len(slugs)} headings, "
        f"{len(EXPECTED_SVGS)} accessible SVGs, "
        "9 source-backed chords, 6+2 checked internal angles, "
        "one GitHub Mermaid diagram, source-locked ledger"
    )


if __name__ == "__main__":
    check()
