#!/usr/bin/env python3
"""Paper 2 source-edit structural and retiming regression.

Checks only the presence and consistent typing of the source audit's
new mathematical statements and the LaTeX environment structure.
This is NOT a mathematical proof, source-authenticity certificate,
or confirmation that the PDF release has been rebuilt.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
TEX = ROOT / "papers/paper2_rooted_end_compactification/main_v2.tex"


def check() -> None:
    source = TEX.read_text(encoding="utf-8")
    expected = [
        r"\label{prop:cycle-exclusion}",
        r"f^m(0)\ne\alpha",
        r"f^{kp}(0)\in\rootK",
        r"\cref{prop:cycle-exclusion}",
        r"\label{rem:fallback}",
        r"\cite[Lemma~2.1]{KLDecorations08}",
        r"g_*=f^\tau",
        r"\bigcup_{r=0}^{\tau-1} f^r(P)",
        r"\Kcyc_{\tau\bmod p}",
        r"choice $g=f^q$",
    ]
    missing = [term for term in expected if term not in source]
    if missing:
        raise AssertionError(f"Missing source-assumption/retiming statements: {missing}")

    obsolete = [
        "the entire architecture of this paper intact; only the transition time",
        "the critical orbit avoids the puzzle graphs\n\\cite{KLDecorations08}",
    ]
    for bad in obsolete:
        if bad in source:
            raise AssertionError(f"Unqualified old source assertion remains: {bad}")

    begins = Counter(re.findall(r"\\begin\{([A-Za-z*]+)\}", source))
    ends = Counter(re.findall(r"\\end\{([A-Za-z*]+)\}", source))
    if begins != ends:
        raise AssertionError(f"Unbalanced environments: {begins - ends} / {ends - begins}")

    labels = re.findall(r"\\label\{([^}]+)\}", source)
    duplicates = [label for label, count in Counter(labels).items() if count > 1]
    if duplicates:
        raise AssertionError(f"Duplicate LaTeX labels: {duplicates}")

    # There must be exactly one conditional deep-fallback remark and
    # the main dynamics theorem must retain the published shallow clock.
    if source.count(r"\label{rem:fallback}") != 1:
        raise AssertionError("Fallback remark was duplicated or lost")
    if r"\label{cpt:action}" not in source:
        raise AssertionError("Missing original shallow branch theorem")
    if "each transition having time $q$" not in source:
        raise AssertionError("Original shallow q-time theorem was silently retimed")
    if r"g=f^q" not in source:
        raise AssertionError("Original shallow map disappeared")

    print("PASS: Paper 2 source proof/retiming anchors, LaTeX environments and labels")
    print("Limit: this checks textual structure, not analytic assumptions or TeX compilation")


if __name__ == "__main__":
    check()
