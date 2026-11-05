#!/usr/bin/env python3
"""Cross-check the canonical proof ledger, the public JSON, and site JS.

The two exported ledgers can use display punctuation that differs from the
canonical research source. This gate compares exact source IDs, statuses,
dependencies, and evidence pointers across all three. It checks exact
statement equality between the public JSON and site JS, while treating
canonical-source display punctuation separately.

This is a consistency check, not a mathematical proof.
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path


def check(root: Path) -> None:
    canonical = json.loads(
        (root / "research/mlc_unified/proof_obligations.json").read_text(encoding="utf-8")
    )
    public = json.loads((root / "ledger.json").read_text(encoding="utf-8"))
    js = (root / "ledger.js").read_text(encoding="utf-8").strip()
    prefix = "window.MLC_LEDGER="
    if not js.startswith(prefix) or not js.endswith(";"):
        raise AssertionError("Unexpected website ledger wrapper")
    site = json.loads(js[len(prefix):-1])

    source_nodes = canonical["obligations"]
    public_nodes = public["obligations"]
    site_nodes = site["obligations"]
    if not len(source_nodes) == len(public_nodes) == len(site_nodes) == 465:
        raise AssertionError("Ledger entry count changed")

    def by_id(entries: list[dict], name: str, key: str) -> dict[str, dict]:
        ids = [x[key] for x in entries]
        if len(ids) != len(set(ids)):
            raise AssertionError(f"{name}: duplicate obligation IDs")
        return {x[key]: x for x in entries}

    src = by_id(source_nodes, "canonical", "id")
    pub = by_id(public_nodes, "public", "id")
    web = by_id(site_nodes, "website", "i")
    if src.keys() != pub.keys() or src.keys() != web.keys():
        raise AssertionError("Mismatch in obligation ID sets")

    for id_, orig in src.items():
        live, view = pub[id_], web[id_]
        if orig["status"] != live["status"] or orig["status"] != view["s"]:
            raise AssertionError(f"Status mismatch: {id_}")
        if orig["dependencies"] != live["deps"] or orig["dependencies"] != view["d"]:
            raise AssertionError(f"Dependency mismatch: {id_}")
        if orig["evidence"] != live["evidence"] or orig["evidence"] != view["e"]:
            raise AssertionError(f"Evidence mismatch: {id_}")
        if live["statement"] != view["t"]:
            raise AssertionError(f"Public text mismatch: {id_}")

    counts = dict(Counter(x["status"] for x in source_nodes))
    if counts != public["counts"] or counts != site["counts"]:
        raise AssertionError("Incorrect or inconsistent published counts")
    print(f"PASS: {len(src)} aligned obligations; counts={counts}")
    print("Canonical statement typography is not required to match display typography")


if __name__ == "__main__":
    check(Path(__file__).resolve().parents[2])
