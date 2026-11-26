#!/usr/bin/env python3
"""Validate the citation overlay against the two unchanged input grids. No network or third-party dependencies."""
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent

def unique(pairs):
    out = {}
    for key, val in pairs:
        if key in out:
            raise ValueError(f"duplicate JSON key: {key}")
        out[key] = val
    return out

def load(path):
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique)

def require(condition, message):
    if not condition:
        raise ValueError(message)

def main():
    report = load(HERE / "resolution.json")
    require(report["schema_version"] == 1 and report["status"] == "imported", "schema/status")
    atlas_path = "research/frontier/mlc_coverage_atlas_20261126/atlas.json"
    open_path = "research/frontier/mlc_open_cells_20261126/open_cells.json"
    sources_path = "research/frontier/mlc_open_cells_20261126/sources.json"
    hash_path = "research/frontier/mlc_open_cells_20261126/input_hashes.json"
    require(set(report["inputs"]) == {atlas_path, open_path, sources_path, hash_path}, "input set")
    for path, fingerprint in report["inputs"].items():
        data = (ROOT / path).read_bytes()
        require(hashlib.sha256(data).hexdigest() == fingerprint["sha256"], f"SHA256 changed: {path}")
        require(hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest() == fingerprint["git_blob"], f"Git blob changed: {path}")
    atlas = load(ROOT / atlas_path)["classes"]
    overlay = load(ROOT / open_path)
    sources = load(ROOT / sources_path)
    require(len(atlas) == 172 and len(overlay) == 62, "grid census")
    require(set(overlay) == {k for k, v in atlas.items() if v["status"] == "open"}, "open-cell keys")
    for key, row in overlay.items():
        require(row["atlas_negated_predicates"] == atlas[key]["earlier_tests_false"], f"precedence mismatch: {key}")
    target = {k for k, v in overlay.items() if v["class"] == "A" or v["verification"] == "UNVERIFIED"}
    require(len(target) == 20 and set(report["items"]) == target, "target census")
    require(Counter(overlay[k]["class"] for k in target) == {None: 16, "A": 4}, "target breakdown")
    evidence = report["source_evidence"]
    allowed = {"VERIFIED", "CORRECTED", "STILL UNVERIFIED"}
    source_keys = {k for k, v in sources.items() if v.get("verification") == "UNVERIFIED"}
    require(source_keys == {"DKL", "DKLP", "GS", "Ldensity"}, "source target census")
    require(set(report["source_items"]) == source_keys | {"survey"}, "source resolution keys")
    for key, record in evidence.items():
        require(record["authors"] and record["title"] and record["publication"] and record["venue"], f"bibliography: {key}")
        if record["opened"]:
            require(record["url"] and record["locator"] and record["hypotheses"] and record["statement"], f"primary locator: {key}")
        else:
            require(record["locator"] is None and record["quote"] is None and record["statement"] is None and record["hypotheses"] is None and record["search_log"], f"unopened source: {key}")
    new_atlas = {k: v["status"] for k, v in atlas.items()}
    new_overlay = {k: v["class"] for k, v in overlay.items()}
    for key, item in report["items"].items():
        before = {"atlas": atlas[key]["status"], "open_cells": overlay[key]["class"], "verification": overlay[key]["verification"]}
        require(item["before"] == before and item["affected_cells"] == [key], f"before/impact: {key}")
        require(item["attributed_hypothesis"] == overlay[key].get("hypothesis"), f"attribution: {key}")
        require(item["verdict"] in allowed and item["reason"] and item["blocker"], f"verdict: {key}")
        require(bool(item["locator"]) and set(item["locator"]) <= set(evidence), f"evidence references: {key}")
        if item["verdict"] == "STILL UNVERIFIED":
            require(item["after"] == before, f"unverified promotion: {key}")
        if before["open_cells"] == "A":
            primary = {"ee": "EE", "kkl": "KKL", "qg": "CS2015"}[key.rsplit("/", 1)[1]]
            require(primary in item["locator"] and evidence[primary]["opened"], f"A primary: {key}")
            require(item["verdict"] == "VERIFIED" and evidence[primary]["publication"] == "preprint only located", f"A status: {key}")
            require(item["after"] == before, f"preprint is not published coverage: {key}")
            if key.startswith("mixed"):
                require("TUN" in item["locator"], f"tuning evidence: {key}")
        else:
            require(item["verdict"] == "STILL UNVERIFIED", f"unresolved whole cell promoted: {key}")
        new_atlas[key] = item["after"]["atlas"]
        new_overlay[key] = item["after"]["open_cells"]
    for key, item in report["source_items"].items():
        refs = sorted(i for i, row in atlas.items() if key in row.get("theorems", []) or key in row.get("reported_theorems", []) or key in overlay.get(i, {}).get("sources", []))
        require(item["affected_cells"] == refs and not item["changed_cells"], f"source crosswalk: {key}")
        require(item["verdict"] in allowed and item["reason"] and set(item["locator"]) <= set(evidence), f"source verdict: {key}")
        if item["verdict"] != "STILL UNVERIFIED":
            require(evidence[key]["opened"], f"source not opened: {key}")
        else:
            require(not evidence[key]["opened"], f"unverified source opened flag: {key}")
    def verdicts(records):
        return {k: sum(v["verdict"] == k for v in records.values()) for k in sorted(allowed)}
    def cls(values):
        counts = Counter(v if v is not None else "UNVERIFIED" for v in values)
        return {k: counts[k] for k in ("A", "B", "C", "UNVERIFIED")}
    c = report["consequences"]
    require(c["cell_verdict_counts"] == verdicts(report["items"]), "cell verdict counts")
    require(c["requested_source_verdict_counts"] == verdicts({k: report["source_items"][k] for k in source_keys}), "source verdict counts")
    require(c["ancillary_source_verdict_counts"] == verdicts({"survey": report["source_items"]["survey"]}), "ancillary verdict")
    require(c["atlas_before"] == Counter(v["status"] for v in atlas.values()) == {"covered": 110, "open": 62}, "atlas before")
    require(c["atlas_after"] == Counter(new_atlas.values()), "atlas after")
    require(c["open_cells_before"] == cls(v["class"] for v in overlay.values()) == {"A": 4, "B": 42, "C": 0, "UNVERIFIED": 16}, "overlay before")
    require(c["open_cells_after"] == cls(new_overlay.values()), "overlay after")
    changed = sorted(k for k, v in atlas.items() if v["status"] != new_atlas[k] or (k in overlay and overlay[k]["class"] != new_overlay[k]))
    require(c["changed_cells"] == changed, "changed cells")
    print(json.dumps(c, indent=2, sort_keys=True))
    print("PASS: locked inputs, exact 20-cell and 4-source census, evidence references and recomputed consequences")

if __name__ == "__main__":
    main()
