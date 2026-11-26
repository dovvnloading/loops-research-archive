"""Validate the documentary follow-up to atlas #132; not a proof of MLC."""
import argparse
from collections import Counter
import json
import hashlib
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ATLAS = HERE.parent / "mlc_coverage_atlas_20261126" / "atlas.json"
RESIDUAL = "S/unbounded/nonreal/unbounded_digits_min_tends_infty/residual"


def unique(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f"duplicate JSON key {key}")
        obj[key] = value
    return obj


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def require(test, message):
    if not test:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict", action="store_true",
                        help="also require all mathematical classifications resolved")
    args = parser.parse_args()
    atlas = load(ATLAS)
    cells = load(HERE / "open_cells.json")
    sources = load(HERE / "sources.json")
    expected = {k: v for k, v in atlas["classes"].items() if v["status"] == "open"}
    require(len(atlas["classes"]) == 172 and len(expected) == 62, "unexpected atlas census")
    require(cells.keys() == expected.keys(), f"missing {expected.keys()-cells.keys()}; extra {cells.keys()-expected.keys()}")
    for source_id, source in sources.items():
        require(bool(source.get("locator")) or source.get("verification") == "UNVERIFIED", f"{source_id}: no locator")
        if source.get("verification") == "VERIFIED":
            require(bool(source.get("url")) and bool(source.get("quote")), f"{source_id}: missing evidence")
    manifest_path = HERE / "input_hashes.json"
    if manifest_path.exists():
        manifest = load(manifest_path)
        for name in ("atlas.json", "NOTE.md"):
            actual = hashlib.sha256((ATLAS.parent / name).read_bytes()).hexdigest()
            require(manifest["local"][name] == actual, f"input hash mismatch: {name}")
        urls = {u for s in sources.values() for u in (s.get("url"), s.get("opened_url")) if u}
        require(set(manifest["downloads"]) == urls, "download URL census mismatch")
        for url, download in manifest["downloads"].items():
            value = download["sha256"]
            require(value == "UNVERIFIED" or re.fullmatch(r"[0-9a-f]{64}", value), f"{url}: invalid hash")
        for source_id, source in sources.items():
            prior = source["prior_atlas_sha256"]
            if prior != "UNVERIFIED":
                require(source.get("url") is not None, f"{source_id}: hash without source URL")
                current = manifest["downloads"][source["url"]]["sha256"]
                require(current in (prior, "UNVERIFIED"), f"{source_id}: prior lock mismatch")
    for cell_id, row in cells.items():
        old = expected[cell_id]
        require(cell_id == "/".join(old[k] for k in ("regime", "period", "locus", "rotation", "refinement")), f"{cell_id}: bad atlas key")
        require(row["class"] in ("A", "B", "C", None), f"{cell_id}: bad classification")
        require(bool(row["hypothesis"]) and bool(row["sources"]), f"{cell_id}: missing rationale")
        require(set(row["sources"]) <= sources.keys(), f"{cell_id}: unknown source")
        if row["class"] is None:
            require(row["verification"] == "UNVERIFIED", f"{cell_id}: unresolved must be explicit")
        if row["class"] == "C":
            require(row["verification"] == "VERIFIED", f"{cell_id}: cannot assert genuinely open if unverified")
        if row["class"] == "A":
            require(row["verification"] == "STATEMENT_ONLY" and row.get("theorem"), f"{cell_id}: label preprint scope")
        if row["class"] == "B":
            require(row["verification"] == "PROVED" and row.get("rule") in {"B1","B2","B3","B4","B5","B6","B7"}, f"{cell_id}: proof required")
    require(cells[RESIDUAL]["class"] is None and cells[RESIDUAL]["hypothesis"] == "see residual thread", "reserved cell")
    counts = Counter(row["class"] for row in cells.values())
    require(counts == Counter({"A": 6, "B": 42, None: 14}), "unexpected documentary census")
    print("62 exact atlas IDs:", dict(counts))
    if args.strict:
        require(counts[None] == 1, "mathematical classifications outstanding (other than reserved cell)")


if __name__ == "__main__":
    main()
