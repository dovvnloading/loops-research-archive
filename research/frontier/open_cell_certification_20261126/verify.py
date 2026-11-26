"""Finite audit of empty atlas cells; not a proof of MLC or of openness."""
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import time
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ATLAS = "research/frontier/mlc_coverage_atlas_20261126/atlas.json"
OLD = "research/frontier/mlc_open_cells_20261126/open_cells.json"
SOURCES = "research/frontier/mlc_open_cells_20261126/sources.json"
HASHES = "research/frontier/mlc_open_cells_20261126/input_hashes.json"
AXES = ("regime", "period", "locus", "rotation", "refinement")
EXPECTED_RULES = Counter(B1=14, B2=12, B3=6, B4=2, B5=4, B6=2, B7=2)
RULE_SOURCES = {
    "B1": ["K", "DL26"], "B2": ["CS2015", "DL26"],
    "B3": ["DL26", "CS2015"], "B4": ["DL26", "CS2015"],
    "B5": ["CS2015", "CS"], "B6": ["EE", "DL26"], "B7": ["KKL", "DL26"],
}

RULE_REASONS = {
    "B1": "Bounded ratios of cofinal absolute primitive periods bound every intervening integer maximal relative period. This contradicts unbounded relative periods.",
    "B2": "An eventually primitive sequence has only finitely many satellite levels; each reduced rational has finitely many signed CF digits, hence their finite union is bounded.",
    "B3": "A real straightened satellite rotation equals its negative modulo one, hence is 1/2. An eventually satellite real sequence has relative period 2 on its tail and a finite prefix, contradicting unbounded periods.",
    "B4": "Real straightening preserves conjugation; each satellite has rotation 1/2 and single signed digit 2, contrary to either unbounded-digit axis.",
    "B5": "Within-level squares make the first digit minimal; the first digit is at most the reduced denominator q_i. Cross-level b_(i+1,1) >= q_i^2 >= b_(i,1)^2, with b_(i,1)>=2, forces minimum digits to infinity. Neither bounded digits nor minimum not tending to infinity is possible.",
    "B6": "For a real straightened map E1 forces its nontrivial dividing rotation 1/q to equal its negative, so q=2. E3 uniformly bounds p=q+b. A finite prefix cannot restore unbounded relative periods.",
    "B7": "Every member of a parabolic tail lies in the 1/(n+1) limb, n>=2; these nonreal limbs are disjoint from their conjugates on infinitely renormalizable parameters. Real types are confined to the finite isolated types, whose periods are bounded.",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate key: {key}")
        result[key] = value
    return result


def load(path):
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def exclusion(cell):
    """Return first sufficient contradiction, independently of prior labels."""
    g, p, l, d, f = (cell[k] for k in AXES)
    unbounded = d in {"unbounded_digits_min_tends_infty",
                      "unbounded_digits_min_not_tends_infty"}
    conditions = (
        ("B1", p == "unbounded" and f == "k"),
        ("B2", g == "mixed_eventually_P" and unbounded),
        ("B3", g == "mixed_eventually_S" and p == "unbounded" and l == "real"),
        ("B4", l == "real" and unbounded),
        ("B5", g in {"S", "mixed_eventually_S"} and f == "qg" and
         d in {"bounded_digits", "unbounded_digits_min_not_tends_infty"}),
        ("B6", g in {"P", "mixed_eventually_P"} and l == "real" and
         p == "unbounded" and f == "ee"),
        ("B7", g in {"P", "mixed_eventually_P"} and l == "real" and
         p == "unbounded" and f == "kkl"),
    )
    return next((rule for rule, applies in conditions if applies), None)


def validate(atlas, old, sources, decisions, ranked):
    cells = atlas["classes"]
    targets = {k: v for k, v in cells.items() if v["status"] == "open"}
    require(Counter(v["status"] for v in cells.values()) ==
            Counter(covered=110, open=62), "atlas census")
    require(set(targets) == set(old) == set(decisions), "exact 62 IDs required")
    require(Counter(v["class"] for v in old.values()) ==
            Counter({"B": 42, "A": 4, None: 16}), "prior census")
    require(atlas["grid"]["semantics"].startswith("First true applicable predicate"),
            "predicate semantics")
    counts, rules = Counter(), Counter()
    for key, cell in targets.items():
        row, prior = decisions[key], old[key]
        require(key == "/".join(cell[k] for k in AXES), f"{key}: malformed ID")
        require(row["atlas_class"] == prior["class"], f"{key}: prior class changed")
        require(row["earlier_tests_false"] == cell["earlier_tests_false"] ==
                prior["atlas_negated_predicates"], f"{key}: negation list changed")
        require(bool(row["reason"]) and bool(row["sources"]) and
                set(row["sources"]) <= set(sources), f"{key}: rationale/source")
        b = exclusion(cell)
        if b:
            require(prior["class"] == "B" and prior["verification"] == "PROVED"
                    and prior["rule"] == b, f"{key}: independent exclusion disagrees")
            require(row["disposition"] == "EMPTY" and row["classification"] is None
                    and row["rule"] == b and row["sources"] == RULE_SOURCES[b],
                    f"{key}: empty row cannot become a mathematical classification")
            require(row["reason"] == RULE_REASONS[b], f"{key}: contradictory rationale changed")
            rules[b] += 1
        elif prior["class"] == "A":
            require(prior["verification"] == "STATEMENT_ONLY" and
                    row["disposition"] == "STATEMENT_ONLY" and
                    row["classification"] == "PREPRINT-ONLY" and row["rule"] is None,
                    f"{key}: preprint match scope")
            require(row["sources"] == prior["sources"] and
                    row["reason"] == prior["hypothesis"] and bool(row["limit"]),
                    f"{key}: inherited evidence changed")
        else:
            require(prior["class"] is None and prior["verification"] == "UNVERIFIED"
                    and row["disposition"] == "UNVERIFIED"
                    and row["classification"] is None and row["rule"] is None,
                    f"{key}: unsupported promotion")
            require(row["sources"] == prior["sources"] and
                    row["reason"] == prior["hypothesis"] and bool(row["limit"]),
                    f"{key}: inherited blocker changed")
        counts[row["disposition"]] += 1
    require(rules == EXPECTED_RULES, f"wrong exclusion counts {rules}")
    require(counts == Counter(EMPTY=42, STATEMENT_ONLY=4, UNVERIFIED=16),
            f"wrong dispositions {counts}")
    eligible = [k for k, v in decisions.items() if v["classification"] == "CERTIFIED-OPEN"]
    require(eligible == [] and ranked == [], "no rankable certified whole cells")
    return counts, rules


def hostile(atlas, old, sources, decisions, ranked):
    """Reject promotions, missing/extraneous rows, false rules and false ranks."""
    b = next(k for k, v in decisions.items() if v["disposition"] == "EMPTY")
    u = next(k for k, v in decisions.items() if v["disposition"] == "UNVERIFIED")
    a = next(k for k, v in decisions.items() if v["disposition"] == "STATEMENT_ONLY")
    mutations = [
        (b, "classification", "CERTIFIED-OPEN"),
        (b, "classification", "COVERED"),
        (b, "classification", "PREPRINT-ONLY"),
        (b, "rule", "B0"),
        (b, "reason", "Unverified or invented rationale"),
        (b, "sources", ["DL26"]),
        (b, "earlier_tests_false", ["fabricated"]),
        (u, "classification", "CERTIFIED-OPEN"),
        (u, "classification", "COVERED"),
        (a, "classification", "COVERED"),
    ]
    cases = []
    for key, field, value in mutations:
        bad = deepcopy(decisions)
        bad[key][field] = value
        cases.append((bad, ranked))
    bad = deepcopy(decisions)
    del bad[b]
    cases.append((bad, ranked))
    bad = deepcopy(decisions)
    bad["invented"] = bad[b]
    cases.append((bad, ranked))
    cases.append((decisions, [{"cell": b, "distance": 0}]))
    for bad, rank in cases:
        try:
            validate(atlas, old, sources, bad, rank)
        except ValueError:
            continue
        raise ValueError("hostile mutation was accepted")
    try:
        json.loads('{"x":1,"x":2}', object_pairs_hook=unique)
    except ValueError:
        pass
    else:
        raise ValueError("duplicate JSON key accepted")
    print(f"hostile checks: {len(cases)+1} rejected")


def verify_downloads(lock, old_sources, manifest):
    for name, entry in lock["sources"].items():
        original = old_sources[name]
        require(entry["url"] == original["url"] and
                entry["locator"] == original["locator"] and
                entry["version"] == original["version_or_venue"],
                f"{name}: source metadata changed")
        expected = entry["sha256"]
        require(re.fullmatch(r"[0-9a-f]{64}", expected) and
                expected == manifest["downloads"][entry["url"]]["sha256"],
                f"{name}: historical hash mismatch")
        error = None
        for attempt in range(3):
            try:
                req = Request(entry["url"], headers={"User-Agent": "open-cell-cert/1.0"})
                with urlopen(req, timeout=60) as response:
                    data = response.read(20_000_001)
                require(len(data) <= 20_000_000 and data.startswith(b"%PDF-"),
                        f"{name}: expected bounded PDF download")
                require(digest(data) == expected, f"{name}: downloaded SHA-256 mismatch")
                print(f"{name}: SHA-256 {expected} OK")
                break
            except (OSError, ValueError) as exc:
                error = exc
                if attempt == 2:
                    raise RuntimeError(f"{name}: source check failed: {error}") from exc
                time.sleep(2 ** attempt)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-downloads", action="store_true",
                        help="re-download and verify historical source byte locks")
    args = parser.parse_args()
    lock = load(HERE / "source_lock.json")
    require(set(lock["repository_inputs"]) == {ATLAS, OLD, SOURCES, HASHES},
            "repository input lock census")
    for path, expected in lock["repository_inputs"].items():
        require(re.fullmatch(r"[0-9a-f]{64}", expected) and
                digest((ROOT / path).read_bytes()) == expected, f"input changed: {path}")
    atlas, old, sources, manifest = (load(ROOT / p) for p in (ATLAS, OLD, SOURCES, HASHES))
    require(set(lock["sources"]) == set().union(*map(set, RULE_SOURCES.values())),
            "source lock census")
    for name, entry in lock["sources"].items():
        require(entry["url"] == sources[name]["url"] and
                entry["locator"] == sources[name]["locator"] and
                entry["version"] == sources[name]["version_or_venue"] and
                entry["sha256"] == manifest["downloads"][entry["url"]]["sha256"],
                f"{name}: inherited lock metadata")
    decisions, ranked = load(HERE / "decisions.json"), load(HERE / "ranked_open.json")
    counts, rules = validate(atlas, old, sources, decisions, ranked)
    hostile(atlas, old, sources, decisions, ranked)
    print("Dispositions:", dict(sorted(counts.items())))
    print("Exclusions:", dict(sorted(rules.items())))
    print("CERTIFIED-OPEN whole cells: 0; ranked list: []")
    if args.check_downloads:
        verify_downloads(lock, sources, manifest)
    else:
        print("Remote PDF bytes not checked (use --check-downloads).")


if __name__ == "__main__":
    main()
