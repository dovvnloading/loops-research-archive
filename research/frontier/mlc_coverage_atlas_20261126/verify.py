#!/usr/bin/env python3
"""Check documentary coverage grid and lock primary-source PDF fingerprints.

No mathematical proof, source discovery or network use in default verification.
--lock is explicit: download source inputs, record byte SHA-256 or UNVERIFIED.
"""
import argparse
import concurrent.futures
import hashlib
import itertools
import json
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parent
REGIMES = ("P", "S", "mixed_eventually_P", "mixed_eventually_S", "mixed_recurrent")
PERIODS = ("bounded", "unbounded")
LOCI = ("real", "nonreal")
ROTATIONS = ("bounded_digits", "unbounded_digits_min_tends_infty",
             "unbounded_digits_min_not_tends_infty")
PREDICATES = {"levin1": "Lev1", "k": "K", "dec": "KLdec", "mol": "KLmol",
              "real_essential": "Lreal", "qg": "CS", "levin2": "Lev2",
              "levinadd": "Levadd", "sl_bounds": "L", "ee": "EE", "kkl": "KKL"}
CATALOG = set(PREDICATES.values()) | {"Y", "Ldensity", "DL23", "DL26", "C",
                                     "LY", "LvS", "GS", "DKL", "survey", "TUN"}

def load(name):
    return json.loads((ROOT / name).read_text(encoding="utf-8"),
                      object_pairs_hook=unique_object)

def unique_object(pairs):
    out = {}
    for k, v in pairs:
        assert k not in out, ("duplicate JSON key", k)
        out[k] = v
    return out

def expected_cells():
    for regime, period, locus in itertools.product(REGIMES, PERIODS, LOCI):
        if (regime, period, locus) == ("S", "unbounded", "real"):
            continue
        if period == "bounded":
            yield (regime, period, locus, "none" if regime == "P" else
                   "bounded_denominators", "all"), [], ["DL26"], []
            continue
        tests = ["levin1"]
        if regime not in ("S", "mixed_eventually_S"):
            tests += ["k"]
        if regime in ("P", "mixed_eventually_P"):
            tests += ["dec", "mol"]
        if regime not in ("S", "mixed_eventually_S"):
            tests += ["real_essential"]
        if regime in ("S", "mixed_eventually_S"):
            tests += ["qg", "levin2", "levinadd"]
        tests += ["sl_bounds"]
        if regime in ("P", "mixed_eventually_P"):
            tests += ["ee", "kkl"]
        for rotation in ("none",) if regime == "P" else ROTATIONS:
            prefix = (regime, period, locus, rotation)
            for i, test in enumerate(tests):
                theorem = PREDICATES[test]
                reported = test in ("ee", "kkl")
                yield prefix + (test,), tests[:i], [] if reported else [theorem, "TUN"], \
                    [theorem] if reported else []
            yield prefix + ("residual",), tests, [], ["DKL"] if locus == "real" else []

def validate(a):
    assert a["status"] == {"atlas": "imported", "residual": "open"}
    t, cells = a["theorems"], a["classes"]
    assert set(t) == CATALOG
    assert {k: v["theorem"] for k, v in a["grid"]["predicates"].items()} == PREDICATES
    assert tuple(a["grid"]["regimes"]) == REGIMES
    assert tuple(a["grid"]["periods"]) == PERIODS
    assert tuple(a["grid"]["loci"]) == LOCI
    assert tuple(a["grid"]["rotations_unbounded_with_satellite"]) == ROTATIONS
    assert [(v["regime"], v["period"], v["locus"]) for v in a["grid"]["excluded"]] == [
        ("S", "unbounded", "real")]
    expected = {"/".join(parts): (parts, prev, cov, rep)
                for parts, prev, cov, rep in expected_cells()}
    assert set(cells) == set(expected), ("missing/excess", sorted(set(expected)-set(cells)),
                                        sorted(set(cells)-set(expected)))
    for id_, (parts, prev, cov, rep) in expected.items():
        row = cells[id_]
        assert tuple(row[k] for k in ("regime", "period", "locus", "rotation",
                                     "refinement")) == parts
        assert row["earlier_tests_false"] == prev
        assert row["theorems"] == cov and row["reported_theorems"] == rep
        assert row["status"] == ("covered" if cov else "open")
        assert row["reason"].strip()
        for k in cov:
            assert t[k]["kind"] in ("mlc", "conditional_mlc")
            assert t[k]["source_status"] == "statement_verified"
        for k in rep:
            assert t[k]["kind"] == "reported_mlc"
    for source in t.values():
        assert all(source[k] for k in ("author", "title", "venue", "locator",
                                      "hypotheses", "conclusion", "kind", "source_status"))
        assert source["url"].startswith("https://") or source["source_status"] == "UNVERIFIED"
    e = a["example"]
    assert e["class_id"] == "S/unbounded/nonreal/unbounded_digits_min_tends_infty/residual"
    assert cells[e["class_id"]]["status"] == "open"
    assert set(e["checks"]) == set(t) and all(v.strip() for v in e["checks"].values())
    assert e["prefix"] == [f"1/{q}" for q in range(3, 8)]
    assert e["formula"] == "t_i=1/(i+2), i>=1"
    # Finite regression of the algebra in NOTE; not a proof of asymptotic or dynamical claims.
    P = 1
    for q in range(3, 101):
        assert q+1 < q*q
        if q >= 6:
            assert P > q and P*P > q
        P *= q
    return len(cells), sum(x["status"] == "covered" for x in cells.values())

def source_urls(a):
    return sorted(set(t["url"] for t in a["theorems"].values() if t["url"]))

def download(url):
    if not (url.endswith(".pdf") or "/pdf/" in url):
        return {"status": "UNVERIFIED", "sha256": None, "reason": "no primary PDF locator"}
    try:
        request = urllib.request.Request(url, headers={"User-Agent": "MLC-source-audit/1.0"})
        with urllib.request.urlopen(request, timeout=35) as response:
            data = response.read(80_000_001)
        if not data.startswith(b"%PDF-") or len(data) > 80_000_000:
            raise ValueError("not a PDF or exceeds byte limit")
        return {"status": "downloaded", "sha256": hashlib.sha256(data).hexdigest(),
                "bytes": len(data)}
    except Exception as e:
        return {"status": "UNVERIFIED", "sha256": None, "reason": type(e).__name__}

def lock(a):
    urls = source_urls(a)
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
        manifest = dict(zip(urls, pool.map(download, urls)))
    print(json.dumps(manifest, indent=2, sort_keys=True))
    (ROOT/"sources.json").write_text(json.dumps(manifest, indent=2, sort_keys=True)+"\n",
                                     encoding="utf-8")
    note = ROOT/"NOTE.md"
    start, end = "<!-- hashes:start -->", "<!-- hashes:end -->"
    old = note.read_text(encoding="utf-8")
    assert old.count(start) == old.count(end) == 1
    rows = ["", "| PDF input | SHA-256 / retrieval status |", "|---|---|"]
    for u, v in manifest.items():
        rows.append(f"| {u} | {v['sha256'] or 'UNVERIFIED ('+v['reason']+')'} |")
    note.write_text(old.split(start)[0]+start+"\n"+"\n".join(rows)+"\n\n"+end+
                    old.split(end)[1], encoding="utf-8")

def verify_lock(a):
    m = load("sources.json")
    assert set(m) == set(source_urls(a))
    note = (ROOT/"NOTE.md").read_text(encoding="utf-8")
    for u, v in m.items():
        if v["status"] == "downloaded":
            assert re.fullmatch(r"[a-f0-9]{64}", v["sha256"])
            assert v["bytes"] > 0 and v["sha256"] in note and u in note
        else:
            assert v["status"] == "UNVERIFIED" and v["sha256"] is None and v["reason"]
            assert u in note and "UNVERIFIED" in note
    return sum(v["status"] == "downloaded" for v in m.values()), len(m)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lock", action="store_true")
    parser.add_argument("--check-lock", action="store_true")
    args = parser.parse_args()
    a = load("atlas.json")
    n, c = validate(a)
    print(f"{n} cells: {c} covered; {n-c} open relative to audited implications")
    if args.lock:
        lock(a)
    if args.lock or args.check_lock:
        print("PDF inputs fingerprinted: %d/%d" % verify_lock(a))

if __name__ == "__main__":
    main()
