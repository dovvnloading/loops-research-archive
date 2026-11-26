#!/usr/bin/env python3
"""Finite source/atlas checks only. Never treat success as a proof of (7.2)."""
import argparse
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import time
from urllib.request import Request, urlopen

BASE = "69db52b89389430572910d36600fb5efa7fe41b3"
ATLAS = "research/frontier/mlc_coverage_atlas_20261126/atlas.json"
ATLAS_SHA = "0f9bc28a8f5392e50f7b9e30a5b2c5ba8fc5f73b9c6d9400545cac0c883df284"
SOURCES = [
    ("2309.02107v3", "e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b",
     41, {3: ["Theorem A", "Theorem B"], 16: ["Lemma 2.5", "(2.13)"],
          17: ["Lemma 2.6"], 22: ["Theorem 3.1"], 27: ["Lemma 3.7", "Remark 3.8"],
          30: ["Definition 3.12"], 32: ["(4.4)"], 33: ["Case (S)"],
          36: ["Theorem 6.1"], 37: ["(6.3)"], 38: ["Remark 6.3", "Theorem 7.1"],
          39: ["Theorem 7.2", "(7.1)", "(7.2)"], 40: ["(7.3)"]}),
    ("math/0609045v3", "46e7ff4d5cc8ea190e439f45b2e4ed7308c1cf588a666daa5150eeb0b435c9c0",
     63, {14: ["Lemma 2.5"], 37: ["Theorem 7.3", "Lemma 7.4"]}),
]

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(["git", *args])

def grep(term, line_numbers=False, scope=()):
    proc = subprocess.run(["git", "grep", "-n" if line_numbers else "-l",
                           "-F", "-e", term, BASE, "--", *scope],
                          capture_output=True, text=True)
    require(proc.returncode in (0, 1), proc.stderr)
    return proc.stdout.splitlines()

def inventory():
    raw = git("show", f"{BASE}:{ATLAS}")
    require(digest(raw) == ATLAS_SHA, "base atlas digest mismatch")
    require(Path(ATLAS).read_bytes() == raw, "working atlas changed")
    cells = json.loads(raw)["classes"]
    require(len(cells) == 172, "atlas size")
    require(sum(c["status"] == "covered" for c in cells.values()) == 110, "covered")
    require(sum(c["status"] == "open" for c in cells.values()) == 62, "open")
    expected = {(r, locus) for r in
                ("P", "S", "mixed_eventually_P", "mixed_eventually_S", "mixed_recurrent")
                for locus in ("real", "nonreal")}
    selected = {key: c for key, c in cells.items() if c["period"] == "bounded"}
    require(len(selected) == 10, "bounded cell count")
    require({(c["regime"], c["locus"]) for c in selected.values()} == expected, "bounded axes")
    require(all(c["theorems"] == ["DL26"] and c["status"] == "covered"
                for c in selected.values()), "DL26 direct credit")
    for key in sorted(selected):
        print("DL26 whole existing row:", key)
    print("Atlas sha256", digest(raw), "172/110/62; 10 DL26, zero added")
    for term in ("2606.27272", "1509.07843", "2601.21905", "2512.24171", "2309.02107"):
        hits = grep(term)
        require(bool(hits), f"expected prior mentions: {term}")
        print(f"base git grep {term}: {len(hits)} files")
        for hit in hits:
            print(" ", hit)
    for term in ("7.0.1", "Proof of (7.2)", "inhomogeneous configuration"):
        hits = grep(term, line_numbers=True, scope=("research",))
        print(f"base git grep exact {term!r}: {len(hits)} lines (inspect, not absence proof)")
        for hit in hits:
            print(" ", hit[:600])

def finite_checks():
    # Combinatorial witness only. No dynamics/geometry asserted.
    for k in (1, 10, 100, 10000):
        edges = [(0, 1, k), (1, 2, 2*k)]
        incident = sum(w * ((a == 0) + (b == 0)) for a, b, w in edges)
        total = sum(w for _, _, w in edges)
        largest = max(edges, key=lambda e: e[2])
        require(incident == k and total == 3*k and 0 not in largest[:2],
                "incidence witness")
    # Exact series law at the equality threshold and on both sides.
    for n in (2, 3, 10, 101):
        delta = Fraction(1, n)
        for w in (Fraction(1, 3), Fraction(7), Fraction(101, 19)):
            u0 = (1-delta)*w/delta
            for factor in (Fraction(1, 2), Fraction(1), Fraction(2)):
                u = factor*u0
                require(((1-delta)*w <= 1/(1/w + 1/u)) == (u >= u0),
                        "series threshold")
    # A scalar sequence only: block samples alone do not control a 2-step shift.
    n = 5
    seq = {i: (i+1 if i % n == 2 else 1) for i in range(102)}
    require(all(seq[m*n] == 1 for m in range(20)) and seq[97] == 98,
            "sparse scalar witness")
    print("Finite incidence, series-law and sparse-index checks passed; NOT native maps")

def get_pdf(identifier):
    url = "https://arxiv.org/pdf/" + identifier
    for attempt in range(3):
        try:
            req = Request(url, headers={"User-Agent": "loops-research-archive source verification (arXiv PDF)"})
            with urlopen(req, timeout=45) as response:
                data = response.read(30_000_001)
            require(len(data) <= 30_000_000 and data.startswith(b"%PDF-"), "not a bounded PDF")
            return data
        except (OSError, AssertionError) as exc:
            if attempt == 2:
                raise
            print("download retry", identifier, type(exc).__name__, flush=True)
            time.sleep(5*(attempt+1))

def source_checks():
    from pypdf import PdfReader
    for ident, sha, pages, anchors in SOURCES:
        data = get_pdf(ident)
        require(digest(data) == sha, f"{ident}: SHA-256 mismatch: {digest(data)}")
        print(ident, "sha256", digest(data))
        reader = PdfReader(io.BytesIO(data))
        require(len(reader.pages) == pages, f"{ident}: page count")
        for page, expected in anchors.items():
            # Remove whitespace to tolerate TeX/PDF extraction line breaks.
            extracted = re.sub(r"\s+", "", reader.pages[page-1].extract_text() or "").casefold()
            for marker in expected:
                require(re.sub(r"\s+", "", marker).casefold() in extracted,
                        f"{ident} p.{page}: missing {marker!r}")
            print(ident, "page", page, "anchors OK")

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--offline", action="store_true")
    args = ap.parse_args()
    inventory()
    finite_checks()
    if args.offline:
        print("OFFLINE: PDF checks NOT run")
    else:
        source_checks()
    print("OPEN: source/finite certificate only; no theorem or MLC proof verification")

if __name__ == "__main__":
    main()
