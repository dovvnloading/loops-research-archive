#!/usr/bin/env python3
"""Exact regression and source-byte lock; not a verifier of the CS proof."""
import argparse
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "arxiv-v1": ("https://arxiv.org/pdf/1509.07843v1", "71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f", 831082),
    "author-2022": ("https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf", "b1d6b0952247efc3cd7a6e0602dbb8246b43b9edf7b3c5d0da942cc822246c25", 851587),
}


def arithmetic():
    # c = log(2)/(2*pi) > 1/16, from log(2)>1/2 and pi<4.
    # PLY bottom point has imaginary magnitude 2*c*S > S/8.
    rows = {}
    for L in (3, 10, 100):
        for label, seq in (
            ("linear", [L+i for i in range(64)]),
            ("power_3_2", [L+math.isqrt(i**3) for i in range(1, 65)]),
            ("i_log2_i_squared_proxy", [L+i*i.bit_length()**2 for i in range(1, 65)]),
            ("power_2", [L+i*i for i in range(1, 65)]),
            ("cross_level_square", [L**(2**i) for i in range(10)]),
            ("product_threshold", [L, L*L-1]),
        ):
            P = 1
            prev_q = prev_s = None
            first = None
            for i, q in enumerate(seq, 1):
                assert q >= 3
                assert -1/F(1,q)+q == 0
                s = F(P,q)
                if prev_s is not None:
                    assert s == prev_s * F(prev_q**2,q)
                if label == "linear":
                    assert s == F(math.factorial(L+i-2), math.factorial(L-1)*q)
                    if i >= 2:
                        assert F(prev_q**2,q) >= 2
                if label == "cross_level_square":
                    assert s == F(1,L)
                if s >= 4 and first is None:
                    # The bottom point of the full PLY disk exceeds every r<1/2.
                    first = i
                # A rational point inside PLY, independent of transcendental c:
                # 1/q - i*P/(16*q). For P>=16 this lies outside the cone
                # if P>16; c>1/16 gives strictly more vertical room.
                if P > 16:
                    assert F(P,16*q) > F(1,q)
                prev_q, prev_s = q, s
                P *= q
            if label in ("linear", "power_3_2", "i_log2_i_squared_proxy", "power_2"):
                assert first is not None
            if label == "cross_level_square":
                assert first is None
            rows[f"{label}_L{L}"] = {"levels": len(seq),
                "first_S_ge_4": first, "last_S": str(s)}
        # Strictly weaker than the recurrence, with the same uniform bound scale:
        # q1=L, q2=L^2-1, then q_i=L*P_(i-1) for all i>=3.
        assert L*L-1 < L*L
        assert F(L,L*L-1) <= F(2,L)
        P = L*(L*L-1)
        for i in range(3,9):
            q = L*P
            assert F(P,q) == F(1,L)
            P *= q
    return {"scope": "finite exact Fraction/integer regression; infinite arguments in NOTE.md",
            "rows": rows}


def download():
    rows = {}
    for key, (url, expected, length) in SOURCES.items():
        try:
            with urlopen(Request(url, headers={"User-Agent":"CSGrowthAudit/1.0"}), timeout=25) as response:
                data = response.read(20_000_001)
                resolved = response.geturl()
            if len(data)>20_000_000 or not data.startswith(b"%PDF-") or b"%%EOF" not in data[-4096:]:
                raise ValueError("invalid PDF")
            sha = hashlib.sha256(data).hexdigest()
            rows[key] = {"url":url, "resolved_url":resolved, "bytes":len(data),
                         "sha256":sha, "matches_135":sha==expected and len(data)==length}
        except Exception as exc:
            rows[key] = {"url":url, "sha256":"UNVERIFIED", "error":type(exc).__name__}
    (ROOT/"sources.lock.json").write_text(json.dumps(rows,indent=2,sort_keys=True)+"\n")
    return rows


def check():
    rows = json.loads((ROOT/"sources.lock.json").read_text())
    assert set(rows)==set(SOURCES)
    for key, (url, expected, length) in SOURCES.items():
        row = rows[key]
        assert row["url"] == url
        if row["sha256"] == "UNVERIFIED":
            assert row["error"]
        else:
            assert len(row["sha256"]) == 64 and int(row["sha256"],16)>=0
            assert row["bytes"]>0 and row["resolved_url"].startswith("https://")
            assert row["matches_135"] == (row["sha256"]==expected and row["bytes"]==length)
    assert json.loads((ROOT/"arithmetic.json").read_text()) == arithmetic()
    print("Source retrieval states:", {k:v["sha256"] for k,v in rows.items()})
    print("Exact finite arithmetic and provenance schema pass (not a source-proof attestation).")


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lock", action="store_true")
    parser.add_argument("--check-lock", action="store_true")
    args=parser.parse_args()
    report=arithmetic()
    if args.lock:
        download()
        (ROOT/"arithmetic.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    if args.lock or args.check_lock:
        check()
    else:
        print(json.dumps(report,indent=2,sort_keys=True))
