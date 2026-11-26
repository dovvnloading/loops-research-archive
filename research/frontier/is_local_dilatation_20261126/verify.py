"""Offline check of reported radial maxima; optional source byte audit.

This is not a proof of a uniform QC comparison or a dynamics computation.
"""
import argparse
import hashlib
import json
import math
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[3]
SUMMARY = ROOT / "research/frontier/cs_multiplier_locus_numerics_20261126/summary.json"
SUMMARY_HASH = "0adb0c726fd7146d9960e432a7b25d2f0532dbd8641cf01ee3e02843603a4bbf"

SOURCES = {
    "IS": ("https://www.math.kyoto-u.ac.jp/~mitsu/pararenorm/ParabolicRenormalization.pdf", None),
    "Levin": ("https://www.ma.huji.ac.il/~levin/Levin1990_Article_BoundariesForMultipliersOfPeri", None),
    "CS_v1": ("https://arxiv.org/pdf/1509.07843v1", "71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f"),
    "Hubbard": ("https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf", "eb28f6376e63683007fee394dee1b4e217d1b8d4fbd43118c2fa7e7f1754bf5d"),
    "BLOT": ("https://publications.hse.ru/pubs/share/direct/1052158150.pdf", "9d0aa40f94afbfb918fd26dbc96b14727b2a59b84b02da8ad93b6b528061adb0"),
    "Lyubich": ("https://commack.math.stonybrook.edu/~mlyubich/papers/acta.pdf", "a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16"),
    "DL_v3": ("https://arxiv.org/pdf/2309.02107v3", "e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b"),
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check():
    raw = SUMMARY.read_bytes()
    assert sha(raw) == SUMMARY_HASH, "Unexpected #139 summary bytes"
    doc = json.loads(raw)
    columns = doc["columns"]
    rows = doc["addresses"]["linear"]["rows"]
    # Support the summary's documented column schema, not an inferred numerator.
    assert len(rows) == 5
    ql_expected = [1.04327547788, 1.03475584798, 1.02825339612,
                   1.02379632826, 1.02057365715]
    b = math.log(2) / (2 * math.pi)
    envelope = math.hypot(1, b) + b
    parent = 1
    out = []
    for i, row in enumerate(rows, 1):
        r = dict(zip(columns, row)) if isinstance(row, list) else row
        q = i + 2
        assert int(r["q"]) == q and int(r["p"]) == parent
        assert int(r["P"]) == parent * q
        parent *= q
        x, y = map(float, r["max_z"])
        assert y < 0
        ql = q * math.hypot(x, y)
        assert math.isclose(ql, float(r["qL"]), rel_tol=2e-10, abs_tol=2e-10)
        assert math.isclose(ql, ql_expected[i - 1], rel_tol=2e-10, abs_tol=2e-10)
        e_req = math.pi * q * ((x - 1 / q) ** 2 + y ** 2) / (-y)
        assert e_req < math.log(2)
        assert ql <= envelope
        out.append({"q": q, "parent": int(r["p"]), "q_abs_z": ql,
                    "E_required": e_req, "K_required_for_disk": e_req / math.log(2)})
    result = {"summary_sha256": sha(raw), "C_K1": envelope,
              "radial_max_samples": out, "status": "conditional numerical compatibility only"}
    print(json.dumps(result, indent=2), flush=True)
    return result


def fingerprint(item):
    name, (url, expected) = item
    record = {"url": url, "expected_sha256": expected}
    try:
        req = Request(url, headers={"User-Agent": "research-source-audit/1.0"})
        with urlopen(req, timeout=15) as response:
            final_url = response.geturl()
            data = response.read(25_000_001)
        if not data.startswith(b"%PDF-") or len(data) > 25_000_000:
            raise ValueError("not a PDF within byte limit")
    except (OSError, ValueError) as exc:
        record.update(status="UNVERIFIED", error=str(exc))
        return name, record
    actual = sha(data)
    record.update(sha256=actual, bytes=len(data), final_url=final_url,
                  status=("MATCH" if actual == expected else
                          "NEW_FINGERPRINT" if expected is None else "MISMATCH"))
    return name, record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()
    result = check()
    if args.manifest:
        with ThreadPoolExecutor(max_workers=5) as pool:
            sources = dict(pool.map(fingerprint, SOURCES.items()))
        manifest = {"numerical_check": result, "source_fingerprints": sources}
        output = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
        args.manifest.write_text(output, encoding="utf-8")
        print(output, flush=True)
        assert not any(r["status"] == "MISMATCH" for r in sources.values()), "Inherited source fingerprint mismatch"


if __name__ == "__main__":
    main()
