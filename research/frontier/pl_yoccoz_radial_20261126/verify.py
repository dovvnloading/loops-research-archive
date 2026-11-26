"""Reproduce finite diagnostics; optionally fingerprint exact source PDFs."""
import argparse
import hashlib
import io
import json
import math
from pathlib import Path
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[3]
SUMMARY = ROOT / "research/frontier/cs_multiplier_locus_numerics_20261126/summary.json"
SUMMARY_SHA = "0adb0c726fd7146d9960e432a7b25d2f0532dbd8641cf01ee3e02843603a4bbf"
SOURCES = [
    ("CS", "https://arxiv.org/pdf/1509.07843v1", "71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f"),
    ("BLOT", "https://publications.hse.ru/pubs/share/direct/1052158150.pdf", "9d0aa40f94afbfb918fd26dbc96b14727b2a59b84b02da8ad93b6b528061adb0"),
    ("Levin", "https://www.ma.huji.ac.il/~levin/Levin1990_Article_BoundariesForMultipliersOfPeri", None),
    ("Hubbard", "https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf", None),
    ("Lyubich", "https://commack.math.stonybrook.edu/~mlyubich/papers/acta.pdf", None),
    ("Douady-Hubbard", "https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf", None),
    ("Dudko-Lyubich", "https://arxiv.org/pdf/2309.02107v3", None),
]


def log_d(m):
    a = max(1.0, math.pi / (2 * m))
    return math.log(2) + 2 * (a + math.log1p(math.exp(-2 * a)) - math.log(2)) - math.log(a)


def radial(e):
    b = e / (2 * math.pi)
    return math.hypot(1, b) + b


def blot(s):
    return 2 * math.pi / math.log(4 * (s + 1))


def fingerprints(path):
    from pypdf import PdfReader
    records = []
    mismatches = []
    for name, url, expected in SOURCES:
        record = dict(name=name, url=url, expected_sha256=expected)
        try:
            with urlopen(Request(url, headers={"User-Agent": "Mozilla/5.0"}), timeout=20) as response:
                data = response.read(80_000_001)
                record["resolved_url"] = response.geturl()
            if len(data) > 80_000_000 or not data.startswith(b"%PDF"):
                raise ValueError("not a PDF within size limit")
            digest = hashlib.sha256(data).hexdigest()
            record.update(sha256=digest, bytes=len(data), status="downloaded")
            if expected and digest != expected:
                mismatches.append(name)
                record["status"] = "HASH MISMATCH"
            try:
                record["pdf_pages"] = len(PdfReader(io.BytesIO(data)).pages)
            except Exception as exc:
                record["page_count_error"] = str(exc)
        except Exception as exc:
            record.update(status="UNAVAILABLE", error=str(exc))
        records.append(record)
    output = json.dumps(records, indent=2, sort_keys=True) + "\n"
    path.write_text(output, encoding="utf-8")
    print(output)
    if mismatches:
        raise AssertionError(f"Inherited PDF hash mismatches: {mismatches}")
    unavailable = [r["name"] for r in records if r["status"] == "UNAVAILABLE"]
    if unavailable:
        print("SOURCE HASH INCOMPLETE; unavailable:", ", ".join(unavailable))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sources", type=Path)
    args = parser.parse_args()
    data = SUMMARY.read_bytes()
    assert hashlib.sha256(data).hexdigest() == SUMMARY_SHA
    summary = json.loads(data)
    rows = [dict(zip(summary["columns"], row, strict=True))
            for row in summary["addresses"]["linear"]["rows"]]
    assert len(rows) == 5
    print("q period qL q-displacement E_req optimistic-q-envelope")
    expected_qL = [1.04327547788, 1.03475584798, 1.02825339612, 1.02379632826, 1.02057365715]
    period = 1
    for q, row, ql in zip(range(3, 8), rows, expected_qL, strict=True):
        period *= q
        # The summary p column is the parent period, not the rotation numerator.
        assert row["q"] == q and row["P"] == period and row["p"] == period // q
        assert abs(float(row["qL"]) - ql) < 1e-10
        x, y = map(float, row["max_z"])
        assert abs(q * math.hypot(x, y) - ql) < 2e-10 and y < 0
        delta = math.hypot(x - 1 / q, y)
        e_req = math.pi * q * delta**2 / -y
        assert e_req < math.log(2)
        optimistic = radial(math.log(2) if q == 3 else log_d(blot(q - 1)))
        print(f"{q} {period} {ql:.11f} {q * delta:.9f} {e_req:.9f} {optimistic:.9f}")
    floors = [log_d(blot(s)) / math.pi for s in (3, 10, 100, 10**6, 10**30, 10**100)]
    assert all(a <= b for a, b in zip(floors, floors[1:]))
    assert floors[-1] > 30
    print("coefficient floors:", floors)
    if args.sources:
        fingerprints(args.sources)


if __name__ == "__main__":
    main()
