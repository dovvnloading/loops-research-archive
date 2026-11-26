#!/usr/bin/env python3
"""Source-byte provenance and finite arithmetic regression; not a proof of MLC."""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "CS-arxiv": "https://arxiv.org/pdf/1509.07843v1",
    "CS-author": "https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf",
    "CS-version": "https://arxiv.org/abs/1509.07843",
    "TUN": "https://www.math.stonybrook.edu/preprints/ims98-13b.pdf",
    "DL26": "https://arxiv.org/pdf/2309.02107v3",
    "DL-neutral": "https://arxiv.org/pdf/2210.09280",
    "DL-neutral-II": "https://arxiv.org/pdf/2509.23031v2",
    "EE": "https://arxiv.org/pdf/2601.21905v1",
    "KKL": "https://arxiv.org/pdf/2606.27272v1",
    "C2010": "https://www.ma.imperial.ac.uk/~dcheragh/Research/2010-1.pdf",
    "Levin": "https://arxiv.org/pdf/0710.4406v4",
    "survey": "https://arxiv.org/html/2512.24171v1",
    "C-list": "https://www.ma.imperial.ac.uk/~dcheragh/research.html",
    "DL-publisher": "https://pmihes.centre-mersenne.org/articles/10.5802/pmihes.2/",
}
BEGIN = "<!-- BEGIN SOURCE LOCK -->"
END = "<!-- END SOURCE LOCK -->"


def retrieve(item):
    name, url = item
    try:
        request = urllib.request.Request(url, headers={"User-Agent": "ResidualSatelliteSourceAudit/1.0"})
        with urllib.request.urlopen(request, timeout=25) as response:
            data = response.read(60_000_001)
            final = response.geturl()
        if len(data) > 60_000_000:
            raise ValueError("source exceeds size cap")
        pdf = "/pdf/" in url or url.endswith(".pdf")
        if pdf and not (data.startswith(b"%PDF-") and b"%%EOF" in data[-4096:]):
            raise ValueError("not a complete PDF")
        if not pdf and b"<html" not in data.lower()[:8192]:
            raise ValueError("not HTML")
        return name, {"url": url, "resolved_url": final, "bytes": len(data),
                      "sha256": hashlib.sha256(data).hexdigest()}
    except Exception as exc:
        return name, {"url": url, "sha256": "UNVERIFIED", "error": type(exc).__name__}


def table(rows):
    lines = ["| Source | Input URL | SHA256 |", "|---|---|---|"]
    for name, url in SOURCES.items():
        lines.append(f"| {name} | <{url}> | {rows[name]['sha256']} |")
    return "\n".join(lines)


def check_arithmetic():
    from fractions import Fraction
    for start in range(3, 129):
        for q in range(start, start + 128):
            x = Fraction(1, q)
            assert 1 / x == q
            assert -1 / x + q == 0
            assert q + 1 < q * q
    print("Finite regression passes; universal inequalities are proved in NOTE.md.")


def lock():
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
        rows = dict(pool.map(retrieve, SOURCES.items()))
    (ROOT / "sources.lock.json").write_text(json.dumps(rows, indent=2) + "\n")
    path = ROOT / "NOTE.md"
    note = path.read_text()
    before, rest = note.split(BEGIN, 1)
    _, after = rest.split(END, 1)
    path.write_text(before + BEGIN + "\n\n" + table(rows) + "\n\n" + END + after)


def check_lock():
    rows = json.loads((ROOT / "sources.lock.json").read_text())
    assert set(rows) == set(SOURCES)
    for name, url in SOURCES.items():
        row = rows[name]
        assert row["url"] == url
        if row["sha256"] == "UNVERIFIED":
            assert row["error"]
        else:
            assert re.fullmatch(r"[0-9a-f]{64}", row["sha256"])
            assert row["bytes"] > 0 and row["resolved_url"].startswith("https://")
    note = (ROOT / "NOTE.md").read_text()
    assert note.split(BEGIN, 1)[1].split(END, 1)[0].strip() == table(rows)
    missing = [name for name, row in rows.items() if row["sha256"] == "UNVERIFIED"]
    print("Source lock schema and NOTE table match; unavailable bytes:", missing)
    # A green test is not an attestation that every download or theorem is verified.


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lock", action="store_true")
    parser.add_argument("--check-lock", action="store_true")
    args = parser.parse_args()
    check_arithmetic()
    if args.lock:
        lock()
    if args.lock or args.check_lock:
        check_lock()
