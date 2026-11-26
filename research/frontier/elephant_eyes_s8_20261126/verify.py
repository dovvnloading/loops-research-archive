"""Standalone source lock; not a proof of the E2 interpretation."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import time
import unicodedata
from urllib.request import Request, urlopen

from pypdf import PdfReader

URL = "https://arxiv.org/pdf/2601.21905v1"
EXPECTED = "5eb36430a51a3fb6a1c04db15713aebc86068118450893ba2042021e4a8db725"
ROOT = Path(__file__).resolve().parents[3]
PRIOR = "research/frontier/dudko_p43_satellite_moduli_20261125/NOTE.md"
MARKERS = {
    9: ["Description of the combinatorics", "E1.", "E2.",
        "is the only little Julia set contained in", "E3.", "Hubbard tree"],
    10: ["Translation domains", "Lemma 4.2", "Lemma 4.3", "Local weights"],
    15: ["Setting", "Translation Property", "pairwise disjoint translation domains"],
    16: ["Amplification Theorem", "Theorem 7.1", "Lemma 7.2", "maximal immersed annulus"],
    18: ["Local connectivity", "fundamental annuli", "non-central little Julia sets"],
    19: ["Step 0.", "Step 1.", "Step 2.", "Step 3."],
}


def normalized(s):
    # Spaces may be split inside words by embedded math fonts.
    return re.sub(r"\s+", "", unicodedata.normalize("NFKC", s)).casefold()


def download():
    last = None
    for i in range(3):
        try:
            req = Request(URL, headers={"User-Agent": "ElephantEyesSourceAudit/1.0"})
            with urlopen(req, timeout=60) as response:
                data = response.read()
            if not data.startswith(b"%PDF-"):
                raise ValueError("response is not PDF")
            return data
        except (OSError, ValueError) as exc:
            last = exc
            if i < 2:
                time.sleep(3 * (i + 1))
    raise RuntimeError("versioned PDF download failed") from last


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    data = download()
    digest = hashlib.sha256(data).hexdigest()
    if digest != EXPECTED:
        raise SystemExit(f"PDF SHA-256 mismatch: {digest}")
    reader = PdfReader(io.BytesIO(data))
    if len(reader.pages) != 20:
        raise SystemExit(f"unexpected page count: {len(reader.pages)}")
    for page, markers in MARKERS.items():
        page_text = normalized(reader.pages[page - 1].extract_text())
        for marker in markers:
            if normalized(marker) not in page_text:
                raise SystemExit(f"PDF page {page}: missing marker {marker!r}")
    prior = (ROOT / PRIOR).read_bytes()
    result = {
        "source": {"version": "2601.21905v1", "url": URL,
                   "sha256": digest, "bytes": len(data), "pages": len(reader.pages),
                   "page_markers": MARKERS},
        "context_only": {"path": PRIOR, "sha256": hashlib.sha256(prior).hexdigest()},
        "scope": "source bytes and page markers only; no dynamical verification",
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Verified versioned PDF SHA-256 {digest}; all page markers matched")


if __name__ == "__main__":
    main()
