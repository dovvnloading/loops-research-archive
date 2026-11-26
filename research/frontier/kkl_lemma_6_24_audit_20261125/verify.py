"""Download exact versions and generate a source-location/checksum certificate.

Not a proof checker. PDF page/line coordinates refer to pypdf extraction, not
printed TeX lines. No mathematical conclusion is inferred from token matches.
"""
import argparse
import hashlib
import io
import json
import re
import time
from pathlib import Path
from urllib.request import Request, urlopen

from pypdf import PdfReader

HERE = Path(__file__).resolve().parent
SOURCES = {
    "KKL": ("2606.27272v1", ["Theorem A", "Theorem C", "Theorem D", "Theorem 3.6",
        "Proposition 3.9", "Lemma 6.1", "Proposition 6.6", "Lemma 6.14",
        "Proposition 6.20", "Proposition 6.21", "Proposition 6.22", "Proposition 6.23",
        "Lemma 6.24", "(6.25)", "(6.26)", "(6.27)", "(6.28)", "(6.29)",
        "(6.30)", "Lemma 6.31", "(6.34)", "A.1. Ideal markings",
        "Lemma A.10", "Lemma A.11", "Proposition A.12", "Lemma A.13",
        "Proposition A.14", "Lemma A.15"]),
    "DL": ("2309.02107v3", ["Lemma 5.1", "Lemma 5.2"]),
}


def download(url):
    for attempt in range(3):
        try:
            with urlopen(Request(url, headers={"User-Agent": "KKL-source-audit/1.0"}), timeout=90) as r:
                return r.read()
        except OSError:
            if attempt == 2:
                raise
            time.sleep(3 * (attempt + 1))


def locations(pdf, needles):
    reader = PdfReader(io.BytesIO(pdf))
    hits = {needle: [] for needle in needles}
    for page_no, page in enumerate(reader.pages, 1):
        lines = (page.extract_text() or "").splitlines()
        # tolerate inter-word whitespace and ligatures introduced by extraction;
        # search one or two lines, preserving the first extracted line number.
        for i, line in enumerate(lines):
            window = re.sub(r"\s+", "", line + " " + (lines[i+1] if i+1 < len(lines) else ""))
            current = re.sub(r"\s+", "", line)
            for needle in needles:
                token = re.sub(r"\s+", "", needle)
                if token in current or (token in window and token not in re.sub(r"\s+", "", lines[i+1] if i+1 < len(lines) else "")):
                    hits[needle].append({"pdf_page": page_no, "extracted_line": i+1})
    return len(reader.pages), hits


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache", type=Path, help="optional external directory containing <id>.pdf files")
    parser.add_argument("--output", type=Path, default=HERE / "source_lock.json")
    args = parser.parse_args()
    result = {"schema": 1, "scope": "source identity and extraction only; not proof of Lemma 6.24", "sources": {}}
    for name, (version, needles) in SOURCES.items():
        url = "https://arxiv.org/pdf/" + version
        path = args.cache / (version + ".pdf") if args.cache else None
        raw = path.read_bytes() if path and path.is_file() else download(url)
        if not raw.startswith(b"%PDF-"):
            raise ValueError(f"{url}: not a PDF")
        pages, hits = locations(raw, needles)
        for required in (["Lemma 6.24", "Lemma A.13"] if name == "KKL" else ["Lemma 5.2"]):
            if not hits[required]:
                raise ValueError(f"{version}: missing {required}; inspect extraction")
        if name == "KKL" and pages != 73:
            raise ValueError(f"{version}: expected 73 PDF pages, got {pages}")
        result["sources"][name] = {"version": version, "pdf_url": url, "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(), "pdf_pages": pages, "locations": hits}
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
