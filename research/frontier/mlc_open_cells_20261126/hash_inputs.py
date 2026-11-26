"""Hash exact local inputs and fetch primary source bytes (no PDFs committed)."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent
ATLAS = HERE.parent / "mlc_coverage_atlas_20261126"
sources = json.loads((HERE / "sources.json").read_text())
urls = sorted({u for s in sources.values() for u in (s.get("url"), s.get("opened_url")) if u})

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def fetch(url):
    try:
        with urlopen(Request(url, headers={"User-Agent": "MLC-source-audit/1.0"}), timeout=20) as r:
            data = r.read(100_000_001)
            if len(data) > 100_000_000:
                raise ValueError("size limit")
            if "/pdf/" in url or url.endswith(".pdf"):
                if not data.startswith(b"%PDF"):
                    raise ValueError("not a PDF")
            return url, {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data), "final_url": r.url}
    except Exception as exc:
        return url, {"sha256": "UNVERIFIED", "reason": type(exc).__name__}

with ThreadPoolExecutor(max_workers=8) as pool:
    downloads = dict(pool.map(fetch, urls))
out = {"local": {p.name: digest(p) for p in (ATLAS/"atlas.json", ATLAS/"NOTE.md")},
       "downloads": downloads}
(HERE/"input_hashes.json").write_text(json.dumps(out, indent=2, sort_keys=True)+"\n")
