#!/usr/bin/env python3
"""Verify the built application, exact-data boundary, and preserved archive URLs.

Uses the Python standard library. Run `npm run build` first. This is a packaging
and provenance check, not a mathematical proof or WebGL rendering test.
"""
from __future__ import annotations

from collections import Counter
from hashlib import sha256
from html.parser import HTMLParser
import http.server
import json
from pathlib import Path
import socketserver
import threading
from urllib.parse import urlsplit
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]
DIST = ROOT / "dist"


class ApplicationHTML(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.language = ""
        self.viewport = False
        self.root = False
        self.modules = []
        self.assets = []
        self.has_title = False

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "html":
            self.language = attrs.get("lang", "")
        if tag == "meta" and attrs.get("name") == "viewport":
            self.viewport = True
        if tag == "title":
            self.has_title = True
        if attrs.get("id") == "root":
            self.root = True
        if tag == "script":
            src = attrs.get("src", "")
            assert not urlsplit(src).netloc, "The app must not depend on a remote JS CDN."
            if attrs.get("type") == "module":
                self.modules.append(src)
        if tag in {"script", "link", "img"}:
            value = attrs.get("src") or attrs.get("href") or ""
            if value and not urlsplit(value).netloc and not value.startswith(("data:", "#")):
                self.assets.append(value.split("?", 1)[0].split("#", 1)[0])


def validate() -> list[str]:
    assert (DIST / "index.html").is_file(), "Run npm run build before checking the site."
    parser = ApplicationHTML()
    parser.feed((DIST / "index.html").read_text())
    assert parser.language == "en" and parser.viewport and parser.root and parser.has_title
    assert parser.modules, "Missing compiled module entry point."
    for path in parser.assets:
        assert not path.startswith("/"), f"Asset would break the project subpath: {path}"
        assert (DIST / path.removeprefix("./")).is_file(), f"Missing bundled asset: {path}"
    for obsolete in ("site-v2.js", "site-v2.css", "site.css", "support.js"):
        assert not (DIST / obsolete).exists(), f"Obsolete presentation runtime still published: {obsolete}"

    manifest = json.loads((DIST / "data/manifest.json").read_text())
    assert manifest["schema"] == "loops-research-data-v1"
    assert manifest["mlc_status"] == "MLC remains open"
    for item in manifest["datasets"]:
        payload = (DIST / "data" / item["file"]).read_bytes()
        assert sha256(payload).hexdigest() == item["sha256"], item["file"]
        assert sha256((ROOT / item["source_path"]).read_bytes()).hexdigest() == item["source_sha256"]

    source = json.loads((ROOT / "ledger.json").read_text())
    browser = json.loads((DIST / "data/ledger.json").read_text())
    all_rows = []
    for group in ("obligations", "research_updates"):
        assert len(source[group]) == len(browser[group])
        for original, enriched in zip(source[group], browser[group]):
            for field, value in original.items():
                assert enriched[field] == value, (original["id"], "source field changed", field)
            if enriched["evidence_path"]:
                assert (DIST / enriched["evidence_path"]).is_file(), enriched["id"]
                assert enriched["evidence_url"].startswith(manifest["source_repository"] + "/blob/")
            else:
                assert enriched["evidence_resolution"] == "unresolved"
                assert enriched["evidence_url"] is None
            all_rows.append(enriched)
    assert dict(Counter(row["status"] for row in browser["obligations"])) == source["counts"]
    actual_missing = {row["id"] for row in all_rows if row["evidence_resolution"] == "unresolved"}
    assert actual_missing == {row["id"] for row in manifest["unresolved_evidence"]}

    tip = json.loads((DIST / "data/tip.json").read_text())["parameter_bracket"]
    assert isinstance(tip["lower_numerator"], str), "Large integers must not cross the JS boundary as numbers."
    assert int(tip["upper_numerator"]) - int(tip["lower_numerator"]) == 1
    assert tip["denominator_power_of_two"] == 128

    catalog = json.loads((DIST / "data/catalog.json").read_text())["files"]
    for entry in catalog:
        payload = (DIST / entry["local_url"]).read_bytes()
        assert len(payload) == entry["bytes"], entry["path"]
        assert sha256(payload).hexdigest() == entry["sha256"], entry["path"]
    for name in ("classic.html", "dossier.html", "template.html"):
        assert "./#archive" in (DIST / name).read_text()
    for name in (".nojekyll", "favicon.svg", "404.html", "robots.txt", "sitemap.xml"):
        assert (DIST / name).is_file(), name
    health = json.loads((DIST / "health.json").read_text())
    assert health["application"] == "loops-fractal-research-engine"
    assert health["entry_sha256"] == sha256((DIST / "index.html").read_bytes()).hexdigest()
    assert health["data_sha256"] == manifest["input_sha256"]
    assert health["archive_files"] == len(catalog)
    print(f"PASS: compiled app; {len(all_rows)} unchanged ledger records; {len(catalog)} intact scholarly files; "
          f"{len(actual_missing)} existing missing-source records disclosed.")
    return ["/", "/health.json", "/data/manifest.json", "/data/ledger.json", "/data/tip.json", "/classic.html",
            "/favicon.svg", "/marked_width_mlc_manuscript.pdf", "/Period27Dyadic.lean", "/research/mlc_unified/source_ledger.md",
            *["/" + value.removeprefix("./") for value in parser.assets]]


class QuietHandler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(DIST), **kwargs)

    def log_message(self, *_args):
        pass


def smoke(paths: list[str]) -> None:
    class Server(socketserver.ThreadingTCPServer):
        allow_reuse_address = True
        daemon_threads = True

    with Server(("127.0.0.1", 0), QuietHandler) as server:
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            for path in dict.fromkeys(paths):
                with urlopen(f"http://127.0.0.1:{server.server_address[1]}{path}", timeout=10) as response:
                    assert response.status == 200 and response.read(64), path
                    while response.read(65536):
                        pass
            print(f"PASS: {len(set(paths))} local HTTP endpoints, including compiled assets, exact data, PDFs, and Lean.")
        finally:
            server.shutdown()
            thread.join(timeout=4)


if __name__ == "__main__":
    smoke(validate())
