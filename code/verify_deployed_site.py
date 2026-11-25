#!/usr/bin/env python3
"""Check the actual public application and archive after a Pages deployment."""
from __future__ import annotations

from hashlib import sha256
from html.parser import HTMLParser
import json
import os
import time
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin, urlsplit
from urllib.request import Request, urlopen

BASE = os.environ.get("SITE_URL", "https://dovvnloading.github.io/loops-research-archive/").rstrip("/") + "/"
RESOURCES = {
    "": b'<html',
    "health.json": b'loops-fractal-research-engine',
    "data/manifest.json": b'loops-research-data-v1',
    "data/tip.json": b'EXACT_PERIOD9_MISIUREWICZ_TIP_CERTIFICATE_PASS',
    "data/ledger.json": b'"obligations"',
    "ledger.json": b'"obligations"',
    "classic.html": b'./#archive',
    "dossier.html": b'./#archive',
    "figs/readme/ledger-status.svg": b'<svg',
    "marked_width_mlc_manuscript.pdf": b'%PDF-',
    "Period27Dyadic.lean": None,
}


def check(path: str, expected: bytes | None = None) -> bytes:
    url = urljoin(BASE, path)
    request = Request(url, headers={"User-Agent": "loops-fractal-engine-smoke/1.0", "Cache-Control": "no-cache"})
    last_error = None
    for attempt in range(4):
        try:
            with urlopen(request, timeout=25) as response:
                assert response.status == 200, f"HTTP {response.status}: {url}"
                content = response.read(2_000_000)
            assert content, f"Empty response: {url}"
            assert expected is None or expected.lower() in content.lower(), f"Resource signature missing: {url}"
            print(f"PASS HTTP 200 {url}", flush=True)
            return content
        except (HTTPError, URLError, TimeoutError, AssertionError) as exc:
            last_error = exc
            if attempt < 3:
                time.sleep(5)
    raise AssertionError(f"Public site check failed: {url}: {last_error}")


class Assets(HTMLParser):
    def __init__(self):
        super().__init__()
        self.paths = []

    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        if tag in {"script", "link"}:
            path = values.get("src") or values.get("href") or ""
            if path and not urlsplit(path).netloc and not path.startswith(("data:", "#")):
                self.paths.append(path)


if __name__ == "__main__":
    responses = {path: check(path, signature) for path, signature in RESOURCES.items()}
    parser = Assets()
    parser.feed(responses[""].decode())
    assert parser.paths, "No bundled application assets found."
    for path in dict.fromkeys(parser.paths):
        check(path)
    health = json.loads(responses["health.json"])
    assert health["entry_sha256"] == sha256(responses[""]).hexdigest(), "Deployment contains inconsistent app entry and health manifest."
    manifest = json.loads(responses["data/manifest.json"])
    assert health["data_sha256"] == manifest["input_sha256"]
    tip = json.loads(responses["data/tip.json"])["parameter_bracket"]
    assert isinstance(tip["lower_numerator"], str), "Exact bracket was rounded by a JSON-number conversion."
    print(f"PASS: {len(RESOURCES) + len(set(parser.paths))} deployed endpoints; consistent app/data manifests; exact integer transport.")
