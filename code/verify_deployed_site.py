#!/usr/bin/env python3
"""Verify deployed GitHub Pages endpoints (not just local HTTP serving).

No third-party packages, tokens, or GitHub Pages settings API required.
Exit nonzero unless the actual public site serves the published artifacts.
"""
from __future__ import annotations

import time
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin
from urllib.request import Request, urlopen

BASE = "https://dovvnloading.github.io/loops-research-archive/"
# A sentinel string is checked only where an informative signature is stable.
RESOURCES = {
    "": b"<html",
    "site-v2.css": None,
    "site-v2.js": None,
    "ledger.json": b'"obligations"',
    "dossier.html": b"<html",
    "classic.html": b"<html",
    "figs/readme/two-scale-return.svg": b"<svg",
    "figs/readme/ledger-status.svg": b"<svg",
    "figs/m_overview.png": b"\x89PNG\r\n\x1a\n",
    "marked_width_mlc_manuscript.pdf": b"%PDF-",
    "papers/paper2_rooted_end_compactification/"
    "paper2_direct_decoration_rooted_end_compactification_v1.1_visual.pdf": b"%PDF-",
}


def check(path: str, expected: bytes | None) -> None:
    url = urljoin(BASE, path)
    request = Request(url, headers={"User-Agent": "loops-research-archive-pages-smoke/1.0"})
    last_error: Exception | None = None
    for attempt in range(4):
        try:
            with urlopen(request, timeout=20) as response:
                if response.status != 200:
                    raise AssertionError(f"HTTP {response.status}: {url}")
                beginning = response.read(32768)
            if not beginning:
                raise AssertionError(f"Empty response: {url}")
            if expected is not None and expected.lower() not in beginning.lower():
                raise AssertionError(f"Missing expected resource signature: {url}")
            print(f"PASS HTTP 200 {url}", flush=True)
            return
        except (HTTPError, URLError, TimeoutError, AssertionError) as exc:
            last_error = exc
            if attempt != 3:
                time.sleep(5)
    raise AssertionError(f"Public Pages check failed: {url}: {last_error}")


if __name__ == "__main__":
    for resource, signature in RESOURCES.items():
        check(resource, signature)
    print(f"PASS: {len(RESOURCES)} public Pages endpoints are accessible")
