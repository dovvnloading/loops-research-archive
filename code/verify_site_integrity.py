#!/usr/bin/env python3
"""Offline website integrity checks and local HTTP smoke test.

Uses Python's standard library only. Intentionally does not pretend to
verify external GitHub Pages settings or public internet availability.
"""
from __future__ import annotations

import collections
import html.parser
import http.server
import json
import pathlib
import re
import socketserver
import threading
import urllib.request
import xml.etree.ElementTree as ET

ROOT = pathlib.Path(__file__).resolve().parents[1]
SITE_URL = "https://dovvnloading.github.io/loops-research-archive/"
EXPECTED = {"imported": 34, "proved": 316, "open": 115}
REQUIRED_ASSETS = (
    "index.html", "404.html", ".nojekyll", "site-v2.css",
    "site-v2.js", "ledger.json", "favicon.svg",
    "figs/m_overview.png", "figs/primitive_airplane.png",
    "figs/cascade_window.png", "figs/fig_rays_light.png",
    "figs/readme/two-scale-return.svg",
    "figs/readme/ledger-status.svg", "classic.html", "dossier.html",
    "marked_width_mlc_manuscript.pdf",
    "papers/paper1_canonical_localization/paper1_forced_noninjectivity_sheet_kernel_v1.1_visual.pdf",
    "papers/paper2_rooted_end_compactification/paper2_direct_decoration_rooted_end_compactification_v1.1_visual.pdf",
    "papers/paper3_protected_carriers/paper3_draft3_visual.pdf",
    "docs/DEPLOYMENT.md",
)

class SiteHTML(html.parser.HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids = []
        self.anchors = []
        self.assets = []
        self.images = []
        self.scripts = []
        self.title = []
        self.in_title = False
        self.language = ""
        self.main = 0
        self.h1 = 0
        self.viewport = False

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "html":
            self.language = attrs.get("lang", "")
        if tag == "title":
            self.in_title = True
        if tag == "meta" and attrs.get("name") == "viewport":
            self.viewport = True
        if tag == "main":
            self.main += 1
        if tag == "h1":
            self.h1 += 1
        if attrs.get("id"):
            self.ids.append(attrs["id"])
        if tag == "a" and attrs.get("href", "").startswith("#"):
            self.anchors.append(attrs["href"][1:])
        for attr in ("href", "src"):
            value = attrs.get(attr, "")
            if value.startswith("./"):
                self.assets.append(value.split("?", 1)[0].split("#", 1)[0])
        if tag == "img":
            self.images.append((attrs.get("src", ""), attrs.get("alt")))
        if tag == "script":
            self.scripts.append(attrs.get("src", ""))

    def handle_endtag(self, tag):
        if tag == "title":
            self.in_title = False

    def handle_data(self, text):
        if self.in_title:
            self.title.append(text)


def check_html(name: str) -> tuple[SiteHTML, str]:
    text = (ROOT / name).read_text(encoding="utf-8")
    parser = SiteHTML()
    parser.feed(text)
    assert parser.language == "en", (name, "missing language")
    assert parser.viewport, (name, "missing viewport")
    assert parser.main == 1 and parser.h1 == 1, (name, "main/H1 hierarchy")
    assert parser.title and "".join(parser.title).strip(), (name, "missing title")
    duplicates = [key for key, count in collections.Counter(parser.ids).items() if count > 1]
    assert not duplicates, (name, "duplicate IDs", duplicates)
    missing_anchors = sorted(set(parser.anchors).difference(parser.ids))
    assert not missing_anchors, (name, "broken anchor links", missing_anchors)
    missing_assets = sorted({
        p for p in parser.assets if not (ROOT / p.removeprefix("./")).exists()
    })
    assert not missing_assets, (name, "broken local links", missing_assets)
    for path, alt in parser.images:
        assert isinstance(alt, str) and alt.strip(), (name, "missing image alt", path)
    return parser, text


def validate() -> None:
    for asset in REQUIRED_ASSETS:
        assert (ROOT / asset).exists(), ("missing publishing asset", asset)
    main, html = check_html("index.html")
    check_html("404.html")
    assert "MLC remains open" in html
    assert "id=\"ledger\"" in html and "id=\"frontier\"" in html
    assert "site-v2.css" in html and "site-v2.js" in html
    assert "ReactDOM" not in html and "<x-dc>" not in html
    assert all(script == "./site-v2.js" for script in main.scripts), (
        "External JS must not be required for the new static homepage",
        main.scripts,
    )
    assert len(main.assets) > 10
    assert SITE_URL in html
    assert "2026-07-27" in html and "2026-11-05" in html

    entries = json.loads((ROOT / "ledger.json").read_text(encoding="utf-8"))
    obligations = entries["obligations"]
    counts = dict(collections.Counter(item["status"] for item in obligations))
    assert len(obligations) == 465 and counts == EXPECTED, (len(obligations), counts)
    for n in EXPECTED.values():
        assert str(n) in html

    for svg in ("favicon.svg", "figs/readme/ledger-status.svg", "figs/readme/two-scale-return.svg"):
        root = ET.parse(ROOT / svg).getroot()
        ns = "{http://www.w3.org/2000/svg}"
        assert root.tag == ns + "svg" and root.find(ns + "title") is not None, svg
        assert root.get("viewBox"), (svg, "missing viewBox")

    sitemap = ET.parse(ROOT / "sitemap.xml")
    locations = [e.text for e in sitemap.iter() if e.tag.endswith("loc")]
    assert SITE_URL in locations
    assert not (ROOT / "CNAME").exists(), "Custom CNAME requires explicit DNS and Pages settings"

    print(f"PASS: {len(obligations)} proof obligations; {len(main.assets)} local references; "
          f"{len(main.images)} accessible images; zero external JS")


class QuietHTTPHandler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(ROOT), **kwargs)

    def log_message(self, fmt, *args):
        pass


def smoke() -> None:
    class ReusableServer(socketserver.ThreadingTCPServer):
        allow_reuse_address = True
        daemon_threads = True

    with ReusableServer(("127.0.0.1", 0), QuietHTTPHandler) as server:
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        port = server.server_address[1]
        requested = (
            "/", "/site-v2.css", "/site-v2.js", "/ledger.json",
            "/favicon.svg", "/404.html", "/figs/m_overview.png",
            "/figs/readme/ledger-status.svg",
            "/papers/paper2_rooted_end_compactification/paper2_direct_decoration_rooted_end_compactification_v1.1_visual.pdf",
        )
        try:
            for path in requested:
                with urllib.request.urlopen(
                    f"http://127.0.0.1:{port}{path}", timeout=10
                ) as response:
                    assert response.status == 200, (path, response.status)
                    first = response.read(350)
                    assert first, ("empty asset", path)
                    if path == "/":
                        assert b"Marked Width" in first or b"doctype html" in first
            print(f"PASS: local HTTP smoke test ({len(requested)} endpoints, all 200)")
        finally:
            server.shutdown()
            thread.join(timeout=4)


if __name__ == "__main__":
    validate()
    smoke()
