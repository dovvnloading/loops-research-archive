#!/usr/bin/env python3
"""Check the model-to-physical register and its public status mirrors offline."""

from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REGISTER = ROOT / "formalization" / "PHYSICAL_BRIDGES.md"
INDEX = REGISTER.with_name("physical_bridge_sources.tsv")
STANDING = {"formal", "written", "imported"}
ROLES = STANDING | {"open", "conditional", "model", "diagnostic"}
ID = re.compile(r"[A-Z][A-Z0-9-]*\Z")
LINK = re.compile(r"\]\(([^\s)]+)\)")
PROOF_NOTES = (
    REGISTER,
    REGISTER.with_name("TWO_SCALE_PHYSICAL_BRIDGES.md"),
    ROOT / "research/tip_family_theorem/PHYSICAL_BRIDGES.md",
)


def fail(message: str) -> None:
    raise ValueError(message)


def read_register() -> dict[str, tuple[str, list[str]]]:
    routes = {}
    for line in REGISTER.read_text().splitlines():
        if not line.startswith("|") or line.startswith(("| ID |", "|---")):
            continue
        cells = [s.strip() for s in line.strip("|").split("|")]
        if len(cells) != 5:
            fail(f"Malformed bridge row: {line}")
        key, inputs, status, claim, proof = cells
        if not ID.fullmatch(key) or key in routes or status not in ROLES:
            fail(f"Invalid or duplicate bridge: {key} ({status})")
        if not claim or not LINK.search(proof):
            fail(f"Missing claim or proof source: {key}")
        deps = [] if inputs == "—" else inputs.split(", ")
        if len(deps) != len(set(deps)):
            fail(f"Repeated premise for {key}")
        routes[key] = (status, deps)
    return routes


def check_dependencies(routes: dict[str, tuple[str, list[str]]]) -> None:
    """Check assumptions transitively, including across model-only rows.

    The register's input column denotes premises, not related evidence.
    A model status does not discharge an open premise inherited through it.
    Retain a shortest witness so a rejected promotion identifies the exact
    dependency path instead of merely reporting an unresolved ancestor.
    """
    checked, active = set(), set()
    unresolved: dict[str, tuple[str, ...] | None] = {}
    unfinished = {"conditional", "open", "diagnostic"}

    def visit(key: str) -> None:
        if key in active:
            fail(f"Circular bridge through {key}")
        if key in checked:
            return
        active.add(key)
        status, deps = routes[key]
        witnesses = []
        for dep in deps:
            if dep not in routes:
                fail(f"{key} refers to unknown premise {dep}")
            visit(dep)
            if unresolved[dep] is not None:
                witnesses.append((key, *unresolved[dep]))
        witness = min(witnesses, key=lambda path: (len(path), path)) if witnesses else None
        if status in STANDING and witness is not None:
            fail(f"{key} claims {status} while relying on "
                 f"{' -> '.join(witness)} ({routes[witness[-1]][0]})")
        unresolved[key] = (key,) if status in unfinished else witness
        checked.add(key)
        active.remove(key)

    for key in routes:
        visit(key)


def check_sources(routes: dict[str, tuple[str, list[str]]]) -> int:
    sources = set()
    for directory in (ROOT, ROOT / "formalization/weighted"):
        lean = set(directory.glob("*.lean"))
        lake = tomllib.loads((directory / "lakefile.toml").read_text())
        names = {p.stem for p in lean}
        registered = {entry["name"] for entry in lake["lean_lib"]} & set(lake["defaultTargets"])
        missing = names - registered
        if missing:
            fail(f"Missing Lake declarations or build targets in {directory.name}: {sorted(missing)}")
        sources.update(lean)
    sources.update((ROOT / "research").rglob("*.py"))
    sources.update((ROOT / "code").glob("exp*.py"))
    sources.add(ROOT / "code/mlc_common.py")
    expected = {p.relative_to(ROOT).as_posix() for p in sources}

    with INDEX.open() as f:
        reader = csv.DictReader(f, delimiter="\t")
        if reader.fieldnames != ["source", "routes"]:
            fail("Invalid source-index header")
        indexed = set()
        for row in reader:
            path = row["source"]
            assigned = row["routes"].split()
            if path in indexed or not assigned or set(assigned) - routes.keys():
                fail(f"Duplicate file, missing bridge or unknown bridge for {path}: {assigned}")
            indexed.add(path)
    if expected != indexed:
        fail(f"Unindexed sources: {sorted(expected - indexed)}. Stale sources: {sorted(indexed - expected)}")
    return len(indexed)


def check_links() -> None:
    for note in PROOF_NOTES:
        for target in LINK.findall(note.read_text()):
            path = target.split("#", 1)[0]
            if path and "://" not in path and not (note.parent / path).exists():
                fail(f"Broken evidence link in {note.name}: {target}")


def check_public_status(routes: dict[str, tuple[str, list[str]]]) -> None:
    data = json.loads((ROOT / "ledger.json").read_text())
    js = (ROOT / "ledger.js").read_text().removeprefix("window.MLC_LEDGER=").strip().removesuffix(";")
    if data["research_updates"] != json.loads(js)["research_updates"]:
        fail("The November JSON and JavaScript registers disagree")
    pages = {name: (ROOT / name).read_text() for name in ("README.md", "RESEARCH_MAP.md")}
    # The Vite app displays the source-backed ledger, not a second handwritten
    # HTML mirror. Regenerate and check the actual data consumed by Archive.tsx.
    subprocess.run([sys.executable, str(ROOT / "scripts/prepare_data.py")], cwd=ROOT, check=True)
    browser_ledger = json.loads((ROOT / "public/data/ledger.json").read_text())
    browser_updates = {row["id"]: row for row in browser_ledger["research_updates"]}
    if set(browser_updates) != {row["id"] for row in data["research_updates"]}:
        fail("Browser research update IDs disagree with source register")
    for row in data["research_updates"]:
        mirror = browser_updates[row["id"]]
        for field in ("statement", "classification", "status", "pr", "physical_bridges", "evidence", "deps"):
            if mirror.get(field) != row.get(field):
                fail(f"Browser ledger changed {field} for {row['id']}")
    updated = {87, 91, 92, 93, 94, 97, 100}
    matched = set()
    for row in data["research_updates"]:
        assignments = row.get("physical_bridges", [])
        if not assignments or set(assignments) - routes.keys():
            fail(f"Missing or unknown bridge for November update {row['id']}")
        pr = row["pr"]
        if pr not in updated:
            continue
        matched.add(pr)
        unresolved = any(routes[key][0] in {"open", "conditional"} for key in assignments)
        if unresolved and row["status"] != "open":
            fail(f"Physical result #{pr} has lost its conditional status")
        scope = row["statement"].split(": ", 1)[1]
        classification = row["classification"]
        for name, page in pages.items():
            needle = f"**{classification}** — {scope}"
            if needle not in page:
                fail(f"{name} lacks the current scope of #{pr}")
    if matched != updated:
        fail(f"Missing reviewed November updates: {sorted(updated - matched)}")


def main() -> None:
    routes = read_register()
    check_dependencies(routes)
    count = check_sources(routes)
    check_links()
    check_public_status(routes)
    print(f"OK: {len(routes)} bridge rows, {count} indexed sources, evidence paths and public statuses agree.")


if __name__ == "__main__":
    main()
