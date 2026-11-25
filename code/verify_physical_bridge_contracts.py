#!/usr/bin/env python3
"""Check the source-to-contract index. Look up a ledger row or a named theorem.

This verifies documentary coverage. Read the linked proofs and run their own
certificates separately to assess the mathematical assertions.
"""

import argparse
import json
import os
import re
import shlex
from collections import defaultdict
from pathlib import Path
from urllib.parse import unquote, urlsplit

from verify_lean_frontier_sync import ROOT, assumptions, canonical_order

INDEX = ROOT / "formalization/physical_bridge_index.json"
CROSSWALK = Path("formalization/LEDGER_EVIDENCE_CROSSWALK.md")
# Public, named theorem/lemma declarations in the syntax used in this archive.
# Supports same-line attributes. Private helper lemmas have no separate entry.
DECLARATION = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:protected|noncomputable)\s+)*"
    r"(?:theorem|lemma)\s+([^\s:(]+)", re.MULTILINE
)


def lean_code(text):
    """Mask strings and comments while preserving line numbers for source checks."""
    pieces = []
    start = 0
    token = re.compile(r'/-|--[^\n]*|"(?:\\.|[^"\\])*"', re.DOTALL)
    delimiter = re.compile(r"/-|-/")
    while match := token.search(text, start):
        pieces.append(text[start:match.start()])
        start = match.end()
        if match[0] == "/-":
            depth = 1
            while depth:
                marker = delimiter.search(text, start)
                if marker is None:
                    raise ValueError("unterminated Lean block comment")
                depth += 1 if marker[0] == "/-" else -1
                start = marker.end()
        pieces.append(" " + "\n" * text.count("\n", match.start(), start))
    pieces.append(text[start:])
    return "".join(pieces)


def declaration_names(text):
    """Index public theorem names using the shared Lean comment/string masking."""
    return set(DECLARATION.findall(lean_code(text)))


def source_files():
    for directory, children, names in os.walk(ROOT):
        children[:] = [name for name in children if not name.startswith(".")]
        for name in names:
            yield (Path(directory) / name).relative_to(ROOT).as_posix()


def require_coverage(label, expected, actual):
    missing = sorted(expected - actual)
    stale = sorted(actual - expected)
    if missing or stale:
        raise ValueError(f"{label}: missing {missing}; stale {stale}")


def unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate index key {key}")
        result[key] = value
    return result


def evidence_filenames(row):
    return dict.fromkeys(re.findall(r"[\w.-]+\.md\b", row["evidence"]))


def guide_sources(index, records, files):
    crosswalk = (ROOT / CROSSWALK).read_text(encoding="utf-8")
    guides = {ROOT / CROSSWALK: crosswalk}
    markdown = {Path(path).name for path in files if path.endswith(".md")}
    for row in records:
        if any(name not in markdown for name in evidence_filenames(row)):
            if crosswalk.count(f'<a id="{row["id"]}"></a>') != 1:
                raise ValueError(f"{row['id']}: missing evidence needs a crosswalk entry")
    for key, row in index.items():
        path, anchor = row["guide"].split("#")
        doc = (ROOT / path).resolve()
        if doc not in guides:
            guides[doc] = doc.read_text(encoding="utf-8")
        if anchor != key or guides[doc].count(f'<a id="{anchor}"></a>') != 1:
            raise ValueError(f"{key}: expected a unique explicit anchor in {path}")
    for doc, content in guides.items():
        for href in re.findall(r"\]\(([^\s)]+)\)", content):
            url = urlsplit(href)
            if url.scheme or url.netloc:
                continue
            target = (doc.parent / unquote(url.path)).resolve() if url.path else doc
            if not target.is_relative_to(ROOT) or not target.is_file():
                raise ValueError(f"{doc.name}: missing local source {href}")
            if url.fragment and target in guides:
                anchor = f'<a id="{unquote(url.fragment)}"></a>'
                if guides[target].count(anchor) != 1:
                    raise ValueError(f"{doc.name}: unresolved contract anchor {href}")


def check(index, records, updates, files):
    declarations = defaultdict(set)
    guide_sources(index, records, files)
    scripts, targets, supplements = set(), set(), set()
    by_id = {row["id"]: row for row in records}
    for key, row in index.items():
        for path, names in row.get("theorems", {}).items():
            if not names or len(names) != len(set(names)):
                raise ValueError(f"{key}: empty or duplicate declaration in {path}")
            declarations[path].update(names)
        for path in row.get("checks", []):
            if path not in files:
                raise ValueError(f"{key}: missing source {path}")
            scripts.add(path)
        for claim in row.get("obligations", []):
            if claim not in by_id:
                raise ValueError(f"{key}: unknown ledger obligation {claim}")
            targets.add(claim)
        supplements.update(row.get("research_updates", []))

    require_coverage("Lean sources", {p for p in files if p.endswith(".lean")}, set(declarations))
    for path, names in declarations.items():
        source = (ROOT / path).read_text(encoding="utf-8")
        require_coverage(path, declaration_names(source), names)

    patterns = (
        "research/native_wave_transfer/regenerate*.py", "research/tip_family_theorem/verify_chain.py",
        "research/mlc_unified/validate*.py", "research/mlc_unified/audit*.py", "code/exp*.py",
    )
    expected_scripts = {
        path for path in files
        if any(Path(path).match(pattern) for pattern in patterns)
        or (path.startswith("research/independent_audits/") and Path(path).match("verify*.py"))
        or (path.startswith("research/mlc_research_push_") and path.endswith(".py")
            and not Path(path).name.startswith("test_"))
    }
    if expected_scripts - scripts:
        raise ValueError(f"unmapped certificate sources: {sorted(expected_scripts - scripts)}")
    required_targets = {
        row["id"] for row in records if row["status"] == "open" or assumptions(row)
    }
    if required_targets - targets:
        raise ValueError(f"unmapped open/conditional claims: {sorted(required_targets - targets)}")
    require_coverage("November entries", {r["id"] for r in updates}, supplements)
    # November hypotheses are prose; only deps contain graph edges.
    canonical_order([dict(row, hyp="none") for row in updates])
    for row in updates:
        if row["evidence"] not in files or row["verifier"] not in scripts:
            raise ValueError(f"{row['id']}: missing evidence file or unregistered verifier")
    print(f"Coverage: {len(index)} contracts, {len(declarations)} Lean files, "
          f"{sum(map(len, declarations.values()))} named theorems/lemmas, "
          f"{len(scripts)} check sources, {len(required_targets)} open/conditional ledger rows, "
          f"{len(supplements)} November records.")


def inspect_claim(claim_id, records, updates, index, files):
    by_id = {row["id"]: row for row in records}
    for row in updates:
        if row["id"] == claim_id:
            print(f"{claim_id} [November status: {row['status']}]\n{row['statement']}")
            print("Classification as recorded:", row["classification"])
            print("Source hypotheses:", row["hyp"])
            print("Dependencies:", ", ".join(row["deps"]) or "none recorded")
            print("Written evidence:", row["evidence"])
            print("Verifier:", row["verifier"])
            for entry in index.values():
                if claim_id in entry.get("research_updates", []):
                    print("Contract with current scope:", entry["guide"])
            return
    if claim_id not in by_id:
        raise ValueError(f"unknown ledger obligation {claim_id}")
    row = by_id[claim_id]
    print(f"{claim_id} [ledger status: {row['status']}]\n{row['statement']}")
    print("Ordinary dependencies:", ", ".join(row["deps"]) or "none recorded")
    print("Conditional hypotheses:", ", ".join(assumptions(row)) or "none recorded")
    if row["clauses"]:
        print("Source clauses:", row["clauses"])
    print("Evidence as recorded:", row["evidence"])
    # A basename match locates candidate files, never authenticates an anchor.
    for name in evidence_filenames(row):
        candidates = sorted(p for p in files if Path(p).name == name)
        print(f"  {name} (file lookup):", ", ".join(candidates) or "missing from checkout")
        if not candidates:
            print(f"  Alternative evidence and remaining scope: {CROSSWALK}#{claim_id}")
    contracts = [e["guide"] for e in index.values() if claim_id in e.get("obligations", [])]
    print("Contract references:", ", ".join(contracts or [index["ledger"]["guide"]]))
    seen = set()
    pending = [*row["deps"], *assumptions(row)]
    while pending:
        node = pending.pop()
        if node not in seen:
            seen.add(node)
            pending.extend(by_id[node]["deps"])
            pending.extend(assumptions(by_id[node]))
    open_nodes = sorted(k for k in seen if by_id[k]["status"] == "open")
    print("Transitive open prerequisites (both edge types):", ", ".join(open_nodes) or "none recorded")


def inspect_theorem(name, index):
    matches = defaultdict(list)
    for entry in index.values():
        for path, theorems in entry.get("theorems", {}).items():
            if name in theorems:
                matches[path].append(entry["guide"])
    if not matches:
        raise ValueError(f"unknown public theorem/lemma {name}")
    for path, references in matches.items():
        print(f"{path} — {name}")
        source = Path(path)
        target = shlex.quote(source.stem)
        if source.parent == Path("formalization/weighted"):
            command = f"(cd formalization/weighted && lake build {target})"
        elif source.parent == Path("."):
            command = f"lake build {target}"
        else:
            command = f"lake build && lake env lean {shlex.quote(path)}"
        print("Kernel check from the repository root:", command)
        for ref in references:
            print(f"  {ref}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    query = parser.add_mutually_exclusive_group()
    query.add_argument("--theorem", metavar="NAME", help="locate a theorem and its contract references")
    query.add_argument("--claim", metavar="ID", help="inspect an exact obligation and its evidence")
    args = parser.parse_args()
    index = json.loads(INDEX.read_text(encoding="utf-8"), object_pairs_hook=unique_keys)
    ledger = json.loads((ROOT / "ledger.json").read_text(encoding="utf-8"))
    records, updates = ledger["obligations"], ledger["research_updates"]
    canonical_order(records)  # Detect duplicate IDs, cycles and missing targets across both edge types.
    files = set(source_files())
    check(index, records, updates, files)
    if args.claim:
        inspect_claim(args.claim, records, updates, index, files)
    elif args.theorem:
        inspect_theorem(args.theorem, index)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        raise SystemExit(str(error))

