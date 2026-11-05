#!/usr/bin/env python3
"""Check proof-ledger wiring and *plain Markdown* evidence paths.

Usage:
  python research/independent_audits/audit_ledger_evidence.py . [--strict]

Standard library only. Finding a file is not proof its mathematical argument
is correct. This deliberately does NOT rewrite evidence, assign proof status,
or accept fabricated placeholder documents as repairs.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re

EVIDENCE_FILE_RE = re.compile(r"^([A-Za-z0-9_./-]+\.md)(?:[#:].*)?$")


def audit(root: Path) -> dict:
    data = json.loads((root / "ledger.json").read_text(encoding="utf-8"))
    nodes = data["obligations"]
    count_status = Counter(n["status"] for n in nodes)
    index = {n["id"]: n for n in nodes}
    duplicates = [key for key, n in Counter(x["id"] for x in nodes).items() if n > 1]

    dangling, proved_with_open = [], []
    for node in nodes:
        for dep in node.get("deps", []):
            if dep not in index:
                dangling.append([node["id"], dep])
            elif node["status"] == "proved" and index[dep]["status"] == "open":
                proved_with_open.append([node["id"], dep])

    visiting, visited, cycles = set(), set(), []

    def visit(node_id: str, stack: list[str]) -> None:
        if node_id in visited:
            return
        if node_id in visiting:
            cycles.append(stack + [node_id])
            return
        visiting.add(node_id)
        for dep in index[node_id].get("deps", []):
            if dep in index:
                visit(dep, stack + [node_id])
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in index:
        visit(node_id, [])

    # This is a permissive basename test. For present files, exact paths,
    # anchors and actual proof content still require separate checking.
    markdown_names = {p.name for p in root.rglob("*.md") if ".git" not in p.parts}
    missing = defaultdict(list)
    recognized = 0
    for node in nodes:
        for piece in re.split(r"[;,\n]", str(node.get("evidence") or "")):
            piece = piece.strip()
            match = EVIDENCE_FILE_RE.fullmatch(piece)
            if not match:
                continue
            recognized += 1
            if Path(match.group(1)).name not in markdown_names:
                missing[match.group(1)].append({
                    "id": node["id"],
                    "status": node["status"],
                    "evidence": piece,
                })

    return {
        "ledger_entries": len(nodes),
        "declared_status_counts": data.get("counts"),
        "actual_status_counts": dict(count_status),
        "duplicate_ids": duplicates,
        "dangling_dependency_ids": dangling,
        "proved_directly_requiring_open": proved_with_open,
        "dependency_cycles": cycles,
        "recognized_markdown_evidence_references": recognized,
        "missing_evidence_files": dict(sorted(missing.items())),
        "missing_evidence_reference_count": sum(map(len, missing.values())),
        "missing_evidence_file_count": len(missing),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, help="Repository directory containing ledger.json")
    parser.add_argument("--strict", action="store_true", help="exit nonzero if problems exist")
    args = parser.parse_args()
    result = audit(args.repo)
    print(json.dumps(result, indent=2, sort_keys=True))
    failed = bool(
        result["duplicate_ids"] or result["dangling_dependency_ids"]
        or result["proved_directly_requiring_open"] or result["dependency_cycles"]
        or result["missing_evidence_reference_count"]
        or result["declared_status_counts"] != result["actual_status_counts"]
    )
    if failed and args.strict:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
