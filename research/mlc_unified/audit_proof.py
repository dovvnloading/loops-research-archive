"""Validate the machine-readable dependency ledger.

The script deliberately exits with status 0 when the ledger is internally valid even
if the mathematical target is open. It exits nonzero only for an inconsistent ledger,
such as a missing dependency, a cycle, or a target marked proved while an obligation is
open.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from urllib.parse import unquote, urlparse


LEDGER = Path(__file__).with_name("proof_obligations.json")
RESEARCH_DIR = LEDGER.parent


def load_ledger() -> dict:
    with LEDGER.open("r", encoding="utf-8") as stream:
        return json.load(stream)


def validate(data: dict) -> tuple[dict[str, dict], list[str]]:
    errors: list[str] = []
    allowed = set(data["statuses"])
    allowed_roles = set(
        data.get(
            "roles",
            [
                "gating",
                "documentary_source_record",
                "optional_alternative",
                "legacy_composite",
            ],
        )
    )
    default_role = data.get("default_role", "gating")
    if default_role not in allowed_roles:
        errors.append(f"unknown default role {default_role!r}")
    obligations = data["obligations"]
    by_id: dict[str, dict] = {}

    for item in obligations:
        item_id = item["id"]
        if item_id in by_id:
            errors.append(f"duplicate obligation id: {item_id}")
        by_id[item_id] = item
        if item["status"] not in allowed:
            errors.append(f"{item_id}: unknown status {item['status']!r}")
        if item.get("role", default_role) not in allowed_roles:
            errors.append(
                f"{item_id}: unknown role "
                f"{item.get('role', default_role)!r}"
            )

    for item in obligations:
        for relation in ("dependencies", "hypotheses"):
            for dependency in item.get(relation, []):
                if dependency not in by_id:
                    label = "dependency" if relation == "dependencies" else "hypothesis"
                    errors.append(
                        f"{item['id']}: missing {label} {dependency}"
                    )
                elif (
                    by_id[dependency].get("role", default_role)
                    == "documentary_source_record"
                ):
                    label = (
                        "dependency"
                        if relation == "dependencies"
                        else "hypothesis"
                    )
                    errors.append(
                        f"{item['id']}: {label} {dependency} is a "
                        "documentary source record and cannot license "
                        "mathematics"
                    )
        clause_ids: set[str] = set()
        for clause in item.get("clauses", []):
            clause_id = clause.get("id", "")
            if not clause_id:
                errors.append(f"{item['id']}: clause has no id")
            elif clause_id in clause_ids:
                errors.append(f"{item['id']}: duplicate clause id {clause_id}")
            clause_ids.add(clause_id)
            if not clause.get("title"):
                errors.append(f"{item['id']}/{clause_id}: clause has no title")
            for mapped_id in clause.get("maps_to", []):
                if mapped_id not in by_id:
                    errors.append(
                        f"{item['id']}/{clause_id}: missing mapped obligation "
                        f"{mapped_id}"
                    )
                elif (
                    item["status"] in {"proved", "imported"}
                    and by_id[mapped_id]["status"] == "open"
                ):
                    errors.append(
                        f"{item['id']}/{clause_id}: {item['status']} obligation "
                        f"maps to open obligation {mapped_id}"
                    )
        validate_evidence(item, errors)

    uptcr = by_id.get("UNIVERSAL_PROTECTED_TOWER_CLOSURE")
    if uptcr is not None:
        expected_uptcr_clauses = {f"UPTCR-{index}" for index in range(1, 7)}
        actual_uptcr_clauses = {
            clause.get("id", "") for clause in uptcr.get("clauses", [])
        }
        if actual_uptcr_clauses != expected_uptcr_clauses:
            errors.append(
                "UNIVERSAL_PROTECTED_TOWER_CLOSURE: clause set must be "
                "UPTCR-1 through UPTCR-6"
            )

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(item_id: str, path: list[str]) -> None:
        if item_id in visiting:
            errors.append("dependency cycle: " + " -> ".join(path + [item_id]))
            return
        if item_id in visited:
            return
        visiting.add(item_id)
        for dependency in by_id[item_id]["dependencies"]:
            if dependency in by_id:
                visit(dependency, path + [item_id])
        visiting.remove(item_id)
        visited.add(item_id)

    for item_id in by_id:
        visit(item_id, [])

    # A proved/imported item is unconditional with respect to its proof dependencies.
    # Open assumptions of a proved conditional implication belong in `hypotheses`,
    # not in `dependencies`.
    for item_id, item in by_id.items():
        if item["status"] not in {"proved", "imported"}:
            continue
        blockers = transitive_open_dependencies(item_id, by_id)
        if blockers:
            errors.append(
                f"{item_id} is marked {item['status']} with open proof dependencies: "
                + ", ".join(blockers)
            )

    target_id = data["target"]
    if target_id not in by_id:
        errors.append(f"missing target obligation: {target_id}")
    elif by_id[target_id]["status"] == "proved":
        blockers = transitive_open_dependencies(target_id, by_id)
        if blockers:
            errors.append(
                f"target {target_id} is marked proved with open dependencies: "
                + ", ".join(blockers)
            )

    validate_markdown_links(errors)
    return by_id, errors


def heading_slug(title: str) -> str:
    title = title.replace("`", "").strip().lower()
    title = re.sub(r"[^\w\s-]", "", title)
    title = re.sub(r"[\s-]+", "-", title)
    return title.strip("-")


def validate_evidence(item: dict, errors: list[str]) -> None:
    evidence = item.get("evidence", "")
    if not evidence:
        errors.append(f"{item['id']}: missing evidence link")
        return
    relative, separator, anchor = evidence.partition("#")
    evidence_file = LEDGER.parent / relative
    if not evidence_file.is_file():
        errors.append(f"{item['id']}: evidence file does not exist: {relative}")
        return
    if not separator:
        return
    headings = set()
    with evidence_file.open("r", encoding="utf-8") as stream:
        for line in stream:
            match = re.match(r"^#{1,6}\s+(.+?)\s*$", line)
            if match:
                headings.add(heading_slug(match.group(1)))
    if anchor not in headings:
        errors.append(
            f"{item['id']}: evidence anchor does not exist: {relative}#{anchor}"
        )


def markdown_headings(path: Path) -> set[str]:
    headings: set[str] = set()
    with path.open("r", encoding="utf-8") as stream:
        for line in stream:
            match = re.match(r"^#{1,6}\s+(.+?)\s*$", line)
            if match:
                headings.add(heading_slug(match.group(1)))
    return headings


def validate_markdown_links(errors: list[str]) -> None:
    """Check every relative Markdown link in the research package."""

    link_pattern = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
    heading_cache: dict[Path, set[str]] = {}

    for source in RESEARCH_DIR.glob("*.md"):
        content = source.read_text(encoding="utf-8")
        for raw_target in link_pattern.findall(content):
            target = raw_target.strip()
            parsed = urlparse(target)
            if parsed.scheme or target.startswith("#"):
                continue

            relative, separator, anchor = target.partition("#")
            target_path = (source.parent / unquote(relative)).resolve()
            if not target_path.is_file():
                errors.append(
                    f"{source.name}: broken relative Markdown link: {target}"
                )
                continue
            if separator and anchor:
                headings = heading_cache.setdefault(
                    target_path, markdown_headings(target_path)
                )
                if anchor not in headings:
                    errors.append(
                        f"{source.name}: missing Markdown anchor: {target}"
                    )


def transitive_open_dependencies(item_id: str, by_id: dict[str, dict]) -> list[str]:
    found: set[str] = set()
    walked: set[str] = set()

    def walk(current: str) -> None:
        if current in walked:
            return
        walked.add(current)
        for dependency in by_id[current]["dependencies"]:
            if by_id[dependency]["status"] == "open":
                found.add(dependency)
            walk(dependency)

    walk(item_id)
    return sorted(found)


def main() -> int:
    data = load_ledger()
    by_id, errors = validate(data)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1

    target_id = data["target"]
    target = by_id[target_id]
    blockers = transitive_open_dependencies(target_id, by_id)
    counts = {
        status: sum(item["status"] == status for item in by_id.values())
        for status in data["statuses"]
    }

    print(f"ledger: valid ({len(by_id)} obligations)")
    print(
        "statuses: "
        + ", ".join(f"{status}={count}" for status, count in counts.items())
    )
    print(f"target: {target_id} [{target['status']}]")
    if blockers:
        print("open blockers: " + ", ".join(blockers))
    else:
        print("open blockers: none")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
