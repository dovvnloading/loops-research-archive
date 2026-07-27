"""Focused regressions for proof-ledger rendering and clause-map auditing.

These tests exercise metadata semantics only.  In particular, ``maps_to`` is a
one-way status-consistency relation and is deliberately not a proof-dependency
edge.
"""

from __future__ import annotations

from unittest.mock import patch

import audit_proof
from latex.generate_ledger_tex import ledger_id, render_group


EVIDENCE = "source_ledger.md#primary-sources"


def obligation(
    identifier: str,
    status: str,
    *,
    dependencies: list[str] | None = None,
    hypotheses: list[str] | None = None,
    clauses: list[dict] | None = None,
    role: str | None = None,
) -> dict:
    item = {
        "id": identifier,
        "statement": f"Fixture statement for {identifier}.",
        "status": status,
        "dependencies": dependencies or [],
        "evidence": EVIDENCE,
    }
    if hypotheses is not None:
        item["hypotheses"] = hypotheses
    if clauses is not None:
        item["clauses"] = clauses
    if role is not None:
        item["role"] = role
    return item


def ledger(*obligations: dict) -> dict:
    return {
        "schema_version": 3,
        "source_lock_date": "2026-07-26",
        "target": "MLC",
        "statuses": ["imported", "proved", "open"],
        "roles": [
            "gating",
            "documentary_source_record",
            "optional_alternative",
            "legacy_composite",
        ],
        "default_role": "gating",
        "obligations": list(obligations),
    }


def validate_fixture(data: dict) -> tuple[dict[str, dict], list[str]]:
    # Fixture evidence points into the real source ledger.  Suppress only the
    # unrelated package-wide Markdown-link scan so each regression has a
    # closed, local failure surface.
    with patch.object(audit_proof, "validate_markdown_links"):
        return audit_proof.validate(data)


def test_latex_renders_hypotheses_separately_from_dependencies() -> None:
    rendered = render_group(
        "proved",
        [
            obligation(
                "CONDITIONAL_THEOREM",
                "proved",
                dependencies=["PROOF_INPUT"],
                hypotheses=["OPEN_ASSUMPTION"],
            )
        ],
    )
    hypotheses_label = r"\emph{Formal hypotheses:}"
    dependencies_label = r"\emph{Proof dependencies:}"
    hypotheses_position = rendered.index(hypotheses_label)
    dependencies_position = rendered.index(dependencies_label)
    assumption_position = rendered.index(ledger_id("OPEN_ASSUMPTION"))
    proof_input_position = rendered.index(ledger_id("PROOF_INPUT"))

    assert hypotheses_position < assumption_position < dependencies_position
    assert dependencies_position < proof_input_position

    rendered_without_hypotheses = render_group(
        "open", [obligation("UNCONDITIONAL_GATE", "open")]
    )
    hypothesis_tail = rendered_without_hypotheses.split(
        hypotheses_label, maxsplit=1
    )[1]
    hypothesis_field = hypothesis_tail.split(dependencies_label, maxsplit=1)[0]
    assert r"\emph{none}" in hypothesis_field


def test_proved_or_imported_clause_cannot_map_to_open_target() -> None:
    for parent_status in ("proved", "imported"):
        parent_id = f"{parent_status.upper()}_PARENT"
        data = ledger(
            obligation("MLC", "open"),
            obligation("OPEN_TARGET", "open"),
            obligation(
                parent_id,
                parent_status,
                clauses=[
                    {
                        "id": "C-1",
                        "title": "Fixture clause",
                        "maps_to": ["OPEN_TARGET"],
                    }
                ],
            ),
        )
        _, errors = validate_fixture(data)
        expected = (
            f"{parent_id}/C-1: {parent_status} obligation maps to open "
            "obligation OPEN_TARGET"
        )
        assert expected in errors


def test_maps_to_is_not_a_dependency_or_cycle_edge() -> None:
    # If A -> B via maps_to were inserted into the dependency graph, the
    # genuine dependency B -> A would create a cycle.  It must not do so.
    data = ledger(
        obligation("MLC", "open"),
        obligation(
            "A",
            "open",
            clauses=[
                {
                    "id": "A-1",
                    "title": "Open clause",
                    "maps_to": ["B"],
                }
            ],
        ),
        obligation("B", "open", dependencies=["A"]),
    )
    by_id, errors = validate_fixture(data)
    assert errors == []
    assert audit_proof.transitive_open_dependencies("A", by_id) == []
    assert audit_proof.transitive_open_dependencies("B", by_id) == ["A"]


def test_documentary_source_record_cannot_license_mathematics() -> None:
    for relation in ("dependencies", "hypotheses"):
        keyword = {relation: ["PRINTED_ONLY"]}
        data = ledger(
            obligation("MLC", "open"),
            obligation(
                "PRINTED_ONLY",
                "imported",
                role="documentary_source_record",
            ),
            obligation("CONSUMER", "open", **keyword),
        )
        _, errors = validate_fixture(data)
        label = "dependency" if relation == "dependencies" else "hypothesis"
        assert (
            f"CONSUMER: {label} PRINTED_ONLY is a documentary source "
            "record and cannot license mathematics"
        ) in errors

    rendered = render_group(
        "imported",
        [
            obligation(
                "PRINTED_ONLY",
                "imported",
                role="documentary_source_record",
            )
        ],
    )
    assert r"\emph{Ledger role:}" in rendered
    assert "documentary source record" in rendered


def main() -> None:
    tests = [
        test_latex_renders_hypotheses_separately_from_dependencies,
        test_proved_or_imported_clause_cannot_map_to_open_target,
        test_maps_to_is_not_a_dependency_or_cycle_edge,
        test_documentary_source_record_cannot_license_mathematics,
    ]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    print("ledger tooling regressions: all passed")


if __name__ == "__main__":
    main()
