"""Machine checks for the independent Push-V re-verification.

These checks validate repository typing, dependency order, status boundaries,
and explicit arithmetic.  They do not prove the dynamical all-depth contact
closure, welding compactness, UPTCR, or MLC.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
LEDGER = HERE / "proof_obligations.json"
ASSESSMENT = HERE / "research_push_5_assessment_and_integration.md"
REEVALUATION = HERE / "push5_independent_reverification_and_extrapolation.md"
SOURCE_LEDGER = HERE / "source_ledger.md"
INTAKE = (
    HERE
    / "external_inputs"
    / "push5_independent_verification_20260725"
    / "push5_independent_verification.md"
)
OUT = HERE / "push5_independent_reverification_20260725.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> None:
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}
    statuses = {
        name: sum(item["status"] == name for item in obligations)
        for name in ("imported", "proved", "open")
    }
    assessment = ASSESSMENT.read_text(encoding="utf-8")
    reevaluation = REEVALUATION.read_text(encoding="utf-8")
    reevaluation_flat = " ".join(reevaluation.split())
    source_ledger = SOURCE_LEDGER.read_text(encoding="utf-8")

    open_ids = {
        "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE",
        "FINITE_LIVE_COMMON_REFINEMENT_FRONTIER",
        "DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS",
        "DIRECT_DECORATION_TRACE_COLLAR_REALIZATION",
        "END_PLUMBING_TRACE_RESPONSE_CONTROL",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    }

    welding_dependencies = set(
        by_id["DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS"]["dependencies"]
    )
    overlay = by_id["FINITE_TAME_CONTACT_OVERLAY_RESPONSE"]
    contact_statement = by_id[
        "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE"
    ]["statement"]

    exact = 0.0004
    cutoff = 1.0004
    absolute_error = abs(cutoff - exact)

    checks = {
        "normalized_intake_hash": sha256(INTAKE)
        == "9A5527099042C9F7F459091455A1D149DB59A8D72B56372A6D1F3737BFE7F7C3",
        "ledger_counts_current_330_23_235_72": (
            len(obligations) == 330
            and statuses == {"imported": 23, "proved": 235, "open": 72}
        ),
        "only_legal_statuses": set(ledger["statuses"])
        == {"imported", "proved", "open"}
        and all(item["status"] in ledger["statuses"] for item in obligations),
        "forbidden_patch_status_absent": all(
            item["status"] != "proved_with_explicit_upstream_dependency"
            for item in obligations
        ),
        "nonexistent_bottcher_id_absent": "BOTTCHER_TRACE_COLLAR_ATLAS"
        not in by_id,
        "all_required_gates_open": all(by_id[item]["status"] == "open" for item in open_ids),
        "finite_overlay_proved_narrowly": overlay["status"] == "proved"
        and "REGULAR_INTERFACE_FIBER_PRODUCT_RESPONSE" in overlay["dependencies"]
        and "does not construct" in overlay["statement"].lower(),
        "welding_depends_on_contact_closure": (
            "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE"
            in welding_dependencies
        ),
        "contact_state_retains_marked_incidence": (
            "current-separator interface state" in contact_statement
            and "multi-branch incidence" in contact_statement
            and "endpoint and prime-end markings" in contact_statement
            and "missing footprint" in contact_statement
            and "complete end-interval" in contact_statement
            and "marked interface atom" in contact_statement
        ),
        "cap_bound_has_addition": (
            "M\\frac{2}{e^{\\lambda_1R}-1}\n +\\frac{2B^2}"
            in assessment
        ),
        "binary_macrobranch_relation_recorded": (
            "components of \\(\\operatorname{dom}(g^n)\\)" in source_ledger
            and "not an unrelated branch family" in source_ledger
        ),
        "relative_error_denominators_correct": (
            abs(absolute_error - 1.0) < 1e-15
            and abs(absolute_error / exact - 2500.0) < 1e-12
            and abs(
                absolute_error / cutoff - 0.9996001599360256
            )
            < 1e-15
            and "relative-to-exact error" in reevaluation
        ),
        "wot_not_accepted_as_welding_algebra": (
            "WOT_WELDING_ALGEBRA_NO_GO" in reevaluation
            and "naive weak-operator compactness does not meet"
            in reevaluation_flat
        ),
    }

    all_checks = all(checks.values())
    payload = {
        "artifact": "PUSH5_INDEPENDENT_REVERIFICATION",
        "date": "2026-07-25",
        "status": (
            "PUSH5_INDEPENDENT_REVERIFICATION_VALID"
            if all_checks
            else "FAILED"
        ),
        "checks": checks,
        "all_checks": all_checks,
        "ledger": {
            "total": len(obligations),
            **statuses,
            "target": ledger["target"],
            "target_status": by_id[ledger["target"]]["status"],
        },
        "scope": (
            "repository, arithmetic, and finite-compiler checks only; "
            "all-depth dynamical contact closure, welding compactness, "
            "UPTCR, and MLC remain open"
        ),
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(payload["status"])
    print(json.dumps(payload, indent=2))

    if not all_checks:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
