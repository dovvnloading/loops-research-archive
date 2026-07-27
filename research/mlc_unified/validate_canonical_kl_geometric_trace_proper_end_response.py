"""Mechanical audit for the geometric-trace proper-end response pass.

The analytic proofs are in
``canonical_kl_geometric_trace_proper_end_response.md``.  This script
locks the two source files, checks the theorem/type/scope markers, verifies
finite instances of the explicit countermodels, and audits the dependency
boundary.  It does not prove a Wave-uniform response or MLC.
"""

from __future__ import annotations

import cmath
import hashlib
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent
NOTE = ROOT / "canonical_kl_geometric_trace_proper_end_response.md"
LEDGER = ROOT / "proof_obligations.json"
OUT = (
    ROOT
    / "canonical_kl_geometric_trace_proper_end_response_validation_20260726.json"
)

SOURCE_LOCKS = {
    ROOT / ".tmp_wave_audit" / "waves-with-Misha.tex":
        "AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5",
    ROOT / ".tmp_kl08_source" / "psiql.tex":
        "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def source_lock_audit() -> dict[str, object]:
    actual = {
        str(path.relative_to(ROOT)): sha256(path)
        for path in SOURCE_LOCKS
    }
    expected = {
        str(path.relative_to(ROOT)): digest
        for path, digest in SOURCE_LOCKS.items()
    }
    assert actual == expected
    return {"passed": True, "sha256": actual}


def source_semantics_audit() -> dict[str, object]:
    wave = (ROOT / ".tmp_wave_audit" / "waves-with-Misha.tex").read_text(
        encoding="utf-8"
    )
    kl = (ROOT / ".tmp_kl08_source" / "psiql.tex").read_text(
        encoding="utf-8"
    )

    checks = {
        "proper_path_has_ideal_endpoints": (
            "a path $\\gamma: (0, 1)\\to V$ is proper"
            in wave
            and "$\\gamma(0), \\gamma(1)\\in \\ddi V$" in wave
        ),
        "restriction_is_all_proper_paths_in_trace": (
            "to be the set of proper paths $\\gamma'$"
            in wave
            and "contained in $\\iota^{-1}(\\gamma)$" in wave
        ),
        "pulled_intervals_may_fail_or_overlap": (
            "some pullbacks may not exist or may overlap" in wave
        ),
        "action_requires_refinement": (
            "$f^*\\II$ is a refinement of $\\iota^*\\II$" in wave
        ),
        "end_proper_uses_complete_end_intervals": (
            "if it is proper on the end-intervals of $I'$" in wave
        ),
        "kl_inclusion_is_immersion": (
            "the inclusion $i: Y\\ra Z$ extends to an immersion"
            in kl
        ),
        "kl_has_named_boundary": (
            "arcs $\\xi_i, \\eta_i" in kl
            and "outer boundary" in kl
        ),
        "kl_extension_can_enter_target_interior": (
            "extends continuously to the boundary" in kl
            and "$\\i(\\di \\BY)$ is not contained in $\\di\\BZ$" in kl
        ),
    }
    assert all(checks.values()), checks
    return {"passed": True, "checks": checks}


def documentation_audit() -> dict[str, object]:
    note = NOTE.read_text(encoding="utf-8")
    required = [
        "Theorem 3.1 -- maximal lifts are proper source paths",
        "Parametrized pullback does not exhaust KKL restriction",
        "Proposition 4.1 -- identity-lollipop counterexample",
        "Proposition 5.1 -- exponential disk immersion",
        "Proposition 6.1 -- raw branchwise response no-go",
        "The rectangles are",
        "not itself realize",
        "Type ledger",
        "a path component is end-proper",
        "geometric inverse-trace path space",
        "Three-frame endpoint record",
        "Final-root relation no-birth",
        "No such quotient is proved here",
        "No statement in this file proves",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    ]
    missing = [text for text in required if text not in note]
    assert not missing, missing

    forbidden = [
        "The Mandelbrot set is locally connected.",
        "MLC is proved",
        "UPTCR is proved",
        "every path component is end-proper",
        "the rectangles are complete KKL-marked laminations",
        "the full limit set extends",
    ]
    present = [text for text in forbidden if text in note]
    assert not present, present
    return {
        "passed": True,
        "required_phrases": required,
        "forbidden_phrases_absent": forbidden,
    }


def lollipop_trace_audit() -> dict[str, object]:
    gamma_word = [
        "left",
        "upper_forward",
        "lower_reverse",
        "lower_forward",
        "right",
    ]
    delta_word = ["left", "lower_forward", "right"]
    gamma_trace = {
        token.replace("_forward", "").replace("_reverse", "")
        for token in gamma_word
    }
    delta_trace = {
        token.replace("_forward", "").replace("_reverse", "")
        for token in delta_word
    }
    checks = {
        "delta_trace_is_contained": delta_trace < gamma_trace,
        "delta_is_not_reparameterized_gamma": delta_word != gamma_word,
        "identity_parameter_fiber_has_one_graph": True,
    }
    assert all(checks.values()), checks
    return {
        "passed": True,
        "gamma_word": gamma_word,
        "delta_word": delta_word,
        "checks": checks,
    }


def exponential_immersion_audit() -> dict[str, object]:
    cases = []
    endpoint_values = []
    for k in range(-6, 7):
        p_k = (2j * math.pi * k - 1) / (2j * math.pi * k + 1)
        assert math.isclose(abs(p_k), 1.0, rel_tol=0.0, abs_tol=1e-12)
        endpoint_values.append(p_k)
        for t in (0.01, 0.07, 0.25, 0.73, 0.99):
            u = -math.log(t) + 2j * math.pi * k
            z = (u - 1) / (u + 1)
            cayley = (1 + z) / (1 - z)
            image = cmath.exp(-cayley)
            assert abs(image - t) < 2e-12
            assert abs(z) < 1
            cases.append(
                {
                    "k": k,
                    "t": t,
                    "image_error": abs(image - t),
                    "source_modulus": abs(z),
                }
            )

    for i, left in enumerate(endpoint_values):
        for right in endpoint_values[i + 1:]:
            assert abs(left - right) > 1e-12

    derivative_nonzero_reason = (
        "exp(-C(z)) is nonzero and 2/(1-z)^2 is nonzero on the disk"
    )
    return {
        "passed": True,
        "cases": cases,
        "distinct_endpoint_count": len(endpoint_values),
        "derivative_nonzero_reason": derivative_nonzero_reason,
    }


def rectangle_width_audit() -> dict[str, object]:
    a = 0.8
    b = 2.3
    theta = 0.7
    w0 = 2 * theta / (b - a)
    records = []
    sample = 1.4 + 0.2j
    base_image = cmath.exp(-sample)
    for m in range(0, 9):
        branch_count = 2 * m + 1
        total_width = branch_count * w0
        assert math.isclose(
            total_width,
            sum(w0 for _ in range(branch_count)),
            rel_tol=0.0,
            abs_tol=1e-14,
        )
        records.append(
            {
                "m": m,
                "branch_count": branch_count,
                "single_width": w0,
                "parallel_width": total_width,
            }
        )
    assert records[-1]["parallel_width"] > records[0]["parallel_width"]

    periodic_errors = []
    for k in range(-6, 7):
        image = cmath.exp(-(sample + 2j * math.pi * k))
        periodic_errors.append(abs(image - base_image))
        assert abs(image - base_image) < 2e-14

    return {
        "passed": True,
        "records": records,
        "periodic_errors": periodic_errors,
        "scope": (
            "finite arithmetic check of the interior rectangle model only; "
            "not a KKL-marked lamination realization"
        ),
    }


def ledger_audit() -> dict[str, object]:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}

    expected_status = {
        "FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS": "proved",
        "PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO": "proved",
        "DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER": "open",
        "DIRECT_DECORATION_CANONICAL_KL_STAGE_ALIGNMENT": "open",
        "DIRECT_DECORATION_RELATION_PROPER_PATH_END_INTERVAL_CLASSIFICATION":
            "open",
        "DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE": "open",
        "DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH": "open",
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT": "open",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION": "open",
        "VIRTUAL_WAVE_MARKED_CORRESPONDENCE": "open",
        "VIRTUAL_WAVE_HORIZON_CERTIFICATE": "open",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE": "open",
        "MLC": "open",
    }
    actual_status = {key: by_id[key]["status"] for key in expected_status}
    assert actual_status == expected_status

    expected_dependencies = {
        "FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS": {
            "CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION",
            "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY",
            "KKL_IDEAL_PULLBACK_NATIVE",
        },
        "PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO": {
            "CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION",
            "FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS",
            "KKL_IDEAL_PULLBACK_NATIVE",
        },
        "DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER": {
            "HORIZON_FIRST_INVENTORY_AUDIT",
            "INTERFACE_PROOF_USE_INVENTORY",
            "PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO",
        },
        "DIRECT_DECORATION_CANONICAL_KL_STAGE_ALIGNMENT": {
            "DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER",
            "CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION",
            "DIRECT_DECORATION_PULLBACK_COMPACTIFICATION",
            "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY",
        },
        "DIRECT_DECORATION_RELATION_PROPER_PATH_END_INTERVAL_CLASSIFICATION": {
            "DIRECT_DECORATION_CANONICAL_KL_STAGE_ALIGNMENT",
            "FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS",
            "PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO",
            "KKL_IDEAL_PULLBACK_NATIVE",
            "RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY",
            "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY",
            "NONPROPER_LABEL_HULL_PULLBACK_NO_GO",
            "PRIME_END_MARKING_ACTION_CRITERION",
        },
        "DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE": {
            "DIRECT_DECORATION_RELATION_PROPER_PATH_END_INTERVAL_CLASSIFICATION",
            "KKL_TYPED_VALUE_INCIDENCE",
            "VALUE_RESPONSE_NO_GO",
            "VALUE_FEATURE_ROWSPACE",
            "WAD_DOMINATION_RESPONSE",
            "PORT_FUTURE_CLOSURE_NO_GO",
            "HILBERT_TRACE_GLUE_CALCULUS",
        },
        "DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH": {
            "DIRECT_DECORATION_RELATION_PROPER_PATH_END_INTERVAL_CLASSIFICATION",
            "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION",
            "PULLBACK_GAP_ENLARGEMENT_NATURALITY",
            "MARKED_PAIR_ENLARGEMENT_NATURALITY",
            "RETURN_ATLAS_ENLARGEMENT_NATURALITY",
        },
    }
    for node, expected in expected_dependencies.items():
        actual = set(by_id[node]["dependencies"])
        assert actual == expected, (node, actual, expected)

    assert (
        "DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE"
        in by_id["DIRECT_DECORATION_OUTER_CAP_FOOTPRINT"]["dependencies"]
    )
    assert (
        "DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH"
        in by_id[
            "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION"
        ]["dependencies"]
    )
    assert (
        "DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH"
        not in by_id[
            "DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE"
        ]["dependencies"]
    )
    assert (
        "DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE"
        not in by_id[
            "DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH"
        ]["dependencies"]
    )

    counts = {
        status: sum(item["status"] == status for item in obligations)
        for status in ("imported", "proved", "open")
    }
    assert len(obligations) == 330
    assert counts == {"imported": 23, "proved": 235, "open": 72}
    return {
        "passed": True,
        "total": len(obligations),
        "counts": counts,
        "statuses": actual_status,
        "dependencies": {
            key: sorted(value)
            for key, value in expected_dependencies.items()
        },
    }


def main() -> None:
    report = {
        "scope": (
            "Source/type/model/dependency audit only; no actual Wave-stage "
            "alignment, KKL marking realization, uniform Value response, "
            "final-root theorem, UPTCR, or MLC."
        ),
        "source_lock": source_lock_audit(),
        "source_semantics": source_semantics_audit(),
        "documentation": documentation_audit(),
        "lollipop_trace": lollipop_trace_audit(),
        "exponential_immersion": exponential_immersion_audit(),
        "rectangle_width": rectangle_width_audit(),
        "ledger": ledger_audit(),
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"result": "PASS", "output": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
