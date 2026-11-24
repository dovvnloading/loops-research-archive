#!/usr/bin/env python3
"""Exact arithmetic record for H3_WIDTH.md; no topological proof is encoded.

The old parameter packets are untrusted inputs and are rechecked by the
audited outward-rational interval core.  Finite SC competitors and source
omitted boxes are recomputed.  The tail error is separately reconstructed
from its recurrence plus parameter motion; the former /3 precedence error
is explicitly rejected.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FINITE = ROOT / "research/independent_audits/tip_family_finite_p_wave_gain_20261116/verify.py"
RESULT = HERE / "width_results.json"

spec = importlib.util.spec_from_file_location("maximal_native_width_finite", FINITE)
if spec is None or spec.loader is None:
    raise RuntimeError("finite quantitative input verifier is unavailable")
finite = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = finite
spec.loader.exec_module(finite)
v, lim, gain = finite.v, finite.lim, finite.gain
I, ONE, TWO = v.Iv, v.ONE, v.TWO


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def interval_record(z) -> dict:
    return {"strict_decimal_endpoints": v.bracket_dec(z, 9),
            "decimal_denominator": 10**9}


def independent_tail_boxes(period: int, orbit: list) -> tuple[dict, dict]:
    """Parameter motion and dynamical errors are distinct contributions.

    Starting from E_0=0, E_(j+1)=4 E_j+88 gives the dynamic coefficient.
    The parameter shift contributes separately 30 times 15246.
    The first coordinate has exactly tau_p and needs only 15246.
    """
    require(type(period) is int and period >= 13, "tail starts at p=13")
    q = F(1, 4**period)
    accumulated = F(0)
    coefficients = {1: F(15246)}
    for j in range(1, 6):
        accumulated = 4*accumulated + 88
        if j in (2, 3, 5):
            coefficients[j] = 30*15246 + accumulated
    boxes = {j: -gain.pad(orbit[j], radius*q)
             for j, radius in coefficients.items()}
    return boxes, coefficients


def finite_record(row: dict) -> dict:
    p, parameter, orbit = v.checked_packet(row)
    report = finite.finite_case(p, parameter, orbit)
    xp, x2, x3, x4, x5 = (orbit[j*p] for j in (1, 2, 3, 4, 5))
    alpha = v.alpha_interval(p, parameter, orbit)
    angles = [gain.acos_positive(x)
              for x in (x4/xp, (-x2)/xp, (-x5)/xp, alpha/xp)]
    a, b, c, d = angles
    gap = (b-a)*(d-c)
    box_start = finite.source_missing_box_start(p, xp)
    missing_lower = gap.low()/F(16*(box_start+5)**4)
    require(box_start <= 7 and gap.low() > F(9, 100),
            "finite common omitted-energy premises changed")
    require(missing_lower > F(1, 5_000_000),
            "finite omitted box has insufficient positive energy")

    cuts, radius = finite.physical_positive_chart(p, orbit)
    h = finite.SEGMENTS[p][0] if p in finite.SEGMENTS else F(7, 5)
    m = (cuts[1]+cuts[2])/TWO
    r = (cuts[1]-cuts[2])/TWO
    gate_margin = (radius - I.point(m.abs_upper())
                   - r*finite.cosh_positive(I.point(h)))
    require(gate_margin.positive(), "parent whole-domain gate is not strict")

    # Independently retain the physical Rouché margin, not a parent proxy.
    R = F(1, 4) if p == 3 else F(1, 2**p)
    center, A, remainder = I.point(0), I.point(0), F(0)
    for j in range(1, p+1):
        remainder = (2*center.abs_upper()*remainder
                     +(A.abs_upper()*R*R+remainder)**2)
        A = ONE if j == 1 else TWO*center*A
        center = center.square()+parameter
    rouche_margin = -A.high()*R*R-center.abs_upper()-remainder-R
    require(rouche_margin > 0, "physical source Rouché gap vanished")

    report.update({
        "source_omitted_box_start": box_start,
        "source_angle_gap_product": interval_record(gap),
        "source_missing_energy_strict_lower": str(missing_lower),
        "source_missing_energy_uniform_floor": "1/5000000",
        "parent_entire_domain_gate_margin": interval_record(gate_margin),
        "source_rouche_strict_margin": interval_record(I.point(rouche_margin)),
    })
    return report


def tail_record() -> dict:
    _, model_orbit = v.isolate_model()
    boxes, coefficients = independent_tail_boxes(13, model_orbit)
    require(boxes == lim.model_positive_boxes(13, model_orbit),
            "upstream tail coefficients disagree with independent recurrence")
    q = F(1, 4**13)
    rejected = []
    for j in (2, 3, 5):
        wrong_radius = F(30*15246+88*(4**j-1), 3)*q
        wrong = -gain.pad(model_orbit[j], wrong_radius)
        needed_low = -model_orbit[j].high()-coefficients[j]*q
        needed_high = -model_orbit[j].low()+coefficients[j]*q
        require(wrong.low() > needed_low and wrong.high() < needed_high,
                "former coefficient error was not rejected")
        rejected.append(j)
    for p in (14, 15, 17, 64):
        smaller, _ = independent_tail_boxes(p, model_orbit)
        require(all(boxes[j].low() <= smaller[j].low()
                    and smaller[j].high() <= boxes[j].high()
                    for j in boxes), "tail boxes must be nested")
    lim.disk_cutoff_certificate(boxes)
    parent = lim.parent_semidisk_width(
        boxes[1], boxes[2], boxes[5], boxes[3], F(5, 2))
    child = gain.coarse_child_plane(
        boxes[1], boxes[2], boxes[5], boxes[3])
    require(child == gain.model_child_envelope(13, model_orbit),
            "coarse child must use the same complete physical error box")
    require(parent.low() > F(13, 20), "corrected parent floor failed")
    require(parent.low() < F(2, 3),
            "documented old stronger interval-floor failure changed")
    require(child.high() < F(63, 50), "corrected child cap failed")
    floor = F(2)/F(63, 50)-F(1)/F(13, 20)
    require(floor == F(40, 819) and floor > F(1, 100),
            "corrected reciprocal sign or threshold failed")
    return {
        "all_periods": "p>=13",
        "widest_box_period": 13,
        "error_coefficients": {str(j): str(c) for j, c in coefficients.items()},
        "old_divide_entire_sum_by_3_rejected_at_coordinates": rejected,
        "parent_explicit_competitor": interval_record(parent),
        "child_coarse_full_path_upper_expression": interval_record(child),
        "proved_parent_gt": "13/20",
        "proved_child_lt": "63/50",
        "proved_defect_gt": str(floor),
        "old_parent_gt_two_thirds_not_certified_by_corrected_interval": True,
    }


def certify() -> dict:
    source_path = gain.s.OLD
    source = json.loads(source_path.read_text())
    require([r["p"] for r in source["periods"]] == list(range(3, 13)),
            "all ten independently checked finite parameter packets required")
    rows = [finite_record(row) for row in source["periods"]]
    return {
        "schema": "maximal-native-wave-width/v1",
        "scope": (
            "Exact arithmetic premises of H3_WIDTH.md. Actual ideal classes, "
            "SC uniformization, complete A.1 foliations and all-path metric "
            "admissibility are the separately written analytic proof; the "
            "physical all-period chart remains an explicit upstream input."
        ),
        "parameter_manifest": str(source_path.relative_to(ROOT)),
        "parameter_manifest_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
        "finite": rows,
        "tail": tail_record(),
        "all_selected_periods_defect_strict_floor": "1/100",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true",
                        help="write the deterministic new width record")
    args = parser.parse_args()
    data = certify()
    if args.write:
        RESULT.write_text(json.dumps(data, indent=2, sort_keys=True)+"\n")
    elif RESULT.exists():
        require(json.loads(RESULT.read_text()) == data,
                "width_results.json differs from recomputed arithmetic")
    for row in data["finite"]:
        print(f'p={row["p"]}: P>{row["proved_parent_gt"]}, '
              f'C<{row["proved_child_lt"]}, D>{row["proved_D_gt"]}; '
              f'omitted box starts at s={row["source_omitted_box_start"]}')
    print("p>=13: corrected physical box gives P>13/20, C<63/50, D>40/819>1/100")
    print("PASS: arithmetic premises only; H3 analytic arguments are in H3_WIDTH.md")


if __name__ == "__main__":
    main()
