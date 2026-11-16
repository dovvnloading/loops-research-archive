#!/usr/bin/env python3
"""Outward-dyadic primitive Chebyshev tips near the real period-3 parabolic root.

This is a negative v1 *marking* certificate. It proves three finite primitive
degree-two returns, but deliberately does not emit a made-up three-phase
PhysicalExample, ideal marking, Wave width, or contact angular width.
No floating point, sampled complex points, or adaptive numerical oracle is
used for any inequality. Reuses only the unchanged native 2^-256 Box type.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

from regenerate import (
    Box, SCALE, HERE, REPO, bracket, canonical, ensure, git_blob, load, sha256,
)

INPUT = HERE / "physical_examples/near_parabolic_primitive_tips.json"
MANIFEST = HERE / "experiment_manifests/near_parabolic_primitive_tips.json"
CODE_PATH = "research/native_wave_transfer/regenerate_near_parabolic.py"

# Frozen *pre-existing* sources and outputs. This experiment never writes them.
SOURCE_LOCKS = {
    "research/native_wave_transfer/SPECIFICATION.md": "4288c3c7a9680fffd8d094b8f25d51c6cd5df648",
    "research/native_wave_transfer/regenerate.py": "0dfa4f4c8d5321a7b9fdd74c9c1218228087e0f2",
    "research/native_wave_transfer/experiment_manifests/tip_pr68.json": "39233f576e7de78cf707b4d616177d0313b98b25",
    "research/native_wave_transfer/experiment_manifests/primitive4_tip12.json": "abcc01ad0b5ab0b59cd46e9d080ce44141603392",
    "research/native_wave_transfer/experiment_manifests/satellite2_period4_obstruction.json": "063132e808fe209473663e28cd12b7eb876c27ed",
    "research/native_wave_transfer/experiment_manifests/satellite2_misiurewicz_tip_refusal.json": "cc78196b8ad25a6ea24912131d6c4f0887317a89",
    "research/native_wave_transfer/experiment_manifests/satellite2_misiurewicz_v2.json": "6bd66c3dac16cace7f52c84a3f848684240c564a",
}

ZERO, ONE, TWO = Box.rational(0), Box.rational(1), Box.rational(2)
EXPECTED_PERIODS = (24, 27, 30)
EXPECTED_RADII = (Q(1, 1024), Q(3, 4096), Q(5, 8192))
EXPECTED_MARGIN_RANGES = (
    (Q(1, 625), Q(17, 10000)),
    (Q(9, 10000), Q(1, 1000)),
    (Q(3, 5000), Q(7, 10000)),
)
EXPECTED_PHASE_RANGES = (
    (Q(23, 10000), Q(1, 400)),
    (Q(9, 5000), Q(19, 10000)),
    (Q(7, 5000), Q(3, 2000)),
)


def mul(a: Box, b: Box) -> Box:
    """Outward product in the unchanged native 2^-256 interval lattice."""
    terms = (a.low * b.low, a.low * b.high,
             a.high * b.low, a.high * b.high)
    return Box(min(terms) // SCALE, (max(terms) + SCALE - 1) // SCALE)


def abs_up(a: Box) -> int:
    return max(abs(a.low), abs(a.high))


def abs_low(a: Box) -> int:
    return a.low if a.low > 0 else (-a.high if a.high < 0 else 0)


def point_scaled(value: int) -> Box:
    return Box(value, value)


def parameter_derivative(c: Box, n: int) -> Box:
    x, derivative = ZERO, ZERO
    for _ in range(n):
        derivative = mul(mul(TWO, x), derivative) + ONE
        x = x.square() + c
    return derivative


def rouche_margin(c: Box, p: int, source_radius: Q,
                  target_radius: Q) -> tuple[Q, Q]:
    """Strict whole-circle Rouché for f^p(z)=d+A*z²+E(z).

    T_{j+1} = 2|d_j| T_j + (|A_j|*rho² + T_j)².
    All bound operations use enclosing dyadic integers, not a floating
    approximation. Compare with A*z² uniformly for |w| <= target_radius.
    """
    rho, target = Box.rational(source_radius), Box.rational(target_radius)
    r2 = mul(rho, rho)
    d, a, tail = ZERO, ZERO, ZERO
    for j in range(1, p + 1):
        error = mul(point_scaled(abs_up(a)), r2) + tail
        tail = mul(mul(TWO, point_scaled(abs_up(d))), tail) + error.square()
        a = ONE if j == 1 else mul(mul(TWO, d), a)
        d = d.square() + c
    low = (mul(point_scaled(abs_low(a)), r2).low
           - abs_up(d) - tail.high - target.high)
    high = (mul(point_scaled(abs_up(a)), r2).high
            - abs_low(d) - tail.high - target.low)
    ensure(abs_up(d) < target.low, "critical value outside target disk")
    return Q(low, SCALE), Q(high, SCALE)


def complex_phase_bounds(x: list[Box], p: int, radius: Q) -> tuple[Q, Q]:
    """Complex disks f^j(D(0,R)) centered at exact x_j, j=0,...,p-1.

    Because the center follows the *same* parameter c, no spurious c
    uncertainty is added to the radius recurrence. The enclosing Box for
    each exact center is used when testing separation and exclusion of zero.
    """
    r = Box.rational(radius).high
    disks = [(x[0], r)]
    noncentral_gap = SCALE * 10
    for j in range(1, p):
        center = x[j - 1]
        r = (2 * abs_up(center) * r + r * r + SCALE - 1) // SCALE
        disks.append((x[j], r))
        noncentral_gap = min(noncentral_gap, abs_low(x[j]) - r)
    closest = SCALE * 10
    for i in range(p):
        for j in range(i + 1, p):
            ai, ri = disks[i]
            aj, rj = disks[j]
            distance_lower = max(ai.low - aj.high, aj.low - ai.high, 0)
            closest = min(closest, distance_lower - ri - rj)
    ensure(closest > 0, "primitive whole-complex phase disks overlap")
    ensure(noncentral_gap > 0, "intermediate image may contain a critical point")
    return Q(closest, SCALE), Q(noncentral_gap, SCALE)


def multiplier_at(a: Box, c: Box, p: int) -> Box:
    z, derivative = a, ONE
    for _ in range(p):
        derivative = mul(mul(TWO, z), derivative)
        z = z.square() + c
    return derivative


def certify_member(row: dict, p: int, radius: Q,
                   margins: tuple[Q, Q],
                   phase_bounds: tuple[Q, Q]) -> dict:
    ensure(row["p"] == p and row["denominator_power_of_two"] == 160,
           "physical return period / parameter precision changed")
    den = 1 << row["denominator_power_of_two"]
    lo, hi = int(row["lower_numerator"]), int(row["upper_numerator"])
    ensure(hi == lo + 1, "parameter root bracket not adjacent dyadics")
    c_lo, c_hi = Q(lo, den), Q(hi, den)
    ensure(-Q(7, 4) < c_lo < c_hi < -Q(17, 10),
           "not on the near-parabolic chaotic-side branch")
    left = bracket(Box.rational(c_lo), 2 * p)
    right = bracket(Box.rational(c_hi), 2 * p)
    ensure((left[2*p] + left[p]).low > 0 and
           (right[2*p] + right[p]).high < 0,
           "no strict opposite tip-equation root signs")
    c = Box(Box.rational(c_lo).low, Box.rational(c_hi).high)
    derivative = parameter_derivative(c, 2*p) + parameter_derivative(c, p)
    ensure(derivative.high < 0, "tip-equation root not locally unique")

    ensure(Q(row["outer_radius"]) == radius and
           tuple(map(Q, row["rouche_margin_between"])) == margins and
           tuple(map(Q, row["phase_separation_between"])) == phase_bounds,
           "domain or claimed exact margins changed")
    x = bracket(c, 2*p)
    ensure(x[p].high < 0 < x[2*p].low and
           (x[2*p] + x[p]).low <= 0 <= (x[2*p] + x[p]).high,
           "wrong Chebyshev-tip critical itinerary")
    ensure(abs_up(x[p]) < Box.rational(radius).low,
           "inner invariant interval not contained in target")
    mlo, mhi = rouche_margin(c, p, radius, radius)
    ensure(margins[0] < mlo <= mhi < margins[1],
           "Rouché margin strict enclosure failed")
    # A second whole-circle Rouché comparison puts *all* inverse fibers
    # of the full target disk inside D(0, 7R/8): an explicit round subcollar.
    inner_margin, _ = rouche_margin(c, p, Q(7, 8)*radius, radius)
    ensure(inner_margin > 0, "no certified round subcollar")

    phase_min, critical_exclusion = complex_phase_bounds(x, p, radius)
    ensure(phase_bounds[0] < phase_min < phase_bounds[1],
           "complex phase separation strict enclosure failed")
    ensure(critical_exclusion > 0,
           "f^p could have extra real turning points on the inner interval")
    # At the exact root: G(0)=-a, G(+/-a)=a by evenness, G(a)=a.
    # Rouché provides exactly two preimages for every target point.
    # The real inner interval has both and is G-invariant, so its full
    # inverse in V has no additional complex components/attachments.
    a = -x[p]
    terminal = multiplier_at(a, c, p)
    ensure(abs_low(terminal) > 3 and
           abs_up(terminal) < 5*SCALE,
           "tip terminal fixed point not certified repelling")

    return {
        "physical_return": p,
        "parameter_bracket": {
            "denominator_power_of_two": 160,
            "lower_numerator": str(lo),
            "upper_numerator": str(hi),
            "width": "2^-160",
            "unique_real_tip_root_by_strict_negative_derivative": True,
            "opposite_endpoint_signs": True,
        },
        "parabolic_side": "strictly greater than -7/4",
        "tip_orbit": "0 -> -a -> a -> a, a=-x_p>0",
        "global_degree": str(2**p),
        "restricted_degree": 2,
        "target_radius": str(radius),
        "central_rouche_margin_strictly_between":
            [str(margins[0]), str(margins[1])],
        "primitive_phase_disk_gap_strictly_between":
            [str(phase_bounds[0]), str(phase_bounds[1])],
        "all_noncentral_phase_disks_avoid_critical_point": True,
        "complex_phases_pairwise_disjoint": True,
        "round_subcollar": {
            "inverse_of_full_target_inside_radius": "7*R/8",
            "certificate": "Rouche margin at source 7R/8, target R is strictly positive",
            "conformal_modulus_lower_bound": "log(8/7)/(2*pi)",
            "not_a_measured_KKL_attachment_collar_h": True,
        },
        "real_inner_geometry": {
            "one_invariant_Chebyshev_tip_interval": "K=[-a,a]",
            "G_of_K_equals_K": True,
            "G_inverse_of_K_in_central_V_equals_K": True,
            "number_of_inner_G_phase_intervals": 1,
            "new_inverse_tree_attachments": 0,
            "repelling_terminal_G_fixed_point": True,
        },
    }


def primitive_baselines() -> dict:
    """Read immutable old physical results instead of recomputing/copying them."""
    result = {}
    for label, name in (("p3", "tip_pr68"), ("p4", "primitive4_tip12")):
        obj = load(HERE / ("experiment_manifests/" + name + ".json"))
        out = obj["outputs"]
        ensure(out["ideal_boundary"]["target_atom_count"] == 10
               and out["ideal_boundary"]["covering_source_atom_count"] == 20
               and len(out["attachment_census"]["components"]) == 1
               and out["sheet_paths"]["counts"] == [2, 1]
               and out["wave"]["harmonic_series_equality"] is True,
               "prior physical regression projection changed")
        result[label] = {
            "target_atoms": out["ideal_boundary"]["target_atom_count"],
            "source_atoms": out["ideal_boundary"]["covering_source_atom_count"],
            "attachments": len(out["attachment_census"]["components"]),
            "filtered_restrictions_cross_avoid": out["sheet_paths"]["counts"],
            "parent_width": out["wave"]["target_width"],
            "each_child_width": out["wave"]["each_child_and_pushed_width"],
            "harmonic_equality": out["wave"]["harmonic_series_equality"],
        }
    return result


def certify(fixture: dict) -> dict:
    ensure(fixture["format"] == "native-wave-near-parabolic-primitive-tip-refusal/v1"
           and fixture["family"] == "z^2+c"
           and fixture["parabolic_parameter"] == "-7/4"
           and fixture["side"] == "c > -7/4 (chaotic/intermittency side)"
           and fixture["tip_equation"] == "x(2*p)+x(p)=0; x(p)<0<x(2*p)",
           "wrong near-parabolic source contract")
    ensure(fixture["record_compatibility"] == "refused"
           and fixture["first_incompatible_field"] ==
               "MarkedHubbardTree.small_julia_intervals"
           and fixture["purpose"] ==
               "negative v1 marking compatibility certificate, NOT a PhysicalExample"
           and "marking" not in fixture and "source_contract" not in fixture
           and "operations" not in fixture and "wave" not in fixture,
           "forged v1 marking field")
    ensure(fixture["sequence_rule"].startswith("p=3*n;")
           and len(fixture["members"]) == 3
           and len(fixture["not_asserted"]) == 7,
           "unsupported infinite-sequence claim or missing research limits")
    members = []
    for i, row in enumerate(fixture["members"]):
        members.append(certify_member(row, EXPECTED_PERIODS[i],
                        EXPECTED_RADII[i], EXPECTED_MARGIN_RANGES[i],
                        EXPECTED_PHASE_RANGES[i]))
    br = [row["parameter_bracket"] for row in members]
    # Exact rational monotonic approach from c24 to c30; this finite
    # ordering is emphatically *not* an all-p convergence theorem.
    ensure(int(br[2]["upper_numerator"]) < int(br[1]["lower_numerator"])
           and int(br[1]["upper_numerator"]) < int(br[0]["lower_numerator"]),
           "parameters not approaching -7/4 in the selected three members")
    return {
        "finite_selected_members": members,
        "finite_parameter_order": "-7/4 < c30 < c27 < c24",
        "infinite_accumulation_status": "not certified by three finite cases",
        "first_incompatible_v1_field": "MarkedHubbardTree.small_julia_intervals",
        "v1_physical_examples_emitted": False,
        "distinct_operations": {
            "covering_f_star": "map from quadratic-like return; no v1 atom table",
            "immersion_iota_star": "physical inclusion pullback; no v1 atom table",
        },
        "new_attachment_electrode_arc": None,
        "canonical_KKL_attachment_h": None,
        "canonical_KKL_attachment_ell": None,
        "annular_contact_resistance_test": "inapplicable: no v1 attachment electrode or certified angular width",
        "unasserted": fixture["not_asserted"],
        "prior_primitive_comparison": primitive_baselines(),
    }


def make_manifest(fixture: dict) -> dict:
    for path, expected_blob in SOURCE_LOCKS.items():
        ensure(git_blob(REPO / path) == expected_blob,
               "pre-existing source/output blob drift: " + path)
    outputs = certify(fixture)
    return {
        "format": "native-wave-near-parabolic-refusal-manifest/v1",
        "schema_version": 1,
        "experiment_id": fixture["id"],
        "inputs": {
            "example_sha256": sha256(INPUT),
            "unchanged_source_and_output_git_blobs": SOURCE_LOCKS,
            "literature": [
                "Lyubich, Dynamics of quadratic polynomials I-II, §2 (primitive copies and parabolic roots)",
                "Hunt-Gallas-Grebogi-Kocak-Yorke, Bifurcation rigidity, Physica D 129 (1999), periodic windows",
                "KKL arXiv:2606.27272v1 §§2.1,2.5,6.1 and Appendix A",
            ],
        },
        "code": {"path": CODE_PATH, "sha256": sha256(Path(__file__))},
        "outputs": outputs,
        "outputs_sha256": hashlib.sha256(canonical(outputs)).hexdigest(),
        "proof_status": {
            "certified": [
                "three locally unique exact dyadic tip-equation roots",
                "whole-complex-circle Rouché degree-two domains and shrinking positive bounds",
                "three complete pairwise-disjoint f^j(V) phase enclosures",
                "one Chebyshev real inner interval, two central inverse branches, no new attachments",
                "strict terminal repelling multiplier and a round annular subcollar lower bound",
                "first unchanged v1 three-phase marking field semantically incompatible",
            ],
            "analytic_inputs": [
                "standard backward-orbit density/straightening identifying the full inner Julia with the real invariant interval",
                "the KKL three-phase primitive marking and its prime-end interpretation",
            ],
            "numerical_only": [
                "decimal parameter displays in RESULTS.md; no decimal is used by the checker",
            ],
            "open": [
                "existence and convergence of the infinite specified saddle-node sequence",
                "replacement source-valid one-phase prime-end/covering and immersion atlas",
                "canonical attachment collar h, angular electrode ell, and any Wave/contact-resistance verdict",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="immutable read-only check (default)")
    parser.add_argument("--write", action="store_true", help="explicit reviewed manifest re-freeze")
    parser.add_argument("--print-manifest", action="store_true", help="print candidate for review")
    args = parser.parse_args()
    ensure(sum((args.check, args.write, args.print_manifest)) <= 1,
           "choose exactly one mode")
    payload = canonical(make_manifest(load(INPUT)))
    if args.print_manifest:
        print("NEAR_PARABOLIC_MANIFEST_BEGIN")
        print(json.dumps(json.loads(payload), sort_keys=True,
                         separators=(",", ":"), ensure_ascii=True))
        print("NEAR_PARABOLIC_MANIFEST_END")
    elif args.write:
        MANIFEST.write_bytes(payload)
        print("WROTE:", MANIFEST)
    else:
        ensure(MANIFEST.read_bytes() == payload,
               "near-parabolic immutable manifest drift")
        print("PASS: 3 certified primitive near-parabolic tips; unchanged v1 marking refused")


if __name__ == "__main__":
    main()
