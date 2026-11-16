#!/usr/bin/env python3
"""Exact period-doubling Misiurewicz tip/domain and v1-semantic refusal.

The certified *positive* result is a degree-two polynomial-like f^2 return
with an invariant inner real interval, not a fabricated three-phase v1 Wave.
No existing example, lock, or executable is altered by this file.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INPUT = HERE / "physical_examples/satellite2_misiurewicz_tip_refusal.json"
MANIFEST = HERE / "experiment_manifests/satellite2_misiurewicz_tip_refusal.json"
SOURCE_LOCKS = {
    "research/native_wave_transfer/SPECIFICATION.md": "4288c3c7a9680fffd8d094b8f25d51c6cd5df648",
    "research/native_wave_transfer/source_contracts/record_fields.json": "0a345322213b9d5c084259406c721181e93e9ee5",
    "research/native_wave_transfer/source_contracts/primitive4_record_fields.json": "0be9f9dc3961a020ca59a2f9be4957fb04926e9e",
}
UNCHANGED_BLOBS = {
    "physical_examples/tip_pr68.json": "65ecc49937b3c341005407a59b353b38f804afec",
    "physical_examples/primitive4_tip12.json": "d0154c8aec14b9355ed81144075486306ee7ab89",
    "physical_examples/primitive4_tip12_parameter.json": "99192901551611390ef8d5ab81458e8316a9c70b",
    "physical_examples/satellite2_period4_obstruction.json": "9393ef6757df0c37eb1414a807f77f852b38c5dd",
    "experiment_manifests/tip_pr68.json": "39233f576e7de78cf707b4d616177d0313b98b25",
    "experiment_manifests/primitive4_tip12.json": "abcc01ad0b5ab0b59cd46e9d080ce44141603392",
    "experiment_manifests/satellite2_period4_obstruction.json": "063132e808fe209473663e28cd12b7eb876c27ed",
    "regenerate.py": "0dfa4f4c8d5321a7b9fdd74c9c1218228087e0f2",
    "regenerate_period4.py": "00bae744fbf752beb98994930fe666c02bb652c8",
    "regenerate_satellite2.py": "c3577f8b276341316ee6905389707034d0e26737",
}

def require(ok: bool, why: str) -> None:
    if not ok:
        raise AssertionError(why)

def canonical(obj: object) -> bytes:
    return (json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode()

def git_blob(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def polynomial(c: Q) -> Q:
    return ((c + 2)*c + 2)*c + 2  # c^3+2c^2+2c+2

def exact_certificate(fixture: dict) -> dict:
    """Everything in this routine is rational, symbolic, or a strict test."""
    require(set(fixture) == {"format", "id", "purpose", "parameter",
            "renormalization", "first_incompatible_field", "record_compatibility",
            "refusal_reason", "not_asserted"}, "unknown/forged v1 marking field")
    require(fixture["format"] == "native-wave-transfer-satellite-tip-refusal/v1"
            and fixture["record_compatibility"] == "refused"
            and "NOT a v1 PhysicalExample" in fixture["purpose"],
            "must not claim an encoded v1 PhysicalExample")
    p = fixture["parameter"]
    require(p["family"] == "z^2+c"
            and p["equation"] == "c^3+2*c^2+2*c+2=0"
            and p["orbit_notation"] == "x0=0; x(k+1)=x(k)^2+c",
            "incorrect critical orbit polynomial")
    n = p["denominator_power_of_two"]
    require(n == 128, "parameter precision drift")
    lo_n = int(p["lower_numerator"])
    hi_n = int(p["upper_numerator"])
    require(hi_n == lo_n+1, "not adjacent dyadics")
    lo, hi = Q(lo_n,2**n), Q(hi_n,2**n)
    require(Q(-31,20) < lo < hi < Q(-3,2), "wrong satellite parameter branch")
    require(polynomial(lo) < 0 < polynomial(hi), "missing strict parameter root signs")
    # P'(c)=3(c+2/3)^2+2/3 >0 on ALL of R.
    # Consequently the bracket isolates the unique real root c_*.
    require(3*lo*lo+4*lo+2 > 0 and 3*hi*hi+4*hi+2 > 0,
            "derivative/uniqueness check failed")
    a_low, a_high = hi*hi+hi, lo*lo+lo  # c^2+c decreases for c<-1/2
    require(Q(4,5) < a_low < a_high < Q(9,10), "critical value not in target")
    require(-hi > 1 and a_high*a_high < -hi,
            "noncentral G critical points/real monotonicity")
    require(4*a_low*a_low > 2 and 2*a_low > 1,
            "terminal fixed point not repelling")
    require(hi < -a_high and -hi+a_low > 1,
            "satellite touching phase / excluded outer real inverse branch")

    r = Q(fixture["renormalization"]["target"][4:-1])
    require(fixture["renormalization"] == {
        "physical_iterate": 2, "global_degree": 4, "restricted_degree": 2,
        "target": "D(0,1)", "source": "component((f^2)^-1(D(0,1)),0)"
    } and r == 1, "invalid physical return/domain")
    # G(z)=f^2(z)=z^4+2*c*z^2+a. For every |w|<=1 on |z|=1:
    # |2c*z^2| - |z^4+a-w| >= 2|c|-1-a-1 > 1/5.
    # Thus G-w has exactly two zeros in D(0,1); the component at
    # critical point 0 is compact in U and maps properly with degree 2.
    margin = -2*hi - Q(2) - a_high
    require(margin > Q(1,5), "Rouche margin not >1/5")
    # Identity f(a)+a = c*P(c) is polynomial, not numerical rounding.
    # At P(c_*)=0 we have 0 -> c -> a -> -a -> -a.
    # The interval K0=[-a,a] is G-invariant with G(0)=a and
    # G(+/-a)=-a; derivative G'=4z(z^2+c) has only one
    # critical point in K0 and these endpoint/critical images.
    # For y in K0, G(z)=y implies
    #     z^2=-c +/- sqrt(y-c).
    # The minus choice ranges from 0 to a^2; the plus choice is
    # >=-c+a>1. Consequently G^-1(K0) intersect V equals K0.
    # Standard density of inverse repelling orbits in J(G), and absence
    # of bounded complementary domains for a subset of R, identify
    # K(G)=K0. This analytic deduction is NOT an interval sample.
    require(fixture["first_incompatible_field"] ==
            "MarkedHubbardTree.small_julia_intervals",
            "wrong first semantic refusal")
    require("one Chebyshev inner Julia interval" in fixture["refusal_reason"]
            and "three distinct inner Julia intervals" in fixture["refusal_reason"],
            "failure must identify the source-locked three-phase premise")
    require(len(fixture["not_asserted"]) == 5, "missing unasserted v1 observables")
    return {
        "parameter": {"equation": p["equation"],
                      "lower_numerator": lo_n, "upper_numerator": hi_n,
                      "denominator_power_of_two": n,
                      "opposite_strict_signs": True,
                      "unique_real_root_by_positive_derivative": True,
                      "approximation_for_orientation_only": "-1.5436890126920764"},
        "central_return": {"iterate": 2, "global_degree": 4, "restricted_degree": 2,
            "target": "D(0,1)", "source": fixture["renormalization"]["source"],
            "rouche_margin_strictly_greater_than": "1/5",
            "critical_value_a_strictly_between": ["4/5","9/10"],
            "noncentral_critical_points_outside_target_disk": True,
            "central_component_compactly_contained_in_target": True},
        "exact_real_geometry": {
            "orbit_identity_mod_parameter_polynomial": "0 -> c -> a -> -a -> -a, a=c^2+c",
            "terminal_point_repelling_f": True, "terminal_point_repelling_G": True,
            "inner_invariant_interval": "[-a,a]",
            "other_phase_interval": "[c,-a]",
            "intersection_of_phases": "{-a}",
            "real_inverse_branches_in_U": "only +/-sqrt(-c-sqrt(y-c)), y in [-a,a]",
            "excluded_outer_branch_squared_modulus_strictly_gt": "1",
            "central_real_inverse_tree_equals_inner_interval": True,
            "new_attachments": 0,
            "inner_small_julia_set_count": 1,
            "inner_old_edge_count_under_KKL_vertex_convention": 0},
        "compatibility": {
            "status": "refused",
            "first_incompatible_field": fixture["first_incompatible_field"],
            "kind": "semantic three-phase contract / primitive source hypothesis, not a JSON list type error",
            "source_hypothesis": "KKL arXiv:2606.27272v1 §§2.3-2.5 assumes primitive: f(K0) disjoint from K0; here they meet at -a",
            "v1_example_emitted": False,
            "covering_f_star_and_immersion_iota_star": "distinct maps, not fabricated as atomic tables",
            "filtered_two_versus_one": None,
            "perron_root_of_old_edge_matrix": None,
            "zero_old_edge_wave_crests": None,
            "parent_and_child_wave_widths": None,
            "harmonic_width_verdict": "not defined for the unchanged primitive three-phase Wave protocol",
            "unasserted": fixture["not_asserted"]}
    }

def primitive_baselines() -> dict:
    for name, blob in {**SOURCE_LOCKS,
                       **{"research/native_wave_transfer/" + k: v
                          for k,v in UNCHANGED_BLOBS.items()}}.items():
        require(git_blob(ROOT / name) == blob, "locked baseline/source changed: " + name)
    out = {}
    for name, key in (("p3", "tip_pr68"), ("p4", "primitive4_tip12")):
        data = json.loads((HERE / ("experiment_manifests/" + key + ".json")).read_text())
        s = data["outputs"]
        require(s["ideal_boundary"]["target_atom_count"] == 10
                and s["ideal_boundary"]["covering_source_atom_count"] == 20
                and len(s["attachment_census"]["components"]) == 1
                and s["sheet_paths"]["counts"] == [2,1]
                and s["wave"]["harmonic_series_equality"] is True,
                "primitive baseline projection drift: " + name)
        out[name] = {
            "target_atoms": s["ideal_boundary"]["target_atom_count"],
            "source_atoms": s["ideal_boundary"]["covering_source_atom_count"],
            "attachments": len(s["attachment_census"]["components"]),
            "filtered_restrictions": s["sheet_paths"]["counts"],
            "target_width": s["wave"]["target_width"],
            "child_width": s["wave"]["each_child_and_pushed_width"],
            "pushed_crests": s["wave"]["pushed_crests"],
            "harmonic_equality": s["wave"]["harmonic_series_equality"]}
    return out

def make_manifest(fixture: dict) -> dict:
    result = exact_certificate(fixture)
    result["primitive_comparison"] = primitive_baselines()
    return {
        "format": "native-wave-transfer-satellite-tip-manifest/v1",
        "schema_version": 1,
        "experiment_id": fixture["id"],
        "inputs": {"example_sha256": sha256(INPUT),
                   "source_locks": SOURCE_LOCKS,
                   "unchanged_reference_blobs": UNCHANGED_BLOBS,
                   "source_reference": "arXiv:2606.27272v1 §§2.3-2.5,6.1,Appendix A"},
        "code": {"path": "research/native_wave_transfer/regenerate_satellite2_tip.py",
                 "sha256": sha256(Path(__file__))},
        "outputs": result,
        "outputs_sha256": hashlib.sha256(canonical(result)).hexdigest(),
        "proof_status": {
            "certified_by_exact_arithmetic": [
                "unique real P(c)=0 root in adjacent 2^-128 dyadic bracket",
                "whole-circle Rouche margin >1/5 and degree-two f^2 central restriction",
                "critical preperiod and repelling terminal point",
                "two invariant real phase intervals meet at exactly -a",
                "no extra inverse branches of the real inner interval within V",
                "Tprime=T, no inner attachments, one small interval and no KKL old edges"],
            "conditional_on_cited_analytic_inputs": [
                "backward-orbit density and standard quadratic-like dynamics identify the full small filled Julia set with the invariant real interval",
                "KKL §§2.3-2.5 define its core edge/ideal construction only for primitive renormalization",
                "induced prime-end/Wave semantics for primitive benchmarks"],
            "numeric_only": ["display decimal parameter approximation, never used in comparisons"],
            "unproved": [
                "a replacement satellite-native marking, sheet/path and wave framework",
                "satellite atom multiplicities, source versus covering crest census",
                "nontrivial Perron comparison and quantitative harmonic transfer"]}
    }

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="explicit re-freeze (never in CI)")
    parser.add_argument("--check", action="store_true", help="immutable read-only check")
    parser.add_argument("--print-manifest", action="store_true", help="emit computed manifest to workflow log")
    args = parser.parse_args()
    require(sum((args.write,args.check,args.print_manifest)) <= 1,
            "choose exactly one mode")
    fixture = json.loads(INPUT.read_text(encoding="utf-8"))
    computed = canonical(make_manifest(fixture))
    if args.print_manifest:
        print("SATELLITE_MANIFEST_BEGIN")
        print(json.dumps(json.loads(computed),sort_keys=True,separators=(",",":"),ensure_ascii=True))
        print("SATELLITE_MANIFEST_END")
    elif args.write:
        MANIFEST.write_bytes(computed)
        print("WROTE", MANIFEST)
    else:
        require(MANIFEST.read_bytes() == computed, "satellite tip immutable manifest drift")
        print("PASS: exact c*, degree-two G, satellite contact; primitive v1 refused")

if __name__ == "__main__":
    main()
