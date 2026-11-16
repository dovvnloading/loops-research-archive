#!/usr/bin/env python3
"""Exact real period-doubling satellite *refusal* certificate.

Never construct a v1 PhysicalExample when its required interval marking is false.
The algebra certifies a central quadratic-like f^2 return and a genuine
non-interval filled Julia set at the period-four center. Satellite taxonomy
uses the cited classical period-doubling tuning identification, not the
finite computations alone. See RESULTS.md for its implications and limits.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INPUT = HERE / "physical_examples/satellite2_period4_obstruction.json"
MANIFEST = HERE / "experiment_manifests/satellite2_period4_obstruction.json"
SOURCE_LOCKS = {
    "research/native_wave_transfer/SPECIFICATION.md": "4288c3c7a9680fffd8d094b8f25d51c6cd5df648",
    "research/native_wave_transfer/source_contracts/primitive4_record_fields.json": "0be9f9dc3961a020ca59a2f9be4957fb04926e9e",
}
R = F(4, 5)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def canonical(obj: object) -> bytes:
    return (json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: Path) -> str:
    content = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self) -> None:
        require(self.lo <= self.hi, "empty interval")

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __mul__(self, other: "Interval") -> "Interval":
        values = (self.lo * other.lo, self.lo * other.hi,
                  self.hi * other.lo, self.hi * other.hi)
        return Interval(min(values), max(values))

    def square(self) -> "Interval":
        return Interval(F(0) if self.lo <= 0 <= self.hi
                        else min(self.lo * self.lo, self.hi * self.hi),
                        max(self.lo * self.lo, self.hi * self.hi))

    @staticmethod
    def value(number: F | int) -> "Interval":
        return Interval(F(number), F(number))


def orbit(c: F | Interval, length: int = 4) -> tuple[list[Interval], Interval]:
    parameter = c if isinstance(c, Interval) else Interval.value(c)
    x, d = Interval.value(0), Interval.value(0)
    xs = [x]
    for _ in range(length):
        d = Interval.value(2) * x * d + Interval.value(1)
        x = x.square() + parameter
        xs.append(x)
    return xs, d


def g_at(x: F, c: Interval) -> Interval:
    """Exact interval evaluation of G=f_c^2 on a rational real endpoint."""
    y = Interval.value(x).square() + c
    return y.square() + c


def absolute_bound(box: Interval) -> F:
    return max(abs(box.lo), abs(box.hi))


def certify(fixture: dict) -> dict:
    require(fixture["format"] == "native-wave-transfer-satellite-obstruction/v1",
            "not a satellite-obstruction input")
    require(fixture["record_compatibility"] == "refused", "v1 refusal removed")
    require(fixture["first_incompatible_field"] ==
            "MarkedHubbardTree.small_julia_intervals", "wrong first incompatible field")
    require(fixture["purpose"] == "negative compatibility certificate, NOT a PhysicalExample",
            "physical example incorrectly asserted")
    require("source_contract" not in fixture and "marking" not in fixture,
            "a v1 PhysicalExample must not be forged")
    p = fixture["parameter"]
    require(p["family"] == "z^2+c" and p["equation"] == "x4=0"
            and p["orbit_notation"] == "x0=0; x(k+1)=x(k)^2+c",
            "incorrect satellite parameter equation")
    n = p["denominator_power_of_two"]
    require(n == 128, "parameter precision changed")
    require(p["upper_numerator"] - p["lower_numerator"] == 1,
            "parameter bracket must be adjacent dyadics")
    lo, hi = (F(p[k], 2**n) for k in ("lower_numerator", "upper_numerator"))
    c = Interval(lo, hi)
    require(-F(1311, 1000) < lo < hi < -F(1310, 1000),
            "not the real period-four doubling-cascade branch")
    left, _ = orbit(lo)
    right, _ = orbit(hi)
    _, deriv = orbit(c)
    require(left[4].hi < 0 < right[4].lo, "no strict x4 root sign change")
    require(deriv.lo > 0, "x4 root uniqueness not proved")
    x, _ = orbit(c)
    require(x[1].hi < -1 and F(2, 5) < x[2].lo < x[2].hi < F(1, 2),
            "period-four branch / critical value interval invalid")
    require(x[3].hi < -1, "critical orbit x3 order invalid")
    require(fixture["renormalization"] == {
        "physical_iterate": 2, "global_degree": 4, "restricted_degree": 2,
        "target": "D(0,4/5)",
        "source": "component((f^2)^-1(D(0,4/5)),0)",
        "satellite_type": "period-doubling tuning; simple satellite identification conditional on classical Douady-Hubbard theory"
    }, "wrong central return or satellite source")

    # G(z) = z^4 + 2c z^2 + d, d=c^2+c. Rouché against
    # 2c z^2 - w on |z|=R, uniformly over |w|<R.
    d = c.square() + c
    require(F(2, 5) < d.lo < d.hi < F(1, 2), "critical value leaves target")
    margin = 2 * (-c.hi) * R**2 - absolute_bound(d) - R**4 - R
    require(margin > F(3, 50), "strict Rouché degree-two margin lost")
    # Other critical points of G solve z^2=-c, outside |z|=R.
    require(-c.hi > R**2, "a noncentral critical point entered the disk")

    # The fixed point alpha of f is isolated by q(t)=t^2-t+c.
    # q is strictly decreasing on [-3/4,-7/10] and changes sign.
    qleft = F(3, 4)**2 + F(3, 4) + c.lo
    qright = F(7, 10)**2 + F(7, 10) + c.hi
    require(qleft > 0 > qright, "dividing fixed point not isolated")
    # On [-3/4,1/2], x^2+c<0. Thus G'=4x(x^2+c) has
    # positive sign for x<0 and negative sign for x>0.
    require(c.hi + F(3, 4)**2 < 0, "G monotonic branch proof failed")
    e_left, e_right = g_at(-F(3, 4), c), g_at(F(1, 2), c)
    require(min(e_left.lo, e_right.lo) > -R and d.hi < R,
            "whole real bridge to alpha leaves central preimage")
    # This whole interval lies in component V containing 0. The fixed
    # alpha lies there and G(alpha)=alpha, so alpha belongs K(G).
    # Furthermore G(0)=d and G(d)=x4=0 at the isolated root.
    # Thus (G^2)'(0)=0, giving an open attracting basin in K(G).
    require(hi < -R, "f(0)=c must lie outside U to separate the two phases")
    require("small filled Julia" in fixture["refusal_reason"]
            and "nonempty complex interior" in fixture["refusal_reason"],
            "reason must identify the exact false interval premise")
    require(len(fixture["not_asserted"]) == 6, "missing uncomputed observables")
    return {
        "parameter": {
            "equation": "x4=0", "denominator_power_of_two": n,
            "lower_numerator": p["lower_numerator"],
            "upper_numerator": p["upper_numerator"],
            "left_x4_strictly_negative": True,
            "right_x4_strictly_positive": True,
            "derivative_x4_dc_strictly_positive_on_bracket": True,
            "unique_real_parameter_in_bracket": True,
            "critical_orbit_exact_period": 4
        },
        "central_return": {
            "iterate": 2, "global_degree": 4, "restricted_degree": 2,
            "target_radius": "4/5", "rouche_margin_strictly_gt": "3/50",
            "central_component_compactly_contained_in_target": True,
            "other_G_critical_points_outside_target_disk": True,
            "critical_value_x2_between": ["2/5", "1/2"],
            "real_bridge_in_central_source": "[-3/4,1/2]",
            "fixed_alpha_between": ["-3/4", "-7/10"],
            "alpha_in_both_physical_phase_filled_sets": True,
            "two_physical_phase_sets_distinct": True,
            "critical_orbit_period_under_G": 2,
            "superattracting_G_squared_at_zero": True,
            "K_of_G_has_nonempty_complex_interior": True
        },
        "compatibility": {
            "status": "refused",
            "first_incompatible_field": fixture["first_incompatible_field"],
            "reason": fixture["refusal_reason"],
            "uncertified_satellite_observables": fixture["not_asserted"],
            "physical_example_v1_emitted": False,
            "wave_harmonic_verdict": "not defined under the unchanged interval/slit specification"
        }
    }


def manifest(fixture: dict) -> dict:
    output = certify(fixture)
    return {
        "schema_version": 1,
        "format": "native-wave-transfer-satellite-obstruction-manifest/v1",
        "experiment_id": fixture["id"],
        "inputs": {"example_sha256": sha256(INPUT),
                   "source_locks": SOURCE_LOCKS,
                   "source_reference": "arXiv:2606.27272v1, §§2.1,2.5,6.1,Appendix A; classical period-doubling tuning"},
        "code": {"path": "research/native_wave_transfer/regenerate_satellite2.py",
                 "sha256": sha256(Path(__file__))},
        "outputs": output,
        "outputs_sha256": hashlib.sha256(canonical(output)).hexdigest(),
        "proof_status": {
            "certified_by_exact_arithmetic": [
                "unique x4=0 root in adjacent 2^-128 dyadic bracket",
                "exact critical period four and G=f^2 period-two superattracting cycle",
                "strict uniform Rouche margin >3/50 and degree-two central proper map",
                "real bridge, dividing fixed alpha in K(G), and f(K(G)) intersect",
                "open Fatou interior of K(G), so not a real Julia interval"],
            "conditional_on_cited_analytic_inputs": [
                "classical Douady-Hubbard period-doubling satellite classification",
                "general KKL native tree/ideal-endpoint interpretation"],
            "numeric_only": [],
            "unproved": [
                "satellite native planar attachment and ideal-boundary census",
                "filtered proper restrictions or once-per-real-edge transition",
                "satellite Wave widths and their harmonic comparison"]
        }
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="read-only manifest check (default)")
    ap.add_argument("--write", action="store_true", help="explicit manifest regeneration")
    args = ap.parse_args()
    require(not (args.check and args.write), "--check and --write are exclusive")
    for name, blob_sha in SOURCE_LOCKS.items():
        require(git_blob(ROOT / name) == blob_sha, "source contract drift: " + name)
    fixture = json.loads(INPUT.read_text(encoding="utf-8"))
    computed = canonical(manifest(fixture))
    if args.write:
        MANIFEST.write_bytes(computed)
        print("WROTE", MANIFEST)
    else:
        require(MANIFEST.read_bytes() == computed,
                "satellite obstruction manifest is not byte-identical")
        print("PASS: exact satellite p=2 return; v1 interval marking refused (no fabricated Wave)")


if __name__ == "__main__":
    main()
