#!/usr/bin/env python3
"""Exact arithmetic for NOTE.md's physical parameter-capacity calibration.

The Green-energy identities, Jensen formula, and infinite-schedule criterion
are written proofs. This program certifies the finite parameter disks and
the entire escaping circle arc used by the physical test. No floating-point
arithmetic enters a proof comparison. Files are read-only by default.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from math import factorial
from pathlib import Path


HERE = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def rat(x: F) -> str:
    return f"{x.numerator}/{x.denominator}"


def exp_upper(x: F, degree: int) -> F:
    """Strict upper bound using a rational geometric Taylor remainder."""
    require(x > 0 and degree >= 0, "positive argument and degree required")
    ratio = x / (degree + 2)
    require(ratio < 1, "Taylor tail geometric ratio must be below one")
    partial = sum((x**k / factorial(k) for k in range(degree + 1)), F(0))
    first_omitted = x ** (degree + 1) / factorial(degree + 1)
    return partial + first_omitted / (1 - ratio)


def certificate() -> dict[str, object]:
    # The parent parameter disk |c|<=1/4 has an invariant dynamical disk.
    parent_parameter_radius = F(1, 4)
    parent_dynamical_radius = F(1, 2)
    require(parent_dynamical_radius**2 + parent_parameter_radius
            <= parent_dynamical_radius, "parent trapping disk failed")

    # For |c+1|<=3/32, f_c^2 traps the dynamical disk |z|<=1/4.
    child_parameter_radius = F(3, 32)
    child_dynamical_radius = F(1, 4)
    two_step_bound = (
        child_dynamical_radius**4
        + 2 * (1 + child_parameter_radius) * child_dynamical_radius**2
        + child_parameter_radius + child_parameter_radius**2
    )
    require(two_step_bound == F(249, 1024), "two-step expansion changed")
    require(two_step_bound < child_dynamical_radius,
            "child parameter disk does not have the stated trapping region")

    inner_radius, outer_radius = F(1, 4), F(1, 2)
    child_distance_lower = 1 - child_parameter_radius
    require(child_distance_lower > outer_radius, "child meets bump support")
    require(outer_radius / inner_radius == 2, "bump energy must use log(2)")
    # For |c|<=1/2, G_M(c)<=log(3/2)<1; exp(1)>1+1=2>3/2.
    ground_log_argument = 1 + outer_radius
    require(ground_log_argument < 2, "support inclusion in D_1 failed")

    # c=(1/2)e^(it), |t|<=1/20: |c-1/2|<=|t|/2<=1/40.
    angle_half_width = F(1, 20)
    center_parameter = F(1, 2)
    parameter_error = center_parameter * angle_half_width
    require(parameter_error == F(1, 40), "arc parameter error changed")
    orbit_center, orbit_error = center_parameter, parameter_error
    orbit_rows = []
    for n in range(1, 6):
        orbit_rows.append({
            "n": n,
            "center": rat(orbit_center),
            "error_upper": rat(orbit_error),
            "modulus_lower": rat(orbit_center - orbit_error),
        })
        if n < 5:
            orbit_error = (
                2 * orbit_center * orbit_error + orbit_error**2 + parameter_error
            )
            orbit_center = orbit_center**2 + center_parameter
    require(orbit_center == F(206657, 65536), "critical fifth iterate changed")
    escape_radius = F(11, 5)
    require(orbit_center - orbit_error > escape_radius,
            "entire-arc fifth-iterate escape enclosure failed")

    # Infinite tail: |x_(k+1)| >= q |x_k|^2 once |x_k|>=L.
    parameter_modulus = F(1, 2)
    require(escape_radius**2 - parameter_modulus > escape_radius,
            "escape moduli need to remain above their first certified radius")
    escape_factor = 1 - parameter_modulus / escape_radius**2
    escape_log_argument = escape_radius * escape_factor
    require(escape_factor == F(217, 242), "escape factor changed")
    require(escape_log_argument == F(217, 110), "escape logarithm changed")
    logarithm_lower = F(2, 3)
    exponential_upper = exp_upper(logarithm_lower, 8)
    require(exponential_upper < escape_log_argument,
            "rational exponential remainder does not prove log(217/110)>2/3")

    # Critical VALUE normalization: G_M=lim 2^(-(n-1)) log|x_n|.
    iterate = 5
    value_normalization = F(1, 2 ** (iterate - 1))
    green_lower = value_normalization * logarithm_lower
    require(green_lower == F(1, 24), "critical-point/value factor-of-two error")

    # Arc average >= (2 theta)/(2 pi) * green_lower; pi<4.
    circle_average_lower = angle_half_width * green_lower / 4
    require(circle_average_lower == F(1, 1920), "circle average bound changed")
    # log(R/r)=log(2)<1 and V_M=T=1.
    energy_increment_lower = circle_average_lower**2
    require(energy_increment_lower == F(1, 3686400), "finite energy gain changed")
    require(exp_upper(F(1), 8) < 3, "D_1 subset B(0,4) uses exp(1)<3")

    return {
        "schema": "parameter-capacity-increment-v1",
        "date": "2026-11-23",
        "normalization": "G_M(c)=lim 2^(-(n-1)) log^+|f_c^n(0)|",
        "ground": "D_1={G_M<1}",
        "parent": "F_0=M; V_D1(F_0)=1",
        "child": {
            "parameter_center": "-1/1",
            "parameter_radius": rat(child_parameter_radius),
            "dynamical_two_step_trap_radius": rat(child_dynamical_radius),
            "two_step_image_radius_upper": rat(two_step_bound),
            "distance_from_bump_center_lower": rat(child_distance_lower),
        },
        "bump": {
            "center": "0/1", "inner_radius": rat(inner_radius),
            "outer_radius": rat(outer_radius),
            "normalized_dirichlet_energy": "1/log(2)",
        },
        "escaping_arc": {
            "circle_radius": rat(outer_radius),
            "angle_half_width_radians": rat(angle_half_width),
            "parameter_error": rat(parameter_error),
            "critical_orbit_enclosures": orbit_rows,
            "escape_iterate": iterate,
            "escape_radius_strict_lower": rat(escape_radius),
            "escape_factor": rat(escape_factor),
            "escape_log_argument": rat(escape_log_argument),
            "exp_two_thirds_strict_upper": rat(exponential_upper),
            "critical_value_normalization": rat(value_normalization),
            "green_strict_lower": rat(green_lower),
        },
        "circle_green_average_strict_lower": rat(circle_average_lower),
        "physical_robin_increment_strict_lower": rat(energy_increment_lower),
        "scope": (
            "Finite physical parameter calibration; analytic potential identities "
            "are written proofs; no infinite schedule, new nonhyperbolic MLC "
            "case, MARK discharge, or global MLC proof."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-certificate", action="store_true")
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    require(not (args.check_certificate and args.write_certificate),
            "choose either checking or writing the certificate")
    result = certificate()
    path = HERE / "certificate.json"
    if args.write_certificate:
        path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if args.check_certificate:
        require(json.loads(path.read_text()) == result,
                "committed certificate differs from fresh exact arithmetic")
    print("PASS: actual parent and child parameter disks, child separation, "
          "and bump support in D_1.")
    print("PASS: entire circle arc |t|<=1/20 has G_M((1/2)e^(it))>1/24 "
          "with the critical-value normalization.")
    print("PASS: physical Green Robin increment >1/3686400; "
          "infinite-schedule and ground-transfer claims remain unproved.")


if __name__ == "__main__":
    main()
