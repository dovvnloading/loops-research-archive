"""Finite checks for the corrected stationary quantitative-defect algebra.

These tests verify exact arithmetic, set logic, and the explicit annular
countermodel only.  They do not construct a KKL lamination, prove QSDB,
establish a measurable selector, or promote any analytic obligation.
"""

from __future__ import annotations

from fractions import Fraction
from math import log, pi


def test_strict_shortness_slack() -> None:
    for numerator in range(1, 20):
        lam = Fraction(numerator, 20)
        lam_prime = (1 + lam) / 2
        epsilon = (1 - lam) / 8
        obtained = lam_prime - 2 * epsilon
        assert obtained == (1 + 3 * lam) / 4
        assert obtained > lam


def test_terminal_constant_is_admissible_and_charges_vertical_term() -> None:
    epsilon = Fraction(1, 40)
    for a_b in (Fraction(0), Fraction(1, 100), Fraction(2), Fraction(100)):
        delta_v = (
            Fraction(1, 2)
            if a_b == 0
            else min(Fraction(1, 2), epsilon / a_b)
        )
        assert 0 < delta_v < 1
        assert a_b * delta_v <= epsilon


def test_relative_width_cannot_absorb_fixed_constant() -> None:
    multiplier = Fraction(100)
    fixed_charge = Fraction(1)
    for denominator in (1_000, 10_000):
        renormalization_width = Fraction(1, denominator)
        wave_width = multiplier * renormalization_width
        assert wave_width >= multiplier * renormalization_width
        assert wave_width < fixed_charge


def test_theta_transfers_shortness_and_terminality() -> None:
    cases = (
        (Fraction(1, 3), Fraction(2, 3), Fraction(1, 5)),
        (Fraction(3, 4), Fraction(7, 8), Fraction(1, 10)),
        (Fraction(9, 10), Fraction(19, 20), Fraction(1, 3)),
    )
    for lam, lam3, delta3 in cases:
        lower = max(lam / lam3, 1 / (1 + delta3))
        theta = (lower + 1) / 2
        assert lower < theta < 1
        assert lam3 * theta > lam
        assert (1 + delta3) * theta - 1 > 0
        delta_a = min(delta3 * theta, (1 + delta3) * theta - 1)
        assert delta_a > 0


def test_disjoint_B_survivors_are_short() -> None:
    horizon = 4
    leaves = {
        "early_break": {"first_break": 1, "short": False},
        "late_break": {"first_break": 3, "short": False},
        "short_survivor": {"first_break": None, "short": True},
        "short_breaker": {"first_break": 2, "short": True},
        "nonshort_survivor": {"first_break": None, "short": False},
    }
    breakable = {
        name
        for name, data in leaves.items()
        if data["first_break"] is not None and data["first_break"] < horizon
    }
    short = {name for name, data in leaves.items() if data["short"]}
    B = breakable | short
    B_survivors = {
        name
        for name in B
        if leaves[name]["first_break"] is None
        or leaves[name]["first_break"] >= horizon
    }
    assert B_survivors <= short
    assert "nonshort_survivor" not in B


def test_degree_two_horizon_radius_and_collar_bound() -> None:
    R = 1.1
    previous_radius = R
    for horizon in range(1, 7):
        radius = R ** (1 / (2**horizon))
        assert 1 < radius < previous_radius
        maximum_modulus = log(R) / (2 * pi * (2**horizon))
        reciprocal_lower_bound = 2 * pi * (2**horizon) / log(R)
        assert maximum_modulus > 0
        assert abs(maximum_modulus * reciprocal_lower_bound - 1) < 1e-12
        previous_radius = radius


def test_qualitative_positive_modulus_is_not_uniform() -> None:
    horizon = 2
    reciprocal_bounds = [
        2 * pi * (2**horizon) / log(1 + Fraction(1, n))
        for n in (10, 100, 1_000, 10_000)
    ]
    assert all(left < right for left, right in zip(reciprocal_bounds, reciprocal_bounds[1:]))
    assert reciprocal_bounds[-1] > 100_000


def test_selected_crossing_does_not_equal_all_continuation_failures() -> None:
    failures = {
        "source_crossing",
        "target_touch_reentry",
        "global_sheet_switch",
        "remote_nonlanding",
    }
    annular_overflow_class = {"source_crossing"}
    assert annular_overflow_class < failures


def main() -> None:
    tests = (
        test_strict_shortness_slack,
        test_terminal_constant_is_admissible_and_charges_vertical_term,
        test_relative_width_cannot_absorb_fixed_constant,
        test_theta_transfers_shortness_and_terminality,
        test_disjoint_B_survivors_are_short,
        test_degree_two_horizon_radius_and_collar_bound,
        test_qualitative_positive_modulus_is_not_uniform,
        test_selected_crossing_does_not_equal_all_continuation_failures,
    )
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    print("stationary quantitative-defect diagnostics: 8 passed")
    print("diagnostic only; QSDB and the uniform native charge remain open")


if __name__ == "__main__":
    main()
