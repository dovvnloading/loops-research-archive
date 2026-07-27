"""Exact-arithmetic regressions for the conditional paired-Wave response.

These checks guard the algebra and inequality directions in
``kkl_stationary_bl0_survivor_analysis.md``.  They are diagnostic only:
they do not construct a native KKL source Wave, prove a uniform Wave-lemma
constant, or close any MLC obligation.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product


def harmonic_sum(values: tuple[Fraction, ...]) -> Fraction:
    assert values and all(value > 0 for value in values)
    return 1 / sum(1 / value for value in values)


def test_uniform_wave_error_response() -> None:
    """B_i <= C_i+E and S <= (oplus B_i) imply max C_i >= rS-E."""

    positive = tuple(Fraction(n, d) for n in range(1, 9) for d in range(1, 5))
    for branch_count in range(2, 5):
        for outputs in product(positive[:8], repeat=branch_count):
            for error in (Fraction(0), Fraction(1, 3), Fraction(2)):
                # Taking the largest admissible B_i and S is the extremal case.
                source_widths = tuple(output + error for output in outputs)
                packet_width = harmonic_sum(source_widths)
                maximum_output = max(outputs)
                assert maximum_output >= branch_count * packet_width - error


def test_smaller_packet_width_preserves_response() -> None:
    outputs = (Fraction(2), Fraction(5))
    error = Fraction(3, 2)
    source_widths = tuple(output + error for output in outputs)
    maximal_packet_width = harmonic_sum(source_widths)
    for scale in (Fraction(1, 5), Fraction(1, 2), Fraction(1)):
        packet_width = scale * maximal_packet_width
        assert max(outputs) >= 2 * packet_width - error


def test_degree_surplus_response() -> None:
    """B_i <= d_i(T+2) gives T >= (sum 1/d_i)S-2."""

    for degrees in ((1, 1), (1, 2), (2, 2), (1, 3, 3)):
        surplus = sum((Fraction(1, degree) for degree in degrees), Fraction())
        for target_width in (Fraction(0), Fraction(1, 2), Fraction(7)):
            source_widths = tuple(
                degree * (target_width + 2) for degree in degrees
            )
            packet_width = harmonic_sum(source_widths)
            assert target_width >= surplus * packet_width - 2


def test_two_degree_two_branches_are_noncoercive() -> None:
    degrees = (2, 2)
    surplus = sum((Fraction(1, degree) for degree in degrees), Fraction())
    assert surplus == 1
    # The fallback then says only T >= S-2, which permits arbitrarily large
    # S with no multiplicative gain over S.
    for packet_width in (Fraction(10), Fraction(1000)):
        target_width = packet_width - 2
        assert target_width == surplus * packet_width - 2
        assert target_width < Fraction(3, 2) * packet_width


def test_truncation_direction_is_not_reversed() -> None:
    # If every full path contains a truncated crossing, overflow gives
    # W(full) <= W(truncation).  These admissible values refute the reverse
    # inequality as a formal consequence.
    full_width = Fraction(1)
    truncated_width = Fraction(3)
    assert full_width <= truncated_width
    assert not truncated_width <= full_width


def test_packet_to_ambient_threshold() -> None:
    for epsilon in (Fraction(1, 10), Fraction(1, 4), Fraction(1, 2)):
        ambient = Fraction(100)
        error = epsilon * ambient
        packet = (Fraction(1, 2) + epsilon) * ambient
        output = 2 * packet - error
        assert output >= (1 + epsilon) * ambient
        for delta in (epsilon / 4, epsilon / 2):
            assert output > (1 + delta) * ambient


def main() -> None:
    tests = (
        test_uniform_wave_error_response,
        test_smaller_packet_width_preserves_response,
        test_degree_surplus_response,
        test_two_degree_two_branches_are_noncoercive,
        test_truncation_direction_is_not_reversed,
        test_packet_to_ambient_threshold,
    )
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    print("diagnostic stationary paired-Wave regressions: all passed")


if __name__ == "__main__":
    main()
