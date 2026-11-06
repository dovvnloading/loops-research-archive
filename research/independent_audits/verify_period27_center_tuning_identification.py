#!/usr/bin/env python3
"""Finite exact-arithmetic input to the period-27 center identification.

The companion note imports classical parameter-ray and tuning results; this
program checks their finite arithmetic hypotheses, not those analytic results.
Uses only the Python standard library and the existing outward-rounded dyadic
certificate. Run without -O, which disables the assertions used as checks:

    python3 -B research/independent_audits/verify_period27_center_tuning_identification.py
"""
from __future__ import annotations

from fractions import Fraction
import json
import platform

from verify_period27_symbolic_atlas import AIRPLANE_BITS, exact_center_orbit
from verify_real_nested_3_9 import C_BITS, C_K, PREC


def periodic_angle(word: str) -> Fraction:
    return Fraction(int(word, 2), (1 << len(word)) - 1)


def substitute(word: str) -> str:
    return "".join(AIRPLANE_BITS[int(bit)] for bit in word)


def certificate() -> dict:
    if not __debug__:
        raise RuntimeError("Run without Python's -O flag: assertions are checks.")
    assert C_BITS == 128 and PREC == 224
    assert C_K == -607890580437450502081459824019535455703
    assert Fraction(-2) < Fraction(C_K, 1 << C_BITS)
    assert Fraction(C_K + 1, 1 << C_BITS) < Fraction(1, 4)

    # This helper verifies opposite endpoint signs for f_c^27(0) and a
    # strictly negative parameter derivative throughout the dyadic bracket.
    # IVT and monotonicity therefore give exactly one root in its interior.
    orbit = exact_center_orbit()
    assert orbit[0].lo == orbit[0].hi == 0
    assert orbit[27].lo == orbit[27].hi == 0
    assert all(x.positive() or x.negative() for x in orbit[1:27])
    # All 26 intermediate iterates are nonzero, so the critical period is 27.
    signs = "".join("+" if x.positive() else "-" for x in orbit[1:27])

    # BFKP §4.3: kappa_0=* gives t_1=0; a negative iterate flips the
    # previous bit, a positive iterate preserves it, and * resets to zero.
    bits = ["0"]
    for sign in signs:
        bits.append(str(int(bits[-1]) ^ int(sign == "-")))
    word = "".join(bits)
    assert word == "011100100100011011100011011"
    theta = periodic_angle(word)
    assert theta == Fraction(59914011, 134217727)

    assert AIRPLANE_BITS == ("011", "100")
    pair = AIRPLANE_BITS
    stages = []
    for period, expected in (
        (3, (Fraction(3, 7), Fraction(4, 7))),
        (9, (Fraction(228, 511), Fraction(283, 511))),
        (27, (theta, 1 - theta)),
    ):
        assert all(len(w) == period for w in pair)
        angles = tuple(periodic_angle(w) for w in pair)
        assert angles == expected and angles[0] + angles[1] == 1
        assert 0 < angles[0] < Fraction(1, 2) < angles[1] < 1
        assert pair[1] == "".join(str(1 - int(b)) for b in pair[0])
        for angle in angles:
            assert angle.denominator % 2 == 1
            assert (angle * (1 << period)) % 1 == angle
            assert all((angle * (1 << j)) % 1 != angle
                       for j in range(1, period))
        stages.append({"period": period, "words": list(pair),
                       "angles": [str(a) for a in angles]})
        if period < 27:
            pair = tuple(substitute(w) for w in pair)

    assert pair[0] == word
    doubling_orbit = [(theta * (1 << j)) % 1 for j in range(27)]
    assert len(set(doubling_orbit)) == 27
    distances = [abs(a - Fraction(1, 2)) for a in doubling_orbit]
    assert all(distances[0] < distance for distance in distances[1:])

    return {
        "finite_checks": "PASS",
        "python": platform.python_version(),
        "parameter_bracket": {
            "lower_numerator": C_K,
            "upper_numerator": C_K + 1,
            "denominator": 1 << C_BITS,
            "endpoints_excluded": True,
        },
        "arithmetic_mesh_denominator": 1 << PREC,
        "critical_period": 27,
        "critical_signs_indices_1_through_26": signs,
        "bfkp_binary_period": word,
        "bfkp_kneading_angle": str(theta),
        "tuning_stages": stages,
        "unique_closest_to_half_in_doubling_orbit": True,
        "analytic_bridge": {
            "machine_checked": False,
            "center_root_ray_pair": "BFKP, section 4.4, printed page 10",
            "tuning_and_unique_root_component": "Zakeri, section 2, printed pages 5-6",
        },
    }


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2, sort_keys=True))
