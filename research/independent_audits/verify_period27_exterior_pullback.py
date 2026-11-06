#!/usr/bin/env python3
"""Exact exterior inverse-ray 9-to-3 address regression for the period-27 center.

Only finite rational-angle, dyadic-bracket and trace-scaling arithmetic is
checked here. Connectedness of K(c*) and existence of a global Böttcher
coordinate are mathematical inputs, *not* proved by this script.

Run: python research/independent_audits/verify_period27_exterior_pullback.py
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
import json

C_BITS = 128
C_K = -607890580437450502081459824019535455703


def angle(level: int, label: int) -> Fraction:
    assert level >= 0 and 0 <= label < (1 << level)
    return Fraction(label, 1 << level)


def forget(level: int, coarse_level: int, label: int) -> int:
    """f^(level-coarse_level) sends k/2^level to k/2^coarse_level."""
    assert 0 <= coarse_level <= level and 0 <= label < (1 << level)
    return label % (1 << coarse_level)


def restore(coarse_level: int, extra: int, coarse: int) -> int:
    """Inverse branch address a and coarse ray b give k = 2^m*a + b."""
    assert extra >= 0 and 0 <= coarse < (1 << coarse_level)
    return (1 << coarse_level) * extra + coarse


def run() -> dict:
    # This merely locates the Lean-proved center inside (-2,-1).
    denominator = 1 << C_BITS
    assert -2 * denominator < C_K < C_K + 1 < -denominator

    fine_level, coarse_level = 9, 3
    degree = 1 << (fine_level - coarse_level)
    assert degree == 64
    counts = Counter()
    witnesses = {}
    for k in range(1 << fine_level):
        b = forget(fine_level, coarse_level, k)
        a = k // (1 << coarse_level)
        fine = angle(fine_level, k)
        coarse = angle(coarse_level, b)
        assert fine * degree % 1 == coarse  # Böttcher f^6: t -> 64*t mod 1
        assert (coarse + a) / degree == fine  # all 64 exact inverse branches
        assert restore(coarse_level, a, b) == k
        counts[b] += 1
        witnesses.setdefault(b, []).append(k)

    assert len(counts) == 8
    assert all(counts[b] == 64 for b in range(8))
    assert witnesses[0][0:2] == [0, 8]
    assert angle(9, 0) != angle(9, 8)
    assert forget(9, 3, 0) == forget(9, 3, 8) == 0

    # Generic finite exact test, including the 27/9/3 residue composition.
    for n in range(13):
        for m in range(n + 1):
            for k in range(1 << n):
                b = forget(n, m, k)
                assert restore(m, k // (1 << m), b) == k
                assert angle(n, k) * (1 << (n-m)) % 1 == angle(m, b)
                for p in (0, m):
                    assert forget(m, p, forget(n, m, k)) == forget(n, p, k)
    for k in (0, 1, 7, 8, 9, 511, 512, (1 << 27) - 1):
        assert forget(27, 3, k) == forget(9, 3, forget(27, 9, k))

    # Sectorwise H^(1/2) trace change of variables: the Jacobian of
    # T_a(theta)=(theta+a)/64 cancels the squared distance scaling.
    branch_scale = Fraction(1, degree)
    jacobian_squared = branch_scale * branch_scale
    distance_squared = branch_scale * branch_scale
    assert jacobian_squared / distance_squared == 1
    # 64 copies each carrying 1/8 amplitude: direct-sum squared seminorm 1.
    amplitude = Fraction(1, 8)
    assert degree * amplitude * amplitude == 1
    arc_l, arc_r = Fraction(1, 10), Fraction(9, 10)
    images = [((arc_l + a) / degree, (arc_r + a) / degree)
              for a in range(degree)]
    assert all(0 <= l < h <= 1 for l, h in images)
    assert all(images[a][1] < images[a+1][0] for a in range(degree-1))
    assert all(h - l == (arc_r - arc_l) / degree for l, h in images)

    return {
        "status": "EXACT_EXTERIOR_9_TO_3_ADDRESS_REGRESSION_PASS",
        "levels": [9, 3],
        "fine_ray_count": 512,
        "coarse_ray_count": 8,
        "fiber_size_each": 64,
        "minimum_extra_binary_bits": 6,
        "first_collision_k": [0, 8],
        "first_collision_angles": ["0", "1/64"],
        "coarse_angle": "0",
        "normalized_sectorwise_trace_amplitude": "1/8",
        "analytic_bottcher_and_landing_checked_by_script": False,
        "global_mlc_gate_claimed": False,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))