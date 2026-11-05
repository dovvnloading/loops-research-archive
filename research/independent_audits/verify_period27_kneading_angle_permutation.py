#!/usr/bin/env python3
"""Exact real kneading-angle and cyclic-permutation source comparison.

Implements Baker--Chen--Li--Qian (European J. Combin. 134 (2026),
arXiv:2508.12924v2), Section 6.1 and Section 4.1, for the unique
critically periodic real period-27 quadratic in the archive.

Uses outward signed 2^-224 integer intervals to determine all signs
and the entire real orbit order. Separately computes:
 (A) the Milnor--Thurston kneading ANGLE from the critical signs;
 (B) the twisted-shift lexical 27-cycle using binary words alone.

No external parameter ray is claimed to land at the center: periodic
parameter rays land at PARABOLIC ROOTS of hyperbolic components.
No source-specific ray, prime-end, KL sheet or MLC gate is established.
"""
from __future__ import annotations

from verify_period27_symbolic_atlas import (
    AIRPLANE_BITS,
    EXPECTED_ANGLES,
    build_certificate,
    exact_center_orbit,
)

N = 27
DEN = (1 << N) - 1
EXPECTED_RANKS = [
    1, 27, 18, 9, 19, 10, 6, 22, 13,
    3, 25, 16, 7, 21, 12, 4, 24, 15,
    2, 26, 17, 8, 20, 11, 5, 23, 14,
]


def complement(word: str) -> str:
    return "".join("1" if bit == "0" else "0" for bit in word)


def signed_kneading_angle(orbit) -> str:
    """Baker--Chen--Li--Qian §6.1, t1=0 and flips at negative κ_j."""
    bits = ["0"]
    assert orbit[0].lo == orbit[0].hi == 0
    for j in range(1, N):
        assert orbit[j].hi < 0 or orbit[j].lo > 0, (
            "uncertified critical sign", j
        )
        bit = int(bits[-1]) ^ int(orbit[j].hi < 0)
        bits.append(str(bit))
    return "".join(bits)


def twisted_shift(word: str) -> str:
    """The modified tent-map shift F of Baker et al., §2.4."""
    left = word[1:] + word[0]
    return left if left[0] == "1" else complement(left)


def source_cycle_from_angle(word: str) -> list[int]:
    """Compute λ([t]) using Baker et al., §4.1, N2 case (odd N)."""
    assert len(word) == N and word[0] == "0"
    mu = [complement(word)]
    assert mu[0][0] == "1"
    for _ in range(N-1):
        mu.append(twisted_shift(mu[-1]))
    assert len(set(mu)) == N, "unexpected N1/extended-shift case"
    assert twisted_shift(mu[-1]) == mu[0]
    # Lexicographic ranks; with distinct fixed-width words, equals
    # their order as binary integers.
    ranks = [1 + sum(s < item for s in mu) for item in mu]
    assert len(set(ranks)) == N
    return ranks


def critical_orbit_ranks(orbit, ordered_indices: list[int]) -> list[int]:
    """Rank each f^j(0), j=1..27, from exact real interval enclosure."""
    assert len(ordered_indices) == N and set(ordered_indices) == set(range(N))
    for i, j in zip(ordered_indices, ordered_indices[1:]):
        assert orbit[i].hi < orbit[j].lo, "non-strict orbit vertex order"
    position = {j: rank + 1 for rank, j in enumerate(ordered_indices)}
    return [position[j % N] for j in range(1, N+1)]


def check() -> None:
    orbit = exact_center_orbit()
    manifest = build_certificate()
    ordered = manifest["real_interval_markov_spine"]["ordered_orbit_indices"]
    word = signed_kneading_angle(orbit)
    a, b, d = EXPECTED_ANGLES[27]

    assert d == DEN
    assert len(word) == N
    assert word == "011100100100011011100011011"
    assert int(word, 2) == a == 59914011
    assert DEN - a == b == 74303716
    assert complement(word) == f"{b:027b}"

    # Source Theorem 6.2: kneading angle has exact doubling period,
    # is <1/2 and is closest to 1/2 within its own doubling orbit.
    doubling = [((1 << j) * a) % DEN for j in range(N)]
    assert len(set(doubling)) == N
    assert doubling[0] == a
    assert 0 < 2*a < DEN
    assert all(abs(2*a - DEN) < abs(2*x - DEN)
               for x in doubling[1:])

    # Two independent constructions: exact real vertex ranks and
    # lexicographic ranks from the rational angle via twisted F.
    actual = critical_orbit_ranks(orbit, ordered)
    combinatorial = source_cycle_from_angle(word)
    assert actual == combinatorial == EXPECTED_RANKS, (
        "full 27-cycle mismatch", actual, combinatorial
    )

    # This exact rank permutation is one cyclic unimodal permutation:
    # the image of the critical vertex is the least rank, and the map
    # decreases to that vertex and increases afterward on the real line.
    index_of_zero = ordered.index(0)
    pos = {j: i + 1 for i, j in enumerate(ordered)}
    successor = [pos[(j + 1) % N] for j in ordered]
    assert successor[index_of_zero] == 1
    assert all(successor[i] > successor[i+1]
               for i in range(index_of_zero))
    assert all(successor[i] < successor[i+1]
               for i in range(index_of_zero+1, N-1))

    # The exact kneading angle is also the twice-tuned lower angular
    # word starting from the period-3 airplane word '011'.
    tuned = "011"
    for _ in range(2):
        tuned = "".join(AIRPLANE_BITS[int(bit)] for bit in tuned)
    assert tuned == word

    print("PASS: exact Baker--Chen--Li--Qian period-27 source comparison")
    print(f"  real critical signs -> kneading angle {a}/{DEN}")
    print("  angle word:", word)
    print("  unique closest-to-1/2 rational doubling orbit element")
    print("  twisted-shift 27-cycle equals all EXACT real orbit ranks:")
    print(" ", actual)
    print("  critical orbit permutation is cyclic unimodal")
    print("  twice-tuned airplane lower ANGULAR word matches exactly")
    print("LIMIT: no assertion that parameter rays land at the center;")
    print("       root component identification and KL accesses/sheets OPEN")


if __name__ == "__main__":
    check()
