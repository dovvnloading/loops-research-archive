#!/usr/bin/env python3
"""Exact symbolic candidate marking and real Markov spine for the period-27 center.

This program certifies only integer/dyadic and rational-angle statements.
It does NOT identify candidate angles with parameter rays of c*, prove
ray landing or prime-end transport, or construct the full Hubbard-tree
external-ray automaton of Sodre (2026).

Run from research/independent_audits (its directory is put on sys.path):
    python research/independent_audits/verify_period27_symbolic_atlas.py
    python research/independent_audits/verify_period27_symbolic_atlas.py --print-json
    python research/independent_audits/verify_period27_symbolic_atlas.py --check-manifest
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from verify_real_nested_3_9 import (
    C_K, C_BITS, PREC, UNIT, ZERO, ONE,
    Interval, parameter, iterate, orbit_and_derivative,
)

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "results" / "period27_symbolic_marking.json"
AIRPLANE_BITS = ("011", "100")
EXPECTED = {
    3: "10*",
    9: "10010110*",
    27: "10010110110010110010010110*",
}
EXPECTED_ANGLES = {
    3: (3, 4, 7),
    9: (228, 283, 511),
    27: (59914011, 74303716, 134217727),
}
EXPECTED_ADDRESSES = {
    3: [1, 2, 3],
    9: [1, 2, 3, 6, 9],
    27: [1, 2, 3, 6, 9, 18, 27],
}


def exact_center_orbit() -> list[Interval]:
    lo, hi = parameter(C_K), parameter(C_K + 1)
    assert iterate(ZERO, lo, 27)[27].positive()
    assert iterate(ZERO, hi, 27)[27].negative()
    enclosure = Interval(lo.lo, hi.hi)
    orbit, derivative = orbit_and_derivative(enclosure, 27)
    assert derivative[27].negative()
    assert orbit[27].lo < 0 < orbit[27].hi
    # f^27(0)=0 is exact at c*; the interval enclosure is not exact zero.
    orbit[27] = ZERO
    return orbit


def angle_kneading(word: str) -> str:
    """Rational-doubling itinerary relative to (theta/2,(1+theta)/2).

    Each comparison is performed between integers over the same
    denominator 2*(2**n-1). This is the definition of angular kneading,
    not a dynamical-plane ray-landing test.
    """
    n = len(word)
    den = (1 << n) - 1
    numerator = int(word, 2)
    assert 0 < numerator < den
    assert all((numerator * pow(2, k, den)) % den != numerator
               for k in range(1, n)), "angle must have exact doubling period"
    itinerary = []
    t = numerator
    for _ in range(n):
        doubled = 2 * t
        if doubled == numerator or doubled == numerator + den:
            itinerary.append("*")
        elif numerator < doubled < numerator + den:
            itinerary.append("1")
        else:
            itinerary.append("0")
        t = (2 * t) % den
    assert t == numerator and itinerary[-1] == "*"
    assert itinerary.count("*") == 1
    return "".join(itinerary)


def rho_address(periodic_word: str) -> list[int]:
    """Internal address via rho(n)=first disagreement with n-shift."""
    n = len(periodic_word)
    assert set(periodic_word) <= {"0", "1"}
    address = [1]
    while address[-1] < n:
        s = address[-1]
        next_value = next((k for k in range(s + 1, 2 * n + s + 1)
                           if periodic_word[(k - 1) % n]
                           != periodic_word[(k - 1 - s) % n]), None)
        if next_value is None or next_value > n:
            break
        address.append(next_value)
    return address


def upper_completion(kneading: str) -> tuple[str, list[int]]:
    assert kneading.endswith("*")
    n = len(kneading)
    options = []
    for bit in "01":
        completed = kneading[:-1] + bit
        address = rho_address(completed)
        if address[-1] == n:
            options.append((completed, address))
    assert len(options) == 1, "the period should select a unique completion"
    return options[0]


def signed_return_kneading(orbit: list[Interval], a: list[Interval], p: int) -> str:
    """Real critical-value word oriented by the sign of z^2 coefficient."""
    assert 27 % p == 0
    assert a[p].positive() or a[p].negative()
    bits = []
    for j in range(1, 27 // p):
        product = orbit[j * p] * a[p]
        assert product.negative() or product.positive()
        bits.append("1" if product.negative() else "0")
    return "".join(bits) + "*"


def sorted_markov_spine(orbit: list[Interval]) -> dict:
    """Exact 26-edge Markov graph of the invariant real interval.

    Vertices are all 27 distinct points f^j(0), j=0..26. Each
    adjacent edge avoids the unique critical point in its interior;
    hence f maps it monotonically over contiguous destination edges.
    This is a REAL interval Markov graph, not the two-sided external-ray
    Hubbard-tree automaton.
    """
    vertices = sorted(range(27), key=lambda i: orbit[i].lo)
    assert vertices[0] == 1 and vertices[-1] == 2
    for i, j in zip(vertices, vertices[1:]):
        assert orbit[i].hi < orbit[j].lo, ("overlap of orbit enclosures", i, j)
    assert orbit[1].negative() and orbit[2].positive()
    assert orbit[3].hi < orbit[2].lo
    # Since |x1| > |x2| and 0 in [x1,x2], f([x1,x2])=[x1,x2].
    assert -orbit[1].hi > orbit[2].hi
    position = {index: rank for rank, index in enumerate(vertices)}
    rows = []
    for source_edge in range(26):
        v, w = vertices[source_edge:source_edge + 2]
        # Critical point 0 is a vertex, never interior to an edge.
        assert not (orbit[v].hi < 0 < orbit[w].lo)
        f_v, f_w = (v + 1) % 27, (w + 1) % 27
        i, j = sorted((position[f_v], position[f_w]))
        assert i < j
        rows.append(list(range(i, j)))
    # The Markov graph is deterministic because f is monotone on each edge.
    # All edge images are nonempty and consist of consecutive edges.
    assert len(rows) == 26 and all(row for row in rows)
    # Exact labels for the physical restrictive intervals, not new results.
    p3 = sorted((position[6], position[3]))
    p9 = sorted((position[9], position[18]))
    assert p3[0] < p9[0] < position[0] < p9[1] < p3[1]
    row_json = json.dumps(rows, separators=(",", ":"), ensure_ascii=True)
    return {
        "ordered_orbit_indices": vertices,
        "edge_destinations": rows,
        "edge_adjacency_sha256": hashlib.sha256(row_json.encode()).hexdigest(),
        "restrictive_interval_vertex_ranks": {"3": p3, "9": p9},
    }


def build_certificate() -> dict:
    orbit = exact_center_orbit()
    for p in (1, 3, 9):
        assert orbit[p].positive() or orbit[p].negative()
    coeff = [ZERO, ONE]
    for j in range(1, 9):
        coeff.append(orbit[j] * coeff[j].times(2))
    assert coeff[1].positive() and coeff[3].negative() and coeff[9].positive()
    # Reuse the earlier real restrictive enclosure witnesses.
    assert orbit[6].hi < orbit[9].lo < 0 < orbit[18].lo < orbit[3].lo

    pair = AIRPLANE_BITS
    scales = {}
    for n in (3, 9, 27):
        den = (1 << n) - 1
        lower, upper = (int(word, 2) for word in pair)
        assert (lower, upper, den) == EXPECTED_ANGLES[n]
        assert lower + upper == den  # reflection in the real axis
        assert all(angle_kneading(word) == EXPECTED[n] for word in pair)
        completed, address = upper_completion(EXPECTED[n])
        assert address == EXPECTED_ADDRESSES[n]
        return_time = 27 // n
        real_word = signed_return_kneading(orbit, coeff, return_time)
        assert real_word == EXPECTED[n], (
            "physical vs angular kneading mismatch", n, real_word, EXPECTED[n]
        )
        scales[str(n)] = {
            "physical_return_time": return_time,
            "lower_binary_period": pair[0],
            "upper_binary_period": pair[1],
            "lower_angle": f"{lower}/{den}",
            "upper_angle": f"{upper}/{den}",
            "angular_kneading": EXPECTED[n],
            "oriented_real_critical_kneading": real_word,
            "upper_kneading_completion": completed,
            "internal_address": address,
            "return_quadratic_coefficient_sign": (
                "+" if coeff[return_time].positive() else "-"
            ),
        }
        # A 3-block substitution intertwines one old doubling step
        # with three new doubling steps on periodic angle words.
        for word in pair:
            image = "".join(AIRPLANE_BITS[int(bit)] for bit in word)
            rotated_input = word[1:] + word[:1]
            image_of_shift = "".join(AIRPLANE_BITS[int(bit)]
                                     for bit in rotated_input)
            assert image[3:] + image[:3] == image_of_shift
        pair = tuple("".join(AIRPLANE_BITS[int(bit)] for bit in word)
                     for word in pair)

    return {
        "schema": "period27-symbolic-marking-v1",
        "scope": "EXACT_SYMBOLIC_MATCH_NOT_CERTIFIED_PARAMETER_RAY_LANDING",
        "parameter_root": f"({C_K}/2^{C_BITS},{C_K+1}/2^{C_BITS})",
        "period": 27,
        "airplane_tuning_substitution": {"0": "011", "1": "100"},
        "scales": scales,
        "real_interval_markov_spine": sorted_markov_spine(orbit),
        "source_reference": "Sodre arXiv:2611.04190v1 sections 2.3 and 2.5",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-json", action="store_true")
    parser.add_argument("--check-manifest", action="store_true")
    args = parser.parse_args()
    report = build_certificate()
    content = json.dumps(report, sort_keys=True, indent=2, ensure_ascii=True) + "\n"
    if args.check_manifest:
        assert MANIFEST.is_file(), f"missing {MANIFEST}"
        assert MANIFEST.read_text(encoding="utf-8") == content, (
            "stale or modified symbolic marking manifest", str(MANIFEST)
        )
    if args.print_json:
        print(content, end="")
    else:
        print("PASS: exact period-27 three-scale candidate marking")
        for n in (3, 9, 27):
            d = report["scales"][str(n)]
            print(f"  angle period {n}, physical return {d['physical_return_time']}:")
            print(f"    angles {d['lower_angle']} and {d['upper_angle']}")
            print(f"    angular = oriented physical kneading = {d['angular_kneading']}")
            print(f"    internal address = {d['internal_address']}")
        spine = report["real_interval_markov_spine"]
        print("  exact invariant real interval [x1,x2], 27 orbit vertices, 26 Markov edges")
        print("  adjacency SHA256:", spine["edge_adjacency_sha256"])
        print("  physical nested return interval ranks:",
              spine["restrictive_interval_vertex_ranks"])
        if args.check_manifest:
            print("  machine-readable manifest matches exact generated data")
        print("BOUNDARY: no ray landing, prime-end transport, sheet/coset atlas, MLC gate")


if __name__ == "__main__":
    main()
