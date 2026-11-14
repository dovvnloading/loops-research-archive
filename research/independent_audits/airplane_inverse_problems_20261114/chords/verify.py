"""Exact recovery of a circular ray set from occupied separations and two counts."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def signed_orbit(n, multiplier=1):
    modulus = (1 << n) - 1
    return frozenset(sign * multiplier * (1 << j) % modulus
                     for j in range(n) for sign in (-1, 1))


def histogram(points, modulus):
    return Counter((x - y) % modulus for x in points for y in points)


def translated(points, delta, modulus):
    return frozenset((x + delta) % modulus for x in points)


def support_completions(points, modulus, anchor):
    """List all sets with the requisite size, support contained in D, and 0,anchor.

    The increasing recursion enumerates each clique exactly once. A branch is
    pruned only when even taking every remaining vertex is insufficient.
    """
    target = len(points)
    allowed = set(histogram(points, modulus))
    require(anchor in allowed and anchor != 0, "invalid anchor")
    candidates = sorted(x for x in allowed - {0, anchor}
                        if (x - anchor) % modulus in allowed)
    completed = set()

    def extend(selected, remaining):
        if len(selected) == target:
            completed.add(frozenset(selected))
            return
        for i, x in enumerate(remaining):
            if len(selected) + len(remaining) - i < target:
                break
            successors = [y for y in remaining[i + 1:] if (y - x) % modulus in allowed]
            extend((*selected, x), successors)

    extend((0, anchor), candidates)
    return candidates, completed


def predicted_anchored(points, modulus, anchor):
    enlarged = points | {0}
    results = set()
    for start in enlarged:
        end = (start + anchor) % modulus
        if end in enlarged:
            base = translated(enlarged, -start, modulus)
            results.update(base - {z} for z in base - {0, anchor})
    return results


def canonical_rotation(points, modulus):
    return min(tuple(sorted(translated(points, -x, modulus))) for x in points)


def crossing_profile(modulus, n, representative):
    orbit = [representative * (1 << i) % modulus for i in range(n)]
    counts = []
    for shift in range(n):
        chords = [sorted((a, -orbit[(i + shift) % n] % modulus))
                  for i, a in enumerate(orbit)]
        counts.append(sum((a < c < b) != (a < d < b)
                          for (a, b), (c, d) in combinations(chords, 2)))
    return counts


def verify_tip(manifest):
    modulus = 511
    points = signed_orbit(9, 228)
    if manifest:
        source = json.loads(manifest.read_text(encoding="utf-8"))
        rows = source["nine_landing_pairs"]
        require(source["first_periodic_landing_phase"] == 10 and len(rows) == 9,
                "manifest phase range mismatch")
        recorded = {pair["phase"]: (Fraction(pair["lower"]), Fraction(pair["upper"]))
                    for pair in rows}
        for i in range(9):
            site = (228 << i) % modulus
            chord = tuple(sorted((Fraction(site, modulus), Fraction(-site % modulus, modulus))))
            require(recorded.get(10 + i) == chord, f"manifest chord mismatch at phase {10 + i}")
    enlarged = points | {0}
    actual = histogram(points, modulus)
    require({d for d, count in actual.items() if count % 2} == points, "odd bins")
    require(Counter(actual.values()) == {18: 1, 2: 90, 3: 18, 4: 18}, "bin histogram")
    vertices, completions = support_completions(points, modulus, 1)
    require(len(vertices) == 43 and len(completions) == 34, "anchored enumeration")
    require(completions == predicted_anchored(points, modulus, 1), "extra completions")
    deletions = {x: histogram(enlarged - {x}, modulus) for x in points}
    require(all(set(counts) == set(actual) for counts in deletions.values()), "new support")
    rotation_classes = {canonical_rotation(enlarged - {x}, modulus) for x in enlarged}
    require(len(rotation_classes) == 19, "coincident rotation classes")

    def indistinguishable(d):
        return {x for x, counts in deletions.items() if counts[d] == actual[d]}

    require(all(indistinguishable(d) for d in range(modulus)), "a single count suffices")
    require(indistinguishable(55) == {55, 456} and indistinguishable(57) == {57, 454},
            "two-count witnesses differ")
    crossings = crossing_profile(modulus, 9, 228)
    require(crossings == [0, 17, 11, 3, 17, 17, 3, 11, 17], "matching mismatch")
    return {"ray_count": len(points), "positive_distance_lengths": (len(actual) - 1) // 2,
            "anchored_extra_candidates": len(vertices), "anchored_completions": len(completions),
            "rotation_classes": len(rotation_classes),
            "single_bin_survivors": {str(d): sorted(indistinguishable(d)) for d in (55, 57)},
            "equivariant_matching_crossings": crossings}


def carry_window_check():
    # Multiply rational signed powers with exponents -4,...,7 by 16.
    powers = {sign * (1 << j) for sign in (-1, 1) for j in range(12)}
    two_sums = {x + y for x in powers for y in powers}
    anchored = two_sums & {144 + x for x in two_sums}

    def in_host(x, centre):
        magnitude = abs(x - centre)
        return magnitude == 0 or magnitude & (magnitude - 1) == 0

    exceptions = {x for x in anchored if not in_host(x, 16) and not in_host(x, 128)}
    expected = {-144, -120, -96, -80, 72, 224, 240, 264, 288}
    require(len(anchored) == 57 and exceptions == expected, "dyadic carry window")
    return sorted(exceptions)


def check_scales(last):
    small = signed_orbit(5)
    witness = {0, 3, 5, 8, 16, 20, 26, 27, 28, 30}
    require(set(histogram(witness, 31)) == set(histogram(small, 31)) == set(range(31)),
            "n=5 counterexample has different support")
    require(all(not witness <= translated(small | {0}, t, 31) for t in range(31)),
            "n=5 counterexample is a deletion")
    for n in range(6, last + 1):
        modulus = (1 << n) - 1
        points = signed_orbit(n)
        anchor = 9
        vertices, actual = support_completions(points, modulus, anchor)
        predicted = predicted_anchored(points, modulus, anchor)
        if n == 6:
            # Here extra cliques can have strictly smaller separation support.
            support = set(histogram(points, modulus))
            actual = {p for p in actual if set(histogram(p, modulus)) == support}
        require(actual == predicted, f"deletion classification failed at n={n}")
        require(len(actual) == 4 * n - 2, f"unexpected count at n={n}")
        if n >= 7:
            require(len(vertices) == 4 * n + 7, f"unexpected candidates at n={n}")
    return [6, last]


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, help="optional archive period27_tip_ray_portrait.json")
    parser.add_argument("--scales", type=int, default=64, help="check every Mersenne scale from 6")
    args = parser.parse_args()
    require(args.scales >= 6, "--scales must be at least 6")
    output = verify_tip(args.manifest)
    output["carry_window_exceptions_times_16"] = carry_window_check()
    output["exhaustive_deletion_classification_n_range"] = check_scales(args.scales)
    print(json.dumps(output, indent=2))
