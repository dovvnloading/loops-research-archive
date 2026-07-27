"""Exact diagnostic certificates for the Research Push V audit.

This script checks only finite/topological consequences used to falsify
unsupported inferences.  It is not evidence for an analytic MLC theorem.

Certificates:

1. Two closed arcs on a circle give at most four genuine endpoints and four
   open atoms; the coordinate seam 0=1 is not an extra endpoint.
2. A nested four-rectangle chain has a nonconsecutive active contact:
   shell 1 and shell 3 approach the same arc while shell 2 does not.  Thus a
   one-sided port can reactivate and bypass an intermediate shell.
3. Uncontrolled trace-coordinate conjugacies can destroy norm precompactness
   even when the standardized operator is fixed.
4. A hard pseudoinverse cutoff can discard a legitimate weak Schur mode.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "push5_contact_welding_no_go_20260725.json"


def in_positive_arc(start: Fraction, end: Fraction, value: Fraction) -> bool:
    """Membership in the positively oriented open arc start -> end on R/Z."""
    if start < end:
        return start < value < end
    return value > start or value < end


def circle_atom_certificate() -> dict[str, object]:
    inherited = (Fraction(82, 100), Fraction(12, 100))
    following = (Fraction(5, 100), Fraction(34, 100))
    endpoints = sorted(set(inherited + following))
    atoms: list[dict[str, str]] = []
    labels = {
        (False, False): "common_active",
        (False, True): "outgoing_only",
        (True, False): "incoming_only",
        (True, True): "double_inactive",
    }

    for index, left in enumerate(endpoints):
        right_raw = endpoints[(index + 1) % len(endpoints)]
        right = right_raw if index + 1 < len(endpoints) else right_raw + 1
        midpoint = (left + right) / 2
        midpoint_mod = midpoint % 1
        activity = (
            in_positive_arc(*inherited, midpoint_mod),
            in_positive_arc(*following, midpoint_mod),
        )
        atoms.append(
            {
                "left": str(left),
                "right": str(right_raw),
                "wraps_seam": str(index + 1 == len(endpoints)).lower(),
                "class": labels[activity],
            }
        )

    return {
        "genuine_endpoint_count": len(endpoints),
        "open_atom_count": len(atoms),
        "coordinate_seam_is_extra_endpoint": False,
        "classes": sorted(atom["class"] for atom in atoms),
        "atoms": atoms,
        "passes": (
            len(endpoints) == 4
            and len(atoms) == 4
            and {atom["class"] for atom in atoms}
            == {
                "common_active",
                "outgoing_only",
                "incoming_only",
                "double_inactive",
            }
        ),
    }


Rectangle = tuple[Fraction, Fraction, Fraction, Fraction]
Point = tuple[Fraction, Fraction]


def in_interior(rectangle: Rectangle, point: Point) -> bool:
    left, right, bottom, top = rectangle
    x, y = point
    return left < x < right and bottom < y < top


def in_shell(outer: Rectangle, inner: Rectangle, point: Point) -> bool:
    return in_interior(outer, point) and not (
        inner[0] <= point[0] <= inner[1]
        and inner[2] <= point[1] <= inner[3]
    )


def bypass_certificate() -> dict[str, object]:
    disks: list[Rectangle] = [
        (Fraction(0), Fraction(10), Fraction(0), Fraction(10)),
        (Fraction(1), Fraction(9), Fraction(1), Fraction(10)),
        (Fraction(3), Fraction(9), Fraction(3), Fraction(8)),
        (Fraction(3), Fraction(8), Fraction(4), Fraction(7)),
    ]
    epsilon = Fraction(1, 10)
    right_sample = (Fraction(9) + epsilon, Fraction(5))
    left_sample = (Fraction(9) - epsilon, Fraction(5))
    approaches: list[bool] = []
    for index in range(3):
        outer, inner = disks[index], disks[index + 1]
        approaches.append(
            in_shell(outer, inner, right_sample)
            or in_shell(outer, inner, left_sample)
        )

    # On J={9}x(3,8), shell 1 approaches from the right, shell 3 from the
    # left, and shell 2 from neither side.
    return {
        "contact_arc": "J={9}x(3,8)",
        "shell_approaches_J": {
            "C1": approaches[0],
            "C2": approaches[1],
            "C3": approaches[2],
        },
        "nonconsecutive_contact": approaches == [True, False, True],
        "intermediate_shell_bypass": approaches == [True, False, True],
        "passes": approaches == [True, False, True],
    }


def welding_conjugacy_certificate(dimension: int = 12) -> dict[str, object]:
    if dimension < 6:
        raise ValueError("dimension must be at least 6")
    base = [1 if index % 2 == 0 else 2 for index in range(dimension)]
    swap_targets = [index for index in range(1, dimension, 2)]
    conjugates: list[list[int]] = []
    for target in swap_targets:
        diagonal = base.copy()
        diagonal[0], diagonal[target] = diagonal[target], diagonal[0]
        conjugates.append(diagonal)

    pair_distances = [
        max(abs(left - right) for left, right in zip(a, b))
        for index, a in enumerate(conjugates)
        for b in conjugates[index + 1 :]
    ]
    return {
        "standard_operator_diagonal": base,
        "conjugate_count": len(conjugates),
        "minimum_distinct_operator_norm_distance": min(pair_distances),
        "norm_precompact_uniformly_separated_family_pattern": True,
        "passes": min(pair_distances) == 1,
    }


def pseudoinverse_cutoff_certificate() -> dict[str, object]:
    epsilon = Fraction(1, 10**13)
    cutoff = Fraction(1, 10**12)
    exact_schur_correction = epsilon * (1 / epsilon) * epsilon
    cutoff_schur_correction = Fraction(0) if epsilon < cutoff else exact_schur_correction
    relative_error = abs(exact_schur_correction - cutoff_schur_correction) / abs(
        exact_schur_correction
    )
    return {
        "weak_mode": str(epsilon),
        "hard_cutoff": str(cutoff),
        "exact_schur_correction": str(exact_schur_correction),
        "cutoff_schur_correction": str(cutoff_schur_correction),
        "relative_correction_error": str(relative_error),
        "passes": relative_error == 1,
    }


def main() -> None:
    result = {
        "certificate": "PUSH5_PHYSICAL_CONTACT_AND_WELDING_NO_GO",
        "circle_open_atoms": circle_atom_certificate(),
        "nonconsecutive_bypass": bypass_certificate(),
        "uncontrolled_welding_conjugacies": welding_conjugacy_certificate(),
        "pseudoinverse_cutoff": pseudoinverse_cutoff_certificate(),
        "scope": (
            "exact finite/topological falsification certificates only; "
            "no numerical or combinatorial check proves an analytic MLC obligation"
        ),
    }
    result["all_checks"] = all(
        result[key]["passes"]
        for key in (
            "circle_open_atoms",
            "nonconsecutive_bypass",
            "uncontrolled_welding_conjugacies",
            "pseudoinverse_cutoff",
        )
    )
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    if not result["all_checks"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
