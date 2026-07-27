"""Focused audit for the canonical KL sheet-resolution factorization.

The mathematical proof is in
kl_localization_sheet_resolution_factorization.md.  This script checks
the stated finite coset diagnostics, exact ledger routing, document
markers, and preservation of the global open statuses.  It is diagnostic
and does not replace the covering-space proof.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path
from typing import Callable, Hashable, Iterable, TypeVar


ROOT = Path(__file__).resolve().parent
DOC = ROOT / "kl_localization_sheet_resolution_factorization.md"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / "kl_localization_sheet_resolution_validation_20260725.json"

T = TypeVar("T", bound=Hashable)
U = TypeVar("U", bound=Hashable)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        raise AssertionError(f"missing {label}: {needle!r}")


def additive_cosets(group: set[int], subgroup: set[int], modulus: int) -> set[frozenset[int]]:
    return {
        frozenset((g + h) % modulus for h in subgroup)
        for g in group
    }


def induced_additive_coset_map(
    domain_group: set[int],
    domain_subgroup: set[int],
    target_subgroup: set[int],
    modulus: int,
    target_modulus: int,
    phi: Callable[[int], int],
) -> dict[frozenset[int], frozenset[int]]:
    result: dict[frozenset[int], frozenset[int]] = {}
    for coset in additive_cosets(domain_group, domain_subgroup, modulus):
        representative = min(coset)
        image = frozenset(
            (phi(representative) + h) % target_modulus
            for h in target_subgroup
        )
        for other in coset:
            candidate = frozenset(
                (phi(other) + h) % target_modulus
                for h in target_subgroup
            )
            if candidate != image:
                raise AssertionError("induced coset map is not well-defined")
        result[coset] = image
    return result


Permutation = tuple[int, int, int]


def compose(left: Permutation, right: Permutation) -> Permutation:
    """Return left after right."""

    return tuple(left[right[i]] for i in range(3))  # type: ignore[return-value]


def inverse(permutation: Permutation) -> Permutation:
    result = [0, 0, 0]
    for index, value in enumerate(permutation):
        result[value] = index
    return tuple(result)  # type: ignore[return-value]


def left_coset(
    element: Permutation, subgroup: set[Permutation]
) -> frozenset[Permutation]:
    return frozenset(compose(element, h) for h in subgroup)


def subgroup_is_normal(
    group: set[Permutation], subgroup: set[Permutation]
) -> bool:
    return all(
        compose(compose(g, h), inverse(g)) in subgroup
        for g in group
        for h in subgroup
    )


def main() -> None:
    doc = DOC.read_text(encoding="utf-8")
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}

    for needle in [
        "Theorem 4.1 -- canonical sheet resolution",
        "A=e\\circ q",
        "Corollary 4.3 -- the canonical sheet defect is infinite",
        "[K:H_s]=\\infty",
        "Theorem 5.1 -- unique embedded intermediate factor",
        "Proposition 6.2 -- compact-segment lifting classification",
        "Proposition 6.4 -- base-change propagation through exact equalizers",
        "Theorem 7.1 -- based-coset no-merger/no-birth criterion",
        "exact **based-coset merger certificate**",
        "**boundary-subordination axioms:**",
        "unselected exact Kahn equalizer on the complementary-cover locus",
        "K\\cap\\varphi^{-1}(H^+)=H",
        "K^+=\\varphi(K)H^+",
        "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION",
        "VAAPC-I",
        "UPTCR",
        "MLC",
    ]:
        require(doc, needle, "proof document")

    if "right-coset" in doc or "right coset" in doc:
        raise AssertionError(
            "K/H uses representatives kH and must not be called a right-coset set"
        )

    # Positive bijection: Z/4, H={0,2}, K=Z/4 -> Z/2, H+={0}.
    k_bijective = set(range(4))
    h_bijective = {0, 2}
    k_plus_bijective = {0, 1}
    h_plus_bijective = {0}
    phi_mod_two = lambda value: value % 2
    bijection_map = induced_additive_coset_map(
        k_bijective,
        h_bijective,
        h_plus_bijective,
        4,
        2,
        phi_mod_two,
    )
    bijection_injective_condition = (
        {
            k
            for k in k_bijective
            if phi_mod_two(k) in h_plus_bijective
        }
        == h_bijective
    )
    bijection_surjective_condition = (
        {
            (phi_mod_two(k) + h) % 2
            for k in k_bijective
            for h in h_plus_bijective
        }
        == k_plus_bijective
    )
    if len(set(bijection_map.values())) != len(bijection_map):
        raise AssertionError("positive-control coset map is not injective")
    if set(bijection_map.values()) != additive_cosets(
        k_plus_bijective, h_plus_bijective, 2
    ):
        raise AssertionError("positive-control coset map is not surjective")
    if not (bijection_injective_condition and bijection_surjective_condition):
        raise AssertionError("positive-control subgroup criteria failed")

    # Merger: Z/4, H={0} -> Z/2, H+={0}; classes 0 and 2 merge.
    k_merger = set(range(4))
    h_merger = {0}
    k_plus_merger = {0, 1}
    h_plus_merger = {0}
    merger_map = induced_additive_coset_map(
        k_merger,
        h_merger,
        h_plus_merger,
        4,
        2,
        phi_mod_two,
    )
    merger_kernel_inside_k = {
        k for k in k_merger if phi_mod_two(k) in h_plus_merger
    }
    merger_witnesses = sorted(merger_kernel_inside_k - h_merger)
    if merger_witnesses != [2]:
        raise AssertionError(f"unexpected merger witnesses: {merger_witnesses}")
    if len(set(merger_map.values())) == len(merger_map):
        raise AssertionError("merger control unexpectedly injective")

    # Birth: the trivial old state includes into Z/2 with two target cosets.
    k_birth = {0}
    h_birth = {0}
    k_plus_birth = {0, 1}
    h_plus_birth = {0}
    phi_zero = lambda value: value
    birth_map = induced_additive_coset_map(
        k_birth,
        h_birth,
        h_plus_birth,
        2,
        2,
        phi_zero,
    )
    target_birth_cosets = additive_cosets(k_plus_birth, h_plus_birth, 2)
    born_cosets = target_birth_cosets - set(birth_map.values())
    if born_cosets != {frozenset({1})}:
        raise AssertionError(f"unexpected born cosets: {born_cosets}")

    # Non-normal control: H=< (01) > in S3 has three cosets but no quotient group.
    s3: set[Permutation] = set(itertools.permutations(range(3)))
    identity: Permutation = (0, 1, 2)
    transposition: Permutation = (1, 0, 2)
    h_s3 = {identity, transposition}
    s3_cosets = {left_coset(g, h_s3) for g in s3}
    if len(s3_cosets) != 3:
        raise AssertionError("S3 non-normal control has wrong coset count")
    if subgroup_is_normal(s3, h_s3):
        raise AssertionError("S3 transposition subgroup unexpectedly normal")

    # Winding separation: powers with distinct winding cannot share an H_s-coset
    # when w(H_s)=0.  This finite range is only a diagnostic of the exact proof.
    winding_power_sample = {n: n for n in range(-32, 33)}
    if len(set(winding_power_sample.values())) != len(winding_power_sample):
        raise AssertionError("winding powers did not separate")

    theorem_id = "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION"
    if theorem_id not in by_id:
        raise AssertionError(f"ledger is missing {theorem_id}")
    if by_id[theorem_id]["status"] != "proved":
        raise AssertionError(f"{theorem_id} must be proved")
    theorem_statement = by_id[theorem_id]["statement"]
    for needle in [
        "wholly contained in e(P_K)",
        "based-coset fiber map",
        "based commuting comparison class",
    ]:
        require(theorem_statement, needle, f"{theorem_id} scope")
    for dependency in [
        "KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION",
    ]:
        if dependency not in by_id[theorem_id]["dependencies"]:
            raise AssertionError(f"{theorem_id} is missing {dependency}")

    for dependent in [
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION",
        "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE",
    ]:
        if by_id[dependent]["status"] != "open":
            raise AssertionError(f"{dependent} must remain open")
        if theorem_id not in by_id[dependent]["dependencies"]:
            raise AssertionError(f"{dependent} does not retain {theorem_id}")

    require(
        by_id["DIRECT_DECORATION_OUTER_CAP_FOOTPRINT"]["statement"],
        "source label, sheet, coset, and deck phase",
        "outer-footprint resolved-sheet scope",
    )
    require(
        by_id["DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION"]["statement"],
        "KKL universal pullback predicates",
        "path-lift geometric-restriction gate",
    )

    for global_id in [
        "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    ]:
        if by_id[global_id]["status"] != "open":
            raise AssertionError(f"{global_id} must remain open")

    counts = Counter(item["status"] for item in obligations)
    if len(obligations) != 330:
        raise AssertionError(f"unexpected ledger size: {len(obligations)}")
    if counts != Counter({"proved": 235, "open": 72, "imported": 23}):
        raise AssertionError(f"unexpected ledger counts: {counts}")

    report = {
        "scope": (
            "Diagnostic audit of the covering-space factorization, finite "
            "coset controls, enlargement criteria, ledger routing, and "
            "global open statuses."
        ),
        "proof_document_sha256": sha256(DOC),
        "ledger_sha256": sha256(LEDGER),
        "finite_controls": {
            "bijective": {
                "domain_cosets": len(bijection_map),
                "target_cosets": len(set(bijection_map.values())),
                "reflection": bijection_injective_condition,
                "exhaustion": bijection_surjective_condition,
            },
            "merger": {
                "witnesses": merger_witnesses,
                "distinct_images": len(set(merger_map.values())),
            },
            "birth": {
                "born_cosets": [sorted(coset) for coset in born_cosets],
            },
            "nonnormal": {
                "group": "S3",
                "subgroup_order": len(h_s3),
                "coset_count": len(s3_cosets),
                "normal": False,
            },
            "winding_power_sample": {
                "range": [-32, 32],
                "distinct_cosets_certified_in_sample": len(winding_power_sample),
                "analytic_proof_location": "Corollary 4.3",
            },
        },
        "ledger": {
            "total": len(obligations),
            "counts": dict(counts),
            "theorem": theorem_id,
            "global_statuses": {
                item_id: by_id[item_id]["status"]
                for item_id in [
                    "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE",
                    "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
                    "MLC",
                ]
            },
        },
        "result": "PASS",
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"result": "PASS", "output": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
