---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="quadratic-component-fiber-degree-20261126"></a>

# Actual quadratic component fiber degree and signed inverse census

## Claim

CI-verified baseline: for an actual connected component of a finite quadratic pullback of an open connected target, distinguish a single signed inverse sheet from a reflection-invariant double sheet, and obtain exact regular-fiber cardinality through all depths without assuming the target is simply connected.

## Evidence

The registered [QuadraticComponentFiberDegree.lean](../../formalization/weighted/QuadraticComponentFiberDegree.lean) contains 13 baseline theorems and three enlargement candidates. One reflected pair forces invariance of the entire component; otherwise the first step is injective. The first step maps the localized fiber onto the tail fiber. The exact nonsymmetric count is the tail count; the symmetric count is twice the tail count minus one precisely when the tail fiber contains the critical value. The all-depth `quadratic_component_fiber_card_exact` theorem gives cardinality plus local defect equal to 2 to the power of the number of reflection-invariant steps along the actual component itinerary. At every regular target, the defect vanishes, so this rank is independent of the regular target. The `quadratic_component_univalent_iff_regular_card_one` theorem drops simple connectivity from the earlier selected-component test; the localized version uses the prior proper-localization identification. The thirteen baseline theorems passed the exact-head weighted Lean build and transitive axiom audit at [acc314b849da60bd0fc948395e60e11785d4aad4](https://github.com/dovvnloading/loops-research-archive/commit/acc314b849da60bd0fc948395e60e11785d4aad4), [PR weighted CI 45886350163](https://github.com/dovvnloading/loops-research-archive/actions/runs/45886350163): `AXIOM_AUDIT weighted QuadraticComponentFiberDegree: 52 declarations, 42 theorems; allowed axioms only`; `AXIOM_AUDIT_PASS weighted: 81 modules, 2235 declarations`. The previous run failed three simplification-order sites; the correction changed proof scripts only.

Extension (pending exact-head CI): `componentReflectionRank_mono` proves persistence of invariant steps under arbitrary target enlargement. `quadratic_enlargement_no_merger_iff_fiber_eq` tests whether the enlarged component absorbs any other old component by comparing one actual local fiber, even at critical targets. `quadratic_enlargement_rank_eq_iff_no_merger` reduces this test to equality of reflection ranks at a regular target, without simple connectivity. These three are not counted until verified. Local Lean and networked git are unavailable in this environment; exact-head CI must validate the Lean statements.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING. Earlier work: [quadratic cylinder ramification](../quadratic_cylinder_ramification_20261126/NOTE.md), [critical fiber census](../critical_fiber_census_20261126/NOTE.md), [single-fiber exhaustion](../cylinder_fiber_exhaustion_20261126/NOTE.md), and [finite-cylinder commuting lift](../../research/mlc_unified/finite_cylinder_commuting_lift.md), sections 4–5.

## Boundary

No actual virtual marking, target ownership, collar or access metadata, H1–H4 or MLC is asserted. No literature priority is claimed.

## Attribution

Builds on the archive's actual quadratic census and ramification work, and Mathlib.
