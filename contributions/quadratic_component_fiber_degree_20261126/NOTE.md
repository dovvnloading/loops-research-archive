---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="quadratic-component-fiber-degree-20261126"></a>

# Actual quadratic component fiber degree and signed inverse census

## Claim

For an actual connected component of a finite quadratic pullback of an open connected target, distinguish a single signed inverse sheet from a reflection-invariant double sheet, and obtain exact regular-fiber cardinality through all depths without assuming the target is simply connected. Under nested open connected targets the reflection rank is monotone, and equality of the ranks is equivalent to exact preservation of the old selected component inside the enlarged component. Equality of the local inverse fiber at a single target point already detects this preservation, including at critical values.

## Evidence

The registered [QuadraticComponentFiberDegree.lean](../../formalization/weighted/QuadraticComponentFiberDegree.lean) contains 16 public theorems (13 baseline and three enlargement theorems). One reflected pair forces invariance of the entire component; otherwise the first step is injective. The first step maps the localized fiber onto the tail fiber. The exact nonsymmetric count is the tail count; the symmetric count is twice the tail count minus one precisely when the tail fiber contains the critical value. The all-depth `quadratic_component_fiber_card_exact` theorem gives cardinality plus local defect equal to 2 to the power of the number of reflection-invariant steps along the actual component itinerary. At every regular target, the defect vanishes, so this rank is independent of the regular target. The `quadratic_component_univalent_iff_regular_card_one` theorem drops simple connectivity from the earlier selected-component test; the localized version uses the prior proper-localization identification. The thirteen baseline theorems passed the exact-head weighted Lean build and transitive axiom audit at [acc314b849da60bd0fc948395e60e11785d4aad4](https://github.com/dovvnloading/loops-research-archive/commit/acc314b849da60bd0fc948395e60e11785d4aad4), [PR weighted CI 45886350163](https://github.com/dovvnloading/loops-research-archive/actions/runs/45886350163): `AXIOM_AUDIT weighted QuadraticComponentFiberDegree: 52 declarations, 42 theorems; allowed axioms only`; `AXIOM_AUDIT_PASS weighted: 81 modules, 2235 declarations`. The previous run failed three simplification-order sites; the correction changed proof scripts only.

Verified enlargement extension: `componentReflectionRank_mono` proves persistence of invariant steps under arbitrary target enlargement. `quadratic_enlargement_no_merger_iff_fiber_eq` tests whether the enlarged component absorbs any other old component by comparing one actual local fiber, even at critical targets. `quadratic_enlargement_rank_eq_iff_no_merger` reduces this test to equality of reflection ranks at a regular target, without simple connectivity. All 16 theorems passed the exact proof-head build and transitive axiom audit at [abf4df230b2407bb903fa2d7f1b8918694ee34ba](https://github.com/dovvnloading/loops-research-archive/commit/abf4df230b2407bb903fa2d7f1b8918694ee34ba), in both [PR weighted CI 45887195995](https://github.com/dovvnloading/loops-research-archive/actions/runs/45887195995) and [push weighted CI 45887188220](https://github.com/dovvnloading/loops-research-archive/actions/runs/45887188220). Both report: `Build completed successfully (8834 jobs)`; `AXIOM_AUDIT weighted QuadraticComponentFiberDegree: 59 declarations, 49 theorems; allowed axioms only`; `AXIOM_AUDIT_PASS weighted: 82 modules, 2267 declarations`. The audit counts include generated declarations. All 26 workflow runs on that proof commit succeeded, including contribution intake and research validation. The earlier enlargement build at 1bb0559d failed on one target-membership elaboration; abf4df2 fixes the proof script without changing its statement. The final documentation commit does not alter the audited Lean source or registries. Local Lean and networked git are unavailable in this environment; the repository's exact proof-head CI provides the verification.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING. Earlier work: [quadratic cylinder ramification](../quadratic_cylinder_ramification_20261126/NOTE.md), [critical fiber census](../critical_fiber_census_20261126/NOTE.md), [single-fiber exhaustion](../cylinder_fiber_exhaustion_20261126/NOTE.md), and [finite-cylinder commuting lift](../../research/mlc_unified/finite_cylinder_commuting_lift.md), sections 4–5.

## Boundary

This is a partial result toward VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION: the test assumes a specified actual connected pullback component (and properness for the localized formulation). It does not identify the authorized virtual cylinders with those components or establish their target ownership, collar/access metadata, or the required enlargement hypotheses in the archive's full dynamical construction. The ledger obligation, H1–H4 and MLC remain open. No literature priority is claimed.

## Attribution

Builds on the archive's actual quadratic census and ramification work, and Mathlib.
