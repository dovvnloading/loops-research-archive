---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="quadratic-component-fiber-degree-20261126"></a>

# Actual quadratic component fiber degree and signed inverse census

## Claim

Candidate: for an actual connected component of a finite quadratic pullback of an open connected target, distinguish a single signed inverse sheet from a reflection-invariant double sheet, and obtain exact regular-fiber cardinality through all depths without assuming the target is simply connected.

## Evidence

The registered [QuadraticComponentFiberDegree.lean](../../formalization/weighted/QuadraticComponentFiberDegree.lean) contains six candidate theorems. One reflected pair forces invariance of the entire component; otherwise the first step is injective. The first step maps the localized fiber onto the tail fiber. The exact nonsymmetric count is the tail count; the symmetric count is twice the tail count minus one precisely when the tail fiber contains the critical value. All six statements are pending CI. Local Lean and networked git are unavailable in this environment; exact-head CI must validate the Lean statements.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING. Earlier work: [quadratic cylinder ramification](../quadratic_cylinder_ramification_20261126/NOTE.md), [critical fiber census](../critical_fiber_census_20261126/NOTE.md), [single-fiber exhaustion](../cylinder_fiber_exhaustion_20261126/NOTE.md), and [finite-cylinder commuting lift](../../research/mlc_unified/finite_cylinder_commuting_lift.md), sections 4–5.

## Boundary

No actual virtual marking, target ownership, collar or access metadata, H1–H4 or MLC is asserted. No literature priority is claimed.

## Attribution

Builds on the archive's actual quadratic census and ramification work, and Mathlib.
