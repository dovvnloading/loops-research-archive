---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Actual quadratic local ramification and multiplicity conservation

## Claim

Work in progress. The intended theorem connects the already formalized local critical order of the actual quadratic iterate with the intrinsic degree of an actual connected pullback component. For f(z)=z²+c, an open connected target V, n ≥ 0, a point x with f^[n](x) in V, and any y in V, the goal is to prove that the sum over actual inverse points z in the selected component of 2 raised to the number of critical encounters before time n is exactly 2 raised to that component's reflection rank. Critical target values are included. No result is claimed until Lean compilation and the transitive axiom audit succeed.

## Evidence

Draft opened before proof implementation to claim the obligation. Planned source: formalization/weighted/QuadraticLocalRamification.lean. Existing QuadraticCriticalWindow proves exact local factorization; QuadraticComponentFiberDegree and QuadraticEnlargementDegree prove distinct-point fiber accounting. The missing bridge is a sum of the actual local ramification orders over the actual inverse fiber, followed by componentwise critical ramification accounting.

Validation will use the pinned Lean 4.32.0 project, default-target registration via code/contribute.py lean-add, repository contribution checks, and the weighted CI build with its transitive axiom audit. Proof placeholders, new axioms, and trust escapes are forbidden.

## Dependencies

Ledger prerequisites: DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING. Lean dependencies under review: QuadraticCriticalWindow, QuadraticComponentFiberDegree, QuadraticEnlargementDegree, and their Mathlib imports.

## Boundary

This contribution targets an actual polynomial component theorem, not the native virtual-cylinder realization. Identification of the authorized virtual demand family, target bases, localization, marked accesses, chronology, sheet metadata, and root-enlargement certificates remains open. The ledger row stays open. H1–H4, UPTCR and MLC are not proved. No literature priority claim.

## Attribution

Builds on the archive's quadratic critical-window, component-fiber-degree, and enlargement-degree contributions and Mathlib. Exact theorem dependencies and verified statements will be recorded as the proof develops.
