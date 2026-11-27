---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-inverse-atlas-20261126"></a>

# Analytic inverse atlases and coherent actual-cylinder transport

## Claim

This draft claims the obligation before proof development.
The result being developed is a complete analytic inverse-branch atlas for actual
quadratic iterates over an open simply connected target avoiding the finite
postcritical set, with exact component exhaustion, intermediate-iterate
compatibility, and coherent restriction under regular target enlargement.

No new theorem is claimed as verified at this initial checkpoint.
The result will count only after the repository's Lean build and transitive
foundational-dependency audit pass.

## Evidence

Proof development is in progress in registered modules inside
formalization/weighted, using the pinned Lean and Mathlib. The following
complete proof scripts are committed for compiler verification:

- QuadraticRegularInverse constructs canonical analytic inverses on full
  actual components, proves their exact derivatives, and classifies continuous
  lifts from any nonempty preconnected source space by their initial value.
- QuadraticInverseBranches constructs the actual-fiber/component equivalence,
  the exhaustive analytic atlas, coherent fiber rebasing, and the exact 2^n
  census of entire continuous lifts. Distinct lifts differ at every point.
- QuadraticInverseTransport proves residual-clock and concatenation identities,
  agreement under regular target enlargement, and same-clock target-component
  selection from actual base-image containment and one anchor. The target-sheet
  containment is derived rather than assumed.

These are candidate proofs pending the unchanged full compiler and dependency
audit. A further parameter-local complete analytic atlas is under development.

Existing component univalence and fiber cardinality results are prerequisites;
the new construction must coordinate all analytic sections and their actual
component addresses.

## Dependencies

Ledger context: DIRECT_DECORATION_PULLBACK_COMPACTIFICATION,
FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, and
INTERIOR_PULLBACK_COMPONENT_FORCING.

Formal prerequisites: QuadraticCylinderCensus, QuadraticCriticalFiberCensus,
QuadraticCylinderRamification, QuadraticComponentFiberDegree, and
TelescopeConformalInverse.

Earlier work reviewed includes the cylinder-fiber exhaustion, critical-fiber
census, critical-window obstruction, cylinder-ramification, and component-fiber
degree packets, together with the finite-cylinder commuting-lift source.

## Boundary

The full native obligation stays open. Regular simply connected targets
must be supplied; no claim is made that every native virtual stage has them.
The work does not identify authorized marked cylinders, boundary accesses,
obstacles, cross-base ownership, or prime-end metadata. No MLC, H1-H4, or
UPTCR conclusion and no priority claim over classical mathematics is made.

## Attribution

Builds on the archive's actual quadratic component and ramification theorems
and Mathlib. Proof development and review are AI-assisted. Human review: none.
