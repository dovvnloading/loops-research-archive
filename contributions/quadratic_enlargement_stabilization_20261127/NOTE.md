---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-enlargement-stabilization-20261127"></a>

# Increasing target enlargements: stabilization of actual quadratic component addresses

Ledger statement being addressed:

> After an actual target base is typed or uniquely selected, every demanded finite-cylinder branch image has the open pullback component forced by INTERIOR_PULLBACK_COMPONENT_FORCING, and that reached localized component, or the globally identical component justified by the Jordan-disk component lemma, is one of the declared equal-depth target cylinders at every proof-used intermediate iterate with complete metadata and enlargement stability.

## Claim

Draft research claim, not yet certified: for every actual quadratic map, fixed finite iterate depth, and increasing sequence of connected open target sets with a common anchor, the component partition of the full inverse fiber eventually agrees with the partition over the union. One stage can be chosen simultaneously for all prefix depths. No uniform stabilization stage is asserted.

## Evidence

This draft claims the obligation before implementation, following AGENTS.md. Work will be committed incrementally and only counted after the existing Lean 4.32.0 Mathlib workflow compiles it and audits its proof dependencies.

The new issue is an infinite ascending enlargement chain. Existing QuadraticComponentFiberDegree.lean and QuadraticEnlargementDegree.lean already prove pairwise merger criteria, degree conservation, and finite component censuses. Those results are prerequisites, not new claims here.

Planned proof: identify each component over an increasing open union as the union of its anchored stage components; use finiteness of the actual inverse fiber to obtain one stage realizing every final pairwise connection; apply the existing actual-quadratic component and no-merger theorems. Test the absence of a uniform stage with an arbitrarily delayed merger for the actual map z squared.

Local Lean is unavailable and the workspace filesystem is full; validation will use the repository's existing CI, without modifying its checks.

## Dependencies

- VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION (target; remains open during this draft).
- INTERIOR_PULLBACK_COMPONENT_FORCING.
- FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS.
- Existing QuadraticComponentFiberDegree.lean, QuadraticEnlargementDegree.lean, and QuadraticCylinderCensus.lean.
- Mathlib topology and finite-set results, imported through the pinned repository project.

## Boundary

No closure is claimed at this stage. Even the proposed stabilization theorem does not identify native virtual-Molecule branch images with declared cylinders, construct a proof-use-complete target base, or prove prime-end, deck, and marking metadata. It is a proposed actual-quadratic enlargement theorem for a fixed finite iterate horizon, not a uniform bound in that horizon, a stopping algorithm, or a proof of H1-H4 or MLC.

The ledger and other status records remain unchanged. A final note will state exactly what the compiled theorems establish and what remains open.

## Attribution

The existing archive supplies the actual quadratic component/fiber machinery and finite enlargement conservation laws. This contribution studies their infinite increasing-enlargement limit. General connected-component and finite-set facts are supplied by Mathlib. No novelty beyond this archive is claimed before the proof and prior-work audit are complete.
