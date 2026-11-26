---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

# Univalent open collars of actual quadratic telescope cores

## Claim

Work in progress. The target is to prove in Lean that an actual finite quadratic
iterate, injective on a compact selected pullback component and with no
preterminal critical encounter there, is injective on an open neighborhood of
that component. Combining this with the existing proper-component perturbation
theorem should give open univalent selected restrictions over sufficiently small
target collars. No result is claimed until its Lean theorem compiles in CI and
passes the repository's transitive axiom audit.

## Evidence

This initial checkpoint claims the obligation before proof development.
Planned proof: compact local-to-global injectivity, actual noncritical quadratic
orbit local injectivity, and selected-component collar recognition. All theorem
names, hypotheses, reproduction commands, and CI evidence will be recorded as
the proofs are completed.

## Dependencies

Research target: MAPPING_TELESCOPE. Existing formal inputs:
TelescopeCollarRecognition, TelescopeRamification, SaturatedTelescope, and the
pinned Mathlib. The ledger prerequisites PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER,
RELATIVE_COVER_LIFT, and STAGE_FORWARD_CLOSURE describe the research context;
their documentary status will not be imported as mathematical assumptions.

## Boundary

This work addresses a conditional actual-map collar construction. The native
virtual-molecule core, its univalence and critical avoidance, compatible cyclic
Jordan domains, marked relative-cover lifts, and complete deck-phase route
remain to be constructed. No closure of MAPPING_TELESCOPE, H1, or MLC is claimed,
and no ledger status change is requested. No priority claim over classical
complex analysis or topology is intended.

## Attribution

Builds on contributions/saturated_telescope_20261126 and
contributions/telescope_ramification_order_20261126, especially the actual
proper-component upper semicontinuity theorem in TelescopeCollarRecognition.
Proof development and adversarial review are AI-assisted; no human review.
