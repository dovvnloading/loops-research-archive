---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="critical-crossing-deck-20261127"></a>

# Critical-value crossings and deck phase of an actual selected return

## Claim

Candidate complete critical-crossing theorem for the actual one-critical selected return: every continuous target path has a continuous lift for every prescribed starting inverse point, even with infinitely many accumulating critical encounters. Relative to a reference lift, all continuous physical lifts correspond exactly to the relatively clopen phase subsets of the regular-time locus. An open connected excursion inventory with N members gives exactly 2^N lifts; fixing one excursion phase removes exactly one bit. These candidates count as results only after the existing weighted Lean build and transitive dependency audit pass.

## Evidence

The main branch already constructs a one-critical proper degree-two return, its analytic deck involution, and paired continuous lifts for paths avoiding the propagated critical value. This work targets paths meeting that value: the precise freedom to change deck phase at critical encounters, including accumulating encounters, and the resulting criterion for phase-coherent continuation. The actual return factorization is reused. The four registered modules are CriticalPhaseCuts, CriticalPhaseCensus, TelescopeCriticalPhase, and TelescopeCriticalLift. The first two prove the exact choice/census interface; the latter two instantiate it for the actual quadratic iterate and construct arbitrary critical-crossing lifts. The existence proof chooses roots by actual connected components of the nonzero-time set. At every zero, the exact square-root norm identity proves continuity, including at accumulation points. The univalent suffix and prefix transport this construction into the selected physical return component; connectedness proves component retention.

The checkout could not be cloned because the workspace filesystem is full, and no local Lean executable is installed. Development will use the GitHub connection and the repository's existing weighted Lean workflow. Intermediate proof attempts will be committed here; only successful kernel compilation and the existing allowed-dependency audit count as validation.

## Dependencies

MAPPING_TELESCOPE; PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER; RELATIVE_COVER_LIFT; STAGE_FORWARD_CLOSURE. Existing TelescopeDeckRigidity, TelescopeUnbranchedCover, TelescopeMovingDeck, and TelescopePathPairing modules, and contributions/analytic_deck_rigidity_20261126/NOTE.md.

## Boundary

The intended critical-crossing theorem does not construct every native virtual stage cycle or its compatible Jordan cores. The exact native component and marking identifications remain separate. The ledger row remains open unless this work additionally proves those clauses. No claim of MLC or mathematical priority is made. The first proof checkpoint is committed for CI validation; it has no unfilled proof terms, but compilation has not yet been observed.

## Attribution

Builds on the archive's existing analytic deck and selected-return formalization and the Kahn localization/telescope program credited there. AI-generated proof work; no human review.
