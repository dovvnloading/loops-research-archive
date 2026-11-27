---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="critical-crossing-deck-20261127"></a>

# Critical-value crossings and deck phase of an actual selected return

## Claim

Work in progress. This draft claims MAPPING_TELESCOPE for a Lean investigation of the exact critical-crossing residue left by TelescopePathPairing. No theorem or ledger closure is claimed before the existing weighted Lean build and transitive dependency audit succeed.

## Evidence

The main branch already constructs a one-critical proper degree-two return, its analytic deck involution, and paired continuous lifts for paths avoiding the propagated critical value. This work targets paths meeting that value: the precise freedom to change deck phase at critical encounters, including accumulating encounters, and the resulting criterion for phase-coherent continuation. The goal is a theorem about the actual return factorization already defined in the repository, with the previous construction reused.

The checkout could not be cloned because the workspace filesystem is full, and no local Lean executable is installed. Development will use the GitHub connection and the repository's existing weighted Lean workflow. Intermediate proof attempts will be committed here; only successful kernel compilation and the existing allowed-dependency audit count as validation.

## Dependencies

MAPPING_TELESCOPE; PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER; RELATIVE_COVER_LIFT; STAGE_FORWARD_CLOSURE. Existing TelescopeDeckRigidity, TelescopeUnbranchedCover, TelescopeMovingDeck, and TelescopePathPairing modules, and contributions/analytic_deck_rigidity_20261126/NOTE.md.

## Boundary

The intended critical-crossing theorem does not construct every native virtual stage cycle or its compatible Jordan cores. The exact native component and marking identifications remain separate. The ledger row remains open unless this work additionally proves those clauses. No claim of MLC or mathematical priority is made. This initial checkpoint contains no new verified theorem.

## Attribution

Builds on the archive's existing analytic deck and selected-return formalization and the Kahn localization/telescope program credited there. AI-generated proof work; no human review.
