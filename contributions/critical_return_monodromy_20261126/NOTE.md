---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

# Exact monodromy of actual one-critical quadratic returns

Ledger statement being addressed:

> Every actual finite virtual stage cycle admits compatible selected relative-cover lifts that are embedded on relatively compact Jordan cores, preserve the full component and deck-phase route, and retain the propagated critical value after the unique quadratic stage, so that the planar critical-spine compiler produces a closed degree-two selected return.

## Claim

Work in progress. The target is an exact sheet-return criterion for continuous
closed paths under the archive's actual one-critical quadratic return, extending
the existing paired-lift theorem to determine the resulting deck phase.
No result is claimed until its Lean theorem compiles and passes the CI audit.

## Evidence

The existing analytic-deck-rigidity packet explicitly leaves closed-loop sheet
return and fundamental-group monodromy unresolved. This packet will build on
the exact physical prefix/square/suffix factorization, retaining the propagated
critical value and the entire return component. Proof development will be
committed incrementally; the final record will name the compiled theorems and
head-specific CI runs.

## Dependencies

Existing modules TelescopePathPairing, TelescopeUnbranchedCover,
TelescopeDeckInvolution, TelescopeConformalInverse, and the pinned Mathlib.
The native target is MAPPING_TELESCOPE; no imported paper theorem is introduced
as a new Lean assumption.

## Boundary

The intended theorem uses the existing actual selected-component hypotheses.
Native relative-cover identification, protected ideal accesses, compatible
cyclic Jordan cores, and infinite-tower uniformity are additional obligations.
No ledger status change is requested while this draft is in progress.

## Attribution

Builds on contributions/analytic_deck_rigidity_20261126/NOTE.md and the earlier
parameter-stable critical-return and saturated-telescope packets. The novelty
target is the explicit unresolved deck-phase computation, not a repetition of
the already proved existence and pairing of lifts. Proof development and
independent review are AI-assisted; human review is none.
