---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; collaborative proof development and verification
human_review: none
---

<a id="telescope-deck-monodromy-20261127"></a>

# Actual return monodromy and the deck-phase closure criterion

Ledger statement being addressed:

> Every actual finite virtual stage cycle admits compatible selected relative-cover lifts that are embedded on relatively compact Jordan cores, preserve the full component and deck-phase route, and retain the propagated critical value after the unique quadratic stage, so that the planar critical-spine compiler produces a closed degree-two selected return.

## Claim

Draft claim under development: determine the endpoint sheet permutation of loops in an actual one-critical quadratic return, connect it to the central square, and prove its compatibility with path composition and deformation. Only compiling Lean theorems will be counted as results. No theorem is claimed verified in this initial checkpoint.

## Evidence

The starting point is the existing actual return in `TelescopePathPairing.lean`: an injective prefix, the critical quadratic step, and an injective suffix on actual connected pullback components. Its two path lifts are already proved. The explicit boundary of `contributions/analytic_deck_rigidity_20261126/NOTE.md` leaves loop endpoint permutation and monodromy open. This packet targets that boundary rather than reproving the existence of those lifts.

The first source checkpoint contains three candidate modules, all registered with the existing strict build. These are pending compiler verification and are not yet counted as results:

- `PathExcursionCensus.lean` constructs binary words of complete source paths and proves an exact all-lifts census from a singleton base fiber and an exhaustive one-excursion classification.
- `TelescopeCriticalExcursions.lean` constructs the physical critical excursion using the actual analytic prefix inverse applied to the central bump `4rt(1-t)`, together with its negative. The suffix transports their common squared path to the actual target. It classifies all lifts of that one excursion.
- `TelescopeLoopMonodromy.lean` constructs actual regular loops from central half-turn circles and determines the endpoint sheet of every lift. It also rules out a continuous global section on the whole regular target.

The connection from the exact finite census to repeated actual critical excursions is the next proof step. Successful local and CI checkpoints will be recorded separately from draft source.

## Dependencies

Target: `MAPPING_TELESCOPE`. Existing Lean inputs: `TelescopePathPairing`, `TelescopeUnbranchedCover`, `TelescopeDeckInvolution`, and the actual `QuadraticEscape.orbit`. The proof uses the pinned Lean/Mathlib project and will add no mathematical axioms.

## Boundary

The draft does not claim every native virtual stage supplies the selected physical components, injective prefix and suffix, relative-cover realization, or compatible Jordan cores. These are genuine clauses of `MAPPING_TELESCOPE`; the ledger stays open unless all are established. No MLC conclusion or priority claim is made. The intended monodromy theorem is about the actual quadratic iterate under the displayed component hypotheses, not a replacement formal model.

## Attribution

The archive's saturated telescope, ramification, univalent collar, parameter-stable return, and analytic deck-rigidity contributions supply the previously verified foundations. Classical covering-space theory supplies the general path-lifting mechanisms through Mathlib; the new work sought here is their exact binding to the physical return's phase and central quadratic branch.
