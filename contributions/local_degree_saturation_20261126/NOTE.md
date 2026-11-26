---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; proof development, Lean implementation, and independent AI review
human_review: none
---

<a id="local-degree-saturation-20261126"></a>

# Local sheet exhaustion for actual quadratic return carriers

## Claim

This draft develops local sheet exhaustion for actual complex quadratic iterates.
The intended conclusion is that a compact embedded copy of a quadratic filled
set, conjugating its intrinsic quadratic dynamics to an actual finite quadratic
return with matching local critical encounters, is relatively open and closed
in its entire ambient inverse image. A connected copy is consequently an entire
connected component of that inverse image.

Only declarations accepted by the existing Lean build and transitive dependency
audit will count as results. This implementation checkpoint is awaiting CI.

## Evidence

1. `formalization/weighted/QuadraticLocalNormalForm.lean` constructs an injective
   open neighborhood at every critical-free finite orbit. At an orbit with exactly
   one critical encounter it constructs analytic injective source and target
   coordinates making the actual finite return exactly the square map. It derives
   at most two distinct local inverse points, and a singleton at the critical target.
2. In progress: construct all nearby intrinsic inverse points using complete
   invariance and openness. Their images must exhaust the ambient local fiber.
3. In progress: derive the local critical compatibility from primitive phase
   separation, then specialize the exhaustion theorem to actual quadratic returns.

Lean 4.32.0 and Mathlib v4.32.0 are pinned by the repository. The current local
environment has no Lean executable and insufficient disk capacity to install it.
The unchanged weighted Lean CI build and kernel dependency audit are the judge.
No workflow or audit is weakened.

## Dependencies

The implementation uses the archive's `QuadraticUnivalentNeighborhood`,
`TelescopeConformalInverse`, `StationaryFiberDynamics`, and
`QuadraticEscapeFullness` modules for compactness, complete invariance, open maps,
and analytic inverse construction. No new mathematical postulate is introduced.

The target ledger prerequisites remain
`KKL_NATIVE_TERMINAL_HUBBARD_TREE`,
`KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE`, and
`KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN`.

## Boundary

The ledger obligation remains open. Section 3.2 of
`research/independent_audits/stationary_fiber_saturation_20261126/NOTE.md` states
a general branched-cover exhaustion lemma; section 3.3 applies it to induced
Kiwi plane maps. A theorem for actual quadratic polynomials and finite iterates
does not identify those quotient maps with polynomials. The KKL projection,
geometric small-Julia correspondence, selected full-preimage equalities, and
marked access compatibility remain separate requirements.

No straightening, polynomial-like recognition, full monotone fiber saturation,
native Wave estimate, H1-H4, or MLC theorem is claimed. This is a formal
specialization of the existing local analytic argument, not a claim of priority
over classical complex dynamics.

## Attribution

The local exhaustion argument is credited to the stationary fiber-saturation
note, section 3.2. Existing compact-univalence and analytic-inverse proofs are
reused directly. Earlier geometric-fiber, monotone-lift, and filled-set-fullness
packets were checked to avoid duplicating their results. New proofs and this
note are contributed under the repository's CC0 license.
