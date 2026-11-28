---
ledger: UNIVERSAL_PROTECTED_TOWER_CLOSURE
result: none
research_status: unsuccessful
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Unsuccessful outlier investigation: no retained new theorem

**Final research outcome: the requested new mathematics was not obtained.** No candidate
passed both the novelty/exclusion screen and the requirement of a proved actual-family
implication to fiber triviality or pointwise MLC. No new Lean theorem was written or
validated. This draft is being closed without merging, in accordance with `AGENTS.md`.
The initial intended `partial` classification has been replaced by `none`: this is an
unsuccessful investigation record, not a completed contribution in any accepted category.

## Claim

No new mathematical claim is submitted. The target was a new criterion or obstruction
for a nontrivial parameter fiber of `f_c(z) = z^2 + c`, with a Lean-proved implication
to fiber triviality or pointwise local connectivity of the actual bounded critical-orbit
locus. The precise candidates and the reasons they were discarded before formalization
are preserved in [REJECTED_CANDIDATES.md](REJECTED_CANDIDATES.md). A classical special
case or a correct theorem with an excluded metric premise was not substituted for the
requested result.

### Exact open hypothesis in the existing reduction

The archive proves the written conditional implication `UPTCR_IMPLIES_MLC`, Theorem 7.2
of [the closure proposition](../../research/mlc_unified/mlc_closure_proposition.md).
Its antecedent is the still-open row `UNIVERSAL_PROTECTED_TOWER_CLOSURE`: the six-clause
Universal Protected-Tower Compactness and Rigidity proposition, for every infinitely
renormalizable quadratic polynomial. Its clauses are canonical carriers, exact analytic
realization, a uniform finite response state, a universal backward transition with its
errors, coercive marked compactness, and tower rigidity with singleton parameter fibers
and connected relative parameter neighborhoods. Section 4 chooses the constants before
the polynomial and tower. Clause 6 includes both the uniform conjugacy/rigidity input
and the neighborhood input; neither follows from a finite model calculation.

This investigation leaves that machinery behind. It does not import KKL Waves, marked
widths, collars, protected carriers, mapping telescopes, or tip-family arguments. It also
excludes abstract metric/sampling criteria, arithmetic denominators of centers,
encounter-charge or geometric-limit obstructions, Green-potential density criteria,
projective cross-ratio jets, mixed two-orbit susceptibility, and two-generator
intertwining rigidity.

## Evidence

### Preliminary rejection tests

1. Singleton fibers imply local connectivity is classical supporting topology, not a
   new candidate. See D. Schleicher, *On Fibers and Local Connectivity of Mandelbrot
   and Multibrot Sets*, arXiv:math/9902155. A criterion must do additional actual-family
   work before applying this implication.
2. A universal strict gap for Thurston pullback spectra cannot be the candidate.
   X. Buff, A. Epstein and S. Koch, *Eigenvalues of the Thurston operator*,
   arXiv:1707.01990, Theorem 4, already gives eigenvalues accumulating on the unit
   circle in unicritical postcritically finite families. Quantitative information
   about a specified degenerating sequence and a proved passage to a parameter
   fiber would both be needed.
3. Existing [mixed susceptibility work](../quadratic_fiber_criterion_20261128/NOTE.md)
   is explicitly excluded. Its classical standalone module
   `QuadraticMonotoneFiberTopology` may supply the final topological implication;
   its two-orbit series is not a proposed new ingredient.

### Completed screening and validation boundary

The [candidate record](REJECTED_CANDIDATES.md) includes the precise universal spectral-gap
statement contradicted by Buff--Epstein--Koch, the unresolved passage from a selected
sequence of marked spaces to an actual fiber, the circular combinatorial-injectivity
criterion, the exact bounded-sequence cohomological calculation and its excluded metric
premise, the nearby classical Cauchy-transform fixed-point theory, and two algebraic
compression criteria that collapse to known or elementary cases.

No screened statement is a retained theorem. No claim is made that the selected-sequence
operator direction is impossible; its essential finite-parameter comparison was not proved.

The local environment was prepared successfully: the official Lean 4.32.0 compiler ran,
the pinned Mathlib cache was obtained, and the existing `QuadraticEscape` target compiled
with `lake build QuadraticEscape`. This verified compiler availability and an existing
module only. A separate blanket-Mathlib import attempt was interrupted and is not recorded
as a successful build. There is no new Lean source, theorem registration, or axiom audit
for this investigation. Documentation intake checks, if green, do not certify mathematics.

The PR records the initial scope, then the candidate rejection audit, then this unsuccessful
outcome as separate commits. No workflow or protected archive status record was changed.

## Dependencies

- Base inspected: `main` at `5e6ef026b3a071416f8dc5cbd9246d0c0add52d1`.
- `UPTCR_IMPLIES_MLC` and `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, for locating the gap only.
- Lean 4.32.0 and the repository's pinned Mathlib project, for any retained theorem.
- The primary classical sources above, used as rejection tests rather than axioms.

## Boundary

No new result, local-connectivity case, canonical quotient construction, or novelty claim
has been established. The user's acceptance criteria have not been met. UPTCR, H1--H4,
and MLC retain their existing statuses. The classical singleton-fiber topology is available,
but the investigation did not find a new actual-quadratic mechanism supplying its singleton
fiber hypothesis. The archive's generic quotient interface also does not construct the
canonical pinched-disk map. This PR must not be cited as a proof, a new reduction, or
progress closing the named ledger obligation.

## Attribution

Classical background is due to the cited authors. The archive and its existing formal
infrastructure are Matthew Robert Wesney's research program and its credited contributors.
OpenAI ChatGPT GPT-6 Astra Pro is conducting the present investigation with parallel
literature, archive, and Lean-environment checks. Human specialist review: none.
