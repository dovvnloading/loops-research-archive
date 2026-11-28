---
ledger: UNIVERSAL_PROTECTED_TOWER_CLOSURE
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Outlier investigation: an actual-quadratic criterion with a proved MLC implication

**Draft research record. No new theorem or successful Lean validation is claimed at this stage.**
The `partial` field reserves the intended contribution category; the mathematical acceptance
conditions below have not yet been met.

## Claim

The target is a new sufficient criterion or obstruction for a nontrivial parameter fiber of
the actual family `f_c(z) = z^2 + c`, together with a Lean-proved implication to triviality
of that fiber or pointwise local connectivity of the bounded critical-orbit locus.
A candidate will be stated and compared with primary literature before its formalization.
An implication obtained just by renaming a known rigidity or local-connectivity theorem
does not satisfy this investigation.

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

No candidate has passed the novelty gate yet. Research and proof updates will be committed
to this draft PR as they become concrete. No numerical experiment is being called proof.

## Dependencies

- Base inspected: `main` at `5e6ef026b3a071416f8dc5cbd9246d0c0add52d1`.
- `UPTCR_IMPLIES_MLC` and `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, for locating the gap only.
- Lean 4.32.0 and the repository's pinned Mathlib project, for any retained theorem.
- The primary classical sources above, used as rejection tests rather than axioms.

## Boundary

No new result, local-connectivity case, canonical quotient construction, or novelty claim
has been established in this initial commit. UPTCR, H1--H4, and MLC retain their existing
statuses. A retained result must compile under the existing CI and pass its transitive
axiom audit, and the Lean conclusion must itself include the MLC-relevant implication.
An honest unsuccessful investigation will remain identified as such; a draft record is
not a completed mathematical contribution.

## Attribution

Classical background is due to the cited authors. The archive and its existing formal
infrastructure are Matthew Robert Wesney's research program and its credited contributors.
OpenAI ChatGPT GPT-6 Astra Pro is conducting the present investigation with parallel
literature, archive, and Lean-environment checks. Human specialist review: none.
