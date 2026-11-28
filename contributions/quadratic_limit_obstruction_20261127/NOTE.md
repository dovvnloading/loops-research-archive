---
ledger: MLC
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-limit-obstruction-20261127"></a>

# Quadratic limit obstructions: independent arithmetic and implosion investigation

Ledger statement being addressed:

> The Mandelbrot set is locally connected.

## Claim

Work in progress. This draft claims no new validated mathematical result yet. Only statements
proved in Lean 4, compiled by repository CI and audited for permitted axioms will be reported
as results. The selected candidate is an exact arithmetic obstruction for the normalized
return germ at **every exact critical center of period N >= 2**.

Write the actual polynomial return as

    f_c^N(z) = A_N z^2 + B_N z^4 + O(z^6),
    R_N(w) = A_N f_c^N(w/A_N) = w^2 + beta_N w^4 + O(w^6).

The candidate conclusion is that `2^k beta_N` is an algebraic integer **if and only if**
`2N-1 <= k`. A stronger certificate gives an integral numerator with an explicit inverse
modulo two. This would locate an unavoidable arithmetic cost of critical normalization,
even though the original PCF polynomial has integral coefficients. It would obstruct
transporting bounded-denominator arithmetic compactness through this normalization.

The research question is whether arithmetic of the actual family
`f_c(z) = z^2 + c`, or a precise algebraic-versus-geometric limit obstruction from
parabolic implosion, supplies a mechanism independent of the archive's marked-width route.

## Evidence

Initial source audit at main commit `cb37633f2dee57c0bd7dfe7a417823a7067aabfb`:

- `README.md`, “The open frontier”, identifies `UPTCR_IMPLIES_MLC` as the proved
  conditional implication.
- Its missing premise is universal protected-tower compactness and rigidity.
  `UNIVERSAL_PROTECTED_TOWER_CLOSURE` remains open, as do the H1–H4 gates.
- `formalization/weighted/QuadraticCriticalTransversality.lean` already proves
  integrality of critical-collision parameters and parity-based transversality.
- `formalization/weighted/QuadraticMultiplierArithmetic.lean` already proves
  arithmetic restrictions on actual spatial multipliers. These facts will not be
  rebranded as new.

The precise missing hypothesis is `UNIVERSAL_PROTECTED_TOWER_CLOSURE`: the six-clause
Universal Protected-Tower Compactness and Rigidity Proposition for every infinitely
renormalizable quadratic. See `research/mlc_unified/mlc_closure_proposition.md`, section 5,
and `research/mlc_unified/uptcr_cross_validation.md`, Theorem 4.1. The written reduction
is conditional. `ResearchGates.lean` is an abstract specification; it also requires a
separate `TerminalBridge`, not yet instantiated with the actual family.

First implementation checkpoint: `QuadraticCriticalUnits.lean` rederives the classical
dynamical-unit input directly from the actual return recursion. If zero and nonzero z
both return at time N, the even-return factorization `f_c^N(z)=z^2 Q(z)` supplies
`z Q(z)=1`, with integral Q(z). This input is not the novelty claim.

Second implementation checkpoint: the actual polynomial jet, its affine normalization,
the exact denominator, Galois-period rigidity, and the integral-coordinate obstruction are
now stated in the following registered Lean modules, awaiting their combined CI result:

- `QuadraticReturnJet.lean`: actual iterate polynomial and exact sixth-order remainder.
- `QuadraticReturnArithmetic.lean`: exact exponent `2N-1`, noncancellation modulo two,
  Galois invariance of the recovered period, and no uniform denominator for unbounded periods.
- `QuadraticJetConjugacy.lean`: genuine polynomial composition modulo `X^5`; higher terms
  unrestricted; an explicit Böttcher jet exists.
- `QuadraticReturnCoordinateObstruction.lean`: every integral coordinate tangent to the
  identity preserves the quartic denominator, and every Böttcher jet has cubic denominator
  exponent exactly `2N`.

The first critical-unit checkpoint has passed the weighted Lean build in
[run 46105220073](https://github.com/dovvnloading/loops-research-archive/actions/runs/46105220073).
This validates the helper only, not the pending main results.

Local Lean installation failed because the workspace has insufficient disk space for the
pinned toolchain. Repository CI will compile and audit every new declaration. This is
an environment limitation, not a relaxation of the proof standard.

## Dependencies

The investigation is independent of KKL Waves, marked widths, collars, protected
carriers, mapping telescopes, and tip families. None of these mechanisms will be
used to prove the new result. Abstract metric, sampling, and covering-number
criteria for fibers are also excluded.

## Boundary

MLC and every existing open gate remain open. This draft has not proved any
statement about infinitely renormalizable parameters or any new MLC case. The proposed
obstruction concerns the specified normalized germ, not bad reduction of its conjugacy
class: the original iterate still has good reduction. It also does not rule out arithmetic
equidistribution with a new period-dependent normalization or adelic metric.
Novelty must be checked against the literature; a familiar lemma with new naming
will not be described as new mathematics.

## Attribution

The archive and its existing formalizations are credited at their exact paths.
Primary literature and theorem references will be added as the candidate is
selected. No human specialist has reviewed this work.
