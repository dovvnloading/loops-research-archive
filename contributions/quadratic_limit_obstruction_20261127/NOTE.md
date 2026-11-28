---
ledger: MLC
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

# Quadratic limit obstructions: independent arithmetic and implosion investigation

Ledger statement being addressed:

> The Mandelbrot set is locally connected.

## Claim

Work in progress. This draft claims no new mathematical result yet. Only statements proved
in Lean 4, compiled by the repository CI and audited for permitted axioms will be reported
as results.

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

Next checkpoints will record the exact conditional reduction, literature audit,
precise candidate theorem, and its Lean validation. No result is inferred from
numerics, an abstract model, or the number of compiled declarations.

## Dependencies

The investigation is independent of KKL Waves, marked widths, collars, protected
carriers, mapping telescopes, and tip families. None of these mechanisms will be
used to prove the new result. Abstract metric, sampling, and covering-number
criteria for fibers are also excluded.

## Boundary

MLC and every existing open gate remain open. This draft has not proved any
statement about infinitely renormalizable parameters or any new MLC case.
Novelty must be checked against the literature; a familiar lemma with new naming
will not be described as new mathematics.

## Attribution

The archive and its existing formalizations are credited at their exact paths.
Primary literature and theorem references will be added as the candidate is
selected. No human specialist has reviewed this work.
