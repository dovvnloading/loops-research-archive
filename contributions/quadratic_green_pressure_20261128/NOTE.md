---
ledger: MLC
result: partial
ai: ChatGPT GPT-6 Astra Pro
human_review: none
---

# Quadratic Green potential and thermodynamic obstruction: working record

Ledger statement being addressed:

> The Mandelbrot set is locally connected.

## Claim

Draft research claim. No new theorem is claimed until it compiles in the unchanged
weighted Lean workflow and passes the transitive axiom audit.

The archive's exact remaining global hypothesis is
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`, the six-clause Universal Protected-Tower
Compactness and Rigidity package for every infinitely renormalizable quadratic
polynomial. Its clauses are canonical protected carriers, exact analytic
realization, a uniformly finite Value-observable response state, a universal
backward transition, coercive marked compactness, and tower rigidity with a
singleton parameter fiber and connected relative neighborhoods.

More precisely, the already proved ledger row `CONDITIONAL_REDUCTION` states
that YOCCOZ plus `H1_MARKED_CONSTRUCTION`, `MBTT`, `H3_COERCIVITY`, and
`H4_RIGIDITY` imply MLC. All four hypotheses remain open. It would therefore
be incorrect to identify H4 alone as the missing theorem. This contribution
leaves that architecture and studies the actual family f_c(z)=z^2+c through
its parameter escape potential.

## Evidence

Initial source audit on main at 6a10209b3cc51878bc45de7668894757b2575e08:

1. `ledger.json`: `CONDITIONAL_REDUCTION`, `UNIVERSAL_PROTECTED_TOWER_CLOSURE`,
   `MBTT`, `H1_MARKED_CONSTRUCTION`, `H3_COERCIVITY`, `H4_RIGIDITY`, `MLC`.
2. `research/mlc_unified/master_transition.md`, sections 6--8.
3. `formalization/weighted/QuadraticEscape.lean` already constructs the actual
   potential G(c)=lim 2^(-n) log(max(1,|f_c^n(c)|)), proves its continuity and
   identifies its zero locus with the bounded critical-orbit locus.
4. `contributions/sharp_escape_exponents_20261126/NOTE.md` and
   `QuadraticEscapeHolder.lean`, `QuadraticEscapeRegularity.lean`,
   `QuadraticEscapeSharpness.lean` already establish a square-root endpoint
   law and better one-sided boundary exponents away from -2. Repeating a
   generic Green-function Holder estimate would not be new progress.

The present execution environment's local command runner fails before executing
commands with a filesystem “No space left on device” error. Repository files are
being read and committed through the GitHub connector. The existing CI is the
authority for Lean compilation; no local success is asserted.

## Dependencies

Existing quadratic escape-potential definitions and proved estimates; mathlib.
External literature and precise theorem dependencies will be recorded with the
final mathematical statement. No new assumptions are added to the Lean kernel.

## Boundary

MLC, every H1--H4 gate, and UPTCR remain open. This draft does not claim a fiber
theorem, a novelty priority, or a completed formal result. The new argument must
concern the actual quadratic family and must avoid marked widths, collars,
protected carriers, mapping telescopes, tip families, abstract metric or
sampling criteria for fibers, arithmetic center denominators, and
critical-orbit encounter-charge or geometric-limit obstructions.

## Attribution

The archive's existing escape-potential formalization is prior work. The
research direction here is potential theory and thermodynamic formalism,
as requested. AI-generated research and formal proof development; no human
specialist review.
