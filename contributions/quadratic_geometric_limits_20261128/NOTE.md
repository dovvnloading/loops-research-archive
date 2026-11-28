---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; research, proof development, and adversarial review
human_review: none
---

<a id="quadratic-geometric-limits-20261128"></a>

# Draft: geometric limits of actual quadratic returns

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

Research checkpoint only: no new theorem is claimed yet. The target is a concrete
geometric obstruction or reduction for actual quadratic maps, motivated by the
possible mismatch between ordinary parameter limits and geometric limits of
long returns. The requested result must be a Lean theorem compiled in the
repository's existing CI, without added axioms or proof escapes.

## Evidence

The base is main commit 6a10209b3cc51878bc45de7668894757b2575e08.

The archive's exact missing global package is
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`, quantified over every infinitely
renormalizable quadratic. `UPTCR_IMPLIES_MLC` is conditional on that package.
Its six clauses are canonical construction, analytic realization, uniformly
finite response state, universal backward transition, coercive compactness,
and rigidity with singleton parameter fibers and connected relative
neighborhoods. H1--H4 remain open. The abstract Lean reduction in
`ResearchGates.lean` separately consumes a geometric terminal bridge and the
Yoccoz complement; it is not an instantiation with the actual Mandelbrot set.

This investigation deliberately leaves the archive's Wave, width, carrier,
collar, telescope, and tip-family methods. Abstract metric or sampling
criteria for fibers and arithmetic denominator arguments at centers are
outside its scope. Candidate mechanisms will be checked against the primary
literature and against the actual polynomial f_c(z)=z^2+c.

A sparse source checkout fits in the workspace, but the pinned Lean toolchain
is not installed and there is insufficient local space to install it.
Compilation and the unchanged transitive axiom audit will be judged by the
existing GitHub workflows. No theorem is validated until those checks pass.

## Dependencies

- H4_RIGIDITY: target only, not an assumption.
- `research/mlc_unified/mlc_closure_proposition.md`, section 5.
- `research/mlc_unified/uptcr_cross_validation.md`, section 4.
- `research/mlc_unified/master_transition.md`, M7.
- `ResearchGates.lean` and the ledger are used to identify the frontier.
- Primary literature and actual proof dependencies will be listed when a
  precise theorem has survived review.

## Boundary

This initial checkpoint contains no proved result and makes no novelty claim.
It does not close H4, UPTCR, or MLC, or assume that harmonic-measure nullity
forces a fiber to be trivial. If no substantive theorem survives the
mathematical and Lean checks, the final note will state that fact.

## Attribution

The archive and cited original authors retain credit for all prior
mathematics. The proposed direction follows the user's geometric-limit
question; AI assistance and the absence of human review are disclosed above.
