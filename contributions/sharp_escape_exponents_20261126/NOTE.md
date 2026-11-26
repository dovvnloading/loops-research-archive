---
ledger: H4_RIGIDITY
result: partial
ai: ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="sharp-escape-exponents-20261126"></a>

# Sharp boundary escape exponents for the actual quadratic family

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

Work in progress. The target is a pair of Lean theorems for the existing actual critical-value escape function `QuadraticEscape.parameterEscape`: an explicit boundary exponent strictly greater than one half away from the Chebyshev parameter, and a square-root lower bound at the Chebyshev endpoint proving that the uniform one-half exponent cannot be increased. No theorem is claimed verified until the exact PR revision passes the weighted Lean build and transitive dependency audit.

## Evidence

The starting point is `formalization/weighted/QuadraticExtremalMultiplier.lean`, especially `parameter_escape_improved_scale`, `parameter_gap_base`, and `parameter_escape_half_holder_sq`. The proof work will be added in registered modules in the same Lean project, with progress committed to this PR.

## Dependencies

The existing `QuadraticEscape` and `QuadraticExtremalMultiplier` modules and their mathematical dependencies. The open H3 coercivity and H4 rigidity obligations are not assumed solved. No new unproved mathematical premises will be added.

## Boundary

These estimates concern actual iterates of `z ↦ z^2+c` and their escape potential. They do not construct shrinking connected relative parameter neighborhoods, identify parameter fibers, or prove MLC. `H4_RIGIDITY` remains open. The intended extension is to this archive's verified results; mathematical priority is not asserted.

## Attribution

Builds on `contributions/escape_boundary_stability_20261126/NOTE.md` and the archive's quadratic escape and extremal multiplier formalization. AI-generated mathematics and Lean proof development; no human specialist review.
