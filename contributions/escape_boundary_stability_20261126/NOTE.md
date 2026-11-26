---
ledger: H4_RIGIDITY
result: partial
ai: ChatGPT GPT-6.2
human_review: none
---

# Exact-base nonlinear shadowing and boundary escape-potential modulus

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

Candidate Lean estimates for the actual quadratic map: for a reference parameter c with parameterEscape c = 0, the critical-value potential at a nearby parameter d satisfies G(d)^2 <= 32 (log 4)^2 |d-c| if |d-c| <= 1/2. The more precise discrete-scale estimate uses A(c)=4-|c+2|^2/576, with 3 <= A(c) <= 4: if 2 A(c)^n |d-c| <= 1, then G(d) <= 2 log(4) / 2^n. The growth base improves away from the Chebyshev endpoint. The declarations are candidates until CI verifies them; no priority assertion.

## Evidence

In `formalization/weighted/QuadraticExtremalMultiplier.lean`:

1. `orbit_difference_step`: retain the quadratic error in the exact difference of two physical iterates.
2. `orbit_perturbation_bound`: absorb parameter forcing by adding the parameter difference to the orbit error. For x=A^n epsilon <= 1, induct with error at most x+x^2; A>=3 permits the quadratic correction at the next scale, without increasing A.
3. `escape_perturbation_scale`: the perturbed iterate lies in the radius-four disk, then the previously checked potential approximation error gives the scale bound.
4. `parameter_gap_base`, `parameter_escape_at_growth_scale`, `parameter_escape_improved_scale`: exploit the existing three-point Chebyshev rigidity inequality to decrease A.
5. `parameter_escape_base_four`, `parameter_escape_half_holder_sq`: select the last scale before 4^n times the input error exceeds one. This gives the squared one-half Hölder estimate with explicit constant.

Reproduction: from the repository root, run `cd formalization/weighted && lake build QuadraticExtremalMultiplier`. The unchanged weighted workflow builds the registered library and audits every compiled declaration against the existing foundational allowlist. No local Lean toolchain or network clone is available in this session; remote CI is the judge. Until its build and transitive audit complete, this is an unverified draft.

## Dependencies

The existing kernel modules QuadraticEscape and QuadraticExtremalMultiplier, especially the uniform approximation error, the radius-two orbit bound, and the three-point parameter-defect estimate. Mathlib ordered-field and norm inequalities. The H4 rigidity gate itself depends on H3_COERCIVITY, which is not assumed solved here.

## Boundary

One-sided quantitative escape control relative to the actual bounded-critical-orbit locus is not a proof of diameter decay for puzzle pieces, connected relative neighborhoods, singleton parameter fibers, or MLC. No H4 or other ledger status changes. The sharper discrete scales are not a claim of the optimal pointwise exponent at any non-Chebyshev parameter. The proposed bounds do not assert the converse estimate at general parameters.

## Attribution

Built on the archive's existing quadratic escape and extremal multiplier formalization, and classical quadratic Green-potential theory. AI-generated proof development, with no human specialist review or mathematical priority claim.
