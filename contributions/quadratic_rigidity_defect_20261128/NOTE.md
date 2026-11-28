---
ledger: H4_RIGIDITY
result: REPLACE
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-rigidity-defect-20261128"></a>

# Critical-orbit projective residue — active draft

## Claim

Candidate, stated before formalization: for the actual quadratic family
f_c(z)=z²+c in the main-cardioid multiplier parameter
c(λ)=λ/2−λ²/4, let x_j(λ)=f_c(λ)^j(0) and, for k≥1, let

R_k(λ)=x_(3k)(x_k−x_(2k))/(x_k(x_(3k)−x_(2k))).

Proposed statement: R_k(λ)=−λ^(−k)−3/4+O(λ) as λ→0, for every k≥1.
The constant finite term is independent of the clock k.
An exact polynomial-unit factorization will replace the asymptotic notation
in the Lean statement. A possible consequence is an explicit leading-bias
correction for the adjacent-clock quotient R_k/R_(k+1).

This is a candidate under proof and novelty checks, not a proved claim.

## Evidence

Starting main snapshot: f05f1b9dc8f5fc6eeb68491da2eb44eca6d6cec9.
The earlier unsuccessful investigation is preserved in PR #266.

The candidate comes from normalizing the actual critical orbit around its
fixed point λ/2. The normalized recurrence is
y_0=−1/2, y_(j+1)=λ(y_j+y_j²).
Its critical first step and its secant products contribute different finite
corrections to the projective observable.

The simpler census of pole orders has been rejected as a novelty claim:
existing multiplicity theorems for quadratic critical relations already
supply it. The present candidate concerns the normalized finite residue and
its exact cancellation, not those orders.

## Dependencies

The archive's terminal written reduction assumes the still-open
UNIVERSAL_PROTECTED_TOWER_CLOSURE (UPTCR). Its last clause already includes
singleton full marked parameter fibers and shrinking connected relative
parameter neighborhoods. No such clause is assumed to establish the new
candidate.

Primary-source comparisons, exact candidate revisions, and compiled theorem
names will be recorded here as the work develops.

## Boundary

No MLC case, fiber-triviality theorem, or global rigidity gate is closed.
This draft is an investigation of a local actual-quadratic projective
obstruction. It does not infer a fiber theorem from a local computation.
No Lean theorem is claimed at this checkpoint.

The investigation excludes the marked-width machinery and the other
directions excluded in the user's original mandate.

## Attribution

OpenAI ChatGPT GPT-6 Astra Pro assists with proof search, primary-source
comparison, formalization, and adversarial review. No human specialist
review has occurred.
