---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation, Lean implementation and adversarial review
human_review: none
---

# Convergence of the unrestricted parent Wave supremum

## Claim

This is an early draft investigation. No new compiled theorem or completed progress is claimed yet. The provisional partial designation does not assert that a result has been obtained.

The target is the convergence clause for the unrestricted parent optimum in NOV26_OPEN_OPTIMAL_LIMIT. The November 23 full-path proof explicitly does not prove continuity of the optimizers or convergence of these suprema. Exact values, optimizer attainment, the covering-restricted optimum, and simultaneous child convergence are outside this claim.

## Proposed argument

Normalize by the actual positive return scale d_p. The parent surface is the disk of radius R_p/d_p minus the real slit [x_{2p}/d_p,1], with the two ending atoms over (x_{5p}/d_p,x_{3p}/d_p) and the relative homotopy class around the left tip.

Four real cutpoints converge, and R_p/d_p tends to infinity. A small explicit Lipschitz perturbation of the horizontal coordinate can match every inner mark. It preserves simple leaves, their banks, their full selected homotopy class, and disjointness.

The missing global step is quantitative control of every discarded leaf when truncating a limiting Wave. A density on N disjoint dyadic shells should bound the modulus of all escaping leaves by 3*pi/N. Combining this proved cutoff with proved modulus distortion should give convergence of the complete supremum without assuming an optimizer exists.

These are obligations to prove, not premises to be inserted into an abstract convergence certificate. The actual marked family, its Borel sublaminations, and the connection to the actual critical-orbit sequence must be made explicit.

## Evidence and validation

Implementation is in progress. A result counts only after the relevant Lean theorem compiles in the repository project and unchanged CI, without proof holes or new axioms. Existing baseline checks do not validate this proposed result.

## Dependencies and prior art

- research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md, especially Section 7.2.
- research/tip_family_theorem/THEOREM.md, Open Problem 2.
- The existing actual-tip estimates and finite critical-orbit perturbation bounds.
- The archive's explicit distinction between full-path envelopes, unrestricted marked Wave optima, and covering-restricted optima.

The analytic tools of modulus, bilipschitz transport, and annular cutoff are classical. The intended new result is their fully justified application to convergence of the actual unrestricted marked parent supremum. No worldwide priority claim is made before that result is proved and checked.

## Boundary

The obligation remains open at this checkpoint. No assumption of width transport, native marking identification, or escaping-family control will be counted as a proof of itself. If no genuine result is established, the draft will be closed to release the claim.
