---
ledger: H4_RIGIDITY
result: partial
ai: ChatGPT GPT-6.2
human_review: none
---

# Arithmetic rigidity of the actual postcritical multiplier

<a id="h4-arithmetic-multiplier-rigidity-20261126"></a>

## Claim

Candidate Lean theorems: for any complex algebraic integers c,z, the actual spatial derivative lambda of the n-fold quadratic iterate at z has the form 2^n U with U integral. If its squared complex modulus is rational, it is an integer multiple of 4^n; if nonzero, that rational squared modulus is at least 4^n. In particular it cannot be neutral at positive iteration length. Every critical collision parameter and every point of its postcritical orbit meet the integral hypotheses without a periodicity or repellingness assumption.

The second proof milestone extends the conclusion to every preperiodic point of every algebraic-integer parameter, not merely its critical orbit. For arbitrary integral c, the spatial iterate polynomial over the integral closure of the integers is monic of degree 2^n; its difference at two distinct times is monic and vanishes at the preperiodic point. Transitivity of integrality removes the integral-starting-point assumption. Therefore all periodic cycles, anywhere in the dynamical plane of a critical-collision parameter, are nonneutral. The squared-modulus quantization extends to every preperiodic point, and the fixed point 1 at c=0 attains the exact gap. These are further candidate declarations, subject to the same CI gate.

## Evidence

[QuadraticMultiplierArithmetic.lean](../../formalization/weighted/QuadraticMultiplierArithmetic.lean) develops the actual return derivative via the already formalized recurrence, with explicit integrality of the residual orbit product. Complex conjugation preserves algebraic integrality, so the product U times its conjugate is integral. If rational, it is an integer by integrally closedness of the integers in the rationals. Norm multiplicativity gives the exact factor 4^n. At positive n, a squared modulus equal to one contradicts the nonzero rational gap. The declarations collision_return_deriv_not_neutral and collision_return_deriv_rational_gap use mathlib's actual complex derivative.

The new module is a default target in the pinned mathlib-backed Lake project and all public theorem names are registered. Reproduce with `cd formalization/weighted && lake build QuadraticMultiplierArithmetic`; the existing full CI also audits every declaration's transitive axioms.

Validation: local Lean and network clone are unavailable. This is candidate source pending exact-head CI, not yet counted as a verified theorem.

## Dependencies

H4_RIGIDITY (open); existing QuadraticCriticalTransversality.lean, especially integral_of_collision, orbit_integral and returnMultiplier_hasDerivAt; mathlib's integrality, complex norm, conjugation and derivative lemmas. The local dynamical input is discussed in research/frontier/sharp_boundary_frontier_20261126/MISIUREWICZ.md section 2.

## Boundary

No claim of a modulus lower bound for irrational squared modulus, exclusion of nonzero attracting multipliers in general, full repellingness of all Misiurewicz landings, construction of a local chart, H4, or MLC. The neutral alternative is only one local ingredient of the source's repellingness input. H4 remains open. No ledger status, dependency or checker is changed.

## Attribution

Builds on the archive's quadratic critical-relation transversality development and classical Misiurewicz theory; this is an arithmetic formalization contribution, not a priority claim.
