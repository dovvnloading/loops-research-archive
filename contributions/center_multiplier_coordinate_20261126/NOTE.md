---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="center-multiplier-coordinate-20261126"></a>

# Multiplier coordinates at exact-period quadratic centers

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

Work in progress. The target is a Lean theorem for every exact-period center of the actual family f_c(z)=z^2+c: construct its analytic periodic-point motion, prove that the multiplier along that motion has nonzero parameter derivative, and construct an analytic inverse multiplier coordinate. A result is accepted only after the repository's Lean CI build and transitive proof-dependency audit pass.

## Evidence

The initial checkpoint claimed the unclaimed H4_RIGIDITY obligation before proof work. The first proof milestone adds QuadraticCenterMultiplier.lean, with the exact initial-factor decomposition, the derivative formula along a moving critical point, the periodic-motion tangent identity, and the all-period nonvanishing argument. The second milestone adds QuadraticMultiplierIteration.lean and QuadraticMultiplierCoordinate.lean: a constructed local analytic inverse of the actual first-return multiplier, persistence of the same attracting exact-period cycle, and the simultaneous normal form t^k for every repeated return. Repetitions k >= 2 are also proved to have zero parameter derivative at the center and no differentiable local left inverse. These proof candidates are pending the repository's CI compilation; no result is counted before that succeeds.

For period p=n+1, the intended exact derivative formula is

    lambda'(c) = 2 * P_p'(c) * (f_c^n)'(c),

where P_p(c)=f_c^p(0)=0 and all earlier positive critical iterates are nonzero. The proof will combine actual periodic motion with an explicit multiplier factorization and the existing center-transversality theorem. The inverse must concern the same constructed motion.

Local Lean is unavailable: the pinned toolchain download exhausted workspace storage and did not finish. CI will be the compilation authority. No toolchain, workflow, trust policy, or status record will be weakened.

## Dependencies

- QuadraticCriticalTransversality.lean: actual iterates, tangents, and center transversality.
- QuadraticPeriodicMotion.lean: analytic motion of the actual periodic point.
- QuadraticPeriodicStability.lean: analyticity of the actual multiplier and exact-period persistence.
- QuadraticCriticalCoordinates.lean: existing analytic inverse-function proof pattern.
- H4_RIGIDITY and its H3_COERCIVITY prerequisite remain open; neither is assumed by the proposed local theorem.

## Boundary

The target is a local theorem in the ambient complex parameter plane at each exact-period center. It does not prove a global multiplier uniformization, a uniform radius over periods, a parameter chart at parabolic or indifferent points, connected relative neighborhoods for arbitrary Mandelbrot parameters, H4, UPTCR, or MLC. No ledger-status change is requested.

## Attribution

Builds on the archive's quadratic periodic-motion and arithmetic-transversality contributions, and Mathlib's analytic implicit- and inverse-function theorems. The mathematical multiplier-coordinate principle is classical; no worldwide novelty or priority claim is made. No human specialist review has occurred.
