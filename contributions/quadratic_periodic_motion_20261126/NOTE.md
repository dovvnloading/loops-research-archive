---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-periodic-motion-20261126"></a>

# Local periodic motion and critical-relation coordinates

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

First Lean proof milestone: the actual local complex-analytic continuation of a periodic point of `z ↦ z²+c` is constructed when its multiplier differs from one, with local uniqueness in both variables and an exact parameter derivative. The existing arithmetic theorem discharges this multiplier premise at every algebraic-integer parameter, including every critical-collision parameter. The companion coordinate module constructs an analytic local inverse for critical returns and first critical collisions. CI validation is pending at this checkpoint. H4 remains open.

## Evidence

The new default targets are `QuadraticPeriodicMotion`, `QuadraticCriticalCoordinates`, and `QuadraticPeriodicStability` in the existing Lean 4.32.0 Mathlib project. Every public theorem is registered using the repository contribution tool. Only theorems compiled by the unchanged CI and accepted by its transitive axiom audit count as accepted results.

- `periodic_point_motion` constructs an analytic branch through an actual periodic point, proves the full local two-variable root criterion, and computes its derivative as `-returnTangent c z 0 p / (returnMultiplier c z p - 1)`.
- `integral_parameter_periodic_point_motion` and `collision_parameter_periodic_point_motion` remove the multiplier premise using the archive's proved arithmetic results.
- `center_parameter_coordinate` constructs the analytic inverse of every positive critical-return polynomial near each of its zeros.
- `first_collision_parameter_coordinate` constructs a moving periodic point and an analytic local inverse for the actual entrance displacement. Its derivative is the collision derivative divided by the return multiplier minus one; its inverse has the reciprocal derivative. Locally, the original collision is equivalent to zero entrance displacement and to equality with the base parameter.

- `periodic_point_exact_period_stability` and `integral_parameter_periodic_point_stability` preserve the actual minimal period and attracting/repelling type on a neighborhood of the selected cycle; the multiplier varies analytically.

All three modules have compiled locally with the pinned toolchain. The local transitive audit for the motion and stability modules passes with the existing foundational allowlist; full CI and the coordinate-module audit remain to be recorded.

The construction uses the actual orbit recurrences, not an abstract dynamical model. The next checkpoint will record the exact CI revision and any additional local stability results.

The starting gap is explicit: `QuadraticCriticalTransversality.landing_motion_identity` and `normalized_entrance_deriv_ne_zero` assume a differentiable moving periodic point. `QuadraticMultiplierArithmetic` excludes neutral periodic multipliers at integral parameters but does not construct the motion. The proposed development joins these existing actual-dynamics results through the complex implicit and inverse function theorems.

## Dependencies

- `QuadraticCriticalTransversality.lean`: actual orbit, return derivatives, first-collision transversality, and the moving-point derivative identity.
- `QuadraticMultiplierArithmetic.lean`: integrality of collision parameters and exclusion of neutral periodic multipliers.
- Mathlib's complex differentiation, implicit function theorem, and inverse function theorem.
- `H4_RIGIDITY` remains open, as does its `H3_COERCIVITY` prerequisite; neither is an assumption of the proposed local theorem.

## Boundary

This checkpoint makes no claim of completed CI validation. The local analytic coordinate does not establish connected relative neighborhoods in the Mandelbrot set, global phase-parameter transfer, marked-tower rigidity, a Koenigs linearization, H4, or MLC. The neighborhood depends on the selected cycle; no radius uniform over periods is proved. The collision return time need not be minimal. No ledger status change is proposed. Classical implicit-function mathematics is not presented as a new mathematical priority claim.

## Attribution

Builds on the archive's quadratic critical-transversality and arithmetic-multiplier formalizations, including `contributions/h4_arithmetic_multiplier_rigidity_20261126/NOTE.md`, and Mathlib's formal analytic inverse and implicit function theorems. AI-assisted proof construction and independent AI review; no human specialist review has occurred.
