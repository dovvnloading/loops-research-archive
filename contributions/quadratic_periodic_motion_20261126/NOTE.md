---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

# Local periodic motion and critical-relation coordinates

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

Draft research target, not yet a proved result: construct the actual local complex-analytic continuation of a periodic point of `z ↦ z²+c` when its multiplier differs from one, and combine it with the archive's first-collision transversality to construct a genuine local parameter coordinate. The arithmetic multiplier theorem should discharge the nonparabolic hypothesis at every critical-collision parameter. The intended contribution is a local analytic ingredient of H4, not closure of the global gate.

## Evidence

No new theorem is claimed at this initial checkpoint. Work will be committed here as it is proved in the existing Lean 4.32.0 project under `formalization/weighted/`. Only theorems compiled by the unchanged CI and accepted by its transitive axiom audit will be reported as results.

The starting gap is explicit: `QuadraticCriticalTransversality.landing_motion_identity` and `normalized_entrance_deriv_ne_zero` assume a differentiable moving periodic point. `QuadraticMultiplierArithmetic` excludes neutral periodic multipliers at integral parameters but does not construct the motion. The proposed development joins these existing actual-dynamics results through the complex implicit and inverse function theorems.

## Dependencies

- `QuadraticCriticalTransversality.lean`: actual orbit, return derivatives, first-collision transversality, and the moving-point derivative identity.
- `QuadraticMultiplierArithmetic.lean`: integrality of collision parameters and exclusion of neutral periodic multipliers.
- Mathlib's complex differentiation, implicit function theorem, and inverse function theorem.
- `H4_RIGIDITY` remains open, as does its `H3_COERCIVITY` prerequisite; neither is an assumption of the proposed local theorem.

## Boundary

This draft makes no claim of completed Lean validation. The intended local analytic coordinate does not establish connected relative neighborhoods in the Mandelbrot set, global phase-parameter transfer, marked-tower rigidity, a Koenigs linearization, H4, or MLC. No ledger status change is proposed. Classical implicit-function mathematics is not presented as a new mathematical priority claim.

## Attribution

Builds on the archive's quadratic critical-transversality and arithmetic-multiplier formalizations, including `contributions/h4_arithmetic_multiplier_rigidity_20261126/NOTE.md`, and Mathlib's formal analytic inverse and implicit function theorems. AI-assisted proof construction and independent AI review; no human specialist review has occurred.
