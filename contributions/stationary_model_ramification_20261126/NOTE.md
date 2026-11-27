---
ledger: KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="stationary-model-ramification-20261126"></a>

# Exact ramification census for geometric quadratic models

## Claim

Draft research claim, not yet a verified result. The target is an exact inverse-level ramification census for every target of a light monotone geometric quotient of the actual quadratic filled set, including nonsingleton physical target fibers.

The current archive proves upper bounds at arbitrary targets and exact counts at singleton anchors. This work aims to derive the unique model critical fiber from physical planar fullness, then remove the singleton-anchor restriction in the census. The critical-fiber identification itself has a written antecedent in the stationary non-LC audit; the all-target census and its consequences are the proposed increment.

## Evidence

First proof checkpoint: `StationaryCriticalFiber.lean` contains the proposed physical critical-fiber recognition and exact one-step predecessor census; `StationaryRamificationCensus.lean` contains the proposed all-depth census, weighted critical defect, and exact loss under semiconjugacy. Both are registered in the pinned Mathlib project. They are candidate proofs until local and CI compilation and the transitive dependency audit succeed. The geometric argument reuses the existing compact bypass theorem rather than reproving planar logarithm theory.

## Dependencies

Existing StationaryLightModel, StationarySeparatorTransport, quadratic filled-set fullness, and QuadraticCriticalFiberCensus. Earlier work: the stationary non-LC predecessor-lift and fiber-saturation audits, and the selected-predecessor endpoint source.

## Boundary

The exact named KKL/Kiwi projection, selected carrier equality, marked small-Julia correspondences, and access identification remain to be constructed. This draft does not claim the full ledger obligation, H1-H4, or MLC. No ledger status change is requested at this stage.

## Attribution

Builds on the archive's actual quadratic dynamics and stationary quotient theory. The planar critical-fiber argument has an existing written antecedent; no priority claim is made for classical plane topology or finite ramification arithmetic. The intended contribution is the strengthened geometric model theorem with all hypotheses explicit and Lean kernel validation.
