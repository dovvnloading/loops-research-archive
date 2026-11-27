---
ledger: TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="actual-physical-period-20261127"></a>

# Exact physical phase separation for constructed quadratic tips

## Claim

Work in progress. This draft targets the missing physical iterate identification in the actual near-minus-two quadratic family: all intermediate phases, the least eventual period, and the critical entrance time. A final claim will be made only for Lean declarations that compile and pass the repository axiom audit.

## Evidence

Baseline: main `e66d25b2a8497448714379bcb283bd448d75bcc4`.

The archive constructs `ActualTip p c`, a proper central p-return and a proper canonical 3p-return. It separates three phases for f^p but leaves exact physical periods and the source branch identification open. The intended proof retains the positive inverse shooting itinerary, proves that every intermediate physical iterate leaves the small parent disk, and uses that exclusion to lift phase separation from f^p to f.

### First compiled milestone

`ActualTipItinerary.exists_actual_tip_with_itinerary` retains the actual positive inverse shooting witness from the archived parameter construction, for every p >= 17.

`ActualFirstReturnSeparation.actual_first_return_exclusion` proves that the entire physical disk of radius (23/20) times the positive critical return value has all intermediate iterates of norm greater than 1, for every 1 <= j < p. The initial disk radius is less than 1/100. The proof compares the complete polynomial iterate with the exact positive inverse critical itinerary; it does not truncate the iterate or assume the required separation. Supporting theorems give uniform orbit shadowing below 1/100 through time p and a lower bound 7/5 on the intermediate real critical orbit.

Both modules compile locally with the pinned Lean 4.32.0 runtime. Their CI and transitive axiom audit results will be recorded after this checkpoint. Exact physical period and connected filled-core work is in progress.

## Dependencies

Existing `NearTwoShooting`, `NearTwoTip`, `ThreeReturnRealization`, and `UniformThreeReturnRenormalization`; pinned Lean 4.32.0 and Mathlib. The open native binder is a target, not a theorem assumed by the proof.

## Boundary

No ledger closure is claimed at this draft checkpoint. Native KKL marked proper paths, prime-end markings, source q/w gates, skip witnesses, and uniform response charge are not supplied by the current archive. Exact physical phase and period theorems alone do not settle those requirements, H1-H4, UPTCR, or MLC.

## Attribution

The existing parameter, collar, and three-phase constructions are credited to the archive modules above. This work addresses their documented physical-period boundary and does not claim those earlier results as new. AI-assisted proof development and review; no independent human review.
