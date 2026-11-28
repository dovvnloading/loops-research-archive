---
ledger: NOV26_OPEN_SAT_WAVE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; proof search, Lean implementation and adversarial review
human_review: none
---

<a id="near-parabolic-return-shape-20261127"></a>

# Near-parabolic physical return shape: investigation

Ledger statement being addressed:

> Satellite/near-parabolic canonical transfer: The refused primitive v1 types supply neither a complete satellite canonical Wave nor an attachment angular electrode for the three near-parabolic tips.

## Claim

This is an initial draft claim, not a theorem or a completed partial result. The investigation targets the actual near-parabolic quadratic family `LoopsParabolic.Shot`, with physical return length `p=3*(k+2)`, and asks whether its normalized full return stays a definite distance from every normalized quadratic model. The intended result is a uniform quantitative physical obstruction, not the elementary fact that a finite polynomial iterate has higher degree.

The target will count only if a substantive new theorem is proved in the repository's Lean project and passes the unchanged CI build and transitive axiom audit. No result or worldwide novelty is claimed at this checkpoint.

## Evidence

Baseline main: `fe12f2a86cab3be5d610fcf37781c3ea5e8c3c64`.

The initial archive audit has checked the existing all-period primitive near-parabolic family, exact critical portraits, phase separation, complex pullback-component isolation and inverse-square parameter bounds. These are established dependencies, not new contributions. Existing finite nonquadratic coefficient results and the currently open center-arithmetic PR must not be repackaged as a new obstruction.

The next proof task is to derive a period-independent lower bound for a higher normalized jet or a direct finite-point shape defect using the actual two channel flights. A Cauchy coefficient estimate would then turn a jet bound into a complete-disk approximation obstruction. Failure to obtain an actual uniform lower bound is a failure of this proposed route, not evidence that the ledger obligation is false.

The local workspace filesystem was already full when cloning was attempted, and no Lean executable is available on its PATH. The GitHub connector is available; candidate proofs will be committed here and judged by the existing CI. No workflow or audit rule will be altered.

## Dependencies

- `NOV26_OPEN_SAT_WAVE` and its prerequisites `NOV26_SAT_V2`, `NOV26_NEAR_PARAB`.
- [Existing near-parabolic family](../../research/native_wave_transfer/near_parabolic_tip_family.md).
- [Actual family theorem](../../formalization/weighted/ParabolicTipFamily.lean).
- [Two-flight shooting data](../../formalization/weighted/ParabolicTipShooting.lean).
- [Actual channel bounds](../../formalization/weighted/ParabolicTipRate.lean).
- [Complex physical component](../../formalization/weighted/ParabolicComplexComponent.lean).
- [Chosen one-slit contract and refusals](../../research/native_wave_transfer/SPECIFICATION_v1_1.md).
- [Satellite contract](../../research/native_wave_transfer/SPECIFICATION_v2_satellite.md).

## Boundary

No compiled new theorem has been obtained. No canonical Wave, attachment electrode, width transfer, impossibility theorem, or closure of this ledger row is claimed. Even a successful obstruction to quadratic approximation would exclude only that specific transfer strategy and would not rule out a correctly marked near-parabolic construction.

All ledger statuses remain unchanged. If the investigation yields no substantive theorem, this draft will be closed to release the obligation, as required by the repository contribution rules.

## Attribution

The physical family, shooting construction and prior bounds belong to the existing archive. Parabolic implosion and analytic coefficient estimates are classical; any eventual contribution must distinguish its actual quantitative statement from those imported principles. Research and review are AI-assisted by OpenAI ChatGPT, GPT-6 Astra Pro. No human mathematical review has occurred.
