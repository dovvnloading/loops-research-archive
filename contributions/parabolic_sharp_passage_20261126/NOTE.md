---
ledger: H2_CALIBRATION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean development and independent AI mathematical review
human_review: none
---

<a id="parabolic-sharp-passage-20261126"></a>

# Sharp accumulation coefficient for the actual period-three parabolic tip family

Ledger statement being addressed:

> QL, WAD, sectorial, and virtual marked coordinates are calibrated on declared interfaces with universal parameters and explicit additive, relative, density-normalized, or discounted errors.

## Claim

Draft research target: prove in the existing Lean project that every sequence of the archive's actual near-minus-seven-fourths shooting tips satisfies
`k * sqrt(t) -> pi / 7`, and consequently
`(p - 6)^2 * (c_p + 7/4) -> 9*pi^2/49`, where `p = 3*(k+2)`.

The archive explicitly leaves this sharp coefficient undetermined in
[the near-parabolic family note](../../research/native_wave_transfer/near_parabolic_tip_family.md).
Its existing family theorem proves only the bounds `1/25 <= (p-6)^2*t <= 900`.
This packet targets the missing limit for that exact family.

## Evidence

Work in progress. The intended proof uses the actual polynomial
`H_t(y) = u - ((u-y^2)^2-u)^2`, `u=7/4-t`,
its parabolic root `a`, rigorous polynomial remainder estimates, and a telescoping arctangent coordinate through the discrete orbit.
The reduced local coefficients are
`A=11/2-2*a^2` and `B=21/2-28*a-14*a^2`; their product is expected to be exactly 49.
That coefficient identity alone is not the claimed passage theorem.

Local Lean is unavailable and the workspace disk is full. The repository's unchanged Lean CI and transitive axiom audit will be the validation authority. No mathematical result is claimed before compilation.

## Dependencies

The existing modules ParabolicChannel, ParabolicTipRate, ParabolicTipShooting,
ParabolicTipFamily, and the Mathlib real calculus and limit library.
The proof will use the actual `Shot` orbit hypotheses; it will not assume the desired asymptotic as a normal-form premise.

## Boundary

This draft does not close H2_CALIBRATION or change the ledger status.
Even the completed sharp rate will concern one actual primitive family near the period-three parabolic root.
Uniform marked-width comparison, native KKL attachment collars, compatible all-scale virtual geometry, and MLC remain open.
Uniqueness of the noncentral shooting root is a separate question and will not be assumed.

## Attribution

The actual reflected channel, shooting construction, disjoint phase theorem, and coarse inverse-square rate are prior archive results.
Classical parabolic passage motivates the arctangent coordinate.
The intended advance is the previously undetermined exact coefficient for the archive's existing actual family, with every new claimed step kernel-checked.
