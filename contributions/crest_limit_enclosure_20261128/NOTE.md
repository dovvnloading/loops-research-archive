---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT GPT-6
human_review: none
---

# Rigorous enclosure of the actual four-return crest modulus-ratio limit

## Claim

**Draft target, not yet a theorem.** For the actual selected quadratic
family `ActualTip (n+17) (c n)`, its complete physical circular parent
and all proper four-return descendants as defined in
`ActualCrestTransportLimit`, prove in Lean an explicit two-sided
rational enclosure of the **same** limiting ratio of all-curve moduli,
ideally
```
347/1000 < fullModelCoefficient κ r < 3471/10000,
```
where `κ` is the unique actual limiting relation root and `r` the
unique real terminal endpoint. (The proposed lower target may require
adjustment after strict exact rational checking.)

The archive already proves existence, qualitative convergence and
`1/3 < fullModelCoefficient κ r`, and this work does not count them
as discoveries. The unverified decimal 0.347004986 is not a certificate.
We will only claim a bound after it is compiled by Lean and is
connected to the physical modulus ratio via the existing theorem.

## Evidence

To be filled by committed Lean theorems and unchanged CI run.

## Dependencies

`GlobalCrestLimit`, `ActualCrestTransportLimit`,
`LimitingCrestLimit`, `LoopsLimitingCrestParameter`,
`CrestIntegralLimit`, exact source interval arithmetic and Mathlib.

## Boundary

F17's unrestricted KKL ideal-marking comparison and general Wave
transport remain open. The selected physical circular families are
not substituted for the unrestricted canonical Wave supremum. No
ledger status change, MLC, or H1-H4 is asserted.

## Attribution

Research by OpenAI ChatGPT GPT-6; human review none.
