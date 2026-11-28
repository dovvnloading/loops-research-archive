---
ledger: NOV26_OPEN_WINDOW
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation, Lean proof development, and independent AI review
human_review: none
---

# Global primitive-window investigation

Ledger statement being addressed:

> Global primitive-component uniqueness: Local p=3..12 seed intervals and signed p>=13 chart do not prove full maximal-real-component uniqueness (F02).

## Claim

Work in progress. No new theorem or closure is claimed at this initial checkpoint.
The target is global localization and uniqueness of the signed critical relation
on a precisely defined full primitive parameter window, rather than another
certificate inside an assumed small parameter chart.

## Evidence

The initial source inspection distinguishes the following existing results:

1. The November 16 all-period note proves unique simple roots in an explicit
   signed near-minus-two chart, with a parameter asymptotic and a derivative
   lower bound. Reproducing that argument is not the proposed contribution.
2. `NearTwoShooting.lean` constructs a positive-inverse shooting chart and
   proves uniqueness of the parameter for each prescribed terminal value.
3. `NearTwoTip.lean` constructs actual signed tips in a broader parameter
   enclosure, but does not identify the whole maximal primitive window or
   prove uniqueness there.

The investigation will first determine the exact hypotheses that distinguish
the intended window from other roots of the same polynomial relation. A
candidate result counts only after its Lean theorem compiles in the unchanged
repository CI and passes the existing transitive dependency audit. No
unproved result is presented as mathematical progress.

## Dependencies

- `NOV26_OPEN_WINDOW` and `NOV26_TIP_THEOREM` in `ledger.json`.
- `research/tip_family_theorem/AUDIT.md`, finding F02.
- `research/tip_family_theorem/THEOREM.md`, parameter-chart convention.
- `research/independent_audits/real_primitive_tip_family_all_p_20261116/NOTE.md`.
- `formalization/weighted/NearTwoInverse.lean`, `NearTwoProduct.lean`,
  `NearTwoShooting.lean`, and `NearTwoTip.lean`.

## Boundary

This is an early draft claim of an open research target. It contains no new
proved mathematical result yet. The ledger remains unchanged. No local
certificate is to be promoted to global window uniqueness, and no classical
kneading-uniqueness theorem is to be relabeled as new mathematics. Any final
result must state its actual dynamical objects, hypotheses, and remaining
gap. If the attempt produces no substantive new theorem, this draft will be
closed rather than submitted as a successful contribution.

## Attribution

The selected family, signed relation, prior local uniqueness, and quantitative
near-minus-two chart belong to the existing archive. The classical quadratic
dynamics literature will be checked before making any novelty claim.
