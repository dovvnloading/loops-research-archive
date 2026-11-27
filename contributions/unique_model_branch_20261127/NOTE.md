---
ledger: KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="unique-model-branch-20261127"></a>

# The unique branch point of the actual quadratic monotone model

## Claim

Work in progress. The target is the critical-point identification clause of
KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION. The existing
StationaryLightModel development constructs an involution on the monotone
model but explicitly leaves open whether its fixed locus is just the
projected physical critical point.

This packet aims to prove that identification for the actual filled set
of z squared plus c with empty interior, and to derive the exact model
inverse-fiber census. No result is counted before Lean compilation and
the repository's transitive dependency audit succeed.

## Evidence

The new theorem will be registered in the existing Mathlib-backed Lean
project. The local workspace filesystem is full and has no Lean executable;
the unchanged repository workflows are the compilation and trust judge.

## Dependencies

StationaryLightModel, StationaryMonotoneGeometry, StationaryCompactContact,
and the actual quadratic filled-set definitions. Prior work:
contributions/stationary_model_degree_20261126/NOTE.md, especially its
explicit boundary on the involution fixed locus.

## Boundary

The full ledger obligation remains open while the exact KKL/Kiwi
projection, selected geometric continua and native carrier lift are not
identified. Empty interior and the monotone semiconjugacy will be explicit
hypotheses, not new proof constants. This draft proposes no ledger status
change and makes no claim about H1-H4 or MLC.

## Attribution

Builds on Matthew Robert Wesney's research archive and its prior Lean
development of monotone model dynamics. AI assistance: OpenAI GPT-6 Astra
Pro. Human review: none.
