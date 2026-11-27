---
ledger: KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="unique-model-branch-20261127"></a>

# The unique branch point of the actual quadratic monotone model

## Claim

This draft now contains 24 public Lean theorem declarations addressing the critical-point identification clause of
KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION. The existing
StationaryLightModel development constructs an involution on the monotone
model but explicitly leaves open whether its fixed locus is just the
projected physical critical point.

The proposed proof identifies that fixed locus for the actual filled set
of z squared plus c with empty interior. For a nontrivial connected model
it also identifies the unique failure of local injectivity. At every depth
and every model target, including non-singleton geometric fibers, the
exact inverse cardinal N_n satisfies

N_(n+1)(y) + [G^n(p(c)) = y] = 2 N_n(y).

Equivalently, N_n(y) + D_n(y) = 2^n, where D_0=0 and
D_(n+1)=2D_n+[G^n(p(c))=y]. Full binary cardinality holds exactly
off the finite projected postcritical set. This supplies an exact
exhaustion test for a proposed finite inverse census.

These statements are unverified pending Lean compilation and the
repository's transitive dependency audit.

## Evidence

The new modules StationaryUniqueBranch, StationaryBranchLocus, and
StationaryBranchCensus are registered in the existing Mathlib-backed Lean
project, with all public theorem names in the source index. The local workspace filesystem is full and has no Lean executable;
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
