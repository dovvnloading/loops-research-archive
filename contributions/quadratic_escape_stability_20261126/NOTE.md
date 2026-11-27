---
ledger: H3_COERCIVITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

# Actual quadratic escape stability and compact limits

Ledger statement being addressed:

> Bounded calibrated potentials and the uniform normalized incidence and congestion hypotheses prevent degeneration of the analytic carriers, branch graphs, relative-cover structures, protected prime ends, response forms, and Value features, so every sequence has a subsequence converging to an admissible nondegenerate marked renormalization. Exact side memory is handled topologically by H3_SYMBOLIC_SIDE_COMPACTNESS, but compact encodings alone do not establish analytic admissibility.

## Claim

Work in progress. This draft investigates analytic and parameter stability of the
actual quadratic escape potential and its compact sublevels, as a partial result
toward the analytic compactness interface of H3_COERCIVITY. No new mathematical
result is claimed at this initial checkpoint.

## Evidence

The base revision is `7c50921352b9f9855e7a3e4e68ed7866b07be79b` on `main`.
The existing `QuadraticEscape.lean` constructs the actual potential from finite
iterates and proves a uniform tail bound and joint continuity.
`QuadraticEscapeFullness.lean` supplies actual compact full dynamical sublevels.
This packet will record exact Lean theorem names and CI results as the proofs
are completed. Only compiled declarations passing the repository's transitive
dependency audit will be counted as results.

## Dependencies

The target is the still-open H3_COERCIVITY obligation, stated at M6 in
`research/mlc_unified/master_transition.md`. The prior packet
`contributions/h3_planar_fill_limit_20261126/NOTE.md` handles planar filling and
its one-sided stability. The present investigation concerns actual polynomial
dynamics. Existing Lean definitions, proofs and pinned Mathlib dependencies
will be named precisely in the completed evidence section.

## Boundary

H3_COERCIVITY remains open. Stability of an escape potential or its sublevels
does not by itself preserve the native marked carriers, relative covers,
protected prime ends, response forms, or all-scale renormalization geometry.
No status change and no worldwide mathematical novelty are claimed.

## Attribution

Matthew Robert Wesney's research archive, its existing quadratic escape and
planar compactness developments, and the pinned Lean/Mathlib libraries.
OpenAI GPT-6 Astra Pro assists with proof development and verification.
No human mathematical review has been performed in this session.
