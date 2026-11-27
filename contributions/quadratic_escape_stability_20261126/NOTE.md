---
ledger: H3_COERCIVITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-escape-stability-20261126"></a>

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
Only compiled declarations passing the repository's transitive dependency audit
will be counted as results.

### Checkpoint 1: whole-orbit parameter shadowing (CI pending)

`formalization/weighted/QuadraticOrbitShadowing.lean` supplies five candidate
theorems: `quadratic_preimage_near`, `finite_orbit_shadow`,
`infinite_orbit_shadow`, `filled_orbit_shadow`, and
`large_parameter_orbit_shadow`. A reference quadratic orbit with every point
of norm at least two has, for every new parameter d, an actual forward orbit
within norm(d-c) at every time. If the reference orbit is bounded, so is the
shadow. The existing large-parameter geometry verifies the separation
hypothesis for every point of K_c when norm(c) is at least eight.

The proof chooses a square-root sign to halve backward error, constructs
arbitrary finite shadows, and intersects their nested nonempty compact
initial-point sets. Local registration and proof-source scans pass. Local
Lean compilation is unavailable: the mandatory pinned compiler artifacts and
Mathlib cache exceed this workspace's free disk capacity. GitHub Actions
compilation and its transitive dependency audit remain the acceptance gate.

### Checkpoint 2: structural conjugacy and harmonic escape (CI pending)

`QuadraticJuliaStability.lean` proposes a global Hausdorff bound
`hausdorffDist (filled c) (filled d) <= norm(d-c)` when both parameter norms
are at least eight. At parameter distance at most one it constructs a
homeomorphism intertwining the actual quadratic maps, with the same error
bound at every forward time. Uniqueness follows from the exact difference
factorization and expansion in the shadow tube. Continuity follows from
compactness of the closed all-time shadow relation.

`QuadraticEscapeHarmonic.lean` proposes a normally convergent analytic
logarithmic correction on the far exterior, proves its exact equality with
the existing escape potential by telescoping, and transports it to every
escaping analytic parameter/point family. The intended consequences are
phase and parameter harmonicity, real analyticity, and the circle mean-value
identity. These declarations are proof candidates until CI accepts them.

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
