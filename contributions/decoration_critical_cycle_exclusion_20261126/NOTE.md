---
ledger: DIRECT_DECORATION_END_PRIME_END_COFINALITY
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="decoration-critical-cycle-exclusion-20261126"></a>

# Critical-cycle exclusion and unramified neighborhoods for actual quadratic decoration cylinders

## Claim

Formalize and strengthen the critical-cycle exclusion step of the November 26 corrected direct-decoration singleton-end theorem. All maps in the Lean module are actual complex quadratic iterates. The phase sets are forward images of the critical little filled set P and the cycle union is indexed by Fin r. A first-step collision in P and surjectivity of the return onto P are sufficient to force a collision in every phase by time r. In particular no degree-one-tail assumption is required. For phase i>0, a collision is forced already at time r-i+1.

An injective closed puzzle cylinder at time n≥r cannot meet the cycle if its cycle-facing frontier consists of iterated preimages of a fixed point alpha. It suffices that P and f(P) are disjoint, rather than pairwise disjointness of all phases. The fixed point and all its preimages are excluded from the forward-invariant cycle, and a connected phase meeting a frontier-free cylinder lies entirely in it, contradicting the collision.

The analytic companion characterizes the critical values of every f^n exactly as {f^k(0): 1≤k≤n}; it proves both directions using algebraic closure and the derivative recurrence. Consequently the entire complement of the compact cycle is a common open neighborhood of the deep cylinder free of critical values of every iterate. Also, every inverse image of a target bounded by R≥1+|c| is bounded by the same R, uniformly in n; the inverse image of a compact target is compact.

The analytic extension targets an actual proper regular covering, seeded holomorphic inverse sections on simply connected open domains, and uniform shrinking on every compact subset of a fixed bounded connected domain of inverse sections. Its new limit argument avoids image stability: each fixed forward iterate of a pointwise inverse limit is bounded by the common escape radius, so the limit image belongs to the actual filled set. Empty interior and open mapping force constancy; Cauchy's estimate and ultrafilter compactness supply normality directly. These new statements are candidates pending CI.

## Evidence

[DecorationCriticalCycle.lean](../../formalization/weighted/DecorationCriticalCycle.lean) contains 32 registered public theorem statements, of which the first 22 passed the exact-head weighted kernel and dependency checks at b2230015; the 10 analytic extensions await the new CI run. Existing project modules supply the genuine orbit, derivative recurrence, and topological component machinery. The new proofs make no new foundational assumptions or use proof placeholders. Build: `cd formalization/weighted && lake build DecorationCriticalCycle`. The unchanged weighted CI performs source coverage, full Lake compilation and transitive dependency auditing.

The first checkpoint passed [weighted CI run 45868921234](https://github.com/dovvnloading/loops-research-archive/actions/runs/45868921234): full kernel build and dependency audit, plus contribution and coverage checks. Local Lean is unavailable; the added analytic statements must pass the same exact-head checks before being counted.

## Dependencies

The source is [the November 26 audit, §2, Lemmas 1–2](../../research/independent_audits/decoration_end_cofinality_20261126/NOTE.md). The ledger prerequisite is DIRECT_DECORATION_PULLBACK_COMPACTIFICATION. Existing [StationarySeparatorTransport.lean](../../formalization/weighted/StationarySeparatorTransport.lean) supplies symmetry of the actual critical filled set of a proper restriction, and [QuadraticExtremalMultiplier.lean](../../formalization/weighted/QuadraticExtremalMultiplier.lean) supplies the actual derivative recurrence. The critical-value and collision arguments do not assume inverse-branch contraction.

## Boundary

A simply connected bounded neighborhood of the compact trace avoiding the cycle, agreement of the seeded inverse section with the native puzzle branch on that trace, and the native angular footprint identification remain separate obligations. The new covering and Rouché-free shrinking statements are not credited until CI. The original whole-trace singleton prime-end assertion has a documented obstruction; this work targets the corrected singleton-end theorem. No claim of MLC, H1–H4, worldwide novelty, or ledger closure.

## Attribution

OpenAI GPT-6.2; builds on the archive's source-defined KL direct-decoration package and the corrected November 26 proof. No human review.
