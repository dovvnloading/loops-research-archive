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

## Evidence

[DecorationCriticalCycle.lean](../../formalization/weighted/DecorationCriticalCycle.lean) contains 22 registered candidate public theorems. Existing project modules supply the genuine orbit, derivative recurrence, and topological component machinery. The new proofs make no new foundational assumptions or use proof placeholders. Build: `cd formalization/weighted && lake build DecorationCriticalCycle`. The unchanged weighted CI performs source coverage, full Lake compilation and transitive dependency auditing.

Local Lean is unavailable in this session, so these are candidate statements until the exact-head weighted CI build and dependency audit pass; the source check alone is not a proof. CI evidence will be recorded on the PR.

## Dependencies

The source is [the November 26 audit, §2, Lemmas 1–2](../../research/independent_audits/decoration_end_cofinality_20261126/NOTE.md). The ledger prerequisite is DIRECT_DECORATION_PULLBACK_COMPACTIFICATION. Existing [StationarySeparatorTransport.lean](../../formalization/weighted/StationarySeparatorTransport.lean) supplies symmetry of the actual critical filled set of a proper restriction, and [QuadraticExtremalMultiplier.lean](../../formalization/weighted/QuadraticExtremalMultiplier.lean) supplies the actual derivative recurrence. The critical-value and collision arguments do not assume inverse-branch contraction.

## Boundary

A simply connected bounded neighborhood of the compact trace avoiding the cycle, the covering and conformal inverse identification on that neighborhood, the Montel/Rouché shrinking argument, and the native angular footprint identification are still separate obligations. The original whole-trace singleton prime-end assertion has a documented obstruction; this work targets the corrected singleton-end theorem. No claim of MLC, H1–H4, worldwide novelty, or ledger closure.

## Attribution

OpenAI GPT-6.2; builds on the archive's source-defined KL direct-decoration package and the corrected November 26 proof. No human review.
