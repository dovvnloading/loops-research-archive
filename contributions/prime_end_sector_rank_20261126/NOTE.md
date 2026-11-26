---
ledger: DIRECT_DECORATION_END_PRIME_END_COFINALITY
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="prime-end-sector-rank-20261126"></a>

# Exact finite-lookahead rank of a limiting angular footprint

## Claim

For nested closed angular footprints in a metric space with a uniformly finite cover by pairwise disjoint compact sectors whose diameters tend uniformly to zero, the limiting footprint is finite. At each fixed depth its surviving sector labels are eventually exactly the labels whose sectors still meet a sufficiently deep finite footprint. At every sufficiently fine depth those surviving labels are in bijection with the limiting angles. This gives an exact eventual finite-contact rank, rather than only the previously established upper bound. No effective bound on either horizon is asserted.

## Evidence

In `formalization/weighted/PrimeEndSectorRank.lean`:

1. `live_iff_all_contacts`: compactness identifies a surviving sector by nonempty contacts at every finite depth.
2. `live_census_stabilizes`: each dead sector has a finite witness, and the maximum over the finite label set gives a common lookahead.
3. `limiting_footprint_finite`: an infinite limit would embed an arbitrarily large finite set, contradicting the earlier sector-capacity theorem.
4. `sectors_eventually_separate`: the minimum distance between distinct limiting angles is positive; sufficiently small sectors contain at most one.
5. `live_sector_equiv` and `exact_finite_lookahead_rank`: disjointness, coverage, compactness and shrinking produce an equivalence from finite-horizon contact labels to the limiting footprint. In particular the finite contact count eventually equals the exact number of limiting angles. A depth-zero label can contain multiple surviving tracks, so counting only the original sectors would not generally be exact.
6. `two_surviving_sectors_obstruct`: two disjoint compact sectors with all-horizon contacts obstruct whole-trace cofinality, even if their angles land at the same physical point.
7. `ancestor_sector_subset`, `contact_iff_ancestor_range`, `live_eq_ancestor_survivors`, and `exact_ancestor_rank`: if each child sector lies in its labelled parent, finite geometric contacts are exactly images of the composed backward ancestor maps. At all sufficiently fine depths the eventual rank of those maps equals the limiting angular cardinality. This requires the full nonempty disjoint sector census at each stage, not a symbolic map with unverified geometric containment.

The file is registered in the weighted Lake package, the physical bridge theorem index, and the source inventory following the repository's lean-add registration algorithm. Run `cd formalization/weighted && lake build PrimeEndSectorRank`; the weighted CI workflow additionally audits every declaration's transitive dependencies. The local chat runtime has no Lean installation and cannot clone the repository; this initial proof submission is **unverified pending CI**, not a result counted as established.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION; `PrimeEndSectorFilters.lean`, `PrimeEndSectorImpressions.lean`, `DecorationCriticalCycle.lean`. The motivating native angular geometry is in `research/independent_audits/decoration_end_cofinality_20261126/NOTE.md`, especially sections 3–4. Uses the Mathlib compactness theorem for a directed family of nonempty compact closed sets and the existing finite-sector capacity bound.

## Boundary

This is a conditional metric/angular-sector theorem. It does not construct the native Böttcher coordinate, prove the geometric sector hypotheses for all native puzzles, or establish an effective stopping bound for the contact census. It does not imply that a whole multisector trace is cofinal at one prime end, that any two angles have different impressions, or that MLC or H1 is proved. No ledger change requested. Compilation and the dependency audit must succeed before this contribution counts as a Lean result.

## Attribution

Builds on Matthew Robert Wesney's archive, the Kahn–Lyubich direct-decoration source geometry as analyzed in the dated audit, the prior Lean sector-capacity and angular-transport contributions, and Mathlib's compactness and finite-type libraries. AI assistance: OpenAI GPT-6.2; human review: none.
