---
ledger: DIRECT_DECORATION_END_PRIME_END_COFINALITY
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="prime-end-impression-decomposition-20261126"></a>

# Exact angular decomposition of nested physical exterior impressions

## Claim

Candidate Lean theorems replace a single-angle requirement by an exact decomposition of the physical exterior cluster set. Let A_n be nested compact angular footprints and H_n positive decreasing heights tending to zero. For the exterior coordinate map ψ, the physical exterior cluster set is exactly the union, over θ in the limiting footprint, of the localized impressions obtained by intersecting each physical trace with every punctured angular-height neighborhood of θ. No continuity, injectivity, single-sector or interiority premise is needed for this decomposition. Every surviving angle contributes a nonempty localized impression if the initial physical trace has compact closure. If θ is interior at all finite stages, its localized impression equals its ordinary full impression even if other angles survive.

For actual complex cylinders Q_n equal to the closures of their exterior traces, a finite surviving angular footprint, singleton full impressions and preconnected nonempty physical end fiber imply a common singleton impression for every surviving angle and the physical end fiber. This avoids the invalid inference from physical pointness to unique prime end.

## Evidence

Registered weighted Lean module `formalization/weighted/PrimeEndImpressionDecomposition.lean`.

1. `exterior_impression_decomposition`: given a physical cluster point z, close the projections of the pairs in the n-th trace whose physical images have distance less than H_n from z. These are nonempty compact nested sets inside A_n. Their intersection supplies one angle simultaneously compatible with every depth and every physical accuracy. Taking a sufficiently deep stage gives a witness in any prescribed angular wedge arbitrarily close to z. The converse uses monotonicity of closure.
2. `restricted_impression_subset_full` and `restricted_impression_eq_full_of_interior`: the former is inclusion of sets; the latter uses reverse wedge inclusion at the particular angle, not cofinality of the whole trace.
3. `restricted_impression_nonempty`: for a surviving angle the point at half the stage height belongs to the intersected trace and wedge. Compactness of the initial physical closure and nestedness give a nonempty intersection, which meets every localized-impression condition.
4. `finite_landing_footprint_subsingleton`: the decomposition embeds the physical cluster set in the finite range of the singleton full-impression points. Preconnectedness implies subsingletonness, using the existing finite-subset theorem.
5. `physical_end_common_impression`: the physical closure identity transfers the decomposition and pointness to the end fiber. Nonempty localized impressions force all surviving angles' singleton full impressions to be that same point. This does not collapse distinct angular coordinates.

### Actual quadratic regular-closed bridge

The extension `quadratic_exterior_closure_of_regular_closed` proves the physical closure identity from the empty interior of the actual `LoopsDecorationCriticalCycle.filledLocus c` and regular closedness of each puzzle piece: an open ball inside a piece cannot be entirely in the filled locus, so exterior points approach every interior point, and regular closedness gives density in the whole piece. `quadratic_end_exact_decomposition` then identifies the actual physical end as the exact union of localized impressions. `quadratic_end_common_impression_of_sector_cover` derives finite angular rank from the existing finite shrinking sector cover theorem, nesting from the exact exterior trace and closure identities, and nonemptiness and preconnectedness of the physical end by compactness and the directed-carrier theorem. No additional limit connectedness, pointness, or exterior-density premise is needed. The filled-locus empty-interior, regular closedness, genuine chart trace and singleton full-impression hypotheses still have to be supplied in the native dynamical setting.

### Finite impression-contact obstruction

`restricted_impression_closed` proves that each localized impression is closed. `finite_footprint_partition_contact` proves that for any partition of the finite surviving angular footprint into two nonempty parts, some localized physical impressions on opposite sides of that partition intersect. The two finite unions are closed, nonempty and cover the preconnected physical cluster set; absence of contact would disconnect it. Thus the intersection graph on surviving angular coordinates has no nontrivial disconnected partition. No point-landing premise is used. This is a necessary physical contact condition rather than a claim that distinct angles have distinct landing points.

The formal proof is new to this branch; no worldwide originality claim. Local Lean and network git are unavailable, so the existing weighted CI and transitive dependency audit are the compiler of record. These declarations are candidates until the exact-head build and audit succeed. Reproduce with `cd formalization/weighted && lake build PrimeEndImpressionDecomposition`; full weighted CI audits all declarations.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION; PrimeEndSectorFilters.lean, PrimeEndSectorImpressions.lean, PrimeEndSectorRank.lean, StationaryGeometricFibers.lean; research/independent_audits/decoration_end_cofinality_20261126/NOTE.md, sections 2–4; research/mlc_unified/critical_chronology_and_retimed_telescope.md, section 15.2. Uses Mathlib metric closure and nested compactness; finite rank can be supplied by the prior sector rank theorem.

## Boundary

The actual Böttcher chart, exterior trace formula, physical closure identity and ordinary singleton impressions must be proved or supplied for the source-defined pieces. In particular this does not prove all angular footprints finite without their sector census, construct a holomorphic boundary extension, or infer endpoint full impressions from a one-sided trace alone. It does not prove uniform physical shrinking or the false universal whole-trace cofinality clause. No ledger status change requested, no MLC, global LC, or protection claim.

## Attribution

Builds on the archive's November 26 direct-decoration audit, prior Lean sector-filter, impression and sector-rank work, and the Mathlib compactness library. No human review.
