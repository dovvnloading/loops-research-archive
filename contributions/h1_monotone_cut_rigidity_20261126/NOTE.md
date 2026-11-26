---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="h1-monotone-cut-rigidity-20261126"></a>

# Nonconstant monotone dynamical quotients of the actual Chebyshev carrier

Ledger statement being addressed: Every virtual-molecule block admits a monotone finite cell-tree quotient of its dynamically relevant Cantor carrier with universal atomic and gate incidence and compatible partial cellular dynamics.

## Claim

For the genuine quadratic f(z)=z²−2, every positive return time p, and every nondegenerate connected subset S of its bounded-orbit set, some finite iterate of f^p maps S onto the entire bounded-orbit set. The universal angular full-cover threshold is exactly 2π. Moreover, even a partially defined quotient action must fail to preserve a collapsed angular interval's fibers at some step strictly before its full-cover horizon if the quotient is nonconstant. Thus a globally equivariant connected-fiber quotient of this carrier either collapses the entire carrier or is injective there. This is an exact restriction on nontrivial monotone compression; no topology on the factor target or continuity of the factor map is required.

## Evidence

The candidate proof is in [ChebyshevQuotientRigidity.lean](../../formalization/weighted/ChebyshevQuotientRigidity.lean). It uses the earlier physical identification in ChebyshevFibers.lean, not an assumed symbolic carrier. The proof is structured into seven declarations:

1. `retimed_angular_interval_covers`: angle coordinate 2 cos(t) intertwines f with doubling. If the expanded angle interval has length at least 2π, each target angle has a translate by an integer multiple of 2π in it (take the ceiling of the difference between its left endpoint and the target angle, divided by 2π); its image is the entire interval.
2. `retimed_connected_subset_covers`: a preconnected subset of the real segment containing two distinct points contains the segment between them. The angular width is strictly positive and powers of 2^p are unbounded for p>0. Hence the full-cover criterion applies.
3. `retimed_collapsed_fiber_forces_constant`: semiconjugacy iterates on the invariant carrier. A fiber containing two points covers the carrier under some retimed iterate, so every image point has the same quotient value.
4. `bounded_orbit_monotone_factor_injective`: translates the dichotomy to the actual bounded-orbit locus using the existing checked identification.

5. `angular_cover_threshold_sharp`: for any smaller nonnegative length δ, the closed angular interval centered at π misses all multiples of 2π and thus misses the actual endpoint 2. This proves sharpness uniformly over the location of the interval.
6. `finite_horizon_fiber_preservation_forces_constant`: if equality of quotient values is preserved on every successive image of a collapsed set until its full-cover horizon, equality propagates to the whole carrier. This is an induction on the actual return, not an assumption of a global model map.
7. `retimed_angular_fiber_collision`: for a nonconstant quotient which initially collapses an angular interval, the quantitative full-cover criterion supplies a pair in an actual forward image with equal quotient values and unequal next-return values, at some step strictly below the specified horizon.

Validation: local Lean and direct network checkout are unavailable in this session. The source is registered in the existing weighted Lake project and theorem index; the exact-head CI build and compiled dependency audit are required before these candidates count as verified results. No validation is asserted at this stage.

## Dependencies

TREE_NERVE_FULLNESS; TOPOLOGY_REPLICATION_NO_GO (ledger prerequisites). The actual mathematical inputs are the archive's ParabolicSegment, ParabolicComplexPullback and ChebyshevFibers modules (especially bounded_iff_realSegment and realSegment_invariant) and Mathlib's real cosine range, double-angle, periodicity, order-connectedness and Archimedean facts. See research/mlc_unified/virtual_hull_realization.md §6.1(2,6).

## Boundary

This is a restriction on globally equivariant quotients and a finite-horizon obstruction to fiber compatibility on actual forward images at the particular physical parameter −2, including every positive retiming. It does not prove that a native virtual block supplies that global semiconjugacy, that its carrier equals the whole bounded-orbit interval, or that a finite access-faithful tree quotient exists at arbitrary parameters. It does not refute the stated partial-dynamics H1 obligation. H1_CELL_TREE_EXTRACTION and MLC remain open; no ledger status change requested. Global originality has not been established.

## Attribution

Builds on the archive's exact Chebyshev fiber and planar segment formalizations and on the classical cosine double-angle identity. The proposed quotient rigidity consequence is distinct from the previously formalized nonexistence of an equivariant single-valued unit-circle section. AI assistance: OpenAI GPT-6.2; independent human review: none.
