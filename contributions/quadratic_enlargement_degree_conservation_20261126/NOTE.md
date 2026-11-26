---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="quadratic-enlargement-degree-conservation-20261126"></a>

# Actual quadratic enlargement: degree conservation and exact merger census

## Claim

Candidate Lean result: for the actual map f(z)=z²+c, an enlarged connected pullback component over V and an open connected U contained in V, one inverse fiber over any y in U enumerates precisely the old components contained in the enlargement. The census is independent of y, even at postcritical values. The old component fiber cardinalities sum to the enlarged fiber cardinality; for regular y this is exactly 2^R, the intrinsic reflection-rank degree of the enlarged component. Any declared subfamily of the actual components exhausts the enlargement if and only if its summed mass reaches this number (or the enlarged distinct-point count at critical y). Equal old rank d gives exact merger count times 2^d = 2^R. Neither target is required to be simply connected.

## Evidence

[QuadraticEnlargementDegree.lean](../../formalization/weighted/QuadraticEnlargementDegree.lean) is registered as a default weighted target, with every public theorem in the bridge index. The argument partitions an actual finite polynomial inverse fiber by its connected-component map, not by declared symbolic labels. Every old component is onto the connected old target by the existing proper/open map theorem; hence it occurs in every anchor census. The partition is disjoint by uniqueness of connected components and has positive mass in each class. Strict monotonicity of a finite sum of positive natural weights detects omitted classes. The existing intrinsic rank-degree theorem gives the regular mass formula.

The initial eight public theorems are mem_mergerCensus, mergerCensus_independent, mergerCensus_fiber_partition, mergerCensus_positive_mass, mergerCensus_complete_iff_mass, mergerCensus_degree_conservation, mergerCensus_uniform_rank_count, and mergerCensus_complete_iff_degree. Local Lean/lake and networked git are unavailable; the exact-head weighted GitHub Actions build and transitive dependency audit are required. Reproduce with `cd formalization/weighted && lake build QuadraticEnlargementDegree`, then from repository root `python3 -B code/verify_lean_coverage.py --audit weighted`. The initial proof commit 8caca5186f9406d8722b941c301d4d3c74ee49fb passed the full weighted Lean build and transitive dependency audit in [PR workflow 45889624159](https://github.com/dovvnloading/loops-research-archive/actions/runs/45889624159): 8840 build jobs, 11 module declarations, 10 kernel theorem constants (eight explicit theorems), 85 modules and 2311 declarations audited, allowed dependencies only. This is a verified checkpoint for the first eight theorems. Validation of the extended head is pending.

The extension adds six candidate theorems. The aggregate critical deficit identity is exact: sum the distinct-point losses over the finite set of postcritical values in the target, add the recursively propagated missing critical charge, then add one; the result is the intrinsic component degree. The new charge records an invariant reflection step whose tail component omits the critical value, and hence whose doubling is not accounted for by an actual critical encounter. The same identity applies to repeated postcritical values because the finite target census counts values once. The component deficit is additive under enlargement when computed against a common regular anchor. A separate geometric recognition theorem proves that a nonempty connected proper open declared piece is an actual old component, and a full mass certificate makes a finite such family exhaust the selected enlarged component. Every nonempty connected reached subset then has a unique actual component address. The additional proof statements are aggregate_defect_debt_eq_degree, component_actual_deficit_accounting, mergerCensus_defect_conservation, proper_piece_mem_mergerCensus, proper_piece_family_eq_census, and mergerCensus_unique_connected_image. All six remain candidates until exact-head CI succeeds. Main advanced to d39ff04a7e732c81de8693ace6810c556853753c during development; the merge preserves its new StationaryCompactContact module and registry entries, without changing this contribution's Lean proof statements.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING. Builds on [finite-cylinder commuting lift](../../research/mlc_unified/finite_cylinder_commuting_lift.md), [single-fiber exhaustion](../cylinder_fiber_exhaustion_20261126/NOTE.md), [quadratic cylinder ramification](../quadratic_cylinder_ramification_20261126/NOTE.md), and [component fiber degrees](../quadratic_component_fiber_degree_20261126/NOTE.md). Uses Mathlib's finite fiberwise sum identity and positivity of natural sums.

## Boundary

The census is of actual planar connected pullback components. The statement does not assert that the authorized virtual-cylinder family is a subfamily of these components, or identify the typed target, actual localization, marked accesses, chronology, sheet metadata, or root-enlargement certificates. No ledger or global gate is closed; H1–H4, UPTCR and MLC remain open. No literature priority claim.

## Attribution

Kahn–Lyubich decoration theory (arXiv:math/0609046), earlier archive contributions on quadratic pullback components and intrinsic reflection rank, and Mathlib.
