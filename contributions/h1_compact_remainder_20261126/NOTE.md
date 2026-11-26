---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="h1-compact-remainder-20261126"></a>

# Compact ambient remainder: exact separation and a physical limit obstruction

Target: VSC4 in `research/mlc_unified/saturated_virtual_seed_forest.md` §8 and its infinite obstacle accumulation warning §9.4; clause 7 of `research/mlc_unified/virtual_hull_realization.md` §6.1. The earlier least-carrier contribution establishes pointwise obstacle absorption and a finite compact split, but explicitly leaves compactness of an infinite avoided union open.

## Claim

For a retained carrier K and an inventory U, write R(K,U) if there is a compact set E disjoint from K with U contained in K union E. In a Hausdorff space with U in a compact ambient set, R(K,U) holds exactly when the closure of U minus K is disjoint from K, and this closure is the least compact remainder. For a nonempty downward-directed family of closed carriers, each satisfying R, the intersection satisfies R exactly when some stage already has the final trace on U.

The criterion has a sharp obstruction on the actual complex bounded-orbit set of the Chebyshev polynomial z²−2: there is a compact inventory for which each of a decreasing sequence of compact connected carriers containing the critical point admits a finite separated remainder, but their intersection does not; no least compact connected separated carrier containing the critical point exists for this inventory.

## Evidence

Lean module `formalization/weighted/CompactObstacleRemainder.lean`, registered as a weighted default target, with these 13 public theorems:

- `remainder_iff_closure_disjoint`, `remainder_iff_compact_difference`, `least_compact_remainder`: a compact witness contains the omitted trace and its closure. Conversely, a disjoint closure is compact inside the ambient bound and itself covers every omitted point. For compact U, the omitted trace is U intersect the witness and is compact.
- `connected_inventory_obstacle_absorbed`: if a connected obstacle meets K but contains a point outside K, the complements of the two disjoint closed pieces form an open separation of that obstacle.
- `canonical_remainder_forward`, `quadratic_canonical_remainder_forward`, `closure_remainder_forward`: if f sends the inventory into the target carrier or target inventory, its omitted points map into the target carrier or target omitted trace. For continuous f and closed target carrier, take closures in the closed preimage of the target carrier union the closure of its omitted trace.
- `directed_remainder_iff_stabilizes`: if E is a compact remainder for the intersection, then E meets no point of the intersection. The compact finite-intersection property and downward directedness give one stage disjoint from E. Its inventory trace is therefore contained in the limit; the reverse inclusion is automatic. Conversely, if a stage has the final trace, its compact remainder is also a remainder for the limit. No compactness of U is required for this equivalence.
- `chebyshev_inventory_compact`, `chebyshev_stage_admissible`, `chebyshev_carrier_intersection`, `chebyshev_limit_remainder_failure`, `chebyshev_no_least_separated_carrier`: set a_n = 1/(n+1), K_n = [-a_n,a_n] on the real axis, U = closure of {a_n : n natural}. All are subsets of the actual bounded-orbit set [-2,2] by `LoopsChebyshev.bounded_iff_realSegment`. At stage n the finite set of a_j with j<n is a disjoint compact remainder; closedness of its union with K_n covers the closure defining U. The intersection is {0} by the Archimedean property. Since a_n is in U intersect K_n but not in K_(n+1), the exact stabilization test fails. Any least admissible carrier containing 0 would lie in every K_n, hence equal {0}, a contradiction.

Reproduce: `cd formalization/weighted && lake build CompactObstacleRemainder`; from the repository root run `python3 -B code/verify_lean_coverage.py --audit weighted`. The existing CI performs both the full weighted build and the transitive dependency audit. The first full build on 5c7e663bbb828fc730a6e5778d8da5892d31dcde failed solely because the imported connected-obstacle theorem includes an unused NormalSpace instance; this revision proves that step directly with the same original separation argument, without adding a hypothesis. The repaired revision 61c28d18e5fb33825cb2379e0901e84a916b6f13 passed the weighted build (run 45873269206); its transitive dependency audit was still running when this integration commit was prepared. The Lean proof source is unchanged; the new head requires its own CI. Local Lean executable and network checkout unavailable.

## Dependencies

TREE_NERVE_FULLNESS and TOPOLOGY_REPLICATION_NO_GO (ledger context); the 2026-11-26 H1 cell-tree extraction audit and `LeastSaturatedCarrier.lean`; actual Chebyshev bounded-orbit identification in `ChebyshevFibers.lean`, and real-segment geometry in `ParabolicSegment.lean`. General topology and real arithmetic from Mathlib.

## Boundary

The Chebyshev example is a compact inventory in a physical bounded-orbit set, not an identification with the proof-used native virtual-Molecule obstacle inventory. The result gives an exact condition for one part of VSC4 and rules out an unrestricted least-carrier extension. It does not construct that inventory, its native access gates, a finite cell-tree quotient, or compatible all-scale partial dynamics. No H1, UPTCR or MLC closure, ledger promotion, or world-first novelty claim is made.

## Attribution

Builds on the archive's 2026-11-26 least Julia carrier audit, the finite obstacle separation and directed compact intersection results of `LeastSaturatedCarrier.lean`, the actual quadratic Chebyshev proof in `ChebyshevFibers.lean`, and Mathlib. No human review.
