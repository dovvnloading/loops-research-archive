---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="h1-least-saturated-carrier-20261126"></a>

# Least-carrier recognition and forced-absorption obstruction

A partial formalization and extension of the least Julia carrier argument in the 2026-11-26 H1 audit.

## Claim

Results at the verified source revision: arbitrary downward-directed compact connected carrier intersections stay preconnected; connected obstacles meeting a carrier with a separated closed obstacle split are forced into the carrier; under hereditary continuum-intersection, any nonempty class of admissible carriers has a least member, even with an infinite obstacle family. Actual quadratic selected pullback saturation and onto image identities persist under directed compact limits at a fixed anchor.

## Evidence

Registered module `formalization/weighted/LeastSaturatedCarrier.lean`. Public theorems: `directed_carrier_preconnected`, `connected_obstacle_forced`, `least_admissible_carrier`, `directed_image_intersection`, `directed_component_intersection`, `quadratic_directed_stage_limit`, `finite_obstacle_split_iff`, `least_carrier_obstruction_criterion`, `hereditary_carrier_intersection`, `quadratic_critical_arbitrary_intersection`, `quadratic_image_loss_iff_conflicting_signs`, `quadratic_image_intersection_iff_pairwise`, `quadratic_reflection_component`, `quadratic_nondirected_noncritical_counterexample`.

The directed-intersection proof separates the hypothetical disconnected limit by disjoint open neighborhoods of its two closed pieces. Compactness and downward directedness force one stage into their union, contradicting stage preconnectedness. The least admissible carrier is the intersection of all solutions, directed by the explicit hereditary intersection condition; a common obstacle encounter forces the whole obstacle into every solution. For the image identity, intersect the compact fibers over a target point using the finite intersection property. Component maximality and monotonicity then give exact saturation. The final theorem specializes to the genuine map z ↦ z²+c.

Reproduce: `cd formalization/weighted && lake build LeastSaturatedCarrier`, followed from the repository root by `python3 -B code/verify_lean_coverage.py --audit weighted`. No new workflow or status edits. All 14 explicitly stated public theorems compiled on commit `f463805e3843e29dc2f1dc961f11f95c6f6ed250`; the [weighted PR CI](https://github.com/dovvnloading/loops-research-archive/actions/runs/45859456296) reports 25 declarations, 19 theorems (including generated theorems), allowed axioms only. All 26 runs for that commit were successful. The source is byte-for-byte unchanged in the subsequent merge of concurrent main registration changes; the merged head must separately pass CI.


### Sharper existence and critical-stage intersection tests

The extension strengthens the result in three ways. First, for finite compact connected obstacles, a separated compact obstacle set exists exactly when each obstacle meeting the carrier is wholly absorbed. The reverse direction constructs the obstacle set as the finite union of all disjoint obstacles. Second, take only obstacles contained in J; J itself is a witness, so there is a least internal core without assuming the original admissible problem has a solution. For every authorized region U, the full constrained problem is feasible iff this core lies in U and every obstacle it meets is wholly contained in J. This gives an exact rejection criterion, not merely an implication from an already admissible forest. Third, hereditary pairwise continuum intersection yields arbitrary compact intersections at a common anchor. For actual quadratic pullback components through 0, the sign involution ensures that the same inverse point lies in every stage component even if the family is not directed. Hence the critical stage retains image equality and selected-component saturation under arbitrary common-anchor intersections. The new proofs passed the exact-source build and audit cited above.


### Sharp noncritical obstruction and two-sign completeness

For an arbitrary nonempty indexed family of actual complex carriers (no compactness or directedness required), a common target point y is lost from the image of their intersection iff two carriers require opposite, distinct square-root lifts: one contains z but not -z, the other contains -z but not z, where z²+c=y. Consequently pairwise common-lift compatibility over every shared target is necessary and sufficient for full common-lift compatibility. This gives a finite witness to any arbitrary-family fiber failure, and identifies what the critical sign involution prevents. The geometric counterexample uses two actual compact connected diagonal segments from 1 to i and -i for c=0. Each is its entire selected pullback component over its own image because it is disjoint from its reflected copy; the common anchor is 1 and their intersection is exactly {1}. Both images contain -1, but the image of the intersection does not. Thus connectedness of the intersection and exact individual stage saturation alone do not imply image equality at a noncritical anchor. These four declarations also passed the exact-source build and dependency audit cited above. The prior directed and critical-anchor positive results are not contradicted.

## Dependencies

TREE_NERVE_FULLNESS, TOPOLOGY_REPLICATION_NO_GO (ledger context); the H1 cell-tree extraction audit of 2026-11-26.

## Boundary

H1_CELL_TREE_EXTRACTION and MLC remain open. No local Lean executable or network-accessible checkout is available; validation must use the existing repository CI. The hereditary continuum-intersection condition and actual source-carrier hypotheses remain explicit; the sharper criterion avoids assuming feasibility of the full obstacle problem by constructing the least internal core. The geometric counterexample concerns actual square-map pullback components of compact arcs, not a demonstrated native virtual-block failure. For infinite obstacle families, the pointwise absorb-or-avoid predicate does not imply compactness or positive separation of the union of avoided obstacles; the compact separated split equivalence is finite only. This neither proves Janiszewski's plane separation theorem nor constructs the native finite cell-tree quotient, actual obstacle and gate incidence, or compatible partial dynamics. No status promotion requested.

## Attribution

Builds on the archive's existing H1 cell-tree audit, the archive's actual quadratic sign-collision and critical-component symmetry theorems in `SaturatedTelescope.lean`, and Mathlib topology. No human review.
