---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="h1-least-saturated-carrier-20261126"></a>

# Least-carrier recognition and forced-absorption obstruction

Draft research claim: formalize a substantive portion of the least Julia carrier argument in the 2026-11-26 H1 audit.

## Claim

Candidate results: arbitrary downward-directed compact connected carrier intersections stay preconnected; connected obstacles meeting a carrier with a separated closed obstacle split are forced into the carrier; under hereditary continuum-intersection, any nonempty class of admissible carriers has a least member, even with an infinite obstacle family. Actual quadratic selected pullback saturation and onto image identities persist under directed compact limits at a fixed anchor.

## Evidence

Registered module `formalization/weighted/LeastSaturatedCarrier.lean`. Public theorems: `directed_carrier_preconnected`, `connected_obstacle_forced`, `least_admissible_carrier`, `directed_image_intersection`, `directed_component_intersection`, `quadratic_directed_stage_limit`.

The directed-intersection proof separates the hypothetical disconnected limit by disjoint open neighborhoods of its two closed pieces. Compactness and downward directedness force one stage into their union, contradicting stage preconnectedness. The least admissible carrier is the intersection of all solutions, directed by the explicit hereditary intersection condition; a common obstacle encounter forces the whole obstacle into every solution. For the image identity, intersect the compact fibers over a target point using the finite intersection property. Component maximality and monotonicity then give exact saturation. The final theorem specializes to the genuine map z ↦ z²+c.

Reproduce: `cd formalization/weighted && lake build LeastSaturatedCarrier`, followed from the repository root by `python3 -B code/verify_lean_coverage.py --audit weighted`. No new workflow or status edits. These are proof candidates until the exact-head weighted CI passes.

## Dependencies

TREE_NERVE_FULLNESS, TOPOLOGY_REPLICATION_NO_GO (ledger context); the H1 cell-tree extraction audit of 2026-11-26.

## Boundary

H1_CELL_TREE_EXTRACTION and MLC remain open. No local Lean executable or network-accessible checkout is available; validation must use the existing repository CI. The hereditary continuum-intersection condition, existence of an admissible solution, and actual directed saturated carriers remain explicit hypotheses. This neither proves Janiszewski's plane separation theorem nor constructs the native finite cell-tree quotient, actual obstacle and gate incidence, or compatible partial dynamics. No status promotion requested.

## Attribution

Builds on the archive's existing H1 cell-tree audit and Mathlib topology. No human review.
