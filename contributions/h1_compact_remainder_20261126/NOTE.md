---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="h1-compact-remainder-20261126"></a>

# Compact ambient remainder: exact separation and limit obstruction

## Claim

Draft target: sharpen the compact obstacle-remainder clause of VSC4 / virtual_hull_realization §6.1, beyond the finite obstacle split in LeastSaturatedCarrier.

## Evidence

Candidate Lean module `formalization/weighted/CompactObstacleRemainder.lean` is registered in the weighted build, theorem index and source table. Initial theorems: exact closure criterion, canonical compact difference, connected-obstacle absorption, forward compatibility (including the actual quadratic map), and exact directed-limit stabilization. CI validation pending; no theorem counted yet. The second proof commit adds the least closed remainder and its forward propagation, and constructs an explicit nonstabilizing compact inventory inside the actual Chebyshev bounded-orbit set at c = -2. Every stage is a compact connected carrier admitting a finite separated remainder, but its intersection {0} fails compact separation, and there is no least separated carrier. This is a counterexample to the unrestricted least-carrier extension, not a counterexample to native H1. No local Lean executable or network checkout is available.

## Dependencies

TREE_NERVE_FULLNESS, TOPOLOGY_REPLICATION_NO_GO; LeastSaturatedCarrier and the H1 cell-tree extraction audit of 2026-11-26.

## Boundary

No native virtual carrier extraction, gate closure, or MLC proof is claimed. The draft requires Lean CI.

## Attribution

Builds on the archive's least-carrier and finite obstacle work; Mathlib.
