---
ledger: KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-multi-interface-separator-20261126"></a>

# Multi-attachment full-carrier separator transport

## Claim

Candidate Lean extension: if two closed ambient sheets cover the retained carrier and all their retained interface points lie in a single connected component of the selected sheet, restriction of every ambient connected component to that sheet equals its local component. Neither compactness nor local connectivity is required; the interface need not be connected or a singleton. If the retained exterior is preconnected and the interface is nonempty, the criterion is necessary as well.

## Evidence

Registered module: [StationaryMultiInterface.lean](../../formalization/weighted/StationaryMultiInterface.lean).

- `preconnected_inter_of_absorbed_interface`: a closed-sheet intersection of a preconnected set is preconnected when its interface is absorbed by a preconnected subset of that intersection. A hypothetical closed separation assigns the absorbing subset entirely to one side, and the exterior can be added to that side without creating any overlap. This contradicts ambient preconnectedness.
- `component_inter_of_single_interface_component`: if an ambient component meets the interface, it contains the entire absorbing local component. If it misses the interface, the absorbing subset is empty. Apply the preceding theorem and component maximality in both directions.
- `no_bypass_iff_single_interface_component`: necessity follows because every point of a connected retained exterior belongs to the same ambient component.
- `exterior_bridge_obstructs_separator`: a preconnected exterior bridge joining locally separated points certifies failure of the local-to-global implication.

Build: `cd formalization/weighted && lake build StationaryMultiInterface`. Local Lean and network access for a git checkout are unavailable. The module is registered in the existing Lake target, theorem index and source inventory. **Candidate only pending successful CI compilation and transitive dependency audit.** No check is weakened.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN, KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN, KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS.

## Boundary

This is a general topological criterion about the actual sets supplied as arguments, not an identification of the native stationary sheets. The physical closed cover, interface absorption at each selected predecessor, base separator, and proof-used collars and marked accesses remain to be proved. The ledger row stays open; no H1–H4 or MLC conclusion is asserted.

## Attribution

Builds on Kahn–Kapiamba–Lyubich, the November 26 stationary non-LC predecessor lift audit, and the archive's CI-verified singleton-frontier transport in `StationarySeparatorTransport.lean`.
