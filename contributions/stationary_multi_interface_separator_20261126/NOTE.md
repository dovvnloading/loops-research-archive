---
ledger: KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-multi-interface-separator-20261126"></a>

# Multi-attachment full-carrier separator transport

## Claim

Lean-verified extension (first eight named results): if two closed ambient sheets cover the retained carrier and all their retained interface points lie in a single connected component of the selected sheet, restriction of every ambient connected component to that sheet equals its local component. Neither compactness nor local connectivity is required; the interface need not be connected or a singleton. If the retained exterior is preconnected and the interface is nonempty, the criterion is necessary as well. For a finite closed cover by preconnected retained exterior patches each anchored to the selected sheet, there is an exact no-bypass equivalence even when patches overlap outside that sheet.

## Evidence

Registered module: [StationaryMultiInterface.lean](../../formalization/weighted/StationaryMultiInterface.lean).

- `preconnected_inter_of_absorbed_interface`: a closed-sheet intersection of a preconnected set is preconnected when its interface is absorbed by a preconnected subset of that intersection. A hypothetical closed separation assigns the absorbing subset entirely to one side, and the exterior can be added to that side without creating any overlap. This contradicts ambient preconnectedness.
- `component_inter_of_single_interface_component`: if an ambient component meets the interface, it contains the entire absorbing local component. If it misses the interface, the absorbing subset is empty. Apply the preceding theorem and component maximality in both directions.
- `no_bypass_iff_single_interface_component`: necessity follows because every point of a connected retained exterior belongs to the same ambient component.
- `exterior_bridge_obstructs_separator`: a preconnected exterior bridge joining locally separated points certifies failure of the local-to-global implication.

- `patchedCarrier_insert`, `patchedCarrier_closed`: finite unions of closed exterior patches are closed, with the insertion identity.
- `component_inter_finite_patches`: attach patches one at a time. A new patch contacts the growing carrier either in the original selected sheet or in a previously attached patch. In the latter case preconnectedness and compatible anchor components force the contact into the same growing component. The first theorem therefore applies at each insertion, without assuming disjointness of exterior patches.
- `finite_patches_no_bypass_iff`: necessity of the two conditions follows by following a connected patch, or two patches with an actual retained overlap, to their anchors. Thus individual contact absorption plus anchor compatibility at every overlap is exactly equivalent to no new component mergers on the selected sheet. This gives a finite incidence criterion, not an assertion that the native carrier already has the required finite closed patch cover.

- `compact_clopen_separator_of_component_disjoint`, `compact_closed_cover_no_bypass_iff`: further candidate compact-carrier extension. On a compact Hausdorff retained carrier, pairwise compatibility of interface points in each exterior component is necessary and sufficient, even for infinitely many exterior components. The proof uses the compact Hausdorff component quotient to separate closed sets by a clopen set, then glues compatible clopen partitions across the closed cover. This removes the finite cover and anchor hypotheses but adds compactness of the retained carrier. **These two additions are pending CI.**

Build: `cd formalization/weighted && lake build StationaryMultiInterface`. Local Lean and network access for a git checkout are unavailable. The module is registered in the existing Lake target, theorem index and source inventory. No check is weakened.

Verification checkpoint for the first eight theorems: [commit c3955b9](https://github.com/dovvnloading/loops-research-archive/commit/c3955b9094892a2f92d5de9ce0cf7383a3baf0aa), [weighted CI job](https://github.com/dovvnloading/loops-research-archive/actions/runs/45870097425/job/140082993420). The build completed successfully, the log reports `Built StationaryMultiInterface (4.2s)`, `AXIOM_AUDIT weighted StationaryMultiInterface: 14 declarations, 13 theorems; allowed axioms only` and `AXIOM_AUDIT_PASS weighted: 70 modules, 1897 declarations`. Upstream synchronization cancelled the workflow after those lines; the original job's final conclusion is cancelled, not green.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN, KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN, KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS.

## Boundary

This is a general topological criterion about the actual sets supplied as arguments, not an identification of the native stationary sheets. The physical closed cover, interface absorption at each selected predecessor, base separator, and proof-used collars and marked accesses remain to be proved. The ledger row stays open; no H1–H4 or MLC conclusion is asserted.

## Attribution

Builds on Kahn–Kapiamba–Lyubich, the November 26 stationary non-LC predecessor lift audit, and the archive's CI-verified singleton-frontier transport in `StationarySeparatorTransport.lean`.
