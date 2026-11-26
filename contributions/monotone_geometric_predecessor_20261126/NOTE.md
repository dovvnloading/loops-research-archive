---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="monotone-geometric-predecessor-20261126"></a>

# Geometric predecessor lift: monotone quotient and marked continua

## Claim

This partial contribution formalizes the topological inference in the November 26 stationary non-LC audit: closed monotone quotient transport for all connected subsets, disjointness of invariant geometric marks under nonfixed-fiber and hereditary-unicoherence hypotheses, construction and projection of least continua, terminal-sheet marked incidence, and the full empty-interior planar subset lemma. The precise hypotheses are those in the Lean statements; only an exact-head successful kernel build and transitive dependency audit count as proof validation.

## Evidence

Lean file: `formalization/weighted/StationaryMonotoneGeometry.lean`.

Theorems: `preconnected_preimage_closed_fibers`, `component_preimage_closed_fibers`, `punctured_component_full_lift`, `disjoint_bridges_impossible`, `invariant_marks_disjoint_image`, `selected_predecessor_full_lift`, `least_carrier_terminal_incidence`, `selected_predecessor_contains_mark`, `least_compact_connected_carrier_exists`, `least_carrier_image_eq`, `preconnected_inter_preimage_path_connected`, `compact_subset_full_of_full_empty_interior`.

1. For a closed surjection with preconnected fibers, a closed cover of the preimage gives a closed cover of the target. A common target point has a fiber meeting both covering sets, hence a point in their intersection. This removes the audit's use of arc-convexity for the noncompact case.
2. Apply the lemma to a connected component and use maximality in both directions; a singleton root fiber gives exact punctured-component transport.
3. If disjoint invariant continua share a quotient point, its fiber meets both. The return image lies in a different fiber by the nonfixed-fiber hypothesis. Both fibers bridge the same marks. The intersection of the two connected closed unions is exactly the disconnected union of the marks, contrary to hereditary unicoherence.
4. At every depth n, semiconjugacy of iterates and the punctured-component identity give the exact inverse-image formula for the full carrier. This is equation (7) of the audit with all topological hypotheses explicit.
5. Construct the terminal pruning map directly by piecewise continuity across its singleton frontier. A least compact connected carrier that visits the terminal region must contain a mark there, or the image under pruning would be a smaller admissible carrier. This requires no local connectivity. Saturation and equality/inclusion of carrier images transfer a hit to the least carrier; a connected mark avoids the root and therefore lies wholly in the selected sheet. Forward invariance then gives its inclusion in the entire selected predecessor. This is the set-level incidence mechanism in equation (8).
6. The least compact connected carrier exists as a directed intersection of all closed connected carriers in a compact Hausdorff hereditarily unicoherent space. If the intersection admitted a disjoint closed separation, normality and compactness would force a whole connected carrier inside one side, a contradiction. Its image is the least model continuum, using the full inverse of the model hull and minimality on both sides.
7. Two points of a physical continuum over a path-connected model region are joined by a preconnected subset of the intersection: take the compact actual path image in the model, lift its entire inverse, and intersect with the physical continuum. This proves the physical intersection lemma without postulating paths in the physical Julia set.
8. Actual planar foundation: every compact subset of a full empty-interior plane set is itself full with connected complement, using the archive's `planarFill` and its unique exterior theorem. The remaining planar unicoherence step (Janiszewski separation) is not claimed.

Verified checkpoint: `36b0a29e7ee7d0763452a2c099e32ab130e7b9ce`, first eight theorems, [weighted build and transitive dependency audit passed](https://github.com/dovvnloading/loops-research-archive/actions/runs/45856259943). The extension must pass the same exact-head CI, whose run and conclusion are recorded in the PR conversation. Main advanced with the independent SaturatedTelescope contribution; the merge commit preserves its source, packet and registrations and retains this PR's full history.

Build: `cd formalization/weighted && lake build StationaryMonotoneGeometry`. The source is registered as METADATA, not a completed physical bridge. The preceding checkpoint passed both compilation and the foundational-dependency audit; validation of any later revision is governed by that revision's CI, not by the checkpoint.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE, KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN; research/independent_audits/stationary_nonlc_predecessor_lift_20261126/NOTE.md, sections 2–5. The actual planar filled-hull theorem uses `formalization/weighted/PlanarFullification.lean` (monotonicity, extensivity and unique unbounded complement). The other topological ingredients are Lean Mathlib's connected-set calculus, compactness, separation and piecewise continuity. Kiwi's quotient and Janiszewski's theorem are not imported as proof constants.

## Boundary

The physical quotient, hereditary unicoherence of the actual filled Julia set, and identification of the marked source objects must not be replaced by finite-tree assumptions or asserted as Lean-proved. The local environment does not have Lean or network git access. The repository CI is the compiler of record. No ledger status changes.

## Attribution

Builds on the archive's November 26 stationary non-LC predecessor audit and its cited work of Jan Kiwi, Kahn–Kapiamba–Lyubich, Douady–Hubbard and classical continuum topology.
