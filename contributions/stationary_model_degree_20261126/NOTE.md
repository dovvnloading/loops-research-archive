---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-model-degree-20261126"></a>

# Light geometric quotient dynamics and exact quadratic model degree

## Claim

Candidate Lean result: for a continuous surjective semiconjugacy from the actual complex quadratic filled set with connected geometric fibers, lightness (total disconnectedness of each model point preimage) suffices for whole-fiber transport; the model then has at most two predecessors of every point. Every nonempty model predecessor fiber is exactly the image pair of two opposite physical roots. Whole-fiber transport also forces model openness. Independently, if the model is open and singleton target fibers are dense, the model has at most two predecessors per point; one singleton anchor with dense backward orbit is sufficient for that density. Thus lightness and finiteness are equivalent in the stated genuine quadratic setting. At every inverse depth, the model predecessor count is bounded by the actual ramification-aware physical count. At a singleton geometric anchor this count is exact, even without model openness, lightness or global whole-fiber transport. Under lightness the physical reflection descends to a continuous involution of the geometric model; every model predecessor pair is one orbit of that involution, and its nonfixed points have two disjoint open inverse sheets over an open target neighborhood. This is a reduction of the prior finite-model-fiber assumption to lightness, not an unconditional identification of the named source quotient.

## Evidence

[StationaryLightModel.lean](../../formalization/weighted/StationaryLightModel.lean) declares the following theorems, pending exact-head compilation:

- `component_image_univ`
- `fiber_image_eq_of_light_model`
- `quadratic_filled_light_fiber_image`
- `quadratic_filled_model_fiber_pair`
- `quadratic_filled_light_model_finite`

1. In a compact Hausdorff domain, each connected component is the intersection of all clopen neighborhoods of its anchor. If a target point were omitted from the component image, compactness of its point preimage would yield a finite clopen intersection also omitting that point. But the image of this nonempty clopen set under an open closed map is clopen and hence all of the preconnected target.
2. Apply this argument to the restriction of the physical map over the connected geometric successor fiber. Lightness forces the model image of the anchor's physical connected component to be a single predecessor. Therefore that predecessor's entire physical fiber maps onto the successor fiber even without model discreteness.
3. Use the actual bounded-orbit quadratic filled set and its compactness and complete invariance already proved in StationaryFiberDynamics. Opposite roots remain in the filled set; every model predecessor must contain a lift of any chosen physical successor point. Factoring the difference of squares exhausts these lifts, giving the exact pair and hence finiteness.

4. Once whole-fiber transport holds, the inverse image of an open model-set image equals the physical image of its inverse image. The compact-source Hausdorff-target quotient property descends openness.
5. If three distinct model predecessors share a target, separate them by pairwise disjoint open neighborhoods. Openness gives a common open image neighborhood, and density supplies a singleton physical fiber in it. Surjectivity of the projection lifts the three model predecessors there, forcing three distinct physical preimages of one point, contrary to quadratic algebra.
6. Backward propagation of singleton fibers along finite physical fibers, together with a dense backward orbit of a single anchor, yields density in the model. This is an alternative route to the finite-model hypothesis, not a proof that the named model is open or that its named anchor has a dense backward orbit.

Additional declarations in this extension:

- `model_open_of_fiber_transport`
- `three_predecessors_collide_of_dense_singleton_targets`
- `finite_of_no_three_predecessors`
- `quadratic_filled_no_three_predecessors`
- `dense_singleton_targets_of_dense_backward_orbit`
- `quadratic_filled_open_model_transport_of_anchor`
- `quadratic_filled_light_iff_finite`

7. At all depths, whole-fiber transport gives an exact set identity: the model inverse-point set equals the projection of the inverse-point set of any one physical point in its successor fiber.
8. At a singleton anchor this identity needs only surjectivity of the semiconjugacy. The existing backward singleton propagation theorem also makes the projection injective on the entire inverse level. Complete invariance identifies all physical inverse roots with points of the actual filled set, including ramification. Transfer the previously proved global inverse-fiber census (QuadraticCriticalFiberCensus) by the finite image of these actual roots. The resulting model count plus the exact critical-value defect is at most the global degree, and equals the degree at a singleton anchor. If the anchor avoids every critical value through that depth, the model has exactly the full binary level.

Additional declarations in the all-depth extension:

- `model_iterate_preimage_projection`
- `model_anchor_iterate_preimage_projection`
- `model_anchor_iterate_preimage_injective`
- `quadratic_filled_iterate_mem_iff`
- `quadratic_filled_model_census_of_projection`
- `quadratic_filled_light_model_ramification_bound`
- `quadratic_filled_singleton_anchor_ramification_exact`
- `quadratic_filled_singleton_anchor_full_degree`

9. Whole-fiber transport forces sign-equivalence to descend: if two physical points have equal model image, then either both reflected points belong to the same fiber or transport from the other predecessor fiber forces their reflected images to coincide. Compact-to-Hausdorff quotient continuity makes the descended involution continuous. Its two-point orbits exhaust the model predecessor fibers.
10. At a nonfixed point, Hausdorff separation and continuity of the involution produce an open set disjoint from its reflected open image. Model openness makes the image an open target neighborhood; the entire inverse image of this neighborhood is exactly these two sheets. The map is injective on each and both cover the neighborhood. This does not assert that the involution fixed locus consists only of the physical critical point.

Additional declarations in the local-sheet extension:

- `model_involution_of_fiber_transport`
- `involution_local_two_sheets`
- `quadratic_filled_light_model_involution`
- `involution_singleton_fiber_iff`

Verified first checkpoint: [commit e605c916](https://github.com/dovvnloading/loops-research-archive/commit/e605c916330bac0694f7ab907101bd0054f3a721), [weighted CI 45879011212](https://github.com/dovvnloading/loops-research-archive/actions/runs/45879011212/job/140113281819) passed the source guard, complete Lean build (8822 jobs), and transitive dependency audit (StationaryLightModel: 6 declarations and 6 theorems including generated declarations; 76 modules and 2057 declarations overall; allowed foundational axioms only). Contribution intake and geometry coverage passed at that checkpoint. Verified second checkpoint: [commit 42807740](https://github.com/dovvnloading/loops-research-archive/commit/42807740c48e2ceebf9ff9571a64d0fe05d057c9), [weighted CI 45879598676](https://github.com/dovvnloading/loops-research-archive/actions/runs/45879598676/job/140115276259) passed the source guard, complete Lean build (8822 jobs), and transitive dependency audit (StationaryLightModel: 13 declarations and 13 theorems including generated declarations; 76 modules and 2064 declarations overall; allowed foundational axioms only). Twelve explicit public theorem declarations verified. Contribution intake and geometry coverage passed. Later additions are candidates until their own exact-head CI passes.

Reproduction: `cd formalization/weighted && lake build StationaryLightModel`, followed by repository-root `python3 -B code/verify_lean_coverage.py --audit weighted`. This environment has no Lean executable or network git access; repository CI is the compiler of record. The first checkpoint compiled and passed the audit; no later revision is credited before its own check.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE, KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN; StationaryFiberDynamics, StationaryGeometricFibers, QuadraticCriticalFiberCensus, Mathlib's compact Hausdorff component theorem and connected-set calculus.

## Boundary

The actual KKL/Kiwi quotient must still be identified as a continuous monotone semiconjugacy, and its lightness or the openness and singleton-anchor backward-orbit density premises must be proved on that named geometry. The carrier and marked-small-Julia identification and access transport remain separate. No ledger status change, H1–H4 closure, or MLC proof is claimed.

## Attribution

Builds on the archive's November 26 stationary geometric fiber dynamics and the source context of Kahn–Kapiamba–Lyubich, Kiwi, and Douady–Hubbard. No external theorem is introduced as a proof constant.
