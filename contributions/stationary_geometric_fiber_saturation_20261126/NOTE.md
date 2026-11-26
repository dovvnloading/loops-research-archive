---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-geometric-fiber-saturation-20261126"></a>

# Geometric predecessor lift via finite-orbit fibers and marked anchors

## Claim

This partial contribution proposes nine Lean theorems sharpening the non-locally-connected geometric predecessor lift: singleton predecessor fibers under finite-to-one dynamics (including actual complex quadratic restrictions), exact component transport relative to nonsaturated physical continua in a hereditarily unicoherent compact space, a frontier-based sufficient criterion for full saturation, exact matching of geometric marks via dense anchors, and a one-contact criterion for physical marked incidence. These are candidate formal statements pending exact-head CI.

## Evidence

Registered Lean module: [StationaryGeometricFibers.lean](../../formalization/weighted/StationaryGeometricFibers.lean).

1. `preconnected_finite_subsingleton`, `singleton_fiber_of_iterate`: a finite T1 fiber cannot contain a nontrivial preconnected subset. If the next fiber is a singleton, semiconjugacy traps the preceding fiber in one finite physical inverse fiber. Induct backwards from one known singleton root, with no local connectivity hypothesis.
2. `quadratic_fiber_finite`, `quadratic_restricted_fiber_finite`: for f(z)=z²+c, any fiber with one point a consists only of possible points a and -a, from (z-a)(z+a)=0. This also applies on actual invariant subsets with their subspace topologies. It supplies the finiteness premise in step 1 for true quadratic dynamics.
3. `relative_preimage_preconnected`, `relative_component_lift`: if C is a closed continuum, the fiber slice C ∩ p⁻¹{y} is preconnected by hereditary unicoherence whenever nonempty. The closed-image separation argument works on every preconnected subset S of p(C), even when S is not path connected or closed. Therefore the actual component of C ∩ p⁻¹S at x is exactly C ∩ p⁻¹(component of S at p(x)). This is strictly weaker in assumptions than requiring C=p⁻¹(p(C)); the earlier path-connected-region result is extended to arbitrary preconnected subsets of p(C).
4. `closed_carrier_saturated_of_frontier_singletons`: a fiber meeting C and its complement must meet C's frontier, by connectedness and the closed cover C ∪ closure(Cᶜ). If every frontier point has a singleton full fiber, such a crossing is impossible. Thus C is saturated. This is a sufficient test, not a claim that the actual KKL carrier satisfies it.
5. `marked_continuum_image_of_dense_anchors`: if A is dense in compact K, B is dense in model L, and p(A)=B, then p(K)=L. The proof uses closedness of the compact image and continuity, not an identification of a small Julia continuum with an abstract finite-tree vertex.
6. `selected_mark_from_single_overlap`: for a connected physical mark K avoiding the selected root a, one point of p(K) in the selected model punctured component is enough. Exact punctured component transport sends that contact back into the physical component, and connectedness puts all of K there. If K⊆T and T is forward invariant, then K⊆F⁻ⁿ(T)∩Ω_n at every requested depth. This rigorously formalizes the alternative following Corollary 4.4, without assuming full carrier saturation or full geometric marked-continuum correspondence.

Public theorem declarations: `preconnected_finite_subsingleton`, `singleton_fiber_of_iterate`, `quadratic_fiber_finite`, `quadratic_restricted_fiber_finite`, `relative_preimage_preconnected`, `relative_component_lift`, `closed_carrier_saturated_of_frontier_singletons`, `marked_continuum_image_of_dense_anchors`, `selected_mark_from_single_overlap`.

Reproduction: `cd formalization/weighted && lake build StationaryGeometricFibers`; from repository root, `python3 -B code/verify_lean_coverage.py` and `python3 -B code/verify_lean_coverage.py --audit weighted`. The module is registered in the existing default targets, theorem index and source inventory (METADATA). Local Lean and network git access are unavailable; exact-head repository CI is the compiler of record. No certified result is claimed before the build and transitive dependency audit pass.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE, KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN. The formal proof imports StationaryMonotoneGeometry and Mathlib. Source context: [stationary predecessor endpoint audit, Corollary 4.4 and Proposition 4.5](../../research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md#corollary-44-model-incidence-and-exact-non-lc-residue); [Kiwi model audit](../../research/mlc_unified/kkl_stationary_n2_kiwi_model_identification_audit_20260727.md).

## Boundary

The actual KKL/Kiwi model identification, hereditary unicoherence for the native filled set, singleton root fiber of the named projection, exact selected-address transport, native dense-anchor identification or contact, and proof that the frontier singleton criterion applies to the actual Hubbard carrier are not established here. The relative component identity is not the unrestricted full-preimage equality. Step 6 is a conditional incidence route and does not construct a selected occurrence, collar or Wave. No ledger status change, H1–H4, or MLC is asserted. No world-first priority is claimed for classical topology.

## Attribution

Builds on the repository's November 26 monotone geometric predecessor contribution and the cited Kahn–Kapiamba–Lyubich, Douady–Hubbard and Kiwi research. No external theorem is introduced as a proof constant.
