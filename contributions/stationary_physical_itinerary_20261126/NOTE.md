---
ledger: KKL_STATIONARY_PROOF_USED_PREDECESSOR_SELECTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-physical-itinerary-20261126"></a>

# Physical critical-limb itinerary and selected component recognition

## Claim

Candidate Lean theorems for the actual quadratic filled Julia set: native critical-limb geometry and a disjoint alternative inverse limb suffice to recognize the full selected predecessor component at every finite depth. No local connectivity, preselected endpoint address, or connectedness of the entire base is required. The supplied endpoint must stay in the critical limb before the terminal time and end in the component of the base anchored by the central mark. Any independently supplied connected physical restriction contained in the full iterate preimage and containing this endpoint is then contained in the selected component.

## Evidence

The registered [StationaryPhysicalItinerary.lean](../../formalization/weighted/StationaryPhysicalItinerary.lean) contains 21 public theorem declarations (the first 14 passed the full kernel build and transitive axiom audit at [`f367e5a`](https://github.com/dovvnloading/loops-research-archive/commit/f367e5a8ff439c93ee827ff1169c8dfba4d8332c); see the [CI log](https://github.com/dovvnloading/loops-research-archive/actions/runs/45889927685/job/140149774513). The expanded module must pass CI):

- `quadratic_critical_limb_injective`
- `limb_inverse_preconnected`
- `limb_inverse_image`
- `limb_inverse_component`
- `mem_limbItinerary`
- `limbItinerary_subset`
- `limbItinerary_component`
- `quadratic_filled_continuous_open`
- `quadratic_selected_itinerary_component`
- `quadratic_restriction_itinerary_contained`
- `limbItinerary_image`
- `limbItinerary_injective`
- `quadratic_critical_limb_unique_inverse`
- `quadratic_mark_itinerary_component`
- `limbItinerary_add`
- `limbItinerary_prefix_image`
- `quadratic_marked_restriction_selection`
- `quadratic_model_carrier_itinerary_component`
- `degree_two_limb_injective`
- `limbItinerary_continuous_inverse`
- `degree_two_independent_inverse_agreement`

The other limb consumes one of the at-most-two inverse roots. Openness and uniqueness on the selected limb preserve connectedness when pulling back the connected target. The fixed cutpoint separates the chosen component from other limbs; iteration gives whole-component recognition, including for a disconnected base by anchoring its terminal component. For an independently supplied physical restriction, connectedness and endpoint membership force inclusion in the same full component. The full-depth itinerary is bijective onto its base: exact image and injectivity are proved separately, so every terminal point of the critical limb has exactly one inverse point with the specified itinerary. A connected central mark containing the anchor discharges the terminal base-component test from actual mark contact alone.

Four further declarations strengthen the test: exact forward images recover every parent of the selected address; actual contact with the pulled-back central mark forces any preconnected supplied restriction into the selected full component, with equality exactly when its image is the entire anchored base. A separate monotone-model theorem obtains connectedness of the physical base from the singleton cut fiber, hereditary unicoherence and a path-connected model limb. It then recognizes the full physical selected component from the model orbit and terminal carrier membership, without assuming the carrier is saturated for the quotient. The needed model and geometric hypotheses remain explicit.

The source-facing generalization uses a native continuous open degree-two map (not a polynomial or a finite graph) with the stated disjoint inverse-limb geometry. It constructs a continuous canonical section on the entire limb. For any independently supplied continuous section of the same iterate on a preconnected target in that limb, a single selected anchor forces the section's whole image to equal the selected itinerary of its target and forces pointwise agreement with the canonical inverse. This removes the need to assume connectedness or a component address of the lifted restriction separately. The native restriction must still supply a continuous section on the indicated physical target and a correctly located anchor; no prime-end boundary extension or ambient occurrence is constructed.

Local Lean is not available in this session; the weighted kernel and transitive axiom CI checks are the verification authority. The first 14 source declarations were fully verified at the pinned commit above: the audit accepted 27 module declarations including 21 theorem constants, using only the three allowed foundational axioms. The later declarations require a successful build and audit on their expanded revision before credit.

## Dependencies

KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN; KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN. The archive's StationaryFiberDynamics, StationaryLightModel and SaturatedTelescope modules supply actual filled-set complete invariance and openness, the degree-two inverse-point bound, and component composition. The native limb hypotheses are explicitly stated, not inferred from a finite tree or from the conclusion.

## Boundary

The terminal anchor condition is a geometric component test on the base, not a construction of the proof-used endpoint or its host. This does not show that KKL's exact ambient proper restriction has the asserted physical trace or itinerary, nor that its marked ideal access lands at the supplied endpoint. No collar, ambient occurrence, host, width estimate, or proof of MLC is constructed. Keep the obligation open pending those source identifications. No ledger status change.

## Attribution

Jeremy Kahn, Alex Kapiamba and Mikhail Lyubich, MLC for parabolically bounded primitive renormalization, arXiv:2606.27272v1, section 2.4; source reconstruction in research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md, Lemmas 2.1–2.2 and section 7. Existing archive Lean developments are credited above. OpenAI GPT-6.2 performed proof search, Lean drafting and registration; no human review.
