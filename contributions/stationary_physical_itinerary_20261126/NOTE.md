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

The registered [StationaryPhysicalItinerary.lean](../../formalization/weighted/StationaryPhysicalItinerary.lean) contains 10 public theorem candidates:

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

The other limb consumes one of the at-most-two inverse roots. Openness and uniqueness on the selected limb preserve connectedness when pulling back the connected target. The fixed cutpoint separates the chosen component from other limbs; iteration gives whole-component recognition, including for a disconnected base by anchoring its terminal component. For an independently supplied physical restriction, connectedness and endpoint membership force inclusion in the same full component.

Local Lean is not available in this session; the weighted kernel and transitive axiom CI checks are the verification authority. Until CI succeeds, these are candidate statements only, not credited results.

## Dependencies

KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN; KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN. The archive's StationaryFiberDynamics, StationaryLightModel and SaturatedTelescope modules supply actual filled-set complete invariance and openness, the degree-two inverse-point bound, and component composition. The native limb hypotheses are explicitly stated, not inferred from a finite tree or from the conclusion.

## Boundary

The terminal anchor condition is a geometric component test on the base, not a construction of the proof-used endpoint or its host. This does not show that KKL's exact ambient proper restriction has the asserted physical trace or itinerary, nor that its marked ideal access lands at the supplied endpoint. No collar, ambient occurrence, host, width estimate, or proof of MLC is constructed. Keep the obligation open pending those source identifications. No ledger status change.

## Attribution

Jeremy Kahn, Alex Kapiamba and Mikhail Lyubich, MLC for parabolically bounded primitive renormalization, arXiv:2606.27272v1, section 2.4; source reconstruction in research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md, Lemmas 2.1–2.2 and section 7. Existing archive Lean developments are credited above. OpenAI GPT-6.2 performed proof search, Lean drafting and registration; no human review.
