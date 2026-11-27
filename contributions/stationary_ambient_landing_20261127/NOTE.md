---
ledger: KKL_STATIONARY_PROOF_USED_PREDECESSOR_SELECTION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="stationary-ambient-landing-20261127"></a>

# Ambient inverse restrictions and canonical predecessor landing

Ledger statement being addressed:

> Prove conditional proof-used compatibility through H=b+2: every independently supplied depth-n proper restriction whose deep endpoint follows the declared central small-Julia parent itinerary lands in the canonical Q_0-selected component L_0^n and carries its actual-component address w_n. This is a universal compatibility assertion only; it does not construct the restriction, its endpoint occurrence, or its host. Those existential clauses remain in the incoming-window anchor, so no occurrence is assumed circularly.

## Claim

Work in progress. The intended new result constructs an ambient univalent collar of an actual compact central quadratic predecessor, and proves canonical landing and complete parent-address compatibility for independently supplied ambient lifts from one physical anchor.

Two proof checkpoints now add twelve public Lean declarations in StationaryAmbientLanding and StationaryLimbCollar. Compilation and the kernel audit are pending; no theorem is yet claimed verified.

## Evidence

The existing StationaryPhysicalItinerary module proves physical inverse-section agreement inside the filled Julia set. The new StationaryAmbientLanding module proves connected component confinement, pointwise inverse agreement, exact full-trace reconstruction, filter-level landing, and a constructed analytic-collar theorem for actual polynomial compact cores. The restriction may lie outside the filled set. The anchor must be in the same connected trace whose entire projected image stays in the constructed collar. StationaryLimbCollar now derives the compact-core hypotheses directly from actual filled-Julia limb data, identifies the entire planar pullback component by complete invariance, and constructs its analytic collar. Its final theorem proves ambient landing and every canonical parent address from those limb hypotheses. The compact core is the selected predecessor of a compact connected central mark Q, not the entire generally noncompact selected limb.

Lean is unavailable locally and the workspace filesystem is full. All compilation and transitive proof-axiom validation will use the repository's existing weighted Lean CI. No result will be claimed proved before that CI passes.

## Dependencies

KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN; KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN. Existing modules StationaryPhysicalItinerary, TelescopeUnivalentCollars, and TelescopeConformalInverse.

## Boundary

The obligation remains open. The compact central target, native inverse-limb geometry, and an independently supplied anchored restriction must be stated explicitly. The analytic-collar construction is for the actual polynomial z^2+c; native psi-quadratic-like ambient correspondence identification is not inferred from straightening on the filled set. This packet does not yet identify KKL's exact proper-path occurrence or construct the incoming-window anchor, host, marked ideal access, or any width estimate. It does not establish MLC or H1-H4. Status records are left for maintainer review.

## Attribution

The stationary predecessor problem is from Kahn, Kapiamba and Lyubich, arXiv:2606.27272v1, section 2.4, as reconstructed in research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md. Existing archive proofs are credited above. OpenAI ChatGPT, GPT-6 Astra Pro performs proof search, Lean development, registration and CI review; human review: none.
