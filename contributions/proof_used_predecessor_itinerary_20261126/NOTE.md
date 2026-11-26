---
ledger: KKL_STATIONARY_PROOF_USED_PREDECESSOR_SELECTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="proof-used-predecessor-itinerary-20261126"></a>

# Connected endpoint itinerary recognition in the full physical carrier

Ledger statement being addressed:

> Prove conditional proof-used compatibility through H=b+2: every independently supplied depth-n proper restriction whose deep endpoint follows the declared central small-Julia parent itinerary lands in the canonical Q_0-selected component L_0^n and carries its actual-component address w_n.

## Claim

For a continuous self-map of an arbitrary topological carrier with a fixed omitted root and the critical-limb inverse branch of Gate N2, a connected endpoint chain is forced into the canonical marked predecessor chain if it maps forward at each step, its root endpoint lies in the root carrier and meets the critical mark, and each positive-level endpoint has one point in the selected punctured limb. A supplied whole-component address with an anchor in each endpoint then agrees at every depth with the canonical actual subsets. Candidate statements; exact-head CI is required.

## Evidence

The new module [StationaryProofUsedItinerary.lean](../../formalization/weighted/StationaryProofUsedItinerary.lean) states eight public theorems. The definitions use connected components of the actual topological carrier, not finite vertex labels.

1. `limb_avoids_root` and `connected_in_limb_of_hit`: a preconnected endpoint set avoiding the fixed root lies wholly in a selected component of its complement once it has one genuine witness there.
2. `inverse_branch_component`: for any target subset S of the limb (possibly disconnected), the full ambient pullback component through g(x) is exactly g applied to the connected component of S through x. The forward inclusion uses continuity of F, avoidance of the fixed root, and the inverse identity on the entire selected limb. The reverse inclusion uses continuity of g and the section identity. `inverse_branch_component_image` gives exact forward image, preserving the distinction between the first disconnected root and its selected component.
3. `endpoint_itinerary_selection`: root contact with Q_0 forces membership in the selected root component by connectedness. At each step, forward mapping into the previous endpoint excludes the fixed root, hence a single limb witness forces the entire endpoint into the limb. The inverse identity and the full component formula propagate selection. This works for every finite H, including H=b+2, without assuming the endpoint already meets Q_n or is contained in the selected L_0^n.
4. `supplied_address_eq`: if the supplied address consists of genuine full pullback components anchored in the independently supplied endpoints, selection implies equality of all actual component subsets, inductively from the common root.

5. `deepest_endpoint_selection`: takes a single actual deepest connected endpoint D, its successive iterate images, and one point z whose entire intermediate orbit lies in the selected limb. All the intermediate endpoint sets and the maps between them are constructed from F, not additional choices. If F^H(D) lies in the root carrier and meets Q_0, the theorem gives simultaneous containment of every F^(H-i)(D) in L_0^i.
6. `chebyshev_terminal_collision_not_component`: for the actual complex polynomial z²-2, the two points 2 and -2 map to the same point 2, but -2 is not in the full pullback component of {2} through 2. The proof splits the fiber into the two closed singleton sets and uses connectedness to rule out membership in both. Thus terminal image data alone cannot encode the sheet selection.

Reproduction: from formalization/weighted, `lake build StationaryProofUsedItinerary`; from repository root, `python3 -B code/verify_lean_coverage.py` and `python3 -B code/verify_lean_coverage.py --audit weighted`. Lean is not locally installed and the shell cannot reach GitHub, so the repository workflows must verify this candidate. Registration follows the transformations in `code/contribute.py lean-add` via GitHub's Git API; the script itself was not run.

## Dependencies

KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN, KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN, KKL_STATIONARY_CRITICAL_LIMB_INVERSE_BRANCH. Uses Mathlib connected-component and continuous-image theorems. The inverse-branch equations and continuity are explicit hypotheses, as in Lemmas 2.1–2.2 of Gate N2.

## Boundary

The result is a sufficient geometric recognition interface, not closure of the ledger row. In particular, it remains to bind each independently supplied actual proper restriction to connected deep endpoint sets and the forward/root-contact/limb-witness hypotheses. Prime-end impressions, accesses, occurrence construction, collars, separators, and hosts are not identified here. No ledger promotion, H1–H4 or MLC claim. No world-first novelty claim.

## Attribution

Builds on [Gate N2, Lemmas 2.1–2.2 and §7](../../research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md), and the archive's existing component transport results in SaturatedTelescope and StationaryMonotoneGeometry. The present criterion is distinct from the monotone quotient/full-preimage lift and assumes no local connectivity.
