---
ledger: KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-separator-no-bypass-20261126"></a>

# Full-carrier separator transport through terminal sheets

## Claim

Candidate exact component restriction and decomposition for arbitrary retained subsets of the full carrier: a singleton frontier gives a continuous retraction and an equivalence of local and global separator predicates. The retained subset need not be compact or locally connected. Also formalize the actual quadratic saturation identity for reflection-invariant sets.

## Evidence

The registered module [StationarySeparatorTransport.lean](../../formalization/weighted/StationarySeparatorTransport.lean) contains the following 14 CI-verified baseline theorems: `terminalRetract_continuous`, `terminalRetract_fixed`, `terminalRetract_mapsTo`, `component_inter_terminalSheet`, `component_eq_local_of_attachment_missing`, `separator_iff_local`, `separator_transport`, `attachment_component_union`, `quadratic_image_preimage_symmetric`, `quadratic_injOn_of_continuous_section`, `quadratic_injOn_over_simplyConnected`, `reflected_points_separated`, `quadratic_image_diff_symmetric`, `quadratic_reflected_base_separator`.

1. The singleton frontier makes piecewise identity/constant retraction continuous; it preserves every retained set containing the attachment.
2. The image of a global connected component under the retraction lies in the local connected component by maximality. Since the retraction fixes the closed sheet, intersection with the sheet gives exactly the local component. If that component misses the attachment then the full global component is contained in the sheet. The attachment component itself decomposes into exactly its two local components; an exterior component not attached at the root is not added.
3. Continuous inverse coordinates on the retained sheet send any ambient bypass to a connected bypass in the base. This is stronger than transporting only paths, and gives the exact no-bypass clause of the source's set-level KSEP argument, conditional on the actual terminal frontier and base separator.
4. The actual quadratic identity f_c^{-1}(f_c(Q))=Q for symmetric Q follows from (w-z)(w+z)=0; no covering degree or abstract deck label is assumed.

5. An alternative analytic base-separator route is formalized: on any preconnected set avoiding 0, a continuous square-root inverse section forces injectivity of the actual quadratic map. The ratio of a point to the selected root is a continuous map into the disconnected two-point set {1,-1}, hence constant. Mathlib's pinned `Complex.exists_continuousOn_pow_eq` constructs such a section on an open simply connected domain missing c. Consequently antipodal points cannot lie in the same retained connected component if its image lies in such a domain. Symmetry of Q gives the exact image-difference formula f(K\\Q)=f(K)\\f(Q), reducing the base separator to construction of a simply connected domain containing that actual difference and missing c. This route applies to connected sets, not merely paths; existence of the required physical domain is not asserted.

Verified baseline: commit 40394d46194cb121ed2753f6c201dcc50ac2fa63, weighted CI run 45860853970, successful compilation and transitive dependency audit.

6. New candidate analytic reduction: `log_lift_homotopy`, `log_on_compact_avoiding_unbounded_cut`, `quadratic_injOn_avoiding_unbounded_cut`, `quadratic_reflected_separator_of_unbounded_cut`, `quadratic_base_separator_of_exterior_ray`. The logarithm is lifted from a far-away center and transported along a path in the open complement of a compact target. To exclude a connected bypass, use a path in the open preimage of the complement of the closed cut and apply the compact logarithm to its image. Thus the retained carrier need not be locally connected. A single exterior ray meeting the compact critical image and avoiding the retained image supplies the cut. Native ray construction and marked collar/access realization remain open. These five additions require their own exact-head CI.

Build: `cd formalization/weighted && lake build StationarySeparatorTransport`. Existing weighted CI checks source registration and all transitive dependencies. Local Lean is unavailable; the additional statements are candidates until exact-head CI succeeds.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN, KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN, KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS. Earlier work: research/independent_audits/stationary_nonlc_predecessor_lift_20261126/NOTE.md §6.

## Boundary

No claim of native collar or access realization, H1–H4, MLC, or ledger closure. Local Lean is unavailable; CI must validate the registered source.

## Attribution

Builds on Kahn–Kapiamba–Lyubich and the archive's stationary non-LC predecessor audit.
