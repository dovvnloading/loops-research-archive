---
ledger: KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-compact-contact-separator-20261126"></a>

# Quadratic compact-contact separator obstruction

## Claim

For the actual map f(z)=z²+c, let K be reflection invariant and Q be a reflection-invariant connected critical set containing zero. Suppose Q meets the closure of a preconnected unbounded exterior R disjoint from K. Then every compact subset of f(K minus Q) admits a continuous logarithm of w-c, and f is injective on every compact preconnected subset of K minus Q. If K is compact, any preconnected retained set on which f fails injectivity must have closure meeting Q. This applies in particular to an ambient component containing antipodal points.

## Evidence

Candidate Lean development (CI pending): [StationaryCompactContact.lean](../../formalization/weighted/StationaryCompactContact.lean).

1. `preconnected_union_of_closure_contact`: a putative closed separation of Q union R must assign each preconnected set to one side; closure contact rules out assigning them to opposite sides.
2. `quadratic_image_unbounded`: the actual quadratic image of an unbounded set is unbounded, by the norm inequality.
3. `quadratic_compact_contact_log`: the image of Q union R is preconnected, unbounded, contains c, and is disjoint from the retained image by exact quadratic reflection saturation. For a compact test set the existing logarithm lifting theorem needs no closedness of the cut.
4. `quadratic_compact_contact_injOn`: exponentiate half the logarithm to construct a continuous inverse section, then apply actual quadratic injectivity on a preconnected set.
5. `quadratic_bypass_forces_critical_contact` and `quadratic_reflected_component_forces_critical_contact`: if a putative bypass closure avoided Q, it would be compact, preconnected and retained, contradicting the preceding theorem.

Build: `cd formalization/weighted && lake build StationaryCompactContact`. The source is registered in the Lake target list, theorem index and source inventory using the same edits as contribute.py lean-add. Local Lean and a network-accessible shell checkout are unavailable. Validation is pending the repository CI; no theorem is counted as verified yet.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN, KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN, KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS. The imported archive module StationarySeparatorTransport supplies the logarithm construction, quadratic saturation, and section-based injectivity.

## Boundary

No accessible exterior ray, local connectivity, compactness of the removed-set complement, or native marked access is assumed by the compact-witness theorem. The actual source-specific exterior closure contact and reflection saturation of the physical carrier must still be established. The punctured carrier can have noncompact connected components: the result only forces any remaining reflected bypass to accumulate on the removed critical set. It does not exclude such accumulation, prove the native collar/access realization, close the ledger row, or prove MLC. No status record changes.

## Attribution

Builds on Kahn–Kapiamba–Lyubich and the archive's November 26 separator transport development; the new argument uses the existing compact logarithm construction and quadratic reflection identity without its closed-ray hypothesis.
