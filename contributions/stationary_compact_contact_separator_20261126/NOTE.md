---
ledger: KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-compact-contact-separator-20261126"></a>

# Quadratic compact-contact separator obstruction

## Claim

For the actual map f(z)=z²+c, let K be reflection invariant and Q be a reflection-invariant connected critical set containing zero. Suppose Q meets the closure of a preconnected unbounded exterior R disjoint from K. Then every compact subset of f(K minus Q) admits a continuous logarithm of w-c, and f is injective on every compact preconnected subset of K minus Q. If K is compact, any preconnected retained set on which f fails injectivity must have closure meeting Q. This applies in particular to an ambient component containing antipodal points. A further conditional closure proves full connected-component separation, including noncompact witnesses, if the actual retained image admits an increasing compact exhaustion by interiors with finitely many connected components at every stage. For a full compact carrier with empty interior, a different route forces every bypass avoiding zero to accumulate specifically at zero, and critical-point clearance suffices for full separation without the exhaustion hypothesis. The actual filled Julia set is full for every parameter: the maximum-modulus principle rules out bounded complementary components of the uniform bounded-orbit locus. Thus on that set the clearance route needs only empty interior and a relative critical neighborhood, not a fullness hypothesis.

## Evidence

Lean development: [StationaryCompactContact.lean](../../formalization/weighted/StationaryCompactContact.lean).

1. `preconnected_union_of_closure_contact`: a putative closed separation of Q union R must assign each preconnected set to one side; closure contact rules out assigning them to opposite sides.
2. `quadratic_image_unbounded`: the actual quadratic image of an unbounded set is unbounded, by the norm inequality.
3. `quadratic_compact_contact_log`: the image of Q union R is preconnected, unbounded, contains c, and is disjoint from the retained image by exact quadratic reflection saturation. For a compact test set the existing logarithm lifting theorem needs no closedness of the cut.
4. `quadratic_compact_contact_injOn`: exponentiate half the logarithm to construct a continuous inverse section, then apply actual quadratic injectivity on a preconnected set.
5. `quadratic_bypass_forces_critical_contact` and `quadratic_reflected_component_forces_critical_contact`: if a putative bypass closure avoided Q, it would be compact, preconnected and retained, contradicting the preceding theorem.

6. `quadratic_compact_contact_section` constructs a reference continuous inverse branch on every compact retained image target. `quadratic_equal_roots_sign` states the exact fiber alternative.
7. `quadratic_branch_extension_iff` proves that prescribed closed positive and negative sign loci extend to a continuous quadratic inverse branch on a compact Hausdorff base if and only if no connected component meets both. Necessity uses the clopen sign locus of any extension; sufficiency uses the existing compact component separation theorem and a piecewise branch.
8. `quadratic_section_restriction_extension_iff` gives the exact compatibility test for an independently selected inverse branch on a closed compact substage. This removes ambiguity between existence of a branch at every finite stage and preservation of a specified older branch.

9. `quadratic_section_finite_of_finite_components` shows that any reference branch gives at most two choices per connected component, with the values at representatives determining the branch.
10. `compatible_finite_system` proves coherence in a countable inverse system of nonempty finite levels by compactness of the product of discrete finite levels, without assuming surjectivity of any restriction. Every finite horizon is supplied by restriction from its last stage.
11. `quadratic_global_section_of_finite_component_exhaustion` applies this to continuous quadratic branches; the compatible family glues continuously because stage interiors cover the target.
12. `quadratic_global_contact_section`, `quadratic_no_bypass_of_finite_component_exhaustion`, and `quadratic_reflected_separator_finite_component_exhaustion` transfer the abstract gluing back to the actual quadratic map and exclude even connected noncompact or non-path-connected antipodal bypasses under the stated finite-component exhaustion hypothesis.

13. `compact_emptyInterior_exterior_data` produces exterior density, disjointness and unboundedness from compactness and empty interior.
14. `quadratic_full_emptyInterior_bypass_accumulates_zero` uses the singleton critical deletion to force accumulation at zero itself, independently of any larger deleted set.
15. `quadratic_full_emptyInterior_separator_critical_clearance` excludes antipodal bypasses for arbitrary deletions with relative clearance at zero; `quadratic_filled_separator_critical_clearance` specializes to the genuine filled Julia set, discharging compactness and reflection from earlier Lean theorems.

16. `compact_uniform_entire_locus_full` rules out bounded complementary components by the maximum-modulus principle, and connects unbounded components across a circle containing the carrier.
17. `quadratic_orbit_entire` proves differentiability of every actual quadratic iterate; `quadratic_filled_full` applies the general lemma using the already proved exact bounded-orbit characterization and uniform orbit bound.
18. `quadratic_filled_bypass_accumulates_zero` and `quadratic_filled_separator_of_emptyInterior_clearance` discharge fullness in the actual-carrier conclusions.

First six theorems: the exact push-head weighted CI job at `dbb52a442e26e80bd7571da0f0121a23790b26c4` [passed](https://github.com/dovvnloading/loops-research-archive/actions/runs/45884095449/job/140130391553). Its log states `AXIOM_AUDIT weighted StationaryCompactContact: 6 declarations, 6 theorems; allowed axioms only`. The next four named theorems [passed](https://github.com/dovvnloading/loops-research-archive/actions/runs/45884581789/job/140131996192) at `20eaa8cbb51e44c9bd1ee27fcd7081aee371ad75` (10 declarations, 10 theorems, allowed axioms only). The six exhaustion theorems compiled at `a52fd537fd895713a7d2552ab736a4496d98e8b6` ([run](https://github.com/dovvnloading/loops-research-archive/actions/runs/45885010430)); the [dependency audit passed](https://github.com/dovvnloading/loops-research-archive/actions/runs/45885010430/job/140133424487) with 16 declarations and 16 theorems, allowed axioms only. The four critical-clearance theorems and the five new fullness theorems are tracked by their subsequent exact-head CI runs.

Build: `cd formalization/weighted && lake build StationaryCompactContact`. The source is registered in the Lake target list, theorem index and source inventory using the same edits as contribute.py lean-add. Local Lean and a network-accessible shell checkout are unavailable. Verification is tracked by exact-head CI results in PR #209; only successful kernel builds plus transitive dependency audits count.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN, KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN, KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS. The imported archive module StationarySeparatorTransport supplies the logarithm construction, quadratic saturation, and section-based injectivity.

## Boundary

No accessible exterior ray, local connectivity, compactness of the removed-set complement, or native marked access is assumed by the compact-witness theorem. The actual source-specific exterior closure contact and reflection saturation of the physical carrier must still be established. The punctured carrier can have noncompact connected components: without the additional exhaustion hypothesis the result only forces any remaining reflected bypass to accumulate on the removed critical set. The exhaustion theorem excludes this residual failure only when the increasing compact finite-component exhaustion of the actual retained image is supplied. Neither the exhaustion hypothesis nor the sign-extension condition is verified for the native KKL carrier. The critical-clearance route instead requires fullness, empty interior, and a relative neighborhood of zero inside the native deleted set. Fullness is proved for the genuine filled Julia set, but empty interior, relative critical clearance, and the identification of the relevant native deleted set remain source-specific premises. The work does not prove the native collar/access realization, close the ledger row, or prove MLC. No status record changes.

## Attribution

Builds on Kahn–Kapiamba–Lyubich and the archive's November 26 separator transport development; the new argument uses the existing compact logarithm construction and quadratic reflection identity without its closed-ray hypothesis.
