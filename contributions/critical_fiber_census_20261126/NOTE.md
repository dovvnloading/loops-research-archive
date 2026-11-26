---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="critical-fiber-census-20261126"></a>

# Ramification-aware exact inverse-fiber census for actual quadratic pullback components

## Claim

Let f_c(z)=z²+c. Write N_n(y) for the number of distinct solutions of f_c^n(z)=y, not the polynomial degree counted with multiplicity. For every complex parameter and target and every finite depth, the exact candidate formalization gives

    N_0(y)=1,
    N_{n+1}(y)+[f_c^n(c)=y]=2 N_n(y),
    D_0(y)=0,
    D_{n+1}(y)=2 D_n(y)+[f_c^n(c)=y],
    N_n(y)+D_n(y)=2^n.

The brackets denote the indicator of the equality. This includes repeated critical orbit hits, not just regular fibers. A local inverse fiber admits a disjoint signed-branch count after filtering by actual membership in the localization. A corrected global census suffices for unique component ownership under the existing proper open localization hypotheses.

## Evidence

The [Lean module](../../formalization/weighted/QuadraticCriticalFiberCensus.lean) imports the earlier actual quadratic census. All 18 public theorem names are registered; it is a default weighted build target.

1. `quadratic_surjective`, `fiberRoot_spec`, `fiberRoot_injective`: existence of an actual inverse point uses the proved open/proper map properties on the connected plane. The selected root need not vary continuously.
2. `mem_globalFiber`, `globalFiber_zero`, `globalFiber_succ`, `inverse_branches_disjoint`: exact set equality with the two signed inverse branches; the negative branch omits the critical value because both inverse points then coincide.
3. `globalFiber_card_step`, `globalFiber_card_exact`, `criticalFiberDefect_zero_iff`, `globalFiber_full_card_iff`: distinct-point counting, exact deficit, and equality with the degree precisely when the target avoids every relevant forward critical orbit value.
4. `globalFiber_census`, `quadratic_critical_component_census`: a finite set reaching the ramification-corrected degree exhausts the actual global fiber; the previous proper open localized count theorem gives unique component ownership under its stated hypotheses.
5. `localFiber_eq_filter_global`, `localFiber_signed_recursion`, `localFiber_signed_count`: exact localized count, without substituting the global degree for the number of inverse points actually in the domain.
6. `zero_parameter_zero_fiber_card`, `chebyshev_fixed_endpoint_fiber_card`: at c=0, the zero fiber has one distinct point at every depth. At c=-2, the fiber of the fixed endpoint 2 at depth n+1 has exactly 2^n+1 distinct points.

Validation protocol: the earlier weighted [CI run 45871708890](https://github.com/dovvnloading/loops-research-archive/actions/runs/45871708890) passed source coverage and rejected the arithmetic proof in `globalFiber_card_exact`: a broad `pow_succ` simplification altered the complex square in only one occurrence of the indicator. The repair restricts rewriting to the natural-number degree power. No theorem statement or trust policy is changed. Local Lean/lake and networked git are unavailable; only a successful weighted CI build and transitive dependency audit establish validation. This note records the candidate proof, not a green CI claim. The pull request conversation records the observed validation checkpoint.

Reproduction from repository root: `cd formalization/weighted && lake build QuadraticCriticalFiberCensus`, then from the root `python3 -B code/verify_lean_coverage.py --audit weighted`.

## Dependencies

`DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`, `FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS`, `INTERIOR_PULLBACK_COMPONENT_FORCING`. Earlier [finite-cylinder commuting lift](../../research/mlc_unified/finite_cylinder_commuting_lift.md), sections 4–5, and [single-fiber exhaustion](../cylinder_fiber_exhaustion_20261126/NOTE.md); Mathlib finite sets, complex arithmetic, and the existing `QuadraticCylinderCensus` module.

## Boundary

The exact local count still requires actual membership data; the arbitrary inverse-root choice is noncomputable, not a numerical root-finding algorithm. The global corrected count does not generally equal the localized count. The component theorem requires openness, properness, a connected open typed target, and distinct declared component anchors. This does not supply those geometric hypotheses in the source's general virtual-stage class, does not construct the marked cylinders, prove access or chronology metadata, establish cross-base ownership or changing-target enlargement naturality, or close the ledger obligation. No claim to literature priority, MLC, or H1–H4 closure.

## Attribution

Builds on Kahn–Lyubich's decoration construction (arXiv:math/0609046), the archive's commuting-iterate and proper-component census, and Mathlib. The distinct-point formula follows from elementary inverse branching; its contribution here is an explicit formalization and integration into the actual complex pullback census, not a priority claim.
