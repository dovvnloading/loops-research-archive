---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-fiber-dynamics-20261126"></a>

# Geometric fiber dynamics and invariant marked-continuum saturation

## Claim

Candidate Lean results: full forward transport of connected geometric fibers under open closed physical dynamics and finite model point fibers; actual complex quadratic specialization; critical-value and two-sheet rigidity; exact recursively selected inverse-component transport; and saturation of maximal invariant marks whose model images avoid the trapping frontier image.

## Evidence

[StationaryFiberDynamics.lean](../../formalization/weighted/StationaryFiberDynamics.lean) contains nine public theorem declarations and one private helper. This is a proof candidate pending exact-head CI, not a claim of successful compilation.

1. `fiber_image_eq_of_finite_model_fibers`: for a continuous surjective monotone semiconjugacy p and an open closed physical map F, the image of each fiber over y is relatively open and closed in the fiber over G(y), provided the model predecessor fiber is finite. Its relative openness follows by deleting all other model predecessors, a finite closed set. Connectedness of the target fiber and nonemptiness force equality.
2. `iterate_fiber_image_eq`, `singleton_fiber_forward`: the equality composes along every finite orbit and preserves singleton fibers forward. Combined with the existing backward theorem this identifies propagation in both directions when its finite physical fiber premise also holds.
3. `quadratic_restriction_open`, `quadratic_restriction_fiber_image`: the actual quadratic on a compact completely invariant subspace is open and closed in its relative topology. This supplies the physical dynamical input, rather than assuming that a restriction to a nonopen filled set is open.
4. `quadratic_model_critical_preimage`, `quadratic_two_model_predecessors_injective`: the actual zero critical point has a unique physical inverse at its critical value; whole-fiber transport forces a unique model predecessor there. If a model point has two different predecessors, each physical predecessor fiber maps injectively onto the common successor fiber: otherwise a third distinct root would be required. The algebra uses the actual factorization of the difference of squares.
5. `selected_pullback_chain_full_lift`: the full preimage equality propagates recursively along actual connected components, given only the base equality and the matching component anchors at each depth. This uses the existing exact connected-component lift, not an equality of abstract tree labels.
6. `invariant_trapping_mark_saturated`: a mark that contains all points staying forever in an open return region and is forward invariant inside that region is saturated if its model image is disjoint from the image of the region frontier. Any orbit of another point in a mark fiber that leaves the region forces its connected fiber to hit the frontier. Unlike the previous global frontier-singleton criterion, only fibers meeting this mark are constrained.

Reproduction: in formalization/weighted run `lake build StationaryFiberDynamics`; at repository root run `python3 -B code/verify_lean_coverage.py`, `python3 -B code/verify_lean_coverage.py --audit weighted` and `python code/contribute.py check`. The local environment has no Lean executable or network git access. Exact-head repository CI is the compiler of record. No passing result is asserted until observed.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE, KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN. Imports StationaryGeometricFibers and QuadraticCylinderCensus. Source context: [stationary predecessor endpoint audit](../../research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md#corollary-44-model-incidence-and-exact-non-lc-residue) and [Kiwi model identification audit](../../research/mlc_unified/kkl_stationary_n2_kiwi_model_identification_audit_20260727.md).

## Boundary

The named native KKL/Kiwi projection, the model finite-to-one premise, the actual complete-invariance/straightening identification, base carrier saturation, matched component anchors and the trapping frontier separation for the physical small-Julia marks remain to be verified on the named geometry. Theorems are conditional, no ledger status change, H1–H4 or MLC is claimed. No priority claim is made.

## Attribution

Builds on the November 26 stationary geometric fiber and quadratic cylinder census contributions; Kahn–Kapiamba–Lyubich, Douady–Hubbard and Kiwi source context. No external theorem is introduced as a proof constant.
