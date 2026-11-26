---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="stationary-model-degree-20261126"></a>

# Light geometric quotient dynamics and exact quadratic model degree

## Claim

Candidate Lean result: for a continuous surjective semiconjugacy from the actual complex quadratic filled set with connected geometric fibers, lightness (total disconnectedness of each model point preimage) suffices for whole-fiber transport; the model then has at most two predecessors of every point. Every nonempty model predecessor fiber is exactly the image pair of two opposite physical roots. This is a reduction of the prior finite-model-fiber assumption to lightness, not an unconditional identification of the named source quotient.

## Evidence

[StationaryLightModel.lean](../../formalization/weighted/StationaryLightModel.lean) declares the following theorems, pending exact-head compilation:

- `component_image_univ`
- `fiber_image_eq_of_light_model`
- `quadratic_filled_light_fiber_image`
- `quadratic_filled_model_fiber_pair`
- `quadratic_filled_light_model_finite`

1. In a compact Hausdorff domain, each connected component is the intersection of all clopen neighborhoods of its anchor. If a target point were omitted from the component image, compactness of its point preimage would yield a finite clopen intersection also omitting that point. But the image of this nonempty clopen set under an open closed map is clopen and hence all of the preconnected target.
2. Apply this argument to the restriction of the physical map over the connected geometric successor fiber. Lightness forces the model image of the anchor's physical connected component to be a single predecessor. Therefore that predecessor's entire physical fiber maps onto the successor fiber even without model discreteness.
3. Use the actual bounded-orbit quadratic filled set and its compactness and complete invariance already proved in StationaryFiberDynamics. Opposite roots remain in the filled set; every model predecessor must contain a lift of any chosen physical successor point. Factoring the difference of squares exhausts these lifts, giving the exact pair and hence finiteness.

Reproduction: `cd formalization/weighted && lake build StationaryLightModel`, followed by repository-root `python3 -B code/verify_lean_coverage.py --audit weighted`. This environment has no Lean executable or network git access; repository CI is the compiler of record. No successful compilation is asserted yet.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE, KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN; StationaryFiberDynamics, StationaryGeometricFibers, Mathlib's compact Hausdorff component theorem and connected-set calculus.

## Boundary

The actual KKL/Kiwi quotient must still be identified as a continuous monotone semiconjugacy, and its lightness or an independent sufficient condition must be proved on that named geometry. The carrier and marked-small-Julia identification and access transport remain separate. No ledger status change, H1–H4 closure, or MLC proof is claimed.

## Attribution

Builds on the archive's November 26 stationary geometric fiber dynamics and the source context of Kahn–Kapiamba–Lyubich, Kiwi, and Douady–Hubbard. No external theorem is introduced as a proof constant.
