---
ledger: DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="kl-overlap-saturation-20261127"></a>

# Full central-overlap saturation in ordinary KL logarithmic tiles

## Claim

First locally compiled checkpoint: nine public Lean theorems classify the full central-overlap equation in logarithmic coordinates, identify its exact angular and height defects, and prove that both direct branches have a defect in every positive-height full-angular collar. The actual-quadratic bridge is in progress; no ledger closure is claimed.

## Evidence

The registered module `formalization/weighted/KLTileSaturation.lean` compiled locally with Lean 4.32.0. Its main theorems are `full_saturation_iff`, `full_angular_collar_saturation_iff`, `saturation_defect_exact`, `retained_saturation_iff`, and `direct_branch_defect_in_every_collar`. For a source angular interval `(a,b)`, source puzzle height `h`, source carrier height `H`, and target interval/height `(A,B,t)`, the full equality holds precisely when `a=A`, `b=B`, and `h=min(H,t)`, under the explicit nonempty nested-seam hypotheses. The exact removed locus is the target seam inside the source tile where angle is at most `a`, angle is at least `b`, or height is at least `h`.

The initial source comparison found that the ordinary side atlas distinguishes puzzle height from the larger carrier height. We will test the resulting height and angular saturation defects against the actual inclusion lift, register all Lean theorems in the repository project, and require the CI build and transitive proof audit before reporting a proved result.

## Dependencies

- DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION.
- KL_DECORATION_ESCAPE_PUZZLE.
- research/mlc_unified/kl_relative_overlap_cartesianity.md.
- research/independent_audits/tip_kl_pseudopiece_side_atlas_20261106.md.
- Kahn and Lyubich, A priori bounds for some infinitely renormalizable quadratics. II. Decorations, sections 3.2.1 and 3.2.4 and Lemmas 3.3–3.4.

## Boundary

The full psi-quadratic-like category, the canonical localized immersions, and their physical-to-coordinate identifications are not assumed to be ordinary nested annuli. Any proved ordinary-coordinate theorem will retain that qualifier. This checkpoint does not establish the target obligation, any of H1–H4, or MLC. The ledger remains unchanged.

## Attribution

This work builds on the archive's relative-versus-full overlap distinction and its actual ordinary KL side atlas. Its intended new contribution is the exact saturation defect and collar classification, not a repetition of the archived gluing theorem.

## Progress checkpoint

Commit `bf6af01e3f5dbac20040738f943ed38577023ab8` passed the full weighted Lean build and transitive axiom audit in [workflow run 45951332396](https://github.com/dovvnloading/loops-research-archive/actions/runs/45951332396). Research validation, contribution intake, and model-to-geometry coverage also passed at that checkpoint.

The next development uses the actual quadratic `z^2-2`, its already-archived Joukowski external coordinate, signed-height puzzle domains, and an arbitrary continuous based lift commuting with the physical projection. The signed-height branch domains are constructed explicitly; their topology and dynamic bijections are being checked. This is a nonrecurrent ordinary top-puzzle instance. It does not instantiate the primitive-renormalization stage package required by the full ledger row. The latter remains open.

The second locally compiled module, `LogarithmicTileLift.lean`, proves eight public adapter theorems. Equality under the physical projection `J(exp z)` on positive-height sheets gives equality of exponential coordinates. Covering uniqueness then gives one constant integer deck displacement on any preconnected source, and one based anchor forces the whole tile map to be the identity. Thus the later application need not assume an identity formula for its tile map. The new module has been compiled locally; its CI result is pending at this commit.
