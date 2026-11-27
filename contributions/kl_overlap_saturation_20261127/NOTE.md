---
ledger: DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="kl-overlap-saturation-20261127"></a>

# A persistent full-angular overlap obstruction in the actual Chebyshev top puzzle

## Claim

For the actual quadratic polynomial `f(z)=z^2-2`, the explicit ordinary top-puzzle parent and its two second-iterate branches have a full central-overlap defect in **every positive-height collar that retains all angles**. The witness is a genuine point of the complex dynamical plane, lies in the parent interior, and lies outside the **closures of both source pieces**. The result also applies to every continuous based logarithmic tile lift commuting with the physical projection; its identity formula is proved, not assumed.

The general coordinate calculation gives a necessary and sufficient saturation criterion and the exact region that a retained set must avoid. The Chebyshev specialization supplies open simply connected physical puzzle domains, compact embedded closures, exact branch dynamics, and their exterior-component dictionary.

**This is a partial result on the ledger obligation.** The Chebyshev critical orbit does not return, so this example does not instantiate the recurrent primitive-renormalization stage package. The universal native KL question remains open; no ledger promotion is requested.

## Evidence

### 1. The actual objects and their maps

Use the archive's already proved Chebyshev external coordinate

\[
 J(w)=w+w^{-1},\qquad
 \Phi(\theta,t)=J\!\left(e^{t+2\pi i\theta}\right).
\]

The source of the physical quadratic, the filled-set identity `K(f)=[-2,2]`, the Joukowski fiber calculation, and exterior injectivity is the existing `ChebyshevFibers.lean`. These classical inputs are reused rather than presented as new results.

For `h>0`, define the following **whole open physical domains**, including height zero and negative signed heights:

| Domain | Angle interval | Signed-height interval |
|---|---|---|
| `parentDomain h`, denoted `P` | `(1/6,1/3)` | `(-h/2,h/2)` |
| `leftDomain h`, denoted `Q_L` | `(7/24,1/3)` | `(-h/8,h/8)` |
| `rightDomain h`, denoted `Q_R` | `(1/6,5/24)` | `(-h/8,h/8)` |

A domain is the image of its rectangle under `Phi`. Negative height supplies the lower exterior component through `Phi(theta,t)=Phi(1-theta,-t)`. Height zero supplies the real filled interval; it is not removed from the domain.

`point_injective_half_turn` proves that `Phi` is injective whenever both angles lie in `(0,1/2)`, with **no sign restriction on either height**. Indeed, the two Joukowski fiber alternatives reduce to an integer difference of angles or an integer sum of angles. The first forces equality; the second is excluded by the half-turn bounds.

`LogarithmicTileGeometry.lean` proves that `J(exp z)` is entire and open. `ChebyshevPuzzleGeometry.lean` then proves:

- `puzzle_isOpen` and `puzzle_isSimplyConnected` for the indicated nonempty rectangles;
- an open embedding of each signed-height rectangle into the actual plane;
- `closed_rectangle_embedding` for the compact closed rectangles;
- `puzzle_closure_eq_closedPuzzle`, so the closure is exactly the image of the closed rectangle.

Consequently the closed rectangles give explicit embedded closures with their four boundary arcs; the topology of the physical domains is not assumed.

The actual second iterate has the following branch formulas:

\[
 f^2(\Phi(\theta,t))
 =\Phi(4\theta-1,4t)\quad\text{on }Q_L,
\]

\[
 f^2(\Phi(\theta,t))
 =\Phi(1-4\theta,-4t)\quad\text{on }Q_R.
\]

`left_domain_second_iterate_bijOn` and `right_domain_second_iterate_bijOn` prove bijectivity of the genuine polynomial iterate from each whole source domain onto `P`. `branch_domains_subset_parent` and `branch_domains_disjoint` prove containment and disjointness. The parent contains the actual critical point, while `critical_exits_whole_parent` proves `f^2(0)=2` and `2` is outside the parent. `parent_ray_vertices` identifies the two parent landing vertices as `1` and `-1`.

The exact physical exterior decomposition is also proved:

\[
 Q_L\setminus[-2,2]
 =\Phi((7/24,1/3)\times(0,h/8))
  \cup\Phi((2/3,17/24)\times(0,h/8)),
\]

\[
 Q_R\setminus[-2,2]
 =\Phi((1/6,5/24)\times(0,h/8))
  \cup\Phi((19/24,5/6)\times(0,h/8)).
\]

Thus the four exterior components are derived from the whole physical domains, rather than supplied as independent labels.

### 2. The explicit defect and its complete record

Given `h>0` and any collar height `delta>0`, set

\[
 t=\frac12\min(\delta,h/8)>0,\qquad
 \zeta_t=t+\frac{\pi i}{2},\qquad
 z_t=J(e^{\zeta_t})=i(e^t-e^{-t}).
\]

The quarter angle lies in the parent upper interval `(1/6,1/3)`, strictly between the two source upper intervals. The signed-height injectivity theorem proves

\[
 z_t\in P\setminus(\overline{Q_L}\cup\overline{Q_R}),
 \qquad z_t\notin[-2,2].
\]

The closed-piece exclusion is `quarter_outside_branch_closures`. In fact its angular separation conclusion holds at every real signed height, not only at the positive heights used here. `ordinary_inclusion_counterexample` packages the positive-height collar, target seam, both source-seam failures, parent membership, closed-source exclusion, and filled-set exclusion into one theorem.

| Required datum | Exact certificate |
|---|---|
| Source component | Upper exterior tile of either `Q_L` or `Q_R` |
| Source gluing angles | Left `(7/24,1/3)`; right `(1/6,5/24)` |
| Target component | Upper parent component `(1/6,1/3)` |
| Full source carrier height | `h/4`, strictly larger than source puzzle height `h/8` |
| Target carrier / puzzle heights | `h` / `h/2` |
| Sheet | Based logarithmic lift with integer offset zero; the full integer sheet coordinate is retained |
| Witness angle / height | `theta=1/4`, `t=min(delta,h/8)/2` |
| Physical point | `i*(exp(t)-exp(-t))` |
| Inclusion itinerary | Source upper tile to target upper tile; no dynamical iterate is inserted |
| Separate dynamical itinerary | Under `f^2`, left upper goes to parent upper; right upper goes to parent lower |
| Target-central location | Parent interior outside both closed source domains |

This is a **saturation or footprint defect**. It does not assert two source preimages of one quotient point. The relative overlap identity over the image of `Q_i`, used in the already archived injectivity argument, is not contradicted.

### 3. Identity of the inclusion lift is a conclusion

Let

\[
 S_H=\{\zeta\in\mathbb C:0<\operatorname{Re}\zeta<H\},
 \qquad \pi(\zeta)=J(e^\zeta).
\]

Consider any `L : C -> C` continuous on `S_(h/4)`, mapping it into `S_h`, satisfying `pi(L(zeta))=pi(zeta)` throughout the source, and fixing one anchor in that source. `LogarithmicTileLift.lean` proves that `L` is the identity on the entire source tile. Positivity excludes the reciprocal Joukowski fiber; exponential covering uniqueness gives one constant integer deck displacement; the anchor forces that displacement to be zero.

This class is nonempty. `ordinary_inclusion_is_based_lift` supplies `L=id`, with the left-seam anchor of angle `5/16` and height `h/16`.

`based_lift_collar_reflection_fails` proves that for every such lift, both source full-reflection equations fail after restriction to

\[
 C_\delta=S_{\min(\delta,h/4)}.
\]

`based_lift_closed_piece_reflection_fails` makes the boundary convention robust. Its source overlap sets may be **any** sets `S_L,S_R` whose physical projections lie in `closure Q_L` and `closure Q_R`; its target overlap may be any set `T` containing the open parent upper seam. It proves

\[
 C_\delta\cap L^{-1}(T)\ne C_\delta\cap S_L,
 \qquad
 C_\delta\cap L^{-1}(T)\ne C_\delta\cap S_R.
\]

No assumption of injectivity of the glued pseudo-piece is used, and no nominal boundary label is substituted for an actual physical point.

### 4. Exact classification and the permitted repair

In `KLTileSaturation.lean`, a full tile is `R x (0,H)` and an interior seam is `(a,b) x (0,h)`. Under the explicit nonempty nested-seam hypotheses

\[
 A\le a<b\le B,\qquad 0<h\le H,\qquad h\le u,
\]

`full_saturation_iff` proves

\[
 (\mathbb R\times(0,H))\cap((A,B)\times(0,u))
 =(a,b)\times(0,h)
\]

if and only if

\[
 a=A,\qquad b=B,\qquad h=\min(H,u).
\]

For a full-angular inner collar below both puzzle heights, reflection is equivalent to equality of the angular intervals. Thus changing height alone cannot repair a strict angular enlargement.

`saturation_defect_exact` identifies the entire defect inside the source tile and target seam by

\[
 \theta\le a\quad\text{or}\quad b\le\theta
 \quad\text{or}\quad h\le t.
\]

These endpoint inequalities belong to the **open-seam** convention. `retained_saturation_iff` proves that an arbitrary retained set restores the equation exactly when it avoids this defect. Angular trimming is therefore allowed; the theorem does not rule out every possible retained collar. `direct_branch_radial_defect` also records the separate positive-height radial defect, but the angular defect is stronger because it persists arbitrarily near the inner end.

### 5. Lean verification

All new Lean files are registered in the weighted project's default build targets, `physical_bridge_index.json`, and `physical_bridge_sources.tsv`. No workflow or ledger file is changed. The proof sources contain no proof placeholders or added axioms. The repository's existing audit checks the complete transitive axiom dependencies against `propext`, `Classical.choice`, and `Quot.sound`.

Project build command:

```sh
cd formalization/weighted
lake build KLTileSaturation LogarithmicTileLift LogarithmicTileGeometry ChebyshevDecoration ChebyshevPuzzleGeometry ChebyshevTileSaturation
```

Repository checks:

```sh
python code/contribute.py check
python code/verify_lean_coverage.py
python code/verify_physical_bridge_contracts.py
```

The full weighted CI workflow runs `python code/verify_lean_coverage.py --audit weighted` after building all registered modules. The first checkpoint `bf6af01e3f5dbac20040738f943ed38577023ab8` passed that full build and audit in [run 45951332396](https://github.com/dovvnloading/loops-research-archive/actions/runs/45951332396); later proof checkpoints remain in this pull request. Final integration validation is recorded below when complete.

## Dependencies

- Ledger target: `DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION`.
- Imported source context: `KL_DECORATION_ESCAPE_PUZZLE`; this contribution does not instantiate its full primitive-renormalization package.
- Existing Lean: `ChebyshevFibers.lean`, and its existing `ParabolicComplexPullback` / `ParabolicSegment` dependencies.
- Mathlib: exponential fibers and covering uniqueness, the complex open mapping theorem, convex contractibility and simple connectivity, and compact/open embedding facts. Their uses are explicit Lean imports and proofs.
- Kahn and Lyubich, *A priori bounds for some infinitely renormalizable quadratics. II. Decorations*, [arXiv:math/0609046v2](https://arxiv.org/pdf/math/0609046), §2.1 and Lemma 2.1 (ordinary top puzzle and direct branches), §3.2.1 and Lemmas 3.3–3.4 (pseudo-piece gluing/naturality), §3.2.4 (boundary conventions). The primitive-renormalizability assumption in §2.2 is retained as a scope restriction, not asserted for `c=-2`.

## Boundary

The result is an exact obstruction for the explicit **nonrecurrent Chebyshev ordinary top puzzle** and for its specified based physical lift class. The critical orbit is `0 -> -2 -> 2 -> 2`; it does not supply the modified principal nest or a terminal primitive little-Julia cycle. There is no formal realization here of an arbitrary recurrent native KL stage, its canonical localization, or its nontrivial sheet groupoid. A separately constructed gluing embedding or an actual native stage must satisfy the theorem's source and target overlap hypotheses before the theorem applies to it.

Accordingly, the full ledger row stays **open**. What is eliminated is the proposed repair by height thinning alone for the demonstrated angular geometry. A valid native retained-collar theorem must control the angular footprint or otherwise remove and account for this defect. The result does not rule out angularly selected collars and does not invalidate the archived relative-cartesian gluing theorem.

No Wave-width estimate, universal compactness statement, H1–H4 assertion, UPTCR, or MLC conclusion is claimed. No priority beyond the inspected archive is claimed.

## Attribution

The target and distinction between full saturation and relative overlap are from the archive's [relative-overlap audit](../../research/mlc_unified/kl_relative_overlap_cartesianity.md), especially §§5, 7.1, and 10. Its abstract disk example and relative gluing theorem are not re-proved here.

The angular labels and the distinction between puzzle height and carrier height are drawn from the [ordinary KL side atlas](../../research/independent_audits/tip_kl_pseudopiece_side_atlas_20261106.md), §§2–3. That atlas's existing `W -> V0` side collisions involve different source tiles entering one target tile. This contribution instead addresses the **direct** `Q_L,Q_R -> P` central-saturation equation and its persistent full-angular collar defect. It builds a separate exact Chebyshev physical realization; it does not assert a Lean identification with the archive's period-three/period-nine tip parameter.

The Joukowski semiconjugacy and classical analytic/topological theorems belong to the cited mathematical sources and existing Lean libraries. The new archive contribution is their use to obtain the direct-branch saturation classification, whole-domain physical witness, closed-source exclusion, and arbitrary-based-lift collar obstruction.
