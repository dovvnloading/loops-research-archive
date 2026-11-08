# Actual four-ray landing bifurcation at the 3/9 Misiurewicz tip

**Date:** 2026-11-07 (Eastern time). **Classification:** local theorem for the *actual ambient dynamical external rays* of a real quadratic family, using a certified ramified precritical pair inside its authentic period-9 and period-3 polynomial-like filled sets. This is not a KL `O/xi/eta` pseudo-piece transport theorem, a holomorphic motion of the full Julia set, a global ray-access atlas, H1--H4 closure, or MLC. Classical rational-ray landing and periodic-ray stability are cited and explicitly imported.

**Prior archive inputs.** [Exact nonattracting real 3/9 tip and four critical-point rays](period27_misiurewicz_tip_ray_access_20261106.md); [positive actual 3/9 complex quadratic-like domains](nonattracting_tip_complex_two_scale_20261106.md); [repelling return transversality and parameter-phase clocks](period9_tip_phase_parameter_transversality_20261107.md), merged #52; [exact precritical braid with both K9/K3 component membership](period9_tip_ramified_precritical_pair_20261107.md), merged #53. Primary classical ray input: J. Milnor, *Periodic Orbits, External Rays and the Mandelbrot Set*, Astérisque 261 (2000), §3, on stability of periodic rays at repelling cycles, https://archive.numdam.org/item/AST_2000__261__277_0/ ; S. Zakeri, *External Rays and the Real Slice of the Mandelbrot Set*, §§2--3, https://www.math.stonybrook.edu/preprints/ims02-02.pdf . The present theorem is an explicit source-specific consequence, not a discovery of general Misiurewicz ray bifurcation theory.

## 1. Fully explicit angle and precritical data

Let `f_c(z)=z²+c`, `P_0(c)=0`, `P_{j+1}(c)=P_j(c)²+c`, and let `c_*` be the exact real root of `P_18(c)+P_9(c)=0` isolated in the source's strict `2^-128` bracket (about `-1.78651054454432`). The critical point is strictly preperiodic (preperiod 10, eventual period 9). Its repelling ninth-return point `Z_*=P_10(c_*)` has multiplier `lambda_*` strictly between 3 and 4, and an analytic continuation `Z(c)` with `f_c^9(Z(c))=Z(c)`.

Merged #53 proves the existence of a holomorphic real-symmetric function `R(c)` with `R(c_*)=0`, `R'(c_*)=-kappa` and

\[
 0.276<\kappa<0.277,
 \qquad f_c^{10}(s)=Z(c)\quad\Longleftrightarrow\quad s^2=R(c)
\tag{1}
\]

in a neighborhood of `(c_*,0)`. For real `c` near `c_*`, the two solutions belong to genuine `K_9(c)\subset K_3(c)` from the already certified central polynomial-like domains. In particular, `s_±=±sqrt(R)` are real for `c<c_*`; they are `s_±=±i sqrt(-R)` for `c>c_*`.

The archive's actual Misiurewicz ray-landing theorem gives precisely these **four selected rational rays landing at 0 for c=c_***:

\[
\boxed{
 a=\frac{116791}{523264},\quad
 b=\frac{144841}{523264},\quad
 d=\frac{378423}{523264},\quad
 e=\frac{406473}{523264}.
}\tag{2}
\]

(The labels `a,b,d,e` are chosen to avoid using the parameter symbol `c` as a ray label.) Their strict cyclic order is `0<a<b<1/2<d<e<1`. The exact double/reflect relations are

\[
\boxed{d=a+\tfrac12,\quad e=b+\tfrac12,\quad
 1-a=e,\quad1-b=d.}\tag{3}
\]

Forward ten iterates give **two periodic rays landing at the same repelling point `Z_*`**:

\[
\boxed{
 2^{10}a=2^{10}d=\frac{283}{511}\pmod1,
 \quad2^{10}b=2^{10}e=\frac{228}{511}\pmod1.
}\tag{4}
\]

Both target angles have exact doubling period 9. These statements are checked by integer rational arithmetic, not by rendered Julia-ray pictures.

## 2. A local ray-pullback lemma with honest scope

**Lemma 2.1 (ray-tail continuation through an unfolding quadratic critical point).** Let `P_τ` be a real-symmetric holomorphic family of quadratic polynomials with connected filled sets for all real `τ` in an interval. Suppose (i) a marked repelling periodic point `Z(τ)` is the landing point of two specified periodic rational rays at `τ=0`, (ii) a selected local inverse of `P_τ^N` at `Z(τ)` has a simple quadratic critical point at `(τ,z)=(0,0)` and unfolds into two distinct roots `s_±(τ)` for `τ≠0`, and (iii) four specified preperiodic ray tails over the two periodic rays land at the critical point for `τ=0`, with each target ray having exactly its two local angle lifts among the four. Then on a sufficiently small punctured **real** parameter interval, all four specified rational rays land at the two roots `s_±(τ)`, one lift of each target periodic ray at each root.

*Proof.* The repelling periodic point and the two periodic-ray landing relations persist for sufficiently small parameter variation by the standard periodic-ray stability theorem (or by pulling back a compact terminal ray segment with the uniformly contracting local inverse of the periodic return map). Choose a small Jordan disk `D` around `Z(0)` containing terminal pieces of both rays and a small disk `U` around 0 such that the component of `P_τ^{-N}(D)` containing 0 is a proper degree-two branched disk for every sufficiently small `τ`. The last assertion follows by Rouché and the local quadratic critical order, after choosing the disks small and reducing the parameter interval. Its two inverse roots over `Z(τ)` are `s_±(τ)`.

Choose a positive equipotential level `t_0` so small that the four given ray points at potential `t_0` lie strictly in this source component at `τ=0`, and their forward-ray terminal segments at potentials up to `2^N t_0` lie in `D`. The ambient Böttcher coordinate at *positive* potential varies continuously with the real connected parameter, so the four ray points at `t_0` remain in the source component for all nearby `τ`. Since their forward images follow the two periodic ray segments strictly within `D`, each entire terminal segment at potentials `0<t≤t_0` stays in the same source component; it cannot cross its boundary without its `P_τ^N`-image crossing `∂D`. Off `τ=0` there is no critical value on these escaping rays (`P_τ^N(0)` is bounded in the filled set), so each terminal ray is an ordinary inverse branch of a periodic ray ending at one of the two simple preimages of `Z(τ)`. The two lifts of any one target ray land at different roots, by proper degree-two lifting (equivalently the exact evenness `P_τ^N(-z)=P_τ^N(z)` and the fact that its two roots are `±s`). This proves the lemma without claiming a global holomorphic motion of the ray all the way through `τ=0`. □

The pointwise ray-tail continuation here is a **real-slice** theorem. The parameter disk includes escaping parameters with possibly disconnected Julia sets, and the algebraic square-root monodromy of #53 does not automatically give a global dynamical-ray motion on that punctured disk.

## 3. Exact right/left ray pairing: a nontrivial dynamical bifurcation

**Theorem 3.1 (source-labelled ray portrait switch).** There exists `epsilon_0>0` such that for every real `c` with `0<|c-c_*|<epsilon_0`, all four selected ambient dynamic rays `R_c(a),R_c(b),R_c(d),R_c(e)` land at the **two actual precritical points** from (1), and their grouping is as follows:

| Parameter side | Precritical point | Exact selected ray landing angles |
|---|---|---|
| `c<c_*` | `+sqrt(R(c))` (positive real) | `{a,e}` |
| `c<c_*` | `-sqrt(R(c))` (negative real) | `{b,d}` |
| `c>c_*` | `+i sqrt(-R(c))` (upper half-plane) | `{a,b}` |
| `c>c_*` | `-i sqrt(-R(c))` (lower half-plane) | `{d,e}` |

Each root receives **one specified ray mapping under `f_c^10` to `283/511` and one mapping to `228/511`**. At the tip all four rays co-land at `0`.

*Proof.* All nearby real parameters lie in the real slice `[-2,1/4]⊂M`, so the global connected-Julia Böttcher map is defined on the entire escaping basin. The two target periodic angles from (4) land at the repelling continuation `Z(c)` by the classical stability of repelling periodic ray portraits. The archive's four critical ray tails at `c_*` satisfy the hypotheses of Lemma 2.1, with `N=10`, because `f_{c_*}^{10}(s)=Z_*` has local degree two at `s=0` and its nonzero quadratic coefficient is `(f_{c_*}^9)'(c_*)` (certified nonzero in #53). Thus each of the four rays lands at one of the two `s_±(c)`, with rays `a,d` landing at opposite roots and `b,e` at opposite roots.

For **every real** `c∈M`, the normalized Böttcher map respects conjugation and evenness:

\[
 \overline{\mathcal R_c(\theta)}=\mathcal R_c(1-\theta),
 \qquad -\mathcal R_c(\theta)=\mathcal R_c(\theta+1/2),
\tag{5}
\]

where the equalities are pointwise equalities of parametrized positive-potential rays at equal Green potential. A ray with `0<θ<1/2` cannot meet the real axis (its Böttcher coordinate has nonreal argument), so it lies entirely in the **upper** half-plane. Likewise `1/2<θ<1` rays lie entirely in the lower half-plane.

For `c>c_*`, `s_+` is strictly in the upper half-plane and `s_-` in the lower. Thus `a,b` land at `s_+`, `d,e` at `s_-`.

For `c<c_*`, both roots are real and each is fixed by conjugation. The reflection identities in (3) force the two selected ray pairs `{a,e}` and `{b,d}` to land at respective (distinct) real roots; they cannot land together, because `a` and `d=a+1/2` must land at opposite roots. Finally, since `a<b` and the positive-potential rays `a,b` are disjoint proper arcs in the upper half-plane from their asymptotic external directions to **distinct** real endpoints, planar cyclic order forces the endpoint of the lower-angle ray `a` to lie strictly to the right of the endpoint of `b` on the real axis. Thus `{a,e}` lands at `+sqrt(R)` and `{b,d}` at `-sqrt(R)`. This proves all four assignments. □

**This is a real, physical ray-pair bifurcation**, not merely a combinatorial angle pairing or an illustration. It identifies which specific rays land on which actual dynamical points on either side of a concrete certified Misiurewicz parameter. It does not assert the listed rays are all rays landing at these points (that would require a separate complete orbit-portrait census).

### Corollary 3.2 (actual marked phase-window ray accesses)

Let `c_n(t)>c_*` be the real phase-to-parameter windows from merged #52 with fixed `t` in its small target interval `J`, for sufficiently large `n`. Those parameters lie in the right-hand regime of Theorem 3.1. Thus the **specific ambient ray access pair `{a,b}` lands at**

\[
 s_+(c_n(t))=i\sqrt{\kappa B(t)}\,\lambda_*^{-n/2}
       \left(1+O(n\lambda_*^{-n})\right),
\tag{6}
\]

and the specific access pair `{d,e}` lands at the conjugate `s_-`. The error is uniform for `t∈J`. The endpoint points remain in the **same actual central 3/9 filled sets** `K_9(c_n(t))⊂K_3(c_n(t))` for all sufficiently large `n`.

These are **genuine, explicitly angle-labelled ambient ray-access germs** over a continuum of actual quadratic parameters. Because `s_±(c)` belong to the interior of both quadratic-like source domains `V_9(c),V_3(c)`, each ray has a terminal access germ in the complements `V_j(c)\setminus K_j(c)`, `j=3,9`. This does **not** assert any whole ray stays in the small domains, assign KL `O/xi/eta` tile sides, identify a local-cover sheet/coset action, or prove non-LC prime-end naturality.

## 4. The remaining geometric interface

This local bifurcation resolves the previously open **selected ray-to-precritical-root assignment on the real parameter slice**, after citing classical periodic-ray stability. It leaves three genuine gates: (i) a complete census of all rays at each root and their KL side labels, (ii) a proper-path and deck-monodromy natural transformation on the **ramified complex** parameter cover (not merely the real slice), and (iii) an all-scale compactness/rigidity statement. The current square-root braid prevents a naive single-valued ordered marking on the punctured complex disk, even though the selected real-ray access pairs are now explicit.

**No global status promotion:** Issue #40, H1--H4, UPTCR and MLC remain OPEN. This is a result for one finitely renormalizable/Misiurewicz tip and its nearby real parameters; analytic and ray-stability inputs are classical; independent specialist review and novelty/priority evaluation are still appropriate. OpenAI GPT-6 assisted in derivation, exact rational verification, and exposition.
