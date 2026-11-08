# All twelve actual coarse-only precritical ray pairs, by the original alpha-puzzle geometry

**Date:** 2026-11-07 (Eastern time). **Target:** [Issue #29](https://github.com/dovvnloading/loops-research-archive/issues/29) and stacked [PR #55](https://github.com/dovvnloading/loops-research-archive/pull/55). **Result:** an exact **complete landed access census** for the 12 precritical points in `K3\K9` at the certified nonattracting real 3/9 Misiurewicz tip. Each point receives its *two genuine ambient dynamical external ray angles*, and each is assigned to a **true depth-three alpha-puzzle face of the once-renormalized map** `G=f^3`. Four source-defined faces hold `2,4,4,2` of those points. Together with the three already known fine-stage points, this exhausts the **15 distinct** physical depth-ten precritical points in `K3` at the tip. A new Lean theorem checks the finite, source-specified angle sieve and numerical pair partition. The analytic steps still use separately named classical/source-proved geometric inputs; this is **not** a Kahn–Lyubich canonical localization-sheet comparison or proof of MLC.

## 1. Why this closes a geometric gap rather than just generating a symbolic table

Merged PRs #52–#54 certify the genuine polynomial `f(z)=z²+c_*`, the exact parameter `c_*` with critical preperiod 10 and repelling period 9, the two nested physical quadratic-like returns `G=f³:V3→U3` and `f⁹:V9→U9`, and the selected eight rational ambient rays at `p,-p,0`. PR #55 (currently draft/stack parent) proves that the depth-ten inverse fiber of the repelling periodic point `Z=P10(c_*)` has **1024 multiplicity-weighted roots globally, 16 in K3, 4 in K9**, and **2048/32/8 corresponding ambient ray accesses**. It identifies the 32 internal period-three ray angles but leaves the 24 ambient angles and the 12 coarse-only landing pairs unnamed.

The critical *new* input is **not an assumed tuning correspondence**. It is the actual landed alpha-ray puzzle from the existing archive:

- [Complete ambient alpha-ray pullback table](./tip_puzzle_ray_tree_20261106.md), §§2–3: the ray-pair boundary of the physical **ambient** central depth-six puzzle piece `Y_f^6`, its strict Jordan containment in `Y_f^3`, and the fact that `f³:Y_f^6→Y_f^3` is a proper degree-two polynomial-like representative of **the same actual** `K3`.
- [Ordinary KL side atlas](./tip_kl_pseudopiece_side_atlas_20261106.md), §3: the exact four **external** angular seam intervals of `Y_f^6`. This is the full ray-pair face, not a made-up set of binary words.
- [Actual ambient lifts of the G-internal alpha puzzle](./tip_internal_puzzle_ambient_lifts_20261106.md), §§2–4: the actual *second-stage* alpha-ray tree, its inverse-branch slit rule, the source-defined `Pi3`, and its genuine internal ray/landing correspondence. Its central top-depth-three face is the union of `(5/24,7/24)` and `(17/24,19/24)` in **G-internal** angle coordinates, not ambient `f` angles.
- [Levin at the nonattracting tip](./levin_tip_p2_carathéodory_two_scale_20261106.md), Theorems 1 and 3, with (p1)/(p2) verified for both returns. In particular `Pi3` has a monotone degree-one circle extension and `Pi3(114/511)=5/7`. **No** identification of these maps with Kahn's infinite coset-valued sheets is made.

The analytically proved ray-trapping implication from these sources is the essential bridge: **if** a rational external ray avoids the finite alpha-puzzle boundary vertices and its angle lies in the critical piece's strict external face, its landing point is in the *interior* of that actual Jordan puzzle piece. This follows by noncrossing of the actual landed boundary rays; otherwise a path from infinity to the landing point would cross one of them. At our chosen fiber, every landing point is a preimage of the period-nine orbit, whereas an alpha-puzzle vertex is preperiodic to the **different** dividing alpha orbit, so boundary-vertex equality is impossible. The strictness is important.

## 2. The exact source-realized two-checkpoint sieve

The ambient normalized Böttcher coordinate identifies a rational angle with an element of `R/Z`, and multiplication by `8` represents one physical `G=f³` iterate. Put

\[
 t_-=228/511,\quad t_+=283/511,
 \qquad \mathcal F_{10}=\{(t+k)/1024:t\in\{t_-,t_+\},\;0\le k<1024\}.
 \tag{2.1}
\]

These are the **2048 distinct exact external angles** of the complete depth-ten preimage fiber, by PR #55. The source's ambient *physical* central `Y_f^6` face has the four **actual** open angular seams

\[
 \boxed{
 \mathcal I_f=
 (41,43)/192\;\cup\;(53,55)/192\;\cup\;
 (137,139)/192\;\cup\;(149,151)/192.}
 \tag{2.2}
\]

Here `(a,b)/192` means `(a/192,b/192)`, not a formal quotient of the dynamically defined ideal boundary. No boundary equality occurs for the angles below.

**Theorem 2.1 (actual geometric 32-ray selector).** Define

\[
 \boxed{\mathcal E=\{\theta\in\mathcal F_{10}:
 \theta\in\mathcal I_f,\quad 8\theta\pmod1\in\mathcal I_f\}.}
 \tag{2.3}
\]

Then **exactly 32** angles survive (2.3). All 32 also satisfy `64θ mod1∈I_f`, and **the set is exactly the 32 actual ambient ray angles landing at the 16-multiplicity central fiber `K3∩f^{-10}(Z)`**. At the tip these rays land at 15 distinct points, as in §4. Equivalently, after writing all angles over the common denominator `523264=1024·511`, the numerators in **strict increasing order** are

\[
\boxed{\begin{gathered}
112137,112192,112648,112703,116225,116280,116736,116791,\\
144841,144896,145352,145407,148929,148984,149440,149495,\\
373769,373824,374280,374335,377857,377912,378368,378423,\\
406473,406528,406984,407039,410561,410616,411072,411127.
\end{gathered}}
\tag{2.4}
\]

**Proof—finite part.** Using rational `Fraction` arithmetic, first filtering all 2048 inputs by `θ∈I_f` leaves **80**; applying the `8θ` filter leaves **32** (16 over each periodic target); a further `64θ` filter removes **none**. The script verifies all strict rational inequalities, all 32 distinct numerators and their ten-step periodic-ray images. `TipActualCoarseRays.lean` kernel-checks the exact `80/32` counts, survivors, and strict source-sector inequalities with `decide +kernel`. Thus the set (2.4) is a **genuine finite source-sector sieve**, not a numerical ray simulation.

**Proof—analytic landing and membership.** Every `θ∈F10` has a rational external ray landing at some root `z` of `f^{10}(z)=Z` by the source's connected-Julia Böttcher covering and the complete repelling-ray portrait. The actual alpha-puzzle faces above give:

\[
 \theta,8\theta,64\theta\in\mathcal I_f
 \quad\Longrightarrow\quad
 z,\;G(z),\;G^2(z)\in\operatorname{int}Y_f^6.
 \tag{2.5}
\]

The endpoints avoid alpha-puzzle vertices because their eventual orbit is the repelling period-nine cycle rather than the dividing alpha cycle. The next point `G³(z)=f^9(z)` is **one of the two genuine points** `p,-p`, both already in `K3⊂intY_f^6`, and all further `G` iterates remain there. Therefore the **entire G-forward orbit of z** stays in `Y_f^6`, proving that `z` belongs to the genuine quadratic-like filled set `K(f³|Y_f^6)=K3`. Thus all 32 filtered rays land in the real `K3` fiber. The independent degree-two return census in PR #55 proves there can be **only 32 such ambient rays in total**. So the inclusion is an equality. This step uses actual analytically landed boundaries and proper domain identification; the checker alone does not prove it. `□`

**No tuning hypothesis is used in this proof.** One can verify afterward that each of the 32 fractions is obtained by applying the airplane digit substitution `σ(0)=011, σ(1)=100`, then discarding the first two binary digits, to its internal angle. That exact match is a second arithmetic check, **not** the rationale for membership or a blanket dynamical tuning theorem.

## 3. All 32 internal labels by source-defined Levin cyclic order

At the same tip, PR #55 and the existing source identify the **32 genuine internal period-three angles** as

\[
 \mathcal Q_3=
 \left\{(q+k)/8: q\in\{2/7,5/7,3/14,11/14\},\; k=0,\ldots,7\right\},
 \tag{3.1}
\]

with no repetition; `Pi3` maps the physical 32-angle set **bijectively** onto it by the source's ray correspondence and exactly matching finite cardinalities. Since the global Levin extension is monotone of degree one, it preserves cyclic order. Sorting both 32-element lists, the source-certified anchor

\[
 \boxed{\Pi_3(114/511)=5/7}
\]

fixes the unique cyclic offset. The ambient ray has **zero-based index 6** in (2.4), whereas `5/7` has **index 22** in sorted (3.1), giving offset **16 modulo 32**. Therefore, for ambient angle `θ_i` (zero-based sorted),

\[
 \boxed{\Pi_3(\theta_i)=q_{(i+16)\bmod32}.}
 \tag{3.2}
\]

This is **not** an arbitrarily assigned finite coding: it is the unique restriction of the actual source-defined Levin map, using its global degree-one monotonicity and one already proved physical anchor. All **eight known labels** from PR #55 agree independently with (3.2). The complete 32-row pairing is in the JSON manifest.

## 4. All twelve previously missing physical ray pairs

The source's genuine once-renormalized quadratic map `G=f³` has a critical value with **internal** ambient ray angles `25/56` and `31/56`. This also follows directly from the already certified `Pi3` values at the four physical rays at `0`: doubling `25/112,31/112,81/112,87/112` gives precisely those two target angles. Take the slit along `25/56`. Its two inverse branches divide the *internal* circle at `25/112` and `25/112+1/2`; this is the same analytic inverse-ray construction used by the archive for the actual G-internal alpha puzzle.

Start with the four **different** internal rays at the two physical target points:

\[
 p:\{2/7,5/7\},\qquad -p:\{3/14,11/14\}.
 \tag{4.1}
\]

Pull each pair back through **three iterations of the physical quadratic-like return `G`**, selecting the inverse ray lift in each of the two critical-value-slit semicircles. Off the critical value, the inverse map is univalent and keeps the two rays of a pair at the same simple inverse landing point. **At the critical value** `{25/56,31/56}`, the four distinct angle halves co-land at the single critical point `0`, and must *not* be split into two fictitious points. This produces precisely **eight** physical pairs over `p`, and **seven** distinct physical landing classes over `-p`, one of which is the four-ray critical point. Thus it constructs 15 genuine physical landing classes, comprising 14 ordinary two-ray classes plus the critical quartet.

Using the bijection (3.2) to transfer these actual internal G accesses to the physical ambient `f` rays yields the following **complete table of the 12 formerly unnamed K3\K9 points**. Every entry is a pair of numerators over the common ambient denominator **523264**; a pair is the *actual two landed physical dynamical rays* at one simple preimage of `Z`.

| Preimage family | Pair index | Exact ambient ray-angle numerators (divide by 523264) |
|:--|--:|:--|
| `G³(z)=p` | 0 | `116280`, `406984` |
| `G³(z)=p` | 1 | `145352`, `377912` |
| `G³(z)=p` | 2 | `112648`, `410616` |
| `G³(z)=p` | 3 | `148984`, `374280` |
| `G³(z)=p` | 6 | `112192`, `411072` |
| `G³(z)=p` | 7 | `149440`, `373824` |
| `G³(z)=-p` | 0 | `116225`, `407039` |
| `G³(z)=-p` | 1 | `145407`, `377857` |
| `G³(z)=-p` | 2 | `112703`, `410561` |
| `G³(z)=-p` | 3 | `148929`, `374335` |
| `G³(z)=-p` | 5 | `112137`, `411127` |
| `G³(z)=-p` | 6 | `149495`, `373769` |

The remaining three physical classes are exactly those known from the earlier PRs: `p` with rays `114/511,397/511`, `-p` with `283/1022,739/1022`, and `0` with the critical quartet `a,b,d,e`. The all-stage ray budget is now accounted for with **no unnamed ambient angles**:

\[
\underbrace{12\times2}_{\text{new coarse-only rays}}+
\underbrace{2+2+4}_{\text{known fine rays}}=32.
\tag{4.2}
\]

Distinctness of the 12 new physical points is **not inferred from different angle pairs alone**. Each is an unramified root of `f^{10}(z)=Z` by the exact first-arrival proof of PR #55. Every simple root has exactly one inverse lift of each of the **two** periodic rays landing at `Z`, so it has **exactly two** ambient rays. Thus two disjoint computed ray pairs cannot co-land at the same simple root. The only four-ray exception is the certified critical point `0`. The arithmetic checker verifies that every pair has one lift of each requisite target, and that all 32 rays appear exactly once.

## 5. True original G depth-three alpha puzzle faces: the 2/4/4/2 theorem

The source's G-internal alpha ray-tree (the **ordinary** G-puzzle, not a KL localized ψ-piece) has **eight** depth-three chords, whose endpoint pairs are

\[
\begin{gathered}
 (1/3,2/3),\;(1/6,5/6),\;(5/12,7/12),\;(1/12,11/12),\\
 (7/24,17/24),\;(5/24,19/24),\;(11/24,13/24),\;(1/24,23/24).
\end{gathered}
\tag{5.1}
\]

They are actual *landed ray pairs* of the dividing alpha point's backward G orbit, from the source's certified internal puzzle, not synthetic straight chords used as dynamical rays. Because their ray tails are disjoint and the eight endpoints land at distinct vertices, they give **nine** finite depth-three complementary Jordan faces. One can identify each face without numerical ray tracing by its **eight-bit side signature**: the bit for a chord `(a,b)` records whether the argument lies in the strict open linear interval `(min(a,b), max(a,b))`. For each physical preimage class, both of its internal ray arguments have the *same* signature (all four at the critical point also share a signature). The arithmetic checker proves this for **all 15 physical points**.

Exactly **five** of the nine ordinary puzzle faces are occupied by the 15 precritical points, with the following complete census. The angular intervals are the actual *access seams* of the indicated complementary face; the chord endpoints are in internal G coordinates, and wrapping is modulo one.

| G alpha-depth-three face signature | Ambient access interval(s), in G-internal angles | Physical precritical points | Relation to K9 |
|:--|:--|--:|:--|
| `00000000` | `(23/24,1+1/24)` (wrap) | 2 | K3 only |
| `00010001` | `(1/12,1/6) ∪ (5/6,11/12)` | 4 | K3 only |
| `01010101` | `(5/24,7/24) ∪ (17/24,19/24)` | 3 | K9 (includes the double root at 0) |
| `11011101` | `(1/3,5/12) ∪ (7/12,2/3)` | 4 | K3 only |
| `11111111` | `(11/24,13/24)` | 2 | K3 only |

Thus the **12 coarse-only physical precritical points occupy precisely four noncentral original G alpha-depth-three puzzle faces, in the strict pattern `2+4+4+2`**, while all three fine-stage points lie in the single central critical face. Every one of the **24 coarse-only ray angles**, as measured in the corresponding G-internal angle coordinate under source-defined `Pi3`, lies outside the entire central top `Y_G^3` face (not merely outside its smaller child `Y_G^6`). All eight fine ray accesses lie in the **strict central `Y_G^6` face**. This is an exact original-puzzle first-failure/first-routing certificate, *not* an identification of those ordinary faces with Kahn's infinite localization-sheet tags `O,ξ,η`.

Proof of face membership is planar Jordan separation by the source's landed alpha rays. The eight-bit signatures are a computationally convenient way of recording which side of each actual ray pair is reached by a proper exterior access; the *geometric interpretation* of the bits uses the already proved source alpha-tree. Full source recurrence and the 15 physical ray classes are finite. A potential future cross-scale KL functor must therefore route **four explicit ordinary face categories**, not an undifferentiated class of twelve points.

## 6. Independent substitution control, Lean scope, and next actual gate

A striking redundant check is that **every one of the 32 ambient rays** agrees *exactly* with the period-three airplane substitution `σ(0)=011,σ(1)=100`, followed by removal of the first two binary digits, applied to its `Pi3` internal angle. This includes the 24 rays that were missing. The source's parameter-tuning identity alone would not justify an ambient dynamical-ray correspondence; that is why the proof establishes actual geometric membership **first**, via (2.3)–(2.5), and the *Levin* cyclic-rank mapping **second**. The exact substitution is a consistency test, not a covert assumption.

Reproduce from repository root:

```sh
python -m py_compile research/independent_audits/verify_tip_actual_coarse_only_ray_pairing.py
python research/independent_audits/verify_tip_actual_coarse_only_ray_pairing.py --check-manifest
lake build TipActualCoarseRays
```

The Python checker uses only standard-library exact `Fraction` arithmetic. It independently verifies `2048→80→32`, all strict ray-sector margins, the third `G` checkpoint, the complete `32`-entry `Pi3` cyclic bijection, all 15 actual landing pair/quartet records, their original depth-three alpha face signatures and counts, and the exact independent 3-bit airplane substitution. The Lean module kernel-checks the finite two-sector count and the 32 rational ambient survivors, the exact 15 physical pair/quartet **arithmetic partition**, and the eight-ray central top/child count. **Lean does not formalize** planar Jordan separation, analytic ray landing, Levin's complex theorem or proper polynomial-like filled-set equivalence; those are cited/source-proved hypotheses applied in the written argument.

**This result is tip-specific.** The full ray partition is proved for `c=c_*`; the exact rational angles also continue to their corresponding unramified roots for sufficiently close **real** parameters by periodic-ray stability and the simple local inverse branch, while the critical quartet switches its pairing across `c_*` as in merged PR #54. The written proof is not a source-defined parameter-independent KL sheet/coset natural transformation; it does not claim full `O/ξ/η` prime-end transport or a universal compactness/coercivity theorem. The remaining genuine task is to transport the just-labelled **four original G-puzzle face sectors**, with their specific accesses and the unbounded integer sheet windings, into the actual direct-vs-iterated canonical localizations described in the archive's [localization comparison](./tip_iterated_direct_canonical_localization_embedding_20261106.md). The PR #55 1024/16/4 degree count is used, but no global H1–H4, UPTCR, Issue #40, or MLC status is upgraded.

**Attribution and status.** The source alpha puzzles and KL pseudo-piece construction are credited to the archive's original cited primary mathematics (Kahn, Kahn–Lyubich, Levin, Milnor, Zakeri, and classical Douady–Hubbard straightening). GPT-6 assisted the new exact sector-sieve theorem, pair reconstruction, code, Lean artifact, and written analysis. Independent originality/priority and specialist validation are **not established**. This is a local research result and a source-defined finite routing atlas, not a completed global proof.
