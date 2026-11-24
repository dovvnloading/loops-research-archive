# A two-component obstruction to the single-base coarse connector prescription

**23 November 2026. Target: Issue #62, the connector prescription in the two
16 November packets. Status: written source-relative theorem and correction,
conditional on the archive's previously written geometric realization.**

There is a stronger obstruction than an unavailable nine-cut computation.
One fine base sheet, followed only by paths in the coarse exterior, cannot
represent all four native KL tiles with their prescribed rooted gluing.
The four tiles occupy **exactly two different components** of the inverse
image of the coarse exterior. Two initial fine sheets suffice, and one does
not. This is a statement about the existing native holomorphic immersion,
not a hypothetical finite-state model.

In particular, for a common rooted basepoint in the lower parent, **44 of
the 88 recorded source ideal witnesses have no source-faithful coarse-only
common-base connector**. Four of those 44 witnesses are among the eight
marked-root witnesses. For those four, the 16 November packet's assertion
that the requested coarse-only defect must lie in `H` cannot hold. The
native rooted witnesses remain valid; it is the proposed common-base
coarse-only representation of them that fails.

This does not compute the missing literal words in an unspecified archived
cut basis, prove KKL unique proper restriction, or establish MLC. It replaces
an impossible simultaneous calibration with a realizable two-sheet
groupoid construction and locates a specific mismatch in the current task.

## 1. Precisely which objects are being compared

Use the archive's physical nonattracting 3/9 parameter and notation

\[
\Omega_3=U^0\setminus(C_0\cup C_1\cup C_2)
 \subset\Omega_9=U^0\setminus\bigcup_{r,k}D_{r,k},
\quad C_0=K_3,\quad D_{0,0}=K_9=[-p,p].
\]

The two other fine intervals in `K3` have certified real order

\[
D_{0,2}<K_9<D_{0,1}.
\]

Let `pi: widehat Omega9 -> Omega9` be the exterior part of Kahn's fine
localization and `s_W:W->widehat T9` the rooted section of the actual
geometric KL first child `W=Y_G^6`, `G=f^3`. The actual ordinary KL
pseudo-piece has four universal annulus tiles `Ahat_j`, with projection
`p_W` and root-normalized immersion `j_W`, satisfying

\[
\pi j_W=p_W,\qquad j_W|_W=s_W.
\tag{1}
\]

Each tile projects into the *same physical* annulus
`A6=U_G^6\setminus K3`, which is contained in `Omega3`. Its original seam
intervals, in G's topological external angle coordinate, are

\[
I_0=(41,43)/192,\quad I_1=(53,55)/192,\quad
I_2=(137,139)/192,\quad I_3=(149,151)/192.
\tag{2}
\]

The natural W-to-V map sends tiles 0 and 1 into the same universal V tile,
and tiles 2 and 3 into the other, with zero unwrapped shifts. Its maps
agree pointwise on equal carrier coordinates in each parent pair. The
fine immersion is natural with this map. These are the hypotheses proved
in the earlier source atlas and used in the C4 wake theorem.

For a physical basepoint `x` in `W\setminus K3`, a **source-faithful coarse
connector to a source tile point u** will mean a path

\[
c:[0,1]\longrightarrow\Omega_3,\qquad
c(0)=x,\ c(1)=p_W(u),
\tag{3}
\]

whose fine lift starting at `s_W(x)` ends at **the prescribed point**
`j_W(u)`. Merely reaching the correct physical endpoint is insufficient.
This missing predicate is essential when a defect word is claimed to
encode the native source sheet.

If `r:x->p_W(u)` is a rooted reference path inside `W\setminus K9`, its
lift ends at `s_W(p_W(u))`. Consequently, for a source-faithful connector,

\[
[c r^{-1}]\in H
\quad\Longleftrightarrow\quad
j_W(u)=s_W(p_W(u)),
\tag{4}
\]

where `H` is the stabilizer at `s_W(x)`. Without source faithfulness,
the right side of (4) cannot be inferred from the word of `c`.

## 2. A physical two-ray obstruction, valid for every coarse connector

The original certified G rays `pR` and `pL` have angles

\[
\theta_-=2/7\in I_1,\qquad \theta_+=5/7\in I_2,
\tag{5}
\]

and both land at the **same physical point `+p` of K9**. The fine access
angle of both is zero. For sufficiently small common external height `t`,
let `x=r_{pR}(t)` and `y=r_{pL}(t)`. Both lie inside `W\setminus K3`.

Let `C_t` be the physical G equipotential arc from `x` to `y` through
increasing angles `2/7` to `5/7`. It lies in the actual coarse annulus
and passes the physical positive-real external access at angle `1/2`.
Choose `r_t:x->y` in a sufficiently small disk about `+p`, inside W,
passing on the right of K9. Such a path exists because K9 is the real
interval ending at `+p` and the other fine intervals are separated from
it. It can be chosen transverse to the two terminal rays and inside their
right-hand wake near the landing point. Define the actual based loop

\[
\gamma_t=C_t r_t^{-1}\quad\hbox{in }\Omega_9.
\tag{6}
\]

The real-symmetric source straightening, noncrossing of the two rays,
their common landing, and the certified real interval order give

\[
\operatorname{wind}_{D_{0,1}}(\gamma_t)=1,
\qquad
\operatorname{wind}_{D_{0,2}}(\gamma_t)=0.
\tag{7}
\]

Here is the geometric content of this step. The two full rays, their
common endpoint, and the equipotential arc bound the right Jordan wake.
Its real part on the Julia side is to the right of `+p`; the entire
`D01` is on that side and `D02` is on the other. Replacing the common
endpoint by a sufficiently small closing arc does not change winding
about either compact interval. This is exactly the physical 1-to-2 wake
argument of the archived C4 theorem, Section 3. It is not a consequence
of rational angle order alone. It does not require a Euclidean polygon
approximation or identify hybrid coordinates with conformal coordinates.

Write

\[
\Delta(g)=\operatorname{wind}_{D_{0,1}}(g)
          -\operatorname{wind}_{D_{0,2}}(g).
\]

**Lemma 2.1.** Every loop in `Omega3` has `Delta=0`. Every loop inside
`W\setminus K9` has `Delta=0`, and in particular `Delta(H)=0`.

**Proof.** The winding function of a loop is locally constant on its
complement. The connected continuum `K3`, which contains both `D01`
and `D02`, is disjoint from every loop in `Omega3`. The two windings are
therefore equal. A loop inside the Jordan disk W has zero winding at
each of the two intervals, since both intervals lie outside W. The root
stabilizer is represented by the root meridian inside W. **QED.**

**Theorem 2.2 (no coarse path reaches this prescribed rooted sheet).**
For **every** path `c:x->y` contained in `Omega3` and **every** rooted
reference `r:x->y` inside `W\setminus K9`,

\[
\boxed{\Delta([c r^{-1}])=1,\qquad [c r^{-1}]\notin H.}
\tag{8}
\]

Thus the fine lift of no such coarse `c` from `s_W(x)` reaches `s_W(y)`.

**Proof.** The loop `c C_t^{-1}` lies in `Omega3`, and the loop
`r_t r^{-1}` lies in `W\setminus K9`. Concatenation, (6), and Lemma 2.1
give

\[
\begin{aligned}
\Delta([c r^{-1}])
 &=\Delta([c C_t^{-1}])+
   \Delta([C_t r_t^{-1}])+\Delta([r_t r^{-1}])\\
 &=0+1+0=1.
\end{aligned}
\]

Membership in H would force Delta zero. The covering-space stabilizer
criterion proves the endpoint statement. This argument covers every
coarse connector, all integer windings, arbitrary nonabelian detours,
and every rooted reference. It does not infer subgroup membership from
vanishing abelianization; a nonzero character is used only to exclude
membership. **QED.**

## 3. Exactly two components occur in the genuine four-tile atlas

Let `R_j` be the component of `pi^{-1}(Omega3)` containing
`j_W(Ahat_j)`. This is well-defined: a tile is connected and its entire
projection lies in `Omega3`.

**Theorem 3.1 (the minimal coarse-component count is two).**

\[
\boxed{R_0=R_1,\qquad R_2=R_3,\qquad R_0\ne R_2.}
\tag{9}
\]

**Proof.** Same-parent equal-coordinate tile points have equal fine
images by the actual W-to-V immersion and (1). Their images therefore
belong to the same component, giving the first two equalities. The
central-gluing lift of the `pR` tail is `s_W(x)` in `R1`; the corresponding
`pL` lift is `s_W(y)` in `R2`. If these two points were in one component,
a path connecting them in that component would project to a coarse path
contradicting Theorem 2.2. **QED.**

This is stronger than observing that opposite-parent zero-deck witnesses
are nonroot. The component obstruction applies to **every interior point
in each original tile**, including every native integer deck translate,
independently of its eventual physical landing.

**Corollary 3.2 (complete common-base existence criterion).** If x lies
in a root-gluing component of parent p, a source-faithful coarse connector
from `s_W(x)` to `j_W(u)` for a point u of tile j exists if and only if

\[
\boxed{\lfloor j/2\rfloor=p.}
\tag{10}
\]

**Proof.** Necessity is (9), since a lifted coarse path cannot change
the component of `pi^{-1}(Omega3)`. For sufficiency, both points belong
to the same connected component of a Riemann surface, hence can be
joined by a path there. Its projection is a coarse path, and uniqueness
of lifting gives the required endpoint. Equivalently, a common source
parent tile supplies such a path directly. **QED.**

The statement is not a demand that paths in W avoid K3. The allowed
source-path category is considered next.

## 4. The original KL path groupoid permits the correct repair

KL II Section 3.2.1 defines paths in `U_G^6\setminus S_W`, starting
somewhere in W, with the prefix-subordination condition when a path
meets `K_W`. It does **not** require the entire path, including a
common-base prefix inside W, to avoid K3. Lemma 3.3 realizes a tile by
an exterior path beginning in its own simply connected gluing component.

Choose a point `a_j` in the jth actual gluing component and a path

\[
d_j:x\longrightarrow a_j\quad\hbox{inside }W\setminus K9.
\tag{11}
\]

For a tile point u represented by an annular path
`eta_j:a_j->p_W(u)` in `A6`, the concatenation `d_j eta_j` is a valid
based representative in the original KL category: every portion meeting
`K_W` occurs in the initial W prefix, while the exterior tail does not
meet K3. Its fine lift starts at `s_W(x)`, follows `s_W(d_j)`, and then
the uniquely determined lift of the exterior tile path. Therefore

\[
\boxed{\operatorname{Lift}_{s_W(x)}(d_j\eta_j)(1)=j_W(u).}
\tag{12}
\]

For the upper parent, the prefix `d_j` cannot be replaced by a coarse-only
prefix while keeping this fine endpoint. Theorem 2.2 proves that failure;
it does not prohibit the legitimate source path (11).

The four *native* tiles remain distinct, even though their fine images
meet in two pairs. The corrected groupoid must retain source tile labels,
integer deck coordinates, and full homotopy words. Equation (12) is not
a finite quotient or a claim that two source paths have become equal.

There is an alternative if all transport morphisms must remain coarse.
Use **two initial fine sheets**, one in each component in (9), at a
common downstairs basepoint. The second can be constructed explicitly:
start with `s_W(y)` and lift `C_t^{-1}` back to x. The resulting point
`sigma_+` has based label

\[
\sigma_+=H[r_t C_t^{-1}]=H[\gamma_t]^{-1},
\qquad \Delta([\gamma_t]^{-1})=-1.
\tag{13}
\]

This is an actual physical path definition, with the entire loop retained.
We do not replace it by a guessed word in the archive's nine-generator
basis. Path lifting from these two initial sheets represents all four
tiles by (10). Two is minimal by (9). All coarse monodromy must still be
retained within each of the two components; there remain infinitely many
sheets, and this construction is not a two-state approximation.

## 5. Exact effect on the existing 88-row task

Take the common root basepoint in parent 0, as in Theorem 2.2. Re-reading
the original 88-row manifest gives:

| Source tile parent | Native root rows | Native nonroot rows | A source-faithful coarse-only common-base path |
|---|---:|---:|---|
| 0, source tiles 0 and 1 | 4 | 40 | Exists for every positive-height source point |
| 1, source tiles 2 and 3 | 4 | 40 | Does not exist for any positive-height source point |

The four positive-root rows in the second line are

| Source ray | Original source tile and side | Unwrapped G angle |
|---|---|---|
| pL | tile 3, xi | `5/7` |
| a | tile 3, xi | `81/112` |
| b | tile 2, eta | `87/112` |
| qL | tile 2, eta | `11/14` |

These are genuine strict ideal J-side points. The first is already enough:
`5/7<149/192`, so pL at zero deck is in tile 3's xi side. Natural W-to-V
gluing identifies its positive-height fine image with the rooted own-seam
image in tile 2. Every common-base coarse connector nevertheless misses
that rooted fine image by (8).

The annotation `conditional_required_F9_root_subgroup_membership=in_H`
can correctly describe a **source-faithful fine connector** such as
(12). It cannot simultaneously describe a connector forced to stay in
Omega3 from one rooted basepoint and represent all four source tiles.
If the intended 16 November prescription did not require source
faithfulness, its words encode a different lift, so the native 8/80
classification cannot be transferred to those words.

Changing the common basepoint to parent 1 exchanges the two rows of the
table; it does not remove the obstruction. The packet therefore does not
change any original `null` word to an invented identity or numerical
word. It adds an explicit existence predicate, required before requesting
a word certificate.

## 6. Proof dependencies, reproduction, and exact scope

The geometric theorem uses the existing written source claims below.
Its dependence on them is stated rather than upgraded by a Python run:

1. Kahn, *A priori bounds I*, Section 7.4.1, Theorem 7.12, original
   printed pp. 43--44: canonical localization and its root chart.
   <https://arxiv.org/pdf/math/0609045v3>.
2. Kahn--Lyubich, *A priori bounds II: Decorations*, Section 3.2.1,
   Lemmas 3.3--3.4, and Section 3.2.4, printed pp. 11--13: the actual
   path category, universal tiles, and inclusion naturality.
   <https://arxiv.org/html/math/0609046v2#S3.SS2>.
3. `tip_kl_pseudopiece_side_atlas_20261106.md`, Theorem 4.1: the
   source-defined same-root immersion and physical phase avoidance.
4. `tip_rooted_native_KL_section_and_four_tile_prime_end_cycle_20261108.md`,
   Theorems 2.3 and 3.2: the rooted W section and its admissible paths.
5. `tip_native_C4_wake_root_sheet_naturality_20261109.md`, Sections 2--3:
   zero-shift parent naturality and the actual right Jordan wake.
6. `tip_localization_refinement_peripheral_monodromy_20261106.md`,
   Sections 2--3, and
   `tip_based_sheet_grid_universal_lift_and_root_access_20261108.md`,
   Section 2: the common exterior, subgroup conventions, and component
   interpretation. Those earlier general covering results are credited;
   the new contribution here is their exact source-tile realization and
   the correction of the common-base connector demand.

Run from the repository root:

```sh
python3 -B research/independent_audits/maximal_root_landing_20261123/verify.py --check
```

The verifier re-reads the original source-angle and 88-row packets,
checks the witness's strict source-side inequalities and common physical
landing, computes both 44/44 splits, and checks that none of the previously
uncomputed F9 words has been filled. It writes/compares
`coarse_component_feasibility.json`. It also verifies the noncommutative
concatenation identity used in (8) on independent symbolic paths.
It does not certify rays, Jordan separation, homotopy classes, or MLC.

**Acceptance consequence.** A source-faithful all-tile gauge using a
single rooted base sheet and exclusively coarse connectors is disproved
under the archive's realized geometry. The narrow corrected statement is
(10), with either the legitimate W-prefix construction (12) or the
minimal two-component construction (13). Full based F9 computation for
selected, correctly typed paths and the proof-used KKL marking remain
open. H1--H4, universal tower closure, and MLC remain open.

Prepared with OpenAI GPT-6 Astra Pro assistance for proof search,
primary-source checking, and exact bookkeeping. No independent external
mathematical specialist review is claimed.
