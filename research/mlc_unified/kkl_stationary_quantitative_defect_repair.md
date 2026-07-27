# KKL stationary Wave repair by a quantitative defect alternative

## 1. Purpose and status

The pointwise assertion at KKL source line 1603 is stronger than the
stationary width argument actually needs.  The source tries to show
that **every** leaf in the last stationary subwave passes through the
selected component.  A sufficient replacement is to prove this only
outside a measurable defect sublamination whose width can be charged
to the vertical surface width and the renormalization width.

This note proves the complete algebraic reduction from such a defect
estimate to the short-or-terminal conclusion.  It does **not** prove
the analytic defect estimate.  In particular, it does not close the
stationary Wave repair, VAAPC-I, UPTCR, or MLC.

The locked source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The proof uses only:

- KKL lines 1547--1589, which reduce the critical-end Wave to the last
  nested stationary subwave;
- KKL lines 1514--1532, which bound the other Wave types;
- KKL lines 1627--1639, which assemble the Wave-type decomposition;
- the corrected degree-two terminal estimate proved in
  `pql_iterate_filled_graph_naturality.md`; and
- the definition of a terminal Wave at KKL lines 1151--1156.

## 2. Frozen notation

Write

\[
 V(F):=\mathcal W(\mathcal U\setminus\mathcal T),
 \qquad
 R(F):=\mathcal W(\mathcal R F).
\tag{2.1}
\]

Let \(b\) be the fixed parabolic bound and let

\[
 N=b+3,\qquad m=N-1=b+2.
\tag{2.2}
\]

For a Wave \(Y\) ending at \(BL_0\), KKL define nested subwaves

\[
 Y_0\supset Y_1\supset\cdots\supset Y_m
\tag{2.3}
\]

in source lines 1547--1548.  The source's telescoping estimate, with
the undefined \(A_N\) avoided, is

\[
 \mathcal W(Y^{N\text{-nbr}})
 \leq
 \mathcal W(Y^{\rm sh})
 +\mathcal W(Y_m)
 +C_b.
\tag{2.4}
\]

Here and below \(C_b<\infty\) denotes a constant depending only on the
fixed parabolic bound.  It may increase from line to line.

The corrected component degree at the final level is two.  Therefore,
whenever a measurable sublamination \(G\subset Y_m\) has the actual
final incidence and proper-path realization required by
`KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION`, the already proved
degree correction gives

\[
 \mathcal W(G)\leq 4R(F)+4.
\tag{2.5}
\]

Equation (2.5) is conditional on the displayed incidence hypothesis;
it is not asserted for all of \(Y_m\).

## 3. Quantitative Stationary Defect Bound

The proposed replacement gate is the following.

> **QSDB (Quantitative Stationary Defect Bound).**  
> For every KKL stationary critical-end block there is a measurable
> partition in the native transverse width measure, modulo a
> width-zero family,
> \[
>    Y_m=G\sqcup D,
> \tag{3.1}
> \]
> such that:
>
> 1. the restrictions of the native transverse width measure to
>    \(G\) and \(D\) agree with their proof-used lamination widths;
> 2. every leaf of \(G\) has the actual final component incidence,
>    proper segmented restriction record, marking survival, and
>    measurable route selection needed for (2.5); and
> 3. for constants \(a_b,c_b<\infty\) depending only on the fixed
>    parabolic bound \(b\),
>    \[
>      \mathcal W(D)
>      \leq
>      a_b V(F)+c_b R(F)+c_b.
>    \tag{3.2}
>    \]

The quantifier order is

\[
 \forall b\geq1\quad
 \exists a_b,c_b<\infty\quad
 \forall\text{ stationary blocks of bound }b\quad
 \exists(G,D).
\tag{3.3}
\]

The constants are independent of the individual block, satellite
period, rotation denominator, and the selected horizon \(h\le b+2\).
When QSDB is used to absorb additive constants in a source-wide
statement, one must additionally work in KKL's high-type
near-degenerate regime \(R(F)\ge R_0(b,k,\lambda)\), or impose the
absolute-scale form

\[
 \mathcal W(A)\ge
 C_{b,k,\lambda}\bigl(R(F)+1\bigr).
\tag{3.4}
\]

A bound relative only to \(R(F)\) does not absorb a fixed additive
constant when \(R(F)\downarrow0\).

The word *segmented* is essential.  Sequential KKL restrictions use
nested subpath windows; the proper one-step paths need not be the
untruncated coordinates of one common-parameter fiber-product path.
The corrected occurrence invariant is developed in
`kkl_stationary_segmented_occurrence_binder.md`.

QSDB is weaker than the pointwise claim at source line 1603.  It
allows exceptional leaves, terminal deck collisions, and failed
complete continuations, provided that all such failures form the
measurable family \(D\) and satisfy (3.2).  A finite combinatorial
count does not prove (3.2).

## 4. Defect bound implies a charged stationary estimate

### Proposition 4.1

Assume QSDB.  Then every Wave \(Y\) ending at \(BL_0\) satisfies

\[
 \mathcal W(Y^{N\text{-nbr}})
 \leq
 \mathcal W(Y^{\rm sh})
 +a_bV(F)
 +(c_b+4)R(F)
 +C_b.
\tag{4.1}
\]

#### Proof

Modulus is subadditive on a union of curve families, so (3.1) gives

\[
 \mathcal W(Y_m)
 \leq
 \mathcal W(G)+\mathcal W(D).
\tag{4.2}
\]

The stronger equality follows from the transverse-measure clause in
QSDB, but it is not needed here and is not inferred from setwise
measurability alone.

Apply (2.5) to \(G\) and (3.2) to \(D\):

\[
\begin{aligned}
 \mathcal W(Y_m)
 &\leq
 4R(F)+4+
 a_bV(F)+c_bR(F)+c_b\\
 &=
 a_bV(F)+(c_b+4)R(F)+(c_b+4).
\end{aligned}
\tag{4.3}
\]

Substitution of (4.3) into the source-locked telescoping estimate
(2.4), followed only by enlargement of \(C_b\), gives (4.1).
\(\square\)

No coefficient-one estimate is used in this proof.  The factor four
is the proved correction for the one central degree-two stage.

## 5. Assembly for an arbitrary controllable Wave

KKL source lines 1627--1635 decompose a \(k\)-controllable Wave \(A\)
as

\[
 A=A^{\rm sh}\cup X\cup Y\cup Z_1\cup\cdots\cup Z_k,
\tag{5.1}
\]

where \(X\) is over \(BL_0\), \(Y\) ends at \(BL_0\), and each \(Z_j\)
is localized away from \(BL_0\).  The nonshort pieces are disjoint
sublaminations.  KKL Propositions 7.8 and 7.9 give

\[
 \mathcal W(X^{\rm nbr})\leq C_b,
 \qquad
 \mathcal W(Z_j^{\rm nbr})\leq C_b.
\tag{5.2}
\]

### Proposition 5.1

Assume QSDB.  There are constants \(a_b,c_b,C_b<\infty\) such that
every \(k\)-controllable Wave \(A\) satisfies

\[
\begin{split}
 \mathcal W(A)
 \leq{}&
 \mathcal W(A^{N\text{-br}})
 +\mathcal W(A^{\rm sh})\\
 &+a_bV(F)+c_bR(F)+C_b(k+1).
\end{split}
\tag{5.3}
\]

#### Proof

Every leaf outside \(A^{N\text{-br}}\) is \(N\)-unbreakable.
Partition the remaining leaves by (5.1).  Use modulus subadditivity on
the resulting covering by measurable sublaminations.  Apply (5.2) to \(X\) and the
\(Z_j\), and Proposition 4.1 to \(Y\).  There are \(k\) localized
families, so their additive constant is at most \(C_bk\).  All other
constant terms are absorbed into \(C_b(k+1)\).  This is exactly
(5.3). \(\square\)

For the source-level terminality argument one needs a disjoint form of
this estimate.

### Proposition 5.2 (disjoint charged estimate)

Assume QSDB and put

\[
 B:=A^{N\text{-br}}\cup A^{\rm sh}.
\tag{5.4}
\]

After renaming the constants in Proposition 5.1,

\[
 \mathcal W(A)
 \leq
 \mathcal W(B)
 +a_bV(F)+c_bR(F)+C_b(k+1).
\tag{5.5}
\]

#### Proof

Partition \(A\) in the native transverse width measure into \(B\) and
the leaves which are simultaneously nonshort and \(N\)-unbreakable.
Partition the latter family by the \(X,Y,Z_j\) classes in KKL source
lines 1627--1635.  The \(X\) and \(Z_j\) estimates are unchanged.  In
the stationary \(Y\)-class the short family is empty by construction,
so Proposition 4.1 contributes only

\[
 a_bV(F)+(c_b+4)R(F)+C_b.
\]

Additivity is used here only in the source-typed transverse measure
required by QSDB.  Summing the disjoint pieces and enlarging the
constants gives (5.5). \(\square\)

## 6. The vertical charge and the corrected source-level implication

The term \(a_bV(F)\) in (5.3) looks different from the source's
claimed estimate, but the definition of terminality was designed to
absorb precisely such a term.  Two additional points are essential:
KKL shortness is strict, and a terminal **subwave** is not automatically
a terminal ambient Wave.

### Theorem 6.1 (local charged short-or-vertical-terminal alternative)

Assume QSDB.  Fix \(0<\lambda<1\) and put

\[
 \lambda'=\frac{1+\lambda}{2},
 \qquad
 \varepsilon=\frac{1-\lambda}{8}.
\tag{6.1}
\]

Define

\[
 \delta_v=
 \begin{cases}
  \min\{1/2,\varepsilon/a_b\},&a_b>0,\\
  1/2,&a_b=0.
 \end{cases}
\tag{6.2}
\]

Suppose

\[
 \mathcal W(A)
 \geq
 \frac{c_bR(F)+C_b(k+1)}{\varepsilon}.
\tag{6.3}
\]

Then every \(k\)-controllable, \((N,\lambda')\)-unbreakable Wave \(A\)
is either:

1. \((\delta_v,\eta_0)\)-terminal through the vertical alternative,
   for any fixed universal \(\eta_0\); or
2. strictly \(\lambda\)-short.

#### Proof

If

\[
 V(F)>\delta_v\mathcal W(A),
\tag{6.4}
\]

then the first alternative in KKL's definition of terminality holds.
The second terminal parameter is irrelevant in this branch, so any
fixed universal \(\eta_0\) is valid.

Assume that (6.4) fails.  Since \(a_b\delta_v\leq\varepsilon\),

\[
 a_bV(F)\leq\varepsilon\mathcal W(A).
\tag{6.5}
\]

The threshold (6.3) gives

\[
 c_bR(F)+C_b(k+1)
 \leq
 \varepsilon\mathcal W(A).
\tag{6.6}
\]

Insert (6.5)--(6.6) into (5.3):

\[
 (1-2\varepsilon)\mathcal W(A)
 \leq
 \mathcal W(A^{N\text{-br}})
 +\mathcal W(A^{\rm sh}).
\tag{6.7}
\]

KKL define \(A^{N\text{-br}}\) as the transverse-measure complement
of \(A^{N\text{-nbr}}\).  Hence \((N,\lambda')\)-unbreakability gives

\[
 \mathcal W(A^{N\text{-br}})
 \leq
 (1-\lambda')\mathcal W(A).
\tag{6.8}
\]

Subtracting (6.8) from (6.7) yields

\[
\begin{aligned}
 \mathcal W(A^{\rm sh})
 &\geq
 \bigl(\lambda'-2\varepsilon\bigr)\mathcal W(A)\\
 &=
 \frac{1+3\lambda}{4}\mathcal W(A)
 >
 \lambda\mathcal W(A).
\end{aligned}
\tag{6.9}
\]

This is strict \(\lambda\)-shortness. \(\square\)

The absolute threshold (6.3) does not follow from width relative to
\(R(F)\) when \(R(F)\) can tend to zero.  It is absorbable in the
source HTND regime, where \(R(F)\) is required large, or under the
explicit \(R(F)+1\) scale condition (3.4).

### Theorem 6.2 (strengthened QSDB suffices for the stationary contribution)

Assume:

1. QSDB with its transverse-measure clause;
2. the disjoint estimate (5.5);
3. KKL Proposition `small breaking` in its source-stated scope; and
4. the HTND or \(R(F)+1\) scale condition needed to absorb the
   additive charge.

Then for every \(0<\lambda<1\), every sufficiently wide
\(k\)-controllable Wave \(A\) is either strictly \(\lambda\)-short or
\((\delta,\eta)\)-terminal, where \(\delta>0\) is independent of \(k\)
and \(\eta\) is universal.  Thus strengthened QSDB is sufficient for
the stationary contribution to KKL Proposition `mostly short`.

#### Proof

Choose

\[
 \lambda<\lambda_3<1.
\tag{6.10}
\]

Apply KKL Proposition `small breaking` with
\(n=N\), \(k_0=12b\), and parameter \(\lambda_3\).  Let
\(\delta_3>0\) and universal \(\eta_3\) be the resulting constants.
The source states that \(\delta_3\) is independent of the eventual
controllability parameter \(k\).

Choose

\[
 \max\left\{
  \frac{\lambda}{\lambda_3},
  \frac1{1+\delta_3}
 \right\}
 <\theta<1,
\tag{6.11}
\]

and put

\[
 \varepsilon_\theta=\frac{1-\theta}{2},\qquad
 \delta_v=
 \begin{cases}
  \min\{1/2,\varepsilon_\theta/a_b\},&a_b>0,\\
  1/2,&a_b=0.
 \end{cases}
\tag{6.12}
\]

Enlarge the scoped absolute threshold until

\[
 c_bR(F)+C_b(k+1)
 \leq
 \varepsilon_\theta\mathcal W(A).
\tag{6.13}
\]

If \(V(F)>\delta_v\mathcal W(A)\), then \(A\) is terminal through the
vertical alternative.  Otherwise
\(a_bV(F)\leq\varepsilon_\theta\mathcal W(A)\), and (5.5) gives

\[
 \mathcal W(B)\geq\theta\mathcal W(A),
 \qquad
 B=A^{N\text{-br}}\cup A^{\rm sh}.
\tag{6.14}
\]

By KKL source lines 1375--1387, \(B^{N\text{-nbr}}\) is short and
therefore \(12b\)-controllable.  Enlarge the original threshold once
more so that (6.14) makes \(B\) wide enough for `small breaking`.
That proposition gives two cases.

If \(B\) is \((\delta_3,\eta_3)\)-terminal, its vertical alternative
implies

\[
 V(F)>\delta_3\mathcal W(B)
 \geq\delta_3\theta\mathcal W(A),
\]

while its wider-Wave alternative supplies an
\(\eta_3\)-controllable \(C\) with

\[
 \mathcal W(C)>
 (1+\delta_3)\mathcal W(B)
 \geq(1+\delta_3)\theta\mathcal W(A).
\]

By (6.11), both alternatives make \(A\)
\((\delta_A,\eta_3)\)-terminal, where

\[
 \delta_A=
 \min\{\delta_3\theta,(1+\delta_3)\theta-1\}>0.
\tag{6.15}
\]

If instead \(B\) is \((N,\lambda_3)\)-unbreakable, then
\(B^{N\text{-nbr}}\subset A^{\rm sh}\): a leaf of \(B\) which survives
\(N\) steps cannot lie in \(A^{N\text{-br}}\).  Therefore

\[
\begin{aligned}
 \mathcal W(A^{\rm sh})
 &\geq\mathcal W(B^{N\text{-nbr}})\\
 &\geq\lambda_3\mathcal W(B)\\
 &\geq\lambda_3\theta\mathcal W(A)
 >\lambda\mathcal W(A).
\end{aligned}
\tag{6.16}
\]

Thus \(A\) is strictly \(\lambda\)-short.  The vertical split and the
two `small breaking` outputs exhaust all cases. \(\square\)

This is a proved conditional implication.  It does not promote the
stationary repair because the strengthened QSDB partition and all of
its analytic defect charges remain open.

## 7. Why QSDB is a better analytic target

The first-failure decomposition for a proposed two-route construction
has the following analytically distinct classes:

```text
D0  untyped encounter or absent local side germ
D1  finite continuation exit from the embedded Kahn neighborhood
D2  nonlanding or nonunique ideal accumulation
D3  fine-marking failure
D4  coarse single-interval subordination
D5  incompatible nested restriction window
D6  terminal family failure
D7  central deck collision
D8  final component-incidence or measurable-selection failure
```

A pointwise proof must eliminate every class.  QSDB permits a
different proof for each class:

- collar-crossing estimates may charge `D1` to \(V(F)\);
- Wave/shift estimates may charge marking defects to \(R(F)\) or a
  controlled Wave family;
- the degree-two collar may charge `D7` with multiplicity two rather
  than requiring noncollision; and
- measurable route partitions may handle `D8` without making one
  canonical choice for every leaf.

None of these charges is asserted here.  The point is the proved
algebraic fact that a vertical charge is compatible with the terminal
alternative.  Theorem 6.2 supplies the additional disjoint-\(B\)
argument needed to propagate terminality to the ambient Wave.

## 8. Adversarial audit

1. The undefined \(A_N\) is never used; the final defined subwave is
   \(Y_{N-1}\).
2. The central map is assigned degree two, not degree one.
3. General curve-family width is used subadditively.  Exact additivity
   is invoked only for KKL's native transverse width measure, and that
   typing is an explicit QSDB hypothesis.
4. A finite list of failure codes is not treated as a width estimate.
5. A pointwise finite schema is not promoted to a sublamination.
6. The vertical term is not silently discarded; it is split by
   (6.4) and absorbed quantitatively.
7. The threshold (6.3) is absolute.  Its absorption is asserted only
   in the HTND regime or under the explicit \(R(F)+1\) scale condition;
   relative width alone is not enough.
8. The factor four in (2.5) is retained.
9. No noncollision theorem is assumed in the defect branch.
10. A terminal subwave is not treated as a terminal ambient Wave.
    Theorem 6.2 proves the required transfer using the disjoint family
    \(B\), KKL `small breaking`, and
    \((1+\delta_3)\theta>1\).
11. KKL shortness is strict; the arithmetic retains strict slack.
12. The terminal constant is capped below one and the vertical branch
    carries a universal second terminal parameter.

## 9. Exact next analytic obligation

The immediate analytic problem is now a choice:

1. prove the pointwise segmented two-route binder and all subsequent
   noncollision/incidence clauses; or
2. prove QSDB directly by constructing measurable defect families and
   charging each of `D0`--`D8` to the right-hand side of (3.2).

The second route is strictly weaker and, with the transverse-measure
and absolute-scale clauses, is sufficient by Theorem 6.2.
Its first concrete subproblem is a **finite continuation-exit charge**:
show that leaves whose selected local lift exits the finite Kahn
embedding collar contain a measurable overflow subcurve family of
width at most

\[
 C_b\bigl(V(F)+1\bigr).
\tag{9.1}
\]

After (9.1), the next independent tasks are unique ideal-end landing,
marking/filter defect charges, the central degree-two collision charge,
and final measurable incidence extraction.

## 10. What can already be proved for continuation exits

The qualitative embedded-neighborhood theorem gives a rigorous
block-dependent exit charge.  The missing point is uniform calibration
of that charge, not the overflow inequality itself.

### Lemma 10.1 (finite nested embedding collar)

Fix a finite Kahn horizon \(h\).  Let

\[
 I_h:U^h\longrightarrow U^0
\]

be its complete immersion and let \(K^h\) be the pulled filled set.
There are Jordan disks

\[
 K^h\subset O_h^-\Subset O_h^+\Subset U^h
\tag{10.1}
\]

such that \(I_h\) is injective on a neighborhood of
\(\overline{O_h^+}\).  Consequently

\[
 Q_h:=
 I_h\!\left(O_h^+\setminus\overline{O_h^-}\right)
\tag{10.2}
\]

is a genuine annulus of positive modulus

\[
 \mu_h:=\operatorname{mod}Q_h>0.
\tag{10.3}
\]

#### Proof

The finite iterated embedded-neighborhood lemma in
`kkl_stationary_two_occurrence_source_attack.md` gives an open
neighborhood \(O\) of \(K^h\) on which \(I_h\) is an embedding.
Shrink \(O\) once so that its closure is still contained in that
embedding neighborhood.

The filled set \(K^h\) is a full compact continuum in the disk
\(U^h\).  Hence it has a nested basis of smooth Jordan neighborhoods.
Choose two members of that basis satisfying

\[
 K^h\subset O_h^-\Subset O_h^+\Subset O.
\]

Inside the embedded neighborhood,
\(I_h^{-1}(K^0)=K^h\), so the annular region is disjoint from the
pulled filled set and its image lies in the proof-used complementary
surface.

The embedding maps both Jordan curves homeomorphically to disjoint
Jordan curves.  It therefore maps the annular region between them
homeomorphically onto the annulus \(Q_h\).  Every nondegenerate
doubly connected Jordan domain has strictly positive modulus, proving
(10.3). \(\square\)

### Proposition 10.2 (exact continuation-exit overflow)

Let \(E_h\) be a measurable sublamination of target leaves equipped
with selected lift germs starting in \(I_h(O_h^-)\).  Suppose that for
every \(\alpha\in E_h\), continuation of the selected germ along the
proof-used orientation first leaves \(I_h(O_h^+)\) before reaching its
declared remote endpoint.  Suppose also that the first-exit subarc is
selected measurably.

Then

\[
 \mathcal W(E_h)\leq\frac{1}{\mu_h}.
\tag{10.4}
\]

#### Proof

For every \(\alpha\in E_h\), the selected continuation begins inside
the inner Jordan disk \(I_h(O_h^-)\) and reaches the complement of the
outer Jordan disk \(I_h(O_h^+)\).  Its segment between the last exit
from the inner disk before that first outer exit and the first outer
exit contains a connected subcurve crossing the annulus \(Q_h\) from
one boundary component to the other.

Let \(\Gamma(Q_h)\) be the full family of such annular crosscuts.
Thus every leaf of \(E_h\) overflows a member of
\(\Gamma(Q_h)\).  The single-curve case of the ordered
submulticurve-overflow inequality gives

\[
 \mathcal W(E_h)\leq\mathcal W(\Gamma(Q_h)).
\tag{10.5}
\]

For an annulus, the extremal width of the family connecting its two
boundary components is the reciprocal of its conformal modulus.
Therefore

\[
 \mathcal W(\Gamma(Q_h))=\frac1{\operatorname{mod}Q_h}
 =\frac1{\mu_h},
\]

which is (10.4). \(\square\)

The measurability hypothesis is indispensable.  Pointwise selection
of a first exit does not by itself define a sublamination or a
transverse-measurable overflow map.

### Corollary 10.3 (the exact remaining uniform collar estimate)

For the proof-used stationary horizons \(h\leq b+2\), the subclass of
continuation exits satisfying every hypothesis of Proposition 10.2
has the QSDB charge required in (3.2) if one proves

\[
 \boxed{
 \frac1{\mu_h}
 \leq
 C_b\bigl(V(F)+1\bigr)
 }
\tag{10.6}
\]

for compatible nested embedding collars and proves measurable
first-exit selection.

#### Proof

Combine (10.4) and (10.6). \(\square\)

To cover the complete `D1` class, one must additionally prove that
every selected failed source continuation reaches
\(\partial O_h^+\) through a measurable source-lift segment whose
embedded image contains the required annular crosscut.  A target trace
may merely touch and reenter the collar or continue on another global
immersion sheet; Proposition 10.2 does not silently identify those
events.

Kahn's polynomial-like restriction theorem proves
\(\mu_h>0\) for each fixed block.  Its qualitative statement does not
give (10.6) in the near-degenerate regime.  Thus no period-independent
or degeneration-independent constant is inferred here.  The next
analytic subgate is an intrinsic calibrated exit estimate, not mere
existence of an embedded collar.

## 11. Qualitative collar existence cannot yield the vertical charge

The collar in Lemma 10.1 is chosen rather than canonical.  Define the
optimized compatible collar conductance

\[
\begin{split}
 \mathfrak C_{\le b+2}^{\rm comp}(F)
 :=
 \inf_{\mathscr Q\ {\rm compatible}}
 \max_{1\le h\le b+2}
 \frac1{\operatorname{mod}Q_h},
\end{split}
\tag{11.1}
\]

where the infimum ranges over prefix-compatible embedded collar
systems, and is \(+\infty\) if none exists.  Then the intrinsic
version of (10.6) is

\[
 \mathfrak C_{\le b+2}^{\rm comp}(F)
 \le C_b\bigl(V(F)+1\bigr).
\tag{11.2}
\]

Even (11.2) does not follow from the qualitative pseudo-polynomial-like
and embedded-neighborhood hypotheses.  Fix \(0<a<1\) and, for
\(1<R<2\), put

\[
 U_R=\mathbb D_R,\qquad
 U_R'=\mathbb D_{\sqrt R},\qquad
 K=\overline{\mathbb D},\qquad
 T=[-a,a],\qquad
 f_R(z)=z^2,\qquad
 \iota_R(z)=z.
\tag{11.3}
\]

This is an exact degree-two pseudo-polynomial-like map with globally
embedded immersion, common full filled set \(K\), and forward-invariant
full tree \(T\).  Its horizon-\(h\) domain is

\[
 U_R^h=\mathbb D_{R^{1/2^h}},
\tag{11.4}
\]

and the complete immersion is inclusion.  Since
\(\operatorname{mod}(\mathbb D\setminus T)=m_a>0\),
ring monotonicity gives

\[
 V(F_R)=\mathcal W(\mathbb D_R\setminus T)\le m_a^{-1}.
\tag{11.5}
\]

On the other hand, every collar
\(K\subset O^-\Subset O^+\Subset U_R^h\) satisfies

\[
\begin{aligned}
 \operatorname{mod}(O^+\setminus\overline{O^-})
 &\le
 \operatorname{mod}(U_R^h\setminus K)\\
 &=\frac{\log R}{2\pi\,2^h}.
\end{aligned}
\tag{11.6}
\]

Thus

\[
 \frac1{\operatorname{mod}Q_h}
 \ge\frac{2\pi\,2^h}{\log R}\longrightarrow\infty
 \quad(R\downarrow1),
\tag{11.7}
\]

while the vertical width remains bounded.  This is a counterexample
to deriving a \(V(F)\)-linear collar charge from the abstract
qualitative hypotheses.  It is not a counterexample in KKL's native
periodically repelling primitive class: \(z^2\) is superattracting
and \(T\) is not asserted to be the native primitive Hubbard tree.
The full KKL gate therefore remains open and must use additional
dynamics.

Kahn's quantitative restriction theorem responds instead to

\[
 \operatorname{mod}(U\setminus K)=\frac1{\mathcal W(F)}.
\]

KKL provide \(V(F)\le\mathcal W(F)\), which is the wrong direction
for (11.2).  A sufficient stronger package would require a reverse
full/vertical comparison, a linear Kahn response, and compatible
finite-horizon selection; none is imported.

The sharper replacement avoids charging unused thin parts of a global
collar.  Let \(\mathscr E_h(F)\) be the marked measurable family of
proof-used selected continuations reaching their first inverse-branch
failure, with occurrence, access, sheet, and first-failure labels, and
put

\[
 \mathfrak E_h(F)=\mathcal W(\mathscr E_h(F)).
\tag{11.8}
\]

The route-localized target

\[
 \sum_{h=1}^{b+2}\mathfrak E_h(F)
 \le C_b\bigl(V(F)+1\bigr)
\tag{11.9}
\]

is weaker than (11.2), presentation independent, and already includes
the measurable selector.  If neither (11.2) nor (11.9) holds, the
collar/route conductances must remain explicit coordinates of the
response state.  They cannot be forgotten after qualitative embedding.
