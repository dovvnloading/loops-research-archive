# Adversarial audit of the KKL quantitative stationary-defect repair

## 1. Verdict

### Post-audit disposition

The defects listed in this audit have now been repaired in
`kkl_stationary_quantitative_defect_repair.md`: the displayed additions,
modulus subadditivity, native transverse-measure typing, capped terminal
constant, strict shortness slack, absolute-scale clause, disjoint-\(B\)
estimate, `small breaking` transfer, and restricted scope of the collar
exit theorem are all explicit there.  This file preserves the hostile
derivation which forced those corrections.

At the time audited, the proposed quantitative-defect strategy was
viable, but the note was **not correct as written**.  The following
repairs were mandatory:

1. equations (2.4) and (4.1) are missing addition signs and therefore
   do not state the source estimate;
2. width additivity must be source-typed as a transverse width measure,
   or replaced by the subadditivity inequality actually needed;
3. Theorem 6.1 needs a capped terminal constant, strict slack in the
   shortness arithmetic, a universal terminal-controllability label,
   and an absolute-scale hypothesis for its additive constant;
4. Corollary 6.2 does not follow from Theorem 6.1 as written, because a
   “short or terminal” conclusion cannot simply replace KKL's
   “short” conclusion inside every later invocation;
5. Proposition 10.2 has the correct overflow direction for its stated
   crossing class, but Corollary 10.3 does not cover all continuation
   failures until every `D1` leaf is proved to have that annular
   crossing and a measurable occurrence relation.

After the explicit repairs in Sections 2--7 below, a strengthened QSDB
is sufficient for the stationary critical-end estimate in the
high-type near-degenerate scale where the additive constant is
absorbable.  The analytic QSDB estimate itself remains open.  No
stationary repair, VAAPC-I, UPTCR, or MLC obligation is promoted.

## 2. Exact correction to equations (2.4) and (4.1)

KKL line 1588 states

\[
 \mathcal W(A^{N\text{-nbr}})
 \leq
 \mathcal W(A^{\rm sh})
 +
 \mathcal W(A_{N-1})
 +
 O(b).
\tag{2.1}
\]

With \(m=N-1\), the only source-faithful form of equation (2.4) is

\[
 \boxed{
 \mathcal W(Y^{N\text{-nbr}})
 \leq
 \mathcal W(Y^{\rm sh})
 +
 \mathcal W(Y_m)
 +
 C_b .
 }
\tag{2.2}
\]

The displayed expression currently printed in (2.4),

\[
 \mathcal W(Y^{\rm sh})\,
 \mathcal W(Y_m)\,
 C_b,
\]

is a product.  It is neither KKL line 1588 nor a dimensionally
appropriate telescoping estimate.

Assuming

\[
 \mathcal W(Y_m)
 \leq
 a_bV(F)+(c_b+4)R(F)+(c_b+4),
\tag{2.3}
\]

substitution in (2.2) gives

\[
 \boxed{
 \mathcal W(Y^{N\text{-nbr}})
 \leq
 \mathcal W(Y^{\rm sh})
 +
 a_bV(F)
 +
 (c_b+4)R(F)
 +
 C_b ,
 }
\tag{2.4}
\]

after enlarging the final \(C_b\).  This is the required correction to
equation (4.1).  Its currently printed juxtaposition of four terms is
again a product, not an additive estimate.

The factor four in (2.3) is correct under the conditional typed
lamination hypothesis: `pql_iterate_filled_graph_naturality.md`,
Corollary 5.3, gives

\[
 \mathcal W(G)\leq4R(F)+4
\]

when the distinguished final component has degree two.

## 3. Width partition: equality is not automatic

For arbitrary path families, extremal width is a modulus and is
countably subadditive:

\[
 \mathcal W(\Gamma_1\cup\Gamma_2)
 \leq
 \mathcal W(\Gamma_1)+\mathcal W(\Gamma_2).
\tag{3.1}
\]

It is not a countably additive measure on every arbitrary set-theoretic
partition of curves.  Therefore the words “measurable disjoint
partition” alone do not justify the equality currently asserted in
(4.2).

Only the inequality

\[
 \mathcal W(Y_m)
 \leq
 \mathcal W(G)+\mathcal W(D)
\tag{3.2}
\]

is needed for (2.3), and (3.2) follows from modulus subadditivity.
Thus the safest correction is to replace equality (4.2) by (3.2).

KKL do treat proof-used foliations as carrying transverse width
measure; see the explicit statement at locked source line 2391.  If
exact additivity is needed later, QSDB must include the stronger typed
clause

\[
 \mu_{Y_m}(Y_m)=\mathcal W(Y_m),\qquad
 \mu_{Y_m}(E)=\mathcal W(E)
\tag{3.3}
\]

for every selected measurable sublamination \(E\), with
\(G,D\) measurable for this one fixed transverse measure.  It must not
infer (3.3) merely from setwise measurability.

The same issue occurs in Theorem 6.1 at equation (6.8).  From

\[
 \mathcal W(A^{N\text{-nbr}})
 \geq\lambda'\mathcal W(A)
\]

one obtains

\[
 \mathcal W(A^{N\text{-br}})
 \leq(1-\lambda')\mathcal W(A)
\tag{3.4}
\]

only under the native transverse-measure identity

\[
 \mathcal W(A)
 =
 \mathcal W(A^{N\text{-nbr}})
 +
 \mathcal W(A^{N\text{-br}}).
\tag{3.5}
\]

KKL themselves use exactly this step at lines 1505--1508.  The repair
note should source-lock (3.5), rather than silently treating general
extremal width as additive.

## 4. Correct status of equation (5.3)

After correcting (4.1), KKL lines 1627--1635 support the weak estimate

\[
\begin{split}
 \mathcal W(A)
 \leq{}&
 \mathcal W(A^{N\text{-br}})
 +
 \mathcal W(A^{\rm sh})\\
 &+
 a_bV(F)
 +
 c_b'R(F)
 +
 C_b'(k+1).
\end{split}
\tag{4.1}
\]

Thus the displayed formula (5.3) is semantically correct after the
constants from (2.4) are renamed.  Its proof should say
“subadditivity on the displayed covering by sublaminations,” not
unqualified additivity, unless (3.3) has been established.

For the later global sufficiency argument, one needs the stronger
disjoint form.  Put

\[
 B=A^{N\text{-br}}\cup A^{\rm sh}.
\tag{4.2}
\]

Partition \(A\) disjointly into:

1. \(B\); and
2. the nonshort, \(N\)-unbreakable leaves in the \(X,Y,Z_j\) classes
   of KKL lines 1627--1635.

The same estimates then give

\[
 \boxed{
 \mathcal W(A)
 \leq
 \mathcal W(B)
 +
 a_bV(F)
 +
 c_b'R(F)
 +
 C_b'(k+1).
 }
\tag{4.3}
\]

Here the stationary \(Y\)-family has no short leaves by construction,
so the \(\mathcal W(Y^{\rm sh})\) term in (2.4) vanishes.  Formula
(4.3), not merely the overlapping sum (4.1), is the clean input for
terminality propagation.

## 5. Theorem 6.1: four mandatory corrections

### 5.1 The terminal constant must lie in \((0,1)\)

KKL line 1154 defines \((\delta,\eta)\)-terminal only for
\(0<\delta<1\).  The choice

\[
 \delta_v=\varepsilon/a_b
\]

may exceed one.  A valid choice is

\[
 \delta_v=
 \begin{cases}
  \min\{1/2,\varepsilon/a_b\},&a_b>0,\\
  1/2,&a_b=0.
 \end{cases}
\tag{5.1}
\]

Then \(a_b\delta_v\leq\varepsilon\), as required.

### 5.2 Strict shortness needs slack

KKL line 1183 defines \(\lambda\)-short by the strict inequality

\[
 \mathcal W(A^{\rm sh})>\lambda\mathcal W(A).
\tag{5.2}
\]

The current arithmetic gives only “\(\geq\lambda\).”  Retain

\[
 \lambda'=\frac{1+\lambda}{2}
\]

but choose

\[
 \varepsilon=\frac{1-\lambda}{8}.
\tag{5.3}
\]

Then

\[
 \lambda'-2\varepsilon
 =
 \frac{1+3\lambda}{4}
 >
 \lambda.
\tag{5.4}
\]

Consequently the nonterminal branch gives the strict conclusion (5.2).

### 5.3 The vertical branch has universal \(\eta\)

If

\[
 V(F)>\delta_v\mathcal W(A),
\]

the first terminal alternative holds independently of the second
parameter \(\eta\).  Therefore the conclusion should be

\[
 A\text{ is }(\delta_v,\eta_0)\text{-terminal}
\tag{5.5}
\]

for any fixed universal \(\eta_0\), not merely
\((\delta_v,k)\)-terminal.  This distinction matters because KKL
Proposition 8.1 requires a universal terminal controllability bound.

### 5.4 A relative-wide threshold does not absorb an absolute constant

The threshold

\[
 \mathcal W(A)
 \geq
 \frac{c_bR(F)+C_b(k+1)}{\varepsilon}
\tag{5.6}
\]

is a valid explicit hypothesis.  However, KKL's notation
\([k,\lambda]\)-wide controls \(\mathcal W(A)\) only relative to
\(R(F)\).  It does not imply (5.6) when \(R(F)\) can be arbitrarily
small.

Thus Corollary 6.2 may absorb (5.6) into the source wide threshold only
after one proves one of:

\[
 R(F)\geq r_b>0,
\tag{5.7}
\]

or the high-type near-degenerate scale assumption

\[
 R(F)\geq R_0(b,k,\lambda),
\tag{5.8}
\]

or a reformulation of wide as

\[
 \mathcal W(A)\geq
 C_{b,k,\lambda}\bigl(R(F)+1\bigr).
\tag{5.9}
\]

The global KKL application does work in an HTND regime where \(R(F)\)
is required large (locked source lines 698--725), so (5.8) is a
plausible scoped repair.  It is not part of the theorem currently
stated.

With (3.5), (5.1), (5.3), and (5.6) imposed, the corrected arithmetic
is

\[
\begin{aligned}
 (1-2\varepsilon)\mathcal W(A)
 &\leq
 \mathcal W(A^{N\text{-br}})
 +
 \mathcal W(A^{\rm sh}),\\
 \mathcal W(A^{\rm sh})
 &\geq
 (\lambda'-2\varepsilon)\mathcal W(A)\\
 &=
 \frac{1+3\lambda}{4}\mathcal W(A)
 >
 \lambda\mathcal W(A).
\end{aligned}
\tag{5.10}
\]

This proves a corrected **short-or-vertical-terminal** theorem.

## 6. Corollary 6.2 is not proved as written

Theorem 6.1 does not give KKL Proposition
`nonbreaking implies short`; it gives

\[
 \text{unbreakable}
 \Longrightarrow
 \text{short or terminal}.
\tag{6.1}
\]

One cannot replace “short” by (6.1) at KKL lines 1381 and 1388 and say
“in the terminal branch there is nothing left to prove.”  A terminal
subwave \(S\subset A\) need not make \(A\) terminal.  If

\[
 \mathcal W(S)=\theta\mathcal W(A)
\]

and \(S\) produces an \(\eta\)-controllable Wave \(C\) with

\[
 \mathcal W(C)>(1+\delta)\mathcal W(S),
\]

then \(C\) is wider than \(A\) only when

\[
 (1+\delta)\theta>1.
\tag{6.2}
\]

The current Corollary 6.2 records no such comparison.  It therefore
does not establish its claimed source-level sufficiency.

### Proposition 6.1 (a valid sufficiency repair)

Assume:

1. the strengthened QSDB partition is typed in the transverse measure
   of Section 3;
2. the disjoint charged estimate (4.3) holds;
3. the additive scale is absorbable by (5.7), (5.8), or (5.9); and
4. KKL Proposition `small breaking` is available in its stated scope.

Then, for every \(0<\lambda<1\), every sufficiently wide
\(k\)-controllable Wave \(A\) is either \(\lambda\)-short or
\((\delta,\eta)\)-terminal, with \(\delta>0\) independent of \(k\) and
\(\eta\) universal.  Hence this strengthened QSDB is sufficient for
the stationary contribution to KKL Proposition `mostly short`.

#### Proof

Choose

\[
 \lambda<\lambda_3<1.
\tag{6.3}
\]

Apply KKL Proposition `small breaking` with

\[
 n=N,\qquad k_0=12b,\qquad\lambda=\lambda_3.
\]

It supplies \(\delta_3>0\) and universal \(\eta_3\); its source
statement says \(\delta_3\) is independent of the eventual
controllability parameter \(k\).

Choose

\[
 \max\left\{
   \frac{\lambda}{\lambda_3},
   \frac{1}{1+\delta_3}
 \right\}
 <
 \theta
 <
 1.
\tag{6.4}
\]

Set

\[
 \varepsilon_\theta=\frac{1-\theta}{2},
\qquad
 \delta_v=
\begin{cases}
 \min\{1/2,\varepsilon_\theta/a_b\},&a_b>0,\\
 1/2,&a_b=0.
\end{cases}
\tag{6.5}
\]

Enlarge the scoped width threshold so that

\[
 c_b'R(F)+C_b'(k+1)
 \leq
 \varepsilon_\theta\mathcal W(A).
\tag{6.6}
\]

If \(V(F)>\delta_v\mathcal W(A)\), then \(A\) is terminal through the
vertical alternative.  Otherwise

\[
 a_bV(F)\leq\varepsilon_\theta\mathcal W(A).
\]

The disjoint estimate (4.3) now gives

\[
 \mathcal W(B)\geq\theta\mathcal W(A),
 \qquad
 B=A^{N\text{-br}}\cup A^{\rm sh}.
\tag{6.7}
\]

KKL's proof at lines 1375--1388 observes that
\(B^{N\text{-nbr}}\) is short and hence \(12b\)-controllable.  Make
the original wide threshold large enough that (6.7) makes \(B\)
wide enough for Proposition `small breaking`.  That proposition gives
two cases.

If \(B\) is \((\delta_3,\eta_3)\)-terminal, then:

- its vertical alternative gives
  \[
    V(F)>\delta_3\mathcal W(B)
    \geq\delta_3\theta\mathcal W(A);
  \]
- its wider-Wave alternative gives an \(\eta_3\)-controllable \(C\)
  satisfying
  \[
    \mathcal W(C)>
    (1+\delta_3)\mathcal W(B)
    \geq
    (1+\delta_3)\theta\mathcal W(A).
  \]

By (6.4), both alternatives make \(A\)
\((\delta_A,\eta_3)\)-terminal for

\[
 \delta_A
 =
 \min\left\{
  \delta_3\theta,\,
  (1+\delta_3)\theta-1
 \right\}
 >0.
\tag{6.8}
\]

If instead \(B\) is \((N,\lambda_3)\)-unbreakable, then
\(B^{N\text{-nbr}}\subset B^{\rm sh}=A^{\rm sh}\), so

\[
\begin{aligned}
 \mathcal W(A^{\rm sh})
 &\geq
 \mathcal W(B^{N\text{-nbr}})\\
 &\geq
 \lambda_3\mathcal W(B)\\
 &\geq
 \lambda_3\theta\mathcal W(A)
 >
 \lambda\mathcal W(A)
\end{aligned}
\tag{6.9}
\]

by (6.4).  Thus \(A\) is \(\lambda\)-short.

The first vertical split and the two small-breaking outputs exhaust all
cases.  The constants depend on \(b,\lambda\), not on \(k\), except
through the permitted wide threshold; \(\eta_3\) is universal in the
source sense. \(\square\)

This proposition supplies the proof missing from the present
Corollary 6.2.  It also shows exactly in what sense QSDB is sufficient:
the disjoint width-measure and absolute-scale clauses are essential.

## 7. Lemma 10.1 and Proposition 10.2

### 7.1 Lemma 10.1

The qualitative conclusion is correct.  A finite composition of Kahn
immersions is embedded on a neighborhood of \(K^h\); after shrinking,
a full compact continuum in a disk admits nested smooth Jordan
neighborhoods

\[
 K^h\subset O_h^-\Subset O_h^+,
\]

and their difference maps conformally to a positive-modulus annulus.
No uniform lower modulus follows.

The proof should explicitly note that inside the embedded
neighborhood

\[
 I_h^{-1}(K^0)=K^h,
\tag{7.1}
\]

so the image annulus is disjoint from the base filled set and lies in
the proof-used complementary surface.

### 7.2 Overflow direction in Proposition 10.2

For the stated class, the direction is correct.  If every
\(\alpha\in E_h\) contains a subcurve \(\sigma_\alpha\) crossing
\(Q_h\), then any metric admissible for the full crossing family
\(\Gamma(Q_h)\) is admissible for \(E_h\).  Therefore

\[
 \mathcal W(E_h)
 \leq
 \mathcal W(\Gamma(Q_h))
 =
 \frac1{\operatorname{mod}Q_h}.
\tag{7.2}
\]

No reverse inequality is available or needed.

The “last inner exit before first outer exit” construction is valid
after fixing an interior start parameter: the relevant time set is a
nonempty closed subset of a compact parameter interval.  The chosen
subcurve then stays in the closed annulus and joins its two boundary
components.

### 7.3 What Proposition 10.2 does not yet cover

A general continuation failure can occur when the source lift reaches
\(\partial O_h^+\) while the target trace merely touches
\(\partial I_h(O_h^+)\), reenters the image, or continues on another
global immersion sheet.  Proposition 10.2 assumes the stronger
statement that the oriented target continuation leaves
\(I_h(O_h^+)\).

To charge the complete `D1` class, formulate the overflow on the
selected **source lift segment** up to its first hit of
\(\partial O_h^+\), then map that segment by the embedded branch.  It
still gives an annular crosscut, but the occurrence relation and its
measurability must be proved for every `D1` leaf.  Until this is done,
Corollary 10.3 applies only to the subclass satisfying Proposition
10.2's explicit hypotheses.

Finally, the uniform estimate

\[
 \frac1{\mu_h}\leq C_b(V(F)+1)
\tag{7.3}
\]

has the correct direction, but remains a genuinely new analytic
calibration.  Kahn's qualitative \(\mu_h>0\) does not imply it.

## 8. Correct quantifier order for strengthened QSDB

The phrase “for universal \(a_b,c_b\)” is ambiguous.  The needed order
is

\[
 \boxed{
 \forall b\geq1\quad
 \exists a_b,c_b,C_b<\infty\quad
 \forall\text{ stationary blocks of parabolic bound }b\quad
 \exists(G,D)
 }
\tag{8.1}
\]

such that:

1. \(G,D\) give a transverse-measurable partition modulo a
   width-zero family;
2. \(G\) satisfies the typed degree-two incidence/extraction clauses;
3. \(D\) satisfies the defect estimate uniformly in the block,
   satellite period, and Wave horizon; and
4. the scale condition needed to absorb the additive constant is
   stated either as HTND input or through \(R(F)+1\).

With this order and the repairs above, QSDB is a sufficient
replacement target for the stationary line-1603 pointwise assertion.
Without them, the present note proves only the local algebraic estimate
(4.1) and the block-dependent exit bound (7.2), not the claimed
source-level closure.
