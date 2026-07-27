# Neutral--corridor transition interface

## 1. Purpose, correction, and status

This note source-locks the DL25 transitional estimates and calibrates their scale
against the KKL corridor state. The original draft compared the project's total WAD
weight \(Q\) with
\[
  A_m=\ell_mK_F.
\]
That comparison was incorrectly normalized: \(A_m\) is the width scale of one neutral
tile, whereas \(Q\) in `corridor_network_calibration.md` is a total retained WAD
weight. The correct target is a tile-density comparison.

The aggregation and absorption lemmas below are proved. Constructing the common
access-faithful analytic surface and preserving parallel orientation remain open.

## 2. Source-locked neutral scales

For an eventually-golden-mean \(\psi^\bullet\)-ql Siegel map \(F\), DL25 writes
\[
  K_F=W^\bullet(F)=W(V\setminus\overline Z)
\tag{2.1}
\]
for total degeneration. At level \(m\), let \(\ell_m\) be the closest-return interval
length and define
\[
  A_m=\ell_mK_F.
\tag{2.2}
\]

The level-\(m\) diffeomorphic tiling has
\[
  r_m=\mathfrak q_{m+1}
\tag{2.3}
\]
tiles, and DL25 records
\[
  \ell_m\asymp\frac1{\mathfrak q_{m+1}}.
\tag{2.4}
\]
Consequently
\[
  r_mA_m\asymp K_F.
\tag{2.5}
\]

At the transition level \(m=m_F\), Proposition
`prop:equidcombinbatorial` gives, for every declared transition tile \(I\),
\[
  W^{+,\mathrm{ver}}(I)\asymp A_m.
\tag{2.6}
\]
Theorem `thm:main:psi-ql maps` gives
\[
  W^{+,\mathrm{per}}_3(I)=O(\sqrt{A_m}).
\tag{2.7}
\]
DL25 then uses the parallel law to add widths over unions of tiles. Thus its
source-compatible scales are
\[
  W_{\rm cell}\asymp A_m,
  \qquad
  W_{\rm total}\asymp r_mA_m\asymp K_F.
\tag{2.8}
\]

The paper explicitly requires global external input for the transitional vertical
alternative. Nothing in (2.1)--(2.8) constructs a KKL corridor realization.

## 3. Corrected corridor coordinates

Rename (3.2) of `corridor_network_calibration.md` as
\[
  Q_{\rm tot}
  =
  2\left(
    \|X^{\rm core}\|+\sum_a\|X_a^{\rm short}\|
  \right).
\tag{3.1}
\]

After constructing an access-faithful assignment to the neutral tiling, define
\[
  Q_I=2\|X_I^{\rm retained}\|,
  \qquad
  Q_{\rm orb}=\sum_{I\in\mathfrak D_m}Q_I,
  \qquad
  Q_{\rm cell}=\frac{Q_{\rm orb}}{r_m}.
\tag{3.2}
\]
Any core or defect weight not assigned to a tile must remain as a separate coordinate.

The corrected comparison target is
\[
  Q_{\rm cell}\asymp A_m,
  \qquad
  Q_{\rm orb}\asymp r_mA_m\asymp K_F,
\tag{3.3}
\]
not \(Q_{\rm tot}\asymp A_m\).

For a general virtual block with \(r_B\) marking cells, the density state is
\[
  q_B=\frac{Q_{\rm tot}}{r_B},
  \qquad
  s_B=\frac S{r_B},
  \qquad
  k_B=\frac\kappa{r_B}.
\tag{3.4}
\]
Dividing the corridor sandwich by \(r_B\) gives the exact normalized inequality
\[
  q_B
  \le
  \frac{W(\mathcal V,\mathcal I)}{r_B}
  \le
  q_B+4s_B+C_{\rm net}k_B.
\tag{3.5}
\]
The raw multiplicity \(r_B\) must still be recorded to reconstruct total width and
audit parallel addition.

## 4. Aggregated square-root absorption

### Lemma 4.1 (one scale)

For every \(C,\delta>0\) and \(x\ge0\),
\[
  C\sqrt x\le\delta x+\frac{C^2}{4\delta}.
\tag{4.1}
\]

**Proof.** Expand the nonnegative square
\[
  \left(\sqrt{\delta x}-\frac C{2\sqrt\delta}\right)^2.
\]
\(\square\)

Applying Lemma 4.1 independently to \(r_m\) tiles would create an additive
\(O(r_m)\) term. The following global form keeps the correct density normalization.

### Proposition 4.2 (tile-aggregated absorption)

Let \(A>0\), \(r\ge1\), and suppose
\[
  crA\le Q_{\rm orb}\le C_0rA.
\tag{4.2}
\]
If the aggregate interface loss satisfies
\[
  E_{\rm orb}\le C_1r\sqrt A+C_2r,
\tag{4.3}
\]
then
\[
  \frac{E_{\rm orb}}{Q_{\rm orb}}
  \le
  \frac{C_1}{c\sqrt A}+\frac{C_2}{cA}.
\tag{4.4}
\]
In particular, \(E_{\rm orb}\le\delta Q_{\rm orb}\) whenever
\[
  A\ge
  \max\left\{
    \left(\frac{2C_1}{c\delta}\right)^2,
    \frac{2C_2}{c\delta}
  \right\}.
\tag{4.5}
\]

**Proof.** Divide (4.3) by the lower bound in (4.2). Each term in (4.4) is at most
\(\delta/2\) under (4.5). \(\square\)

### Corollary 4.3

If instead
\[
  E_{\rm orb}
  \le
  C_1\sum_{I}\sqrt{Q_I}+C_2r\sqrt A+C_3r
\tag{4.6}
\]
and \(\sum_IQ_I=Q_{\rm orb}\le C_0rA\), then Cauchy--Schwarz gives
\[
  \sum_I\sqrt{Q_I}
  \le\sqrt{rQ_{\rm orb}}
  \le\sqrt{C_0}\,r\sqrt A.
\]
Hence Proposition 4.2 applies with
\(C_1\sqrt{C_0}+C_2\) in place of \(C_1\).

This is the correct reason that a DL25 peripheral loss
\(O(r_m\sqrt{A_m})\) is harmless relative to
\(Q_{\rm orb}\asymp r_mA_m\): its relative size is
\(O(A_m^{-1/2})\), independently of \(r_m\), in the large-\(A_m\) branch. A
bounded-\(A_m\) branch must instead be absorbed into the regularization threshold.

## 5. A common-width bridge

Access labels on the same surface do not imply comparability of curve families.
Left--right and bottom--top families in a \(t\)-by-\(1\) rectangle have reciprocal
extremal scales, and a covering of unbounded degree changes annular width by that
degree. The interface must control distortion, multiplicity, and whether the families
are combined in parallel or in series.

### Lemma 5.1 (two calibrations through one width)

Suppose a common marked family has width \(W\), and
\[
  cA-C_0\le W\le CA+C_0,
\tag{5.1}
\]
while
\[
  Q\le W\le(1+\varepsilon)Q+E_0.
\tag{5.2}
\]
Then
\[
  \frac{cA-C_0-E_0}{1+\varepsilon}
  \le Q\le CA+C_0.
\tag{5.3}
\]

**Proof.** Combine the lower inequality in (5.1) with the upper inequality in (5.2)
for the left side, and the lower inequality in (5.2) with the upper inequality in
(5.1) for the right side. \(\square\)

Thus (3.3) should be obtained by calibrating both charts to an actual common curve
family, not by postulating a direct numerical comparison.

## 6. Normalized KKL tail and the stride obstruction

For an \((n,p)\)-translation marking, KKL has
\[
  N=2(n+1)p,
  \qquad
  \|X^{\rm long}\|\le2W_{\rm std}+6N.
\tag{6.1}
\]
Dividing by the \(n+1\) translation cells gives
\[
  \frac{\|X^{\rm long}\|}{n+1}
  \le
  \frac{2W_{\rm std}}{n+1}+12p.
\tag{6.2}
\]
For the doubled contribution in the corridor sandwich,
\[
  \frac{2\|X^{\rm long}\|}{n+1}
  \le
  \frac{4W_{\rm std}}{n+1}+24p.
\tag{6.3}
\]

In KKL's inner parabolically bounded application, \(p\) is bounded by the parabolic
bound. In that case the marking charge has bounded density after orbit normalization.
No imported theorem identifies \(n+1\) with the neutral tile count
\(\mathfrak q_{m+1}\), and KKL's shift \(p\) is not a continued-fraction coefficient.
Unbounded \(p\) remains a separate obstruction.

## 7. Corrected Neutral--Corridor Interface Lemma

### Interface theorem (`OPEN`)

At every transition level \(m=m_F\):

1. construct the \(\psi^\bullet\)-ql Siegel surface required by DL25;
2. construct an access-faithful assignment of the retained corridor WAD to the
   \(r_m=\mathfrak q_{m+1}\) neutral tiles;
3. identify an actual common marked family so that, tilewise,
   \[
     c\,W^{+,\mathrm{ver}}(I)-C
     \le Q_I
     \le
     C\bigl(
       W^{+,\mathrm{ver}}(I)+
       W^{+,\mathrm{per}}_3(I)+1
     \bigr);
   \tag{7.1}
   \]
4. prove universally bounded quasiconformal distortion and lift/projection
   multiplicity, and preserve parallel electrical orientation;
5. prove the corridor orbit length is comparable to \(r_m\);
6. retain defect/core weight separately and prove it is relatively small,
   locally telescoping, or paid by a quantified entropy estimate;
7. classify \(W_{\rm std}\) in the common chart and handle unbounded KKL shift \(p\);
8. audit every omitted critical-orbit point and every pullback used in the comparison.

There is a universal threshold \(A_*\) (chosen after all additive comparison
constants) such that, when \(A_m\ge A_*\), (2.6)--(2.8), Lemma 5.1, and Proposition
4.2 give
\[
  Q_{\rm cell}\asymp A_m,
  \qquad
  Q_{\rm orb}\asymp K_F,
\]
with global peripheral relative loss \(O(A_m^{-1/2})\).

Indeed, if the lower affine comparison after Lemma 5.1 is
\[
  Q_{\rm cell}
  \ge
  \frac{cA_m-C_0-E_0}{1+\varepsilon},
\]
choose \(A_*\ge2(C_0+E_0)/c\); the lower bound is then a fixed positive multiple of
\(A_m\), and all additive upper terms are absorbed similarly. For \(A_m<A_*\), the
upper half of (7.1) and the DL peripheral bound give only
\[
  Q_{\rm cell}=O(A_m+\sqrt{A_m}+1)=O_{A_*}(1).
\]
This is the bounded normalized branch to be placed under \(D_*\); no multiplicative
claim \(Q_{\rm cell}\asymp A_m\) is made there.

All eight items are new interface work. DL25 supplies the neutral estimates only after
its category and grounded-tile hypotheses have been met; KKL explicitly does not
perform the transfer to the \(\psi^\bullet\) category.

## 8. Adversarial boundary cases

1. **Wrong normalization:** \(Q_{\rm tot}\asymp A_m\) loses a factor
   \(r_m\).
2. **Parallel-to-series change:** equal local widths \(A\) add to \(rA\) in parallel
   but combine to \(A/r\) in series.
3. **Unbounded multiplicity:** a degree-\(d\) projection can change width by \(d\).
4. **Missing equidistribution:** total mass \(K_F\) alone gives no two-sided control
   on one interval of length \(\ell_m\).
5. **Global square-root fallacy:** with \(Q_{\rm orb}\asymp rA\) and
   \(\kappa\asymp r\), the condition \(\kappa=O(\sqrt{Q_{\rm orb}})\) would force
   \(r=O(A)\); it is neither source-supplied nor needed.
6. **Infinite alternation:** a relative loss at each interface must occur within a
   block having a bounded interface count or a proved telescoping/discounted error
   profile. Pointwise \(O(\sqrt A)\) estimates alone do not sum over arbitrary chart
   alternation.
