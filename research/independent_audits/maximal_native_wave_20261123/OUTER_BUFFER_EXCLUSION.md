# Selected outer buffered classes: the matched peripheral-cover proof

**Date:** 2026-11-23. **Status:** a written analytic proof from the actual
selected-family physical package and the existing exact collar estimates.
It supplies the peripheral-cover interpretation needed for the stated
outer-class exclusion. It does not determine inner canonical coefficients
or settle a global H4, stationary N2, UPTCR, or MLC statement.

**AI disclosure:** GPT-6 Astra Pro assisted proof search, source comparison,
and drafting. Review by collaborating AI agents is not human mathematical
referee certification or a formalization of the complex analysis.

## 1. Exact statement and attribution

The generic peripheral interval estimate and the numerical collars were
already proposed in [the November 16 buffered-WAD note, §§2–3](../tip_family_buffered_wad_20261116/NOTE.md)
and [v2, the peripheral lemma and buffered theorem](../../../papers/tip_family_preprint_v2_20261116/sections/buffer_depth.tex).
The v2 referee retained their physical interpretation as local hypothesis
H4 in [the scope definition](../../../papers/tip_family_preprint_v2_20261116/sections/referee_scope.tex).
This note supplies a complete application to the actual four-boundary
surface, including the primitive outer loop, injective cyclic-cover lift,
transverse normalization, and all returning outer classes. It does not
claim a new numerical bound or a new generic elliptic formula.

Use the actual three little filled intervals established by
[the physical bridge proof, §§1–3](../../tip_family_theorem/PHYSICAL_BRIDGES.md)
and specified in [the access note, §1](NOTE.md). For the selected parameter
of each integer \(p\ge3\), write \(x_j=f_{c_p}^{\,j}(0)\) and

\[
 U_p=D(0,R_p),\qquad R_3=1/4,\quad R_p=2^{-p}\ (p\ge4),
\]
\[
 K_{0,p}=[x_{3p},x_{6p}],\quad
 K_{1,p}=[x_{4p},x_p],\quad
 K_{2,p}=[x_{2p},x_{5p}],\qquad
 Y_p=U_p\setminus(K_{0,p}\cup K_{1,p}\cup K_{2,p}).
 \tag{1.1}
\]

The certified strict order makes these three nondegenerate intervals
pairwise disjoint and compactly contained in \(U_p\). A Joukowski collar
of each slit identifies its two physical banks with one entire ideal
circle; an ordinary collar identifies the analytic outer circle with its
entire ideal circle. Thus \(Y_p\) is the actual genus-zero four-boundary
surface, minimally marked by \(I_{\rm out},I_0,I_1,I_2\). Its fundamental
group is free of rank three. In particular it is not the exceptional
minimally marked annulus of KKL Appendix A.2.3.

For an admissible simple unoriented ideal class \(\gamma\), choose the
two ideal intervals of a universal-cover lift and let \(q_\gamma\) be
their full quadrilateral width. The KKL buffered coefficient is

\[
 w_\gamma=(q_\gamma-2)_+.
 \tag{1.2}
\]

**Theorem 1.1.** On these actual selected surfaces, for every \(p\ge11\)
and every admissible class incident on \(I_{\rm out}\), including every
essential outer-to-outer class,

\[
 q_\gamma<2,\qquad w_\gamma=0.
 \tag{1.3}
\]

The input package remains explicit: the actual intervals, physical
domains, signed order, and separately quantified all-period chart. The
proof does not infer that package from the finite verifier.

## 2. The actual outer annulus and its primitive lift

Use the positive conformal scale \(\xi=\sigma_p z\), where

\[
 \sigma_p=-[z^2]f_{c_p}^{\,p}>0.
\]

Let \([L,R]=[\sigma_p x_{2p},\sigma_p x_p]\), with center \(M\) and
half-length \(a>0\). This is the whole carrier containing all three
holes. The map

\[
 \mathcal J(w)=M+\frac a2(w+w^{-1})
 \tag{2.1}
\]

is conformal from \(|w|>1\) to the exterior of that carrier. If

\[
 |M|+\frac a2(t+t^{-1})<\sigma_pR_p,
 \tag{2.2}
\]

then the full annulus \(A_t=\mathcal J(\{1<|w|<t\})\) is contained
in \(\sigma_pY_p\). It avoids the entire carrier and therefore avoids
each of the actual three holes. The gaps of the carrier remain points
of \(Y_p\); no additional hole is introduced.

For \(1<s<t\), the curve \(\mathcal J(\{|w|=s\})\) is a Jordan
ellipse enclosing all three holes once. The region between it and the
outer physical circle contains no hole. Its homotopy class is therefore
the primitive outer peripheral class, up to orientation and conjugacy;
it is not a multiple turn or an inner peripheral class.

Let \(\widetilde Y\to Y_p\) be the universal cover, let

\[
 H=\langle\tau\rangle
\]

be the stabilizer of a chosen lift of \(I_{\rm out}\), and let

\[
 \pi_H:\mathbb A_{\rm out}=\widetilde Y/H\longrightarrow Y_p
\]

be the corresponding peripheral cyclic cover. Choose the base point and
the conjugate of \(H\) compatibly with \(A_t\). The inclusion of \(A_t\)
has fundamental-group image exactly \(H\), so the covering lifting
criterion gives a holomorphic lift \(j:A_t\to\mathbb A_{\rm out}\).
It is injective: \(j(z_1)=j(z_2)\) would imply equality of their images
under the original embedded inclusion. Its core has degree one in the
cyclic annulus because the physical ellipse represents the primitive
peripheral generator.

For the compactly contained truncated annuli

\[
 A_{s,t}=\mathcal J(\{s<|w|<t\}),\qquad 1<s<t,
\]

their lifts are essential embedded subannuli. Modulus monotonicity gives

\[
 \operatorname{mod}\mathbb A_{\rm out}
 \ge \operatorname{mod}A_{s,t}
 =\frac{\log(t/s)}{2\pi}.
\]

Letting \(s\downarrow1\) proves

\[
 \mathcal W_{Y_p}(I_{\rm out})
 =\frac1{\operatorname{mod}\mathbb A_{\rm out}}
 \le\frac{2\pi}{\log t}.
 \tag{2.3}
\]

This truncation avoids any assertion that the inner edge of \(A_t\)
itself is a boundary component of \(Y_p\). The local width in (2.3) is
exactly KKL Appendix A.2.4's cyclic-cover width, the convention also used
in [the exit-transfer note, §§3–4](../maximal_exit_transfer_20261123/NOTE.md).
It has not been identified with an individual \(q_\gamma\).

## 3. Every incident universal-cover quadrilateral

Uniformize \(\widetilde Y\) as the upper half-plane, normalize the
chosen lift of \(I_{\rm out}\) to \(J=(0,\infty)\), and write its
primitive stabilizer as

\[
 \tau(z)=\lambda z,\qquad \lambda>1,\qquad \ell=\log\lambda.
\]

The logarithm gives the cyclic quotient a strip of height \(\pi\)
and periodic circumference \(\ell\). Its modulus is \(\pi/\ell\),
so its transverse width is

\[
 \mathcal W_{Y_p}(I_{\rm out})=\ell/\pi.
 \tag{3.1}
\]

Lift any admissible class incident on \(I_{\rm out}\) with one end
on \(J\). Its other interval \(J'\) differs from \(J\): a path whose
two lifted ends lie on \(J\) is subordinate to that single marked
interval and is excluded by KKL A.1. This also treats essential
outer-to-outer classes, whose two ends lie on distinct lifts of the same
whole boundary circle.

The components of the ordinary set in the universal boundary are
pairwise disjoint open intervals, and the deck group permutes them.
Thus \(J'\) and \(\tau J'\) are either equal or have disjoint
interiors. A distinct \(J'\) cannot share \(0\) or \(\infty\) with
\(J\): dilation would give overlapping intervals with different finite
endpoints, unless \(J'=(-\infty,0)\). That last case would leave the
limit set contained in \(\{0,\infty\}\), making the group elementary,
in contradiction to the four-boundary surface. The same observation
excludes a second interval stabilized by \(\tau\).

Consequently

\[
 J'=(-b,-a),\qquad 0<a<b<\infty,
 \qquad J'\cap\tau J'=\varnothing.
\]

Since \(\tau J'=(-\lambda b,-\lambda a)\), disjointness implies

\[
 b/a\le\lambda.
 \tag{3.2}
\]

The Schwarz–Christoffel four-point formula in the transverse-width
normalization gives, for these exact ideal electrodes,

\[
 k^2=1-a/b,\qquad
 q_\gamma=\frac{K(k)}{K(\sqrt{1-k^2})},
 \quad
 K(k)=\int_0^{\pi/2}\frac{d\theta}
 {\sqrt{1-k^2\sin^2\theta}}.
 \tag{3.3}
\]

This is the generic formula used in the earlier buffered note; the
rectangle normalization is also derived in [H3_WIDTH.md, §2](H3_WIDTH.md).
The numerator increases and the denominator decreases with \(k\).
Equations (3.1)–(3.3) therefore give the class-independent comparison

\[
 q_\gamma\le
 \frac{K(\sqrt{1-e^{-\ell}})}{K(e^{-\ell/2})},
 \qquad
 \ell=\pi\mathcal W_{Y_p}(I_{\rm out}).
 \tag{3.4}
\]

The local cyclic width and the quadrilateral width are distinct
quantities. In particular, a bound \(\mathcal W(I_{\rm out})\le2\)
alone is not the required exclusion test. The lamination estimate in
exit-transfer Theorem 3.1 does not replace (3.4), especially for returning
classes.

## 4. Exact threshold and the existing physical collars

Put \(k_0=1/\sqrt2\) and

\[
 k_*^2=12\sqrt2-16,\qquad
 k_*'=3-2\sqrt2.
\]

The quadratic Landen identities give

\[
 K(k_*)=(1+k_0)K(k_0),\qquad
 K(k_*')=\frac{1+k_0}{2}K(\sqrt{1-k_0^2}),
\]

so \(K(k_*)/K(k_*')=2\). Since

\[
 (k_*')^2=17-12\sqrt2=(17+12\sqrt2)^{-1},
\]

strict monotonicity in (3.4) proves

\[
 \ell<\log(17+12\sqrt2)
 \quad\Longrightarrow\quad q_\gamma<2
 \quad\text{for every incident class.}
 \tag{4.1}
\]

The already implemented whole-ellipse checks supply:

| Selected period | Actual outer collar parameter | Certified bound from (2.3) |
|---|---:|---:|
| \(p=11\) | \(t=300\) | \(\ell\le2\pi^2/\log300<7/2\) |
| \(p=12\) | \(t=512\) | \(\ell\le2\pi^2/\log512<7/2\) |
| every \(p\ge13\) | \(t=1024\) | \(\ell\le2\pi^2/\log1024<3\) |

For the tail, the existing corrected all-period chart yields

\[
 |M|<2,\quad a<2,\quad
 \sigma_pR_p>\frac3{20}2^p.
\]

Thus (2.2) holds simultaneously for every \(p\ge13\), because

\[
 |M|+\frac a2(1024+1024^{-1})
 <2+1024+1024^{-1}
 <\frac3{20}2^{13}\le\frac3{20}2^p.
\]

Also \(2\pi^2/\log1024=\pi^2/(5\log2)<3\), using
\(\pi^2<10\) and \(\log2>2/3\). For both finite cases the existing
Machin-\(\pi\) and atanh-log rational enclosures give the displayed
strict \(7/2\) bound. The exact sufficient comparisons are

\[
 e^{7/2}<(33/20)^7<169/5<17+12\sqrt2,
 \qquad e^3<27<17+12\sqrt2.
\]

The first uses the certified positive-Taylor remainder
\(e^{1/2}<33/20\) and \(\sqrt2>7/5\). Hence every row satisfies
(4.1). Equation (1.2) proves Theorem 1.1, including all essential
outer self-classes and all winding choices. No finite word cutoff is used.

## 5. Exact remaining scope and reproducibility

This proves the selected outer-buffer application of the local H4
peripheral comparison on \(Y_p\). It does not assert a general
peripheral comparison for an unidentified native surface. Nor does it
identify the four-boundary classes with the ten-atom tree-annulus
classes or the twenty-atom source classes used for unbuffered gain.

The four outer-involving endpoint types have zero coefficients for
\(p\ge11\). No assertion here settles any coefficient of the six inner
endpoint types, gives a complete support enumeration, gives a positive
norm lower bound, or constructs a WAD-to-Wave amplification transfer.

The existing read-only verifier and its adversarial tests are sufficient:

```sh
python -B research/independent_audits/tip_family_buffered_wad_20261116/verify.py
python -B -m unittest discover -s research/independent_audits/tip_family_buffered_wad_20261116 -p 'test_*.py' -v
```

The relevant functions are `check_order`, `ellipse_check`,
`width_log_length_bounds`, `tail_chart`, `elliptic_threshold_finite_logic`,
and `check_cyclic_exclusion` in [that verifier](../tip_family_buffered_wad_20261116/verify.py).
Its tail propagation already uses
\(30\cdot15246+88(4^j-1)/3\), with only the recurrence term divided by
three. It checks the exact analytic premises used above; it does not
formalize covering-space theory, uniformization, modulus monotonicity,
Schwarz–Christoffel uniformization, or Landen's identity.

Primary source: Kahn–Kapiamba–Lyubich,
[*MLC for parabolically bounded primitive renormalization*, v1](https://arxiv.org/html/2606.27272v1),
Appendix A.1 for admissible paths and whole-circle markings,
A.2.1–A.2.3 for the ideal quadrilateral and its two-square buffer,
and A.2.4 for the peripheral cyclic-cover definition. The generic
comparison and exact collar inputs are attributed to the November 16
packet at the start of this note; the new contribution is the fully
matched selected-surface application.
