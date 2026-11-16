# Canonical real-primitive-tip marked Wave: certified sandwich and its exact boundary

**2026-11-16.** This is a *new-only* supplement to
[the canonical-width gap audit](../real_primitive_tip_family_canonical_width_20261116/NOTE.md).
It does not modify any pre-existing research, native-wave code, source lock, or
CI. It proves the missing **inclusions of curve families**, *given the physical
slit/ideal-marking identification stated by that audit*, and adds certified
finite arithmetic for the first large periods. It does **not** determine the
supremal width or prove its convergence. Its finite numerical assertions are
recomputed by [verify.py](verify.py); the mathematical statements about
ideal-boundary homotopy and conformal extremal width are proved below rather
than treated as Python theorems.

## 1. Exact KKL contract and the marking hypothesis

Primary reference: Kahn–Kapiamba–Lyubich,
[MLC for parabolically bounded primitive renormalization, arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272v1),
**Appendix A.1** (ideal markings, paths, Waves, ends/crest),
**A.2.1** (conformal width of a rectangle and its vertical foliation),
**A.3.1** (covering pushforward), **A.3.2** (immersion restriction,
Lemma A.11 and Proposition A.12), and **§6.1, Propositions 6.5–6.6**
(the physical pullback marking and its combinatorial action).
A.1 explicitly *excludes* a proper path subordinate to a multi-interval
of length at most two. A Wave is a lamination subordinate to a
multi-interval; its base is the smallest such interval and its crest is
base minus its endpoint multi-intervals. A.3.2 **does not** impose a
two-surviving-children condition on A.1 parents.

Write \(f_c(z)=z^2+c\), \(x_j=f_{c_p}^{\,j}(0)\),
\(G_p=f_{c_p}^{\,p}\), \(T_p=[x_{2p},x_p]\),
\(T'_p=[-x_p,x_p]\), \(U_p=D(0,R_p)\), and
\(\Omega_p=U_p\setminus T_p\), with \(R_3=1/4\) and
\(R_p=2^{-p}\) for \(p\ge4\). Let \(V_p\) denote the
central degree-two pullback component. From
[the ten-period exact audit](../real_primitive_tip_family_unconditional_20261116/NOTE.md)
and [the all-period realization lemma](../real_primitive_tip_family_all_p_20261116/NOTE.md),
the strict real orders are, for every \(p\ge3\),
\[
x_{2p}<x_{5p}<x_{3p}<0<x_{6p}<\alpha_p<x_{4p}<x_p
\]
and
\[
-x_p<-x_{4p}<x_{2p}<x_{5p}<-\alpha_p<x_{3p}
 <x_{6p}<\alpha_p<-x_{5p}<-x_{2p}<x_{4p}<x_p.
\]
The slit-side ideal marking is the cyclic list \(I_0,\ldots,I_9\).
**Identification input M:** \(I_9,I_1\) are the two opposite accesses
to \((x_{5p},x_{3p})\), \(I_0\) is the *left-tip terminal atom*,
and the source has the twenty atoms \(S_0,\ldots,S_{19}\) with
the pullback blocks in §3 below. These are the KKL physical
prime-end interpretations asserted in the prior family and native
source audits, not facts derivable from real-orbit interval arithmetic
alone. In particular, this supplement does not independently prove
that the actual little Julia/Hubbard tree has no extra complex
prime-end accesses. **Every statement here about the actual KKL
canonical Wave is conditional on M.** On the explicitly defined
marked slit \((\Omega_p,I)\), the sandwich proof itself is unconditional.

Fix \(B=(I_9,I_0,I_1)\), crest \(I_0\), and
\[
W_p^*=\sup\{W(\mathcal S):\mathcal S\text{ is an A.1 Wave on }
(\Omega_p,I),\ {\rm base}(\mathcal S)=B,\ I_0\subset{\rm crest}(\mathcal S)\}.
\]
If two A.3.2-surviving source children are required *additionally*,
write \(W_{p,2}^*\) for that **smaller** supremum. Our bounds apply
to both, and do not claim they are equal.

## 2. Lower inclusion: every round leaf belongs to an A.1 Wave

Put
\[
m_p={x_{2p}+x_{5p}\over2},\quad
r_{0,p}={x_{5p}-x_{2p}\over2},\quad
r_{1,p}=\min\{-\alpha_p-m_p,\ x_{4p}+m_p\}.
\]
The certified strict orders imply \(0<r_{0,p}<r_{1,p}\).
For every \(r_{0,p}<s<r_{1,p}\), let
\[
 q_s=m_p+s,\quad w_s=m_p-s,\qquad
 \gamma_s(t)=m_p+s\,e^{2\pi i t},\quad 0<t<1.
\]
The *entire* radius interval, not a selected sample, satisfies
\[
x_{5p}<q_s<-\alpha_p<x_{3p},\qquad
-x_{4p}<w_s<x_{2p}.
\tag{2.1}
\]
Thus the circle meets the **target** slit only at \(q_s\), where its
upper and lower approaches are distinct ideal endpoints. The rest of
the circle lies in \(\Omega_p\), provided its disk lies in \(V_p\).

For \(3\le p\le12\), the old interval audit and the new rerun
certify the entire *closed* maximal gate disk under \(G_p\), with
image margin \(>2R_p/5\) and its real center in \(V_p\).
For \(p\ge13\), the all-period lemma gives
\(|A_p|4^{-p}>3/20\), \(|\tau_p|<1.795\), and, for
\(|u|\le2.1\),
\(|h_p(u)-(u^2+\tau_p)|<88\,4^{-p}\), where
\(h_p(u)=A_pG_p(u/A_p)\).
The whole gate disk obeys \(|z|\le x_{4p}<x_p\), hence
\(|A_pz|\le|\tau_p|<2\). Therefore
\[
 |G_p(z)|<\frac7{|A_p|}
 <\frac{140}{3}\,4^{-p}<\frac35\,2^{-p}<R_p
 \quad (p\ge13).
\tag{2.2}
\]
The center lies in the certified real central component;
connectedness of the gate disk and (2.2) give containment in \(V_p\).
This supplies the needed *whole-leaf*, not point-sampled, properness.

Now check **each KKL rule**:

1. **A.1 proper-path endpoints and homotopy.** \(\gamma_s\) is simple
   in \(\Omega_p\), its only missing endpoint is \(q_s\) with accesses
   \(I_9,I_1\) under M, and it is homotopic relative to those endpoints
   into an arbitrarily thin collar of the *left-tip* boundary arc
   \(I_9\cup I_0\cup I_1\). It cannot be homotoped into the collar
   of either one- or two-atom subinterval: \(I_0\) separates the two
   side accesses on that boundary arc. Hence it is an A.1 path, not
   a forbidden short path.
2. **A.1 lamination, base and crest.** Circles of distinct radii
   are disjoint. The open family \(\mathcal S_p^{\rm rad}\) is a proper
   simple-path lamination. Every leaf is subordinate to \(B\) and no
   strictly smaller multi-interval supports all leaves. Its ends are
   \(I_9,I_1\); its base is exactly \(B\), and its crest contains \(I_0\).
   The outer *whole-component* ideal atom is not an endpoint.
3. **A.2.1 width.** In the annular collar
   \(r_{0,p}<|z-m_p|<r_{1,p}\) the slit removes precisely the
   *rightward radial ray*. The log chart
   \(z\mapsto \log((z-m_p)/r_{0,p})\) identifies it with
   \((0,\log(r_{1,p}/r_{0,p}))\times(0,2\pi)\);
   \(\gamma_s\) are the vertical leaves. A.2.1/elementary
   extremal length gives the **conformal** width
   \[
   W(\mathcal S_p^{\rm rad})=
     W_p^{\rm rad}={\log(r_{1,p}/r_{0,p})\over2\pi}.
   \tag{2.3}
   \]
   Enlarging the ambient surface does not change the width of a
   path family wholly contained in this rectangle: restrict an
   admissible density to the rectangle, or extend it by zero.
   It is not a geometric annulus substituted for a canonical Wave.

By the *definition of the supremum*, without any immersion assumption,
\[
\boxed{W_p^{\rm rad}\le W_p^*.}\tag{2.4}
\]

## 3. A.3.2 children: immersion restriction versus covering pushforward

To check the *optional* two-child admissibility, use the source
\(\Omega'_p=V_p\setminus T'_p\). Since (2.1) puts
\(w_s\) in the new source attachment \((-x_{4p},x_{2p})\),
\(\gamma_s\cap\Omega'_p\) consists of **two** open semicircles,
each proper relative to the induced source marking. This is an
**immersion restriction \(\iota^*\)**, not an inverse of \(G_p\).
The source ideal endpoint pairs are
\((S_3,S_1)\) and \((S_{19},S_{17})\).
Their shortest cyclic spans (number of atoms, endpoints included)
are \(3,3\), so neither is discarded by A.1.

The A.3.2 immersion pullback marking has exactly these blocks
(§6.1 Propositions 6.5–6.6 and the physical all-period cut order):
\[
\begin{array}{lll}
P_0=[18,19,0,1,2],&P_1=[3,4],&P_2=[5],\\
P_3=[6],&P_4=[7,8,9],&P_5=[10],\\
P_6=[11,12,13],&P_7=[14],&P_8=[15],\\
P_9=[16,17].
\end{array}
\]
The \(S_1/S_3\) endpoints belong to **different** \(P\) blocks,
as do \(S_{19}/S_{17}\). Therefore neither proper child is
subordinate to *one* immersion-pullback block, and **both survive**
the additional A.3.2 filter. This verifies
\[
\boxed{W_p^{\rm rad}\le W_{p,2}^*\le W_p^*.}\tag{3.1}
\]
That statement does *not* assert two children for arbitrary A.1 parents.
Indeed the avoiding comparison has source endpoints
\((S_3,S_{17})\), source short span **7**, not 3.

**Separate covering \(f_*\):** the unbranched proper map
\(G_p:V_p\setminus T'_p\to\Omega_p\) is the covering in
A.3.1, whose twenty source atoms satisfy
\(f_*(S_j)=I_{j\bmod10}\).
It sends the two child pairs above to
\((I_3,I_1)\) and \((I_9,I_7)\), of target short spans \(3,3\);
the avoiding pair maps to \((I_3,I_7)\), target span \(5\).
These are **pushforward** facts and say nothing about which children
survive the **immersion** restriction. Conversely, a source block
\(P_0\) contains nonproper parts whose physical image under the
inclusion is target *interior*, not a single target atom.
The two operations must not be identified.

## 4. Upper inclusion: every admissible parent leaf is in a full lifted class

This argument uses **only A.1**, not an unproved assertion that every
parent has a particular A.3.2 restriction.

Fix a leaf \(\gamma\) of any admissible Wave with base \(B\) and
crest \(I_0\). Its two ends lie in \(I_9,I_1\): if an end contained
\(I_0\), the A.1 crest would omit \(I_0\), and if an end met another
atom, its base would not be \(B\). Moreover **subordinate to \(B\)**
means (KKL A.1) that its relative-endpoint homotopy class can be
represented in *every collar* of the three-atom left-tip arc. This
selects the left-tip lift of the endpoints in the universal cover.
A route around the *right* tip, an extra whole-slit winding, or an
endpoint on the outer boundary is **not** subordinate to this \(B\).
The statement concerns the homotopy lift of the **actual arbitrary
curve**, not an assumption that all curves look circular.

For clarity write
\[
 m={x_{2p}+x_p\over2},\quad r={x_p-x_{2p}\over2},\quad
 J(\zeta)=m+\frac r2(\zeta+\zeta^{-1}).
\]
The exterior unit disk is mapped conformally to the *physical
plane-slit complement*. The physical disk-slit \(\Omega_p\) maps to
a subannulus. In the logarithmic universal cover
\(\zeta=-e^{s+it}\), the left-tip access pairs in
\((x_{5p},x_{3p})\) are exactly
\[
 E_-=\{-b<t<-a,\ s=0\},\qquad
 E_+=\{a<t<b,\ s=0\},
\tag{4.1}
\]
where
\[
a=\arccos((m-x_{5p})/r),\qquad
b=\arccos((m-x_{3p})/r),\qquad 0<a<b<\pi.
\]
Define \(\widetilde\Gamma_p\) to be **all** locally rectifiable
proper paths in the corresponding lifted \(\widetilde\Omega_p\)
joining \(E_-\) to \(E_+\), with no circularity, simplicity,
pullback-child, or prescribed-radius restriction. The homotopy
argument above proves the *literal family inclusion*
\[
\{\text{lifts of leaves of any A.1 Wave with base }B
  \text{ and crest }I_0\}\subseteq\widetilde\Gamma_p.
\tag{4.2}
\]
No other deck-translation class enters (4.2); all possible
wiggles, excursions and noncircular geometry **are** allowed.

The step from a lifted width to the physical Wave needs care:
**it is not an extremal-width identity under a covering.**
Let \(\pi:\widetilde\Omega_p\to\Omega_p\) be the log cover,
with deck shift \(t\mapsto t+2\pi\).
For any finite-area density \(\widetilde\rho\) admissible for
\(\widetilde\Gamma_p\), define the *periodized* physical density in
local conformal coordinates by
\[
\rho(\pi z)^2=\sum_{n\in\mathbb Z}
                 \widetilde\rho(z+2\pi i n)^2.
\tag{4.3}
\]
The sum is well-defined almost everywhere; Tonelli gives
\(\int_{\Omega_p}\rho^2=\int_{\widetilde\Omega_p}
\widetilde\rho^2\).
For every projected leaf \(\gamma=\pi\widetilde\gamma\)
covered by (4.2), pointwise \(\rho\ge\widetilde\rho\) on
the selected lift, hence
\(\ell_\rho(\gamma)\ge\ell_{\widetilde\rho}
(\widetilde\gamma)\ge1\).
Taking infima of areas in the definition of extremal width gives
\[
W(\mathcal S)\le
W_{\Omega_p}(\pi\widetilde\Gamma_p)
\le W_{\widetilde\Omega_p}(\widetilde\Gamma_p)
=:Q_p.
\tag{4.4}
\]
The intermediate family can contain nonsimple projections:
this is harmless for width monotonicity and actually makes
the upper family larger. Thus
\[
\boxed{W_{p,2}^*\le W_p^*\le Q_p.}\tag{4.5}
\]
For the **immersion**, \(\iota^*\) can only discard parent-leaf
restriction components, and cannot create a parent leaf outside
(4.2). For the **cover**, \(f_*\) transports *source* atoms and
curves, and cannot be substituted for \(\iota^*\) or for the
physical projection \(\pi\) in (4.3).

## 5. Certified upper chart and period-uniform inequalities

The finite-disk Joukowski inverse lies in the annular outer
envelope \(|\zeta|<\rho_+\), where
\[
 B_+=(R_p+m)/r,\qquad \rho_+=B_++\sqrt{B_+^2+1},
 \qquad L_+=\log\rho_+.
\]
Indeed for \(|\zeta|>\rho_+\),
\(|J(\zeta)|\ge(r/2)(|\zeta|-|\zeta|^{-1})-m>R_p\);
hence \(\Omega_p\) is contained in this annulus.
Conformal monotonicity on the *lifted* full path family then yields
\[
 Q_p\le Q(L_+),\quad
 Q(L)={K(k_L)\over K(\sqrt{1-k_L^2})},\quad
 k_L={\sinh(\pi(b-a)/(2L))\over\sinh(\pi(b+a)/(2L))}.
\tag{5.1}
\]
The Schwarz–Christoffel quadrilateral formula in the prior audit
computes (5.1) by exponentiating the lifted strip to the upper
half-plane. It is an **upper envelope**, not the unknown maximal
KKL Wave width. Enlarging the finite disk further to the plane slit
gives
\[
 Q_p\le Q_{\rm plane,p}
 ={K(k_p)\over K(\sqrt{1-k_p^2})},\qquad
 k_p={b-a\over b+a}.
\tag{5.2}
\]

The *original* exact \(2^{-512}\) source recomputation gives the
following strict brackets, and the new verifier recomputes them
independently of this table. Decimal brackets are outward rational
intervals, **not floats**:

| \(p\) | \(W_p^{\rm rad}\): strict witness interval | \(Q(L_+)\): strict upper-envelope interval |
|---:|---:|---:|
| 3 | (0.2516729, 0.2516732) | (0.5967637, 0.5967640) |
| 4 | (0.2584721, 0.2584724) | (0.6080487, 0.6080490) |
| 5 | (0.2600034, 0.2600037) | (0.6811880, 0.6811883) |
| 6 | (0.2603715, 0.2603718) | (0.7182629, 0.7182632) |
| 7 | (0.2604624, 0.2604627) | (0.7377890, 0.7377893) |
| 8 | (0.2604850, 0.2604853) | (0.7489371, 0.7489374) |
| 9 | (0.2604907, 0.2604910) | (0.7558001, 0.7558004) |
| 10 | (0.2604921, 0.2604924) | (0.7602937, 0.7602940) |
| 11 | (0.2604924, 0.2604927) | (0.7633845, 0.7633848) |
| 12 | (0.2604925, 0.2604928) | (0.7655967, 0.7655970) |

The new checker also **isolates the distinguished \(p=13,14,15,16\)
roots** by inverting the normalized \(\tau\)-chart before bisecting
\(P_p=x_{6p}+x_{3p}\). It explicitly rejects the attractive but
*wrong* shortcut of bisecting a broad \(P_p\) bracket: that bracket
can include other, incorrectly kneaded roots. It then checks the
full-hull derivative, entire signed itinerary, fixed-point bracket,
whole-gate-disk margin and both strict width intervals. The
new results snapshot records the four additional numerical rows.

The four newly certified strict enclosures are:

| \(p\) | \(W_p^{\rm rad}\) strict enclosure (lower witness) | \(Q(L_+)\) strict enclosure (upper envelope) |
|---:|---:|---:|
| 13 | (0.2604925, 0.2604928) | (0.7672322, 0.7672325) |
| 14 | (0.2604925, 0.2604928) | (0.7684743, 0.7684746) |
| 15 | (0.2604925, 0.2604928) | (0.7694393, 0.7694396) |
| 16 | (0.2604925, 0.2604928) | (0.7702036, 0.7702039) |

For **each** finite row, let \(\ell_p\) be the displayed
radial lower endpoint and \(u_p^{\rm env}\) the displayed
full-path upper endpoint. The proved statement is
\(\ell_p<W_p^{\rm rad}\le W_p^*\le Q(L_+)<u_p^{\rm env}\).
Neither auxiliary interval by itself encloses the canonical
width; in particular the upper endpoint is **not** an attained
Wave width.


For all \(p\ge13\), the old all-period normalized-orbit theorem gives,
with \(q=4^{-p}\), \(\tau_*\) the distinguished limiting root,
and \(u_j=(w\mapsto w^2+\tau_*)^j(0)\),
\[
\begin{split}
|\tau_p-\tau_*|&\le 15246q,\\
|(-A_p)x_{jp}-(-u_j)|&\le
 \bigl(30\cdot15246+88(4^j-1)/3\bigr)q,\quad j=2,3,5,\\
|(-A_p)x_p-(-u_1)|&\le15246q.
\end{split}
\tag{5.3}
\]
Here \(-A_p>0\), so this is a *positive* affine normalization.
[verify.py](verify.py) uses (5.3), a fresh root isolation for
\(\tau_*\), and outward rational elementary-function/elliptic
series to form explicit interval functions \(H_p\) with
\(Q_{\rm plane,p}\le H_p\) for **every** \(p\ge13\).
At and beyond \(p=17\), all coordinate uncertainty intervals
are contained in the \(p=17\) interval box; interval inclusion
then supplies a *single* certified strict upper enclosure
\(H_{17}<0.7750748<0.78\), with
\(H_{17}\in(0.7747715,0.7750748)\).
The round lower error from the prior audit is
\[
 W_p^* \ge W_p^{\rm rad}
 >0.2604925-7{,}000{,}000\,4^{-p}
 \quad(p\ge13).
\tag{5.4}
\]
That lower expression already exceeds \(0.26\) for \(p\ge17\).
**Do not claim it exceeds \(0.26\) for \(13\le p\le16\)**:
those periods need the separate exact bisections above.
Combining (5.1)–(5.4), every period \(p\ge13\) has an
explicitly certified pair of bounds: the individual rows above
give the strict bounds for \(13\le p\le16\), while for **all**
\(p\ge17\) the rational formulas imply
\[
 0.2604925-7{,}000{,}000\cdot4^{-p}
 <W_p^*<0.7750748.
\]
In particular the first four high periods and the universal tail yield
\[
 0.26<W_p^*<0.78\qquad(p\ge13).
\tag{5.5}
\]

As \(p\to\infty\) the normalized cuts converge to the model cuts
in (5.3). The plane-slit elliptic expression is continuous
at those strict-separated endpoints, and the prior exact
model calculation certifies
\[
 W_\infty^{\rm rad}\in(0.2604925,0.2604928),
 \qquad Q_\infty\in(0.7749230,0.7749233).
\]
Consequently, **without assuming convergence of the maximal Wave**,
\[
\boxed{0.26<\liminf_{p\to\infty}W_p^*
       \le\limsup_{p\to\infty}W_p^*<0.78.}
\tag{5.6}
\]
The same inequalities hold for \(W_{p,2}^*\) under M. None of
these wide brackets is a certified numerical value of a
canonical limiting width.

## 6. What would prove convergence (and what has not been proved)

Let \(W_\infty^*\) be the **separately defined** supremal A.1
Wave width on the normalized limiting marked plane slit.
A sufficient *non-circular* missing theorem would establish a
compactness/continuity principle for the **constrained** marked
Wave classes under the positive affine normalization:
(i) every admissible limiting Wave can be approximated by
finite-\(p\) admissible Waves of asymptotically no smaller
conformal width (recovery/liminf), and
(ii) any sequence of finite-\(p\) near-maximizing admissible
Waves has a subsequence, after accounting for possible escape
towards the expanding outer boundary, whose limiting
lamination is admissible and whose width is no smaller than
the corresponding limsup (upper semicontinuity).
These two statements imply
\(\lim W_p^*=W_\infty^*\). For the **two-child** quantity,
they additionally need stability of the *immersion restriction*
and its proper-block filter. Alternatively, one could prove
that the full lifted-path extremal quadrilateral admits an
attaining **embedded projected A.1 lamination** with the
required base/crest for every \(p\); this would force
\(W_p^*=Q_p\), but is **not** asserted here.
Convergence of \(W_p^{\rm rad}\) and \(Q_p\) alone does **not**
imply convergence of \(W_p^*\): their limiting values differ.

**Hostile-review limits.** (a) The width of a chosen radial
collar is only a *lower witness*, never automatically maximal.
(b) The full family in the universal cover cannot be equated
to a family on the physical annulus; inequality (4.4) requires
the explicit square-sum pushdown. (c) A.3.2 cannot retroactively
exclude an A.1 parent, and \(f_*\ne\iota^*\).
(d) Source spans \(3,3,7\), pushed spans \(3,3,5\), and
the distinct \(P\) blocks are checked separately.
(e) The limiting \(\tau_*\) is *not* the physical \(c_3\).
(f) Numerical interval programs do not certify the imported
prime-end/Hubbard-tree identification or a new theorem about
extremal length. No counterexample leaf to either inclusion
exists **within the specified marked slit interpretation**;
the homotopy lifting and lower construction prove the
inclusions in that setting. Nothing here rules out a
counterexample if a different, unverified physical marking
were substituted.

## 7. Reproduce

From repository root:

```sh
python research/independent_audits/real_primitive_tip_family_canonical_width_sandwich_20261116/verify.py
python -m unittest discover -s research/independent_audits/real_primitive_tip_family_canonical_width_sandwich_20261116 -p 'test_*.py' -v
```

The **dedicated** workflow
[real-primitive-tip-canonical-width-sandwich.yml](../../../.github/workflows/real-primitive-tip-canonical-width-sandwich.yml)
also runs the existing Research validation Python audit and the
unchanged Lean kernel build, even though those workflows' own
path filters would not necessarily fire on this new directory.
This verifier uses only exact fractions, outward fixed-grid
\(2^{-512}\) intervals, and the prior audited elementary-series
implementation, not floating-point premises; it never alters
the previous audit or native-wave generator. Its stored result
is checked by default; `--write` is required to intentionally
regenerate that **new-only** snapshot.
