# Dense terminal obstacles and the submulticurve replacement

## 1. Result and status boundary

The strong terminal-collar route has a structural obstruction.  This
note proves

```text
TERMINAL_LC_NATIVE_HUBBARD_CARRIER_PROPER
TERMINAL_FORWARD_INVARIANT_CARRIER_DENSE_OBSTACLE_NO_GO
TERMINAL_KL_SUBMULTICURVE_OVERFLOW_TRANSFER
```

The first theorem says that, unless the native forward-invariant
carrier already equals the whole filled Julia continuum, the relative
obstacle \(K\setminus T\) accumulates on **every** inner ideal interval
of the carrier complement.  Thus the proposed positive obligation
`TERMINAL_DYNAMICAL_ACCESS_NONACCUMULATION` cannot be the universal
terminal gate.

The second theorem gives the source-faithful replacement at the level
actually needed for a width estimate: a physical curve connecting two
KL exterior components contains a horizontal KL submulticurve with the
correct tagged pseudo-piece accesses, and the corresponding KL family
has at least the physical conformal width.

None of these results identifies an original KKL Wave endpoint with one
particular KL prime end.  Exact carrier-pair naturality still requires
that stronger datum.  In particular,
`TERMINAL_TAGGED_ENDPOINT_ACCESS_MATCH`,
`WAVE_TO_KL_ADDRESS_ACCESS_SELECTOR`, VAAPC-I, UPTCR, and MLC remain
open.

## 2. Source lock and exact hypotheses

The source files used below are:

1. KKL, `waves-with-Misha.tex`, SHA-256
   `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`.
   Lines 497--501 define the nondividing fixed point \(\beta_F\), with
   \(K\setminus\{\beta_F\}\) connected.  Lines 514--520 define, in the
   locally connected case, the smallest
   connected carrier \(T\subset K\) containing the complete small-Julia
   cycle and state explicitly that it is compact and forward invariant.
   Lines 542--543 pass to the rational-lamination model and lift the
   corresponding objects when \(K\) is not locally connected.

2. Kahn--Lyubich, `psiql.tex`, SHA-256
   `6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF`.
   Lines 95--161 construct the pseudo-piece \(\Psi(Y)\); lines 231--244
   define its tile-tagged \(J\)-boundary accesses
   \(\partial^v\Psi(Y)\); lines 256--260 define ordered finite
   multicurves; and Lemma `lifts`, lines 270--275, extracts a
   horizontal lifted submulticurve from every physical curve connecting
   \(S_Y^v\) to \(S_Y^w\).

3. Kahn--Lyubich, `appendix.tex`, SHA-256
   `05A13ED2D46CB9E2D188E6D96F4A2B639626F99657723118B4DE3479CD980916`.
   Lines 10--15 define extremal length \(\mathcal L\) and width
   \(\mathcal W=\mathcal L^{-1}\).  Corollary `two families`, lines
   38--45, gives the precise lifting/overflow inequality used below.

4. Douady--Hubbard, *On the dynamics of polynomial-like mappings*,
   Ann. Sci. ENS 18 (1985), Chapter I, Sections 1--2.  The
   straightening theorem is Theorem 1; the external construction in
   Section 2 associates to a connected degree-\(d\) polynomial-like
   map a real-analytic strongly expanding degree-\(d\) circle map.
   Equivalently, the induced inner prime-end dynamics is topologically
   conjugate to \(m_d(t)=dt\pmod 1\).

The first theorem uses the following exact analytic data.

- \(g:U'\to U\) is a degree-\(d\), \(d\ge2\), polynomial-like map with
  connected filled Julia set \(K\).
- \(\operatorname{int}K=\varnothing\).
- \(T\subset K\) is a nondegenerate compact connected continuum and is
  forward invariant:
  \(g(T)\subset T\).
- \(K\Subset\Omega\) for a bounded Jordan domain \(\Omega\),
  and
  \[
   A=\Omega\setminus K,\qquad M=\Omega\setminus T.
  \tag{2.1}
  \]
- \(p_T:\widetilde M\to M\) is the universal cover and
  \[
   \widetilde A=p_T^{-1}(A),\qquad
   \mathscr F_{\rm rel}=p_T^{-1}(K\setminus T).
  \tag{2.2}
  \]

By `TERMINAL_RELATIVE_COVER_SUBGROUP_ALIGNMENT`,
\(\widetilde A\) is the connected universal cover of \(A\).
For the KKL application, Kahn's induced quadratic-like restriction
(KKL lines 451--457) has the same filled continuum \(K\) and agrees
with the \(\psi\)-quadratic-like dynamics on \(K\).  Hence KKL's
forward invariance \(F(T)\subset T\) gives the analytic hypothesis
\(g(T)\subset T\) used below.

### Proposition 2.1
(`TERMINAL_LC_NATIVE_HUBBARD_CARRIER_PROPER`)

In KKL's locally connected native category, the Hubbard carrier of a
primitive renormalization satisfies
\[
 T\subsetneq K.
\tag{2.3}
\]

#### Proof

Write the primitive cycle as
\[
 \mathcal K=\bigcup_{j=0}^{p-1}K_j,
 \qquad p>1,
\tag{2.4}
\]
with the \(K_j\) pairwise disjoint and \(F(K_j)=K_{j+1}\), indices
modulo \(p\).  KKL line 499 supplies the fixed point \(\beta_F\) for
which \(K\setminus\{\beta_F\}\) is connected.

The point \(\beta_F\) lies in no \(K_j\).  Indeed, if
\(\beta_F\in K_j\), then fixedness and
\(F(K_j)=K_{j+1}\) imply
\(\beta_F\in K_{j+1}\); iteration places \(\beta_F\) in every
\(K_i\), contradicting pairwise disjointness and \(p>1\).
Consequently \(K\setminus\{\beta_F\}\) is a connected set containing
the complete cycle \(\mathcal K\).  By KKL's inclusion-minimal
definition of \(T\),
\[
 T\subset K\setminus\{\beta_F\}.
\tag{2.5}
\]
Thus \(\beta_F\in K\setminus T\), proving (2.3).

This proves the stated locally connected theorem. \(\square\)

For a non-locally-connected \(K\), KKL lines 542--543 say only that
the combinatorial Hubbard objects are lifted by the rational-lamination
projection.  The locked sentence does not spell out whether the
physical carrier equals \(\pi^{-1}(T_{\rm com})\), nor whether the
fiber of \(\beta_F\) is excluded.  The corresponding physical
properness statement is therefore retained separately as

```text
TERMINAL_NONLC_HUBBARD_CARRIER_PROPER
```

and remains open pending that exact source-level identification.  This
does not weaken the no-go for the universal collar proposal: the
locally connected native subcategory already supplies proper terminal
carriers to which Theorem 4.2 applies.

## 3. No open external arc can be supported on a proper invariant carrier

Let \(\mathbb S_K\) denote the inner prime-end circle of the complement
of \(K\), canonically identified with the external prime-end circle of
\(\widehat{\mathbb C}\setminus K\) by restricting crosscut chains to a
common annular neighborhood of \(K\).  Let
\[
 \sigma_g:\mathbb S_K\longrightarrow\mathbb S_K
 \tag{3.1}
\]
be the external prime-end map induced by \(g\).
For \(\mathfrak p\in\mathbb S_K\), write
\(\operatorname{Imp}_K(\mathfrak p)\) for its impression in \(K\).

### Lemma 3.1 -- exact external expansion

The map \(\sigma_g\) is topologically conjugate to
\[
 m_d:\mathbb R/\mathbb Z\longrightarrow\mathbb R/\mathbb Z,
 \qquad m_d(t)=dt\pmod 1.
 \tag{3.2}
\]
Consequently, for every nonempty open arc \(J\subset\mathbb S_K\)
there is \(N\ge0\) such that
\[
 \sigma_g^N(J)=\mathbb S_K.
 \tag{3.3}
\]

#### Proof

Use the global quasiconformal straightening construction to straighten
\(g\) to a degree-\(d\) polynomial \(P\).  The straightening
homeomorphism conjugates the maps on a full neighborhood of \(K\) and
therefore carries crosscut chains near \(K\) to crosscut chains near
\(K(P)\).  It induces a conjugacy of the inner prime-end circles.  The
Bottcher coordinate of \(P\) conjugates its external prime-end map to
\(m_d\).  This proves (3.2).  Equivalently, one may use directly
Douady--Hubbard's strongly expanding external circle map and its
standard conjugacy to \(m_d\); degree alone would not be sufficient.

For completeness, if an arc in \(\mathbb R/\mathbb Z\) has a lift of
length \(\ell>0\), then a lift of its \(N\)-th image has length
\(d^N\ell\).  Choose \(N\) with \(d^N\ell>1\).  Its projection is the
whole circle.  Conjugating back gives (3.3). \(\square\)

### Lemma 3.2 -- covariance of impressions

For every \(\mathfrak p\in\mathbb S_K\),
\[
 g\bigl(\operatorname{Imp}_K(\mathfrak p)\bigr)
 =
 \operatorname{Imp}_K\bigl(\sigma_g(\mathfrak p)\bigr).
 \tag{3.4}
\]

#### Proof

It is enough to prove the identity after straightening.  Let
\(\psi:\widehat{\mathbb C}\setminus K(P)\to
\widehat{\mathbb C}\setminus\overline{\mathbb D}\) be the Bottcher
coordinate, so
\[
 \psi(P(z))=\psi(z)^d.
\tag{3.5}
\]
Let \(\zeta=e^{2\pi i\theta}\).  If
\(x\in\operatorname{Imp}(\zeta)\), choose an arbitrary defining
sequence \(u_n\to\zeta\) in the exterior disk with
\(\psi^{-1}(u_n)\to x\).  Equation (3.5) and continuity give
\[
 P(x)\in\operatorname{Imp}(\zeta^d).
\tag{3.6}
\]

Conversely, let \(y\in\operatorname{Imp}(\zeta^d)\).  Choose an
arbitrary defining sequence \(w_n\to\zeta^d\) with
\(\psi^{-1}(w_n)\to y\).  On a sufficiently small sector at
\(\zeta^d\), take the branch of the \(d\)-th root for which
\[
 u_n^d=w_n,\qquad u_n\to\zeta.
\tag{3.7}
\]
After passing to a subsequence,
\(\psi^{-1}(u_n)\) converges to some
\(x\in\operatorname{Imp}(\zeta)\).  Equation (3.5) gives \(P(x)=y\).
Thus both inclusions hold for full prime-end impressions, not merely
radial cluster sets.  Transport by the straightening homeomorphism
proves (3.4). \(\square\)

### Lemma 3.3 -- invariant-impression arc no-go

Define
\[
 \mathcal P(T)
 =
 \left\{
  \mathfrak p\in\mathbb S_K:
  \operatorname{Imp}_K(\mathfrak p)\subset T
 \right\}.
 \tag{3.5}
\]
If \(\mathcal P(T)\) contains a nonempty open arc, then \(T=K\).

#### Proof

Forward invariance of \(T\) and (3.4) imply
\[
 \sigma_g(\mathcal P(T))\subset\mathcal P(T).
 \tag{3.6}
\]
If \(J\subset\mathcal P(T)\) is a nonempty open arc, Lemma 3.1 gives
\[
 \mathbb S_K=\sigma_g^N(J)\subset\mathcal P(T)
 \tag{3.7}
\]
for some \(N\).

Prime-end impressions cover every boundary component of a plane
domain.  Here is the direct verification needed in this setting.  For
any \(x\in\partial K\), choose
\(z_n\in\widehat{\mathbb C}\setminus K\) with \(z_n\to x\).  In the
external Riemann coordinate the radii tend to \(1\).  Pass to a
subsequence whose angular coordinates converge to some
\(\zeta\in\mathbb S^1\).  Then, by the defining cluster-set
description of the corresponding prime-end impression,
\(x\in\operatorname{Imp}_K(\zeta)\).  Thus
\[
 \partial K
 \subset
 \bigcup_{\mathfrak p\in\mathbb S_K}
 \operatorname{Imp}_K(\mathfrak p).
\tag{3.8}
\]
Equations (3.5) and (3.7)--(3.8) give
\(\partial K\subset T\).  Since \(\operatorname{int}K=\varnothing\),
\(K=\partial K\), so \(K\subset T\).  The reverse inclusion was assumed;
hence \(T=K\). \(\square\)

## 4. The lifted relative obstacle is dense at the entire inner boundary

Write
\[
 \mathscr F_{\rm rel}^{\rm PE}
 =
 \overline{\mathscr F_{\rm rel}}^{
   \,\overline{\widetilde M}^{\,\operatorname{PE}}}.
\tag{4.1}
\]
Write
\(\partial_{\rm in,fin}^{\rm PE}\widetilde M\cong\mathbb R\) for the
finite inner boundary line in a strip uniformization.  If the chosen
compactification also adjoins the two deck-limit corners \(c_-,c_+\),
they are treated separately below.

### Lemma 4.1 -- a protected native interval creates an external arc

Suppose a nondegenerate compact interval
\[
 I_0\Subset\partial_{\rm in,fin}^{\rm PE}\widetilde M
 \tag{4.2}
\]
satisfies
\[
 I_0\cap\mathscr F_{\rm rel}^{\rm PE}=\varnothing.
 \tag{4.3}
\]
Then \(\mathcal P(T)\) contains a nonempty open arc.

#### Proof

Use \(\widetilde{\mathscr F}=\mathscr F_{\rm rel}\) in
`TERMINAL_ACCESS_SURVIVAL_EQUIVALENCE`.  Condition (4.3) supplies a
one-sided native quadrilateral and a source prime-end arc
\[
 J_A\subset\partial_{\rm in}^{\rm PE}\widetilde A
 \tag{4.4}
\]
whose physical crosscut chains are the same chains in
\(\widetilde A\) and \(\widetilde M\).  The avoidance here is avoidance
of the **complete PE closure**, not merely physical disjointness.
Although that equivalence is stated inside a predeclared native
interval \(\widetilde I\), choose here any slightly larger local native
arc containing \(I_0\).  Its transfer proof is local and uses no
marking hypothesis beyond the existence of that inner ideal arc.

The annular covering extends in strip coordinates over every finite
inner-boundary interval.  Shrink the protected quadrilateral, if
necessary, so that its closure lies in one evenly covered boundary
chart.  It then projects injectively to a closed one-sided
quadrilateral in \(M\).  This projected quadrilateral is disjoint from
the PE closure of \(K\setminus T\): otherwise an obstacle sequence in
the projected chart would lift, eventually in the selected sheet, to
an obstacle sequence accumulating on the original lifted
quadrilateral.  The projected source arc is therefore a nonempty open
arc \(J\subset\mathbb S_K\).

Let \(\mathfrak p\in J\), and use one of the common crosscut chains
from the protected quadrilateral.  Its collar-side nested components
in \(A=M\setminus(K\setminus T)\) are contained in the corresponding
ambient caps.  Viewed in \(M\), their impression is contained in the
inner complementary continuum \(T\).  Viewed in \(A\), the same
physical crosscuts represent \(\mathfrak p\).  Therefore
\[
 \operatorname{Imp}_K(\mathfrak p)\subset T.
 \tag{4.5}
\]
Thus \(J\subset\mathcal P(T)\). \(\square\)

### Theorem 4.2
(`TERMINAL_FORWARD_INVARIANT_CARRIER_DENSE_OBSTACLE_NO_GO`)

If \(T\ne K\), then
\[
 \partial_{\rm in,fin}^{\rm PE}\widetilde M
 \subset
 \mathscr F_{\rm rel}^{\rm PE}.
 \tag{4.6}
\]
Equivalently, no nondegenerate compact inner ideal interval is
disjoint from the lifted relative-obstacle closure.

#### Proof

If (4.6) failed, the complement of the closed set
\(\mathscr F_{\rm rel}^{\rm PE}\) would contain a nonempty relatively
open inner-boundary arc, and hence a nondegenerate compact subinterval
\(I_0\) satisfying (4.3).  Lemma 4.1 would put a nonempty open arc in
\(\mathcal P(T)\).  Lemma 3.3 would then give \(T=K\), contrary to the
hypothesis. \(\square\)

If the strip compactification contains \(c_-\) and \(c_+\), they also
belong to \(\mathscr F_{\rm rel}^{\rm PE}\).  Indeed,
the hypothesis \(T\ne K\) supplies a point of \(K\setminus T\); the
positive and negative deck translates of any one of its lifts converge respectively
to the two deck-limit corners.  Thus (4.6), together with this
observation, saturates the entire compactified inner boundary.

### Corollary 4.3 -- exact failure of the strong gate

For every locally connected primitive terminal KKL Hubbard carrier,
Proposition 2.1 gives \(T\subsetneq K\).  Hence equation (5.2) of
`terminal_protected_access_reduction.md` fails for every nondegenerate
\(I_0\Subset I_{1\to0}\).  In fact there is no single obstacle-free
finite inner prime end.  Adding further obstacles cannot repair the
failure.

The analytic hypotheses of Theorem 4.2 apply because
`PQL_SAME_FILLED_CONTINUUM_QUADRATIC_LIKE_RESTRICTION` supplies a
quadratic-like map with the same \(K\) and carrier dynamics, while
`PERIODICALLY_REPELLING_PQL_FILLED_JULIA_EMPTY_INTERIOR` supplies
\(\operatorname{int}K=\varnothing\).

For the abstract theorem the only exceptional case is \(T=K\), when
\(K\setminus T=\varnothing\) and the relative obstacle vanishes.  The
locally connected native terminal primitive carrier is not in that
exceptional case.  The non-locally-connected properness coordinate is
the separate open item recorded after Proposition 2.1.

## 5. The source-faithful width replacement

Let \(Y\in\mathcal Y^m(l)\) be a KL geometric puzzle piece, let \(v,w\)
be distinct vertices of \(Y\), and let
\[
 \mathcal H_Y(v,w)
 \tag{5.1}
\]
be a nonempty family of physical curves in \(\mathbf U^l\) connecting
\(S_Y^v\) to \(S_Y^w\).  Let
\[
 \Gamma_Y(v,w)
 \tag{5.2}
\]
be KL's family of horizontal multicurves in \(\Psi(Y)\) connecting the
tagged accesses \(\partial^v\Psi(Y)\) and
\(\partial^w\Psi(Y)\).

For binder traceability, define the relation
\[
 \begin{split}
 \mathcal R_Y^{v,w}
 =
 \{(\gamma,\gamma^*,\gamma'):\;&
 \gamma\in\mathcal H_Y(v,w),\
 \gamma'\subset\gamma,\\
 &\gamma^*\in\Gamma_Y(v,w),\
 \pi_Y(\gamma^*)=\gamma'\}.
 \end{split}
 \tag{5.3}
\]
Here \(\gamma'\) and \(\gamma^*\) are ordered multicurves.  No arbitrary
choice is quotiented away: all witnesses remain in the fiber over
\(\gamma\).

### Lemma 5.0: ordered-multicurve overflow

For a finite ordered multicurve
\[
 c=\bigsqcup_{r=1}^q c_r
\]
and a conformal metric \(\rho\), define
\[
 \ell_\rho(c)=\sum_{r=1}^q\ell_\rho(c_r),
\tag{5.4a}
\]
and define \(\mathcal L\) by the usual extremal-length infimum and
supremum using this summed length.

Let \(f:X\to Z\) be a holomorphic immersion, let \(\mathcal G\) be a
family of finite ordered multicurves in \(X\), and let \(\mathcal H\)
be a family of curves in \(Z\).  Suppose every \(h\in\mathcal H\)
contains pairwise parameter-disjoint ordered subarcs whose union is
\(f(c_h)\) for some \(c_h\in\mathcal G\), with image-component
multiplicity retained.  Then
\[
 \mathcal L(\mathcal H)\ge\mathcal L(\mathcal G),
 \qquad
 \mathcal W(\mathcal H)\le\mathcal W(\mathcal G).
\tag{5.4b}
\]

#### Proof

First extend holomorphic monotonicity from curves to finite ordered
multicurves.  Given a finite-area conformal metric
\(\rho(z)|dz|\) on \(X\), define on \(Z\)
\[
 \sigma(w)^2
 =
 \sum_{z\in f^{-1}(w)}
 \frac{\rho(z)^2}{|f'(z)|^2}.
\tag{5.4c}
\]
The sum is allowed to be countable; Tonelli's theorem and change of
variables give
\[
 \operatorname{Area}_\sigma(Z)
 =
 \operatorname{Area}_\rho(X).
\tag{5.4d}
\]
For every component \(c_r\),
\[
 \ell_\sigma(f(c_r))\ge\ell_\rho(c_r),
\tag{5.4e}
\]
because the summand in (5.4c) belonging to the chosen lift already
gives that inequality pointwise.  Summing (5.4e) over the ordered
components proves
\[
 \mathcal L(f(\mathcal G))\ge\mathcal L(\mathcal G).
\tag{5.4f}
\]

Next let \(\tau\) be any finite-area conformal metric on \(Z\).
Pairwise parameter-disjointness of the selected subarcs gives, for
each \(h\),
\[
 \ell_\tau(h)
 \ge
 \ell_\tau(f(c_h))
 \ge
 \inf_{c\in\mathcal G}\ell_\tau(f(c)).
\tag{5.4g}
\]
Taking the infimum over \(h\), then the supremum over \(\tau\), gives
\(\mathcal L(\mathcal H)\ge\mathcal L(f(\mathcal G))\).  Combine this
with (5.4f), and invert, to obtain (5.4b). \(\square\)

### Theorem 5.1
(`TERMINAL_KL_SUBMULTICURVE_OVERFLOW_TRANSFER`)

Every fiber of the projection
\[
 \mathcal R_Y^{v,w}\longrightarrow\mathcal H_Y(v,w)
 \tag{5.4}
\]
is nonempty.  Moreover,
\[
 \mathcal L\bigl(\mathcal H_Y(v,w)\bigr)
 \ge
 \mathcal L\bigl(\Gamma_Y(v,w)\bigr),
 \tag{5.5}
\]
or, equivalently,
\[
 \mathcal W\bigl(\mathcal H_Y(v,w)\bigr)
 \le
 \mathcal W\bigl(\Gamma_Y(v,w)\bigr).
 \tag{5.6}
\]
Every witness \(\gamma^*\) ends on the actual tile-tagged KL boundary
\[
 \partial^v\Psi(Y)=\eta_i\cup\xi_{i+1}
 \tag{5.7}
\]
and the analogous boundary at \(w\).

#### Proof

KL Lemma `lifts` says exactly that each
\(\gamma\in\mathcal H_Y(v,w)\) contains an ordered multicurve
\(\gamma'\) lifting to some
\(\gamma^*\in\Gamma_Y(v,w)\).  This proves the nonemptiness in (5.4)
and the endpoint statement (5.7).

KL's phrase “contains a multicurve” means precisely that its ordered
components occupy pairwise disjoint parameter subintervals of the
original curve.  Apply Lemma 5.0 with
\(\mathcal H=\mathcal H_Y(v,w)\),
\(\mathcal G=\Gamma_Y(v,w)\), and \(f=\pi_Y\).
It gives (5.5).  Since
\(\mathcal W=\mathcal L^{-1}\), inversion gives (5.6). \(\square\)

### Corollary 5.2 -- binder-aware conditional terminal transfer

Let \(\mathcal B\) be an actual KKL proof-use binder family.  Suppose
one proves, for every bound leaf occurrence \(\delta\), an ordered
physical component record
\[
 \operatorname{CompEnd}(\delta)
 =
 (Y(\delta),v(\delta),w(\delta))
 \tag{5.9}
\]
and a physical representative in
\(\mathcal H_{Y(\delta)}(v(\delta),w(\delta))\), with the conformal
family and its multiplicity unchanged.  Then (5.3) gives a
provenance-preserving KL submulticurve relation for every binder
occurrence, and (5.6) transfers every lower bound on the physical width
to the corresponding KL horizontal family.

If \(v(\delta)=v_*\), the lifted endpoint is in
\(\partial^{v_*}\Psi(Y)\) by construction; no claim that the **original
KKL endpoint** equals that KL prime end is made or needed for (5.6).

### Proposition 5.3 -- exact conditional Wave-width chain

Let \(S_0\) be a KKL Wave sublamination and let \(\mathcal H\) be a
complete binder-declared proper restriction family which is an
admissible lamination in the restriction surface and such that:

1. every leaf of \(S_0\) has in its immersion restriction a member of
   \(\mathcal H\);
2. every \(h\in\mathcal H\) is a physical curve connecting the same
   pair \(S_Y^v,S_Y^w\); and
3. all occurrences and multiplicities in the restriction are retained.

For any assignment \(\sigma\) choosing one witness in the nonempty
fiber (5.4) for every \(h\), let
\(\widehat{\mathcal H}_\sigma\subset\Gamma_Y(v,w)\) be the resulting
family of ordered lifted multicurves.  Then
\[
 \mathcal W(S_0)
 \le
 \mathcal W(\mathcal H)
 \le
 \mathcal W(\widehat{\mathcal H}_\sigma)
 \le
 \mathcal W(\Gamma_Y(v,w))
 =
 \operatorname{Bd}_Y(v,w)^{-1}.
\tag{5.10}
\]
There is no degree factor, additive charge, or collar constant.

#### Proof

The first inequality is KKL Lemma `domination`, with one source
restriction lamination.  The second is Lemma 5.0, applied to the chosen
ordered-multicurve witnesses.  The third is monotonicity under
\(\widehat{\mathcal H}_\sigma\subset\Gamma_Y(v,w)\).  The final equality
is KL's definition
\(\operatorname{Bd}_Y(v,w)=\mathcal L(\Gamma_Y(v,w))\).
Each step has constant one, which is attained when the restriction and
lift are conformal copies of one tile family. \(\square\)

If, in addition,
\[
 \mathcal W(S_0)\ge\theta\,\mathcal W(S)-E
 \qquad(\theta>0,\ E\ge0),
\tag{5.11}
\]
then (5.10) gives the explicit response
\[
 \mathcal W(S)
 \le
 \theta^{-1}
 \left(\operatorname{Bd}_Y(v,w)^{-1}+E\right).
\tag{5.12}
\]

## 6. Exact replacement obligations

The next positive gate is no longer an empty-collar statement.  It is:

```text
TERMINAL_WAVE_KL_CONNECTING_SUBFAMILY
```

For every actual proof-use leaf occurrence, construct (5.9) from its
native KKL side, itinerary, and terminal puzzle package; prove that the
physical representative connects the stated \(S_Y\)-components; and
retain occurrence multiplicity and order.  The terminal anchor already
selects \(v_*\) set-theoretically for the \(K_1\) component, but the
other end, non-locally-connected endpoint realization, and complete
binder substitution remain to be proved.

There is a further source-level type check.  KKL lines 1874--1875
distinguish a Wave's **ends** from its **crest**.  Saying that a Wave
crests over \(I_{1\to0}\) does not say that any leaf ends there.
Therefore the binder theorem must prove one of the following, without
interchanging them:

1. \(I_{1\to0}\) is an actual proof-used end of the selected
   sublamination; or
2. every retained leaf contains a physical subcurve ending in
   \(S_Y^{v_*}\), with the complete-restriction width inequality of
   Proposition 5.3.

Appending an auxiliary connector to a leaf would not prove the
overflow hypothesis and is forbidden.

The native stationary branch now has one additional proved datum:
`KKL_STATIONARY_TWO_PULLBACK_PASS_THROUGH` says that every retained
occurrence in \(A_{N-1}\) passes through \(K_0^b\) and
\(K_0^{b+1}\) in KKL's successive-pullback sense.  The canonical
filled-set graph theorem now identifies their distinct final components.
It does not prove one final retained occurrence is incident to both, or
their order.  Moreover both final graph restrictions have degree two,
not the degree one printed in KKL.  The exact intermediate gates are

```text
KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION
KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT
KKL_STATIONARY_NESTED_INCIDENCE_ORDER
KKL_STATIONARY_FIXED_PAIR_PROPER_RESTRICTION
TERMINAL_STATIONARY_RESTRICTION_KL_PUZZLE_SELECTOR
```

The pass-through and graph/degree statements are proved, while the listed
gates are delimited and remain open, in
`kkl_stationary_wave_component_incidence.md`.

For the crest-compatible width route, a fixed endpoint pair is still not
enough.  One must also construct

```text
TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER
```

with a fixed separating piece and a componentwise skip witness.  The
conditional coefficient-one transfer and the adjacent-tile obstruction
are proved in `terminal_wave_crest_to_kl_skipping_bridge.md`.

Once that gate is closed, the proved relation (5.3), rather than a
single independently chosen endpoint lift, is the canonical width
selector:

```text
TERMINAL_KL_SUBMULTICURVE_BINDER_SELECTOR
```

Exact carrier-pair naturality may still require
`TERMINAL_TAGGED_ENDPOINT_ACCESS_MATCH`; the width-only branch does
not.  The ledger must keep those two uses separate.

## 7. Skeptic audit

1. **Density in \(K\) was not silently promoted to side density.**
   The proof uses external-map exactness and impression covariance to
   obtain every side, not mere Euclidean density.

2. **Sections 3--5 do not use local connectivity.**  Prime-end
   impressions replace landing points there.  Proposition 2.1 is
   explicitly LC-only, and non-LC physical-carrier properness remains
   open.

3. **A general degree-\(d\) circle covering was not assumed exact.**
   Exactness comes from the polynomial-like external conjugacy to
   \(m_d\), not from degree alone.

4. **Empty interior is used exactly once.**  It converts
   \(\partial K\subset T\) into \(K\subset T\) in Lemma 3.3.

5. **The universal-cover projection is only local at the boundary.**
   Lemma 4.1 shrinks to a subarc before quotienting; it does not assert
   a global prime-end extension of the inclusion.

6. **The no-go has an explicit exceptional case.**  It does not claim
   obstacle density when \(T=K\).

7. **The KL theorem selects a submulticurve, not the original
   endpoint.**  This distinction is the reason (5.6) survives while
   exact endpoint naturality remains open.

8. **No numerical result or model promotes an analytic claim.**  Both
   the no-go and width transfer are analytic deductions from the stated
   hypotheses and locked source theorems.
