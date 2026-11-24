# Every maximal native annular restriction has ideal endpoints

Date: 2026-11-23  
Status: proved for the stated full, connected, forward-invariant
carrier package and hyperbolic disk domains. Native marking, sequential
retention, and the existence and pairing of the required canonical
occurrences remain separate. No stationary N2 or MLC conclusion is claimed.

AI disclosure: GPT-6 Astra Pro was used for proof search, source comparison,
and drafting. Independent review is by collaborating AI agents; no new
human mathematical verification is represented.

## 1. Result and exact setting

Let \(F=(f,\iota)\) be a pseudo-quadratic-like map with connected filled
set \(K\), hyperbolic conformal disk domains, and actual finite iterates

\[
 P_h=f^h:U^h\longrightarrow U,\qquad
 I_h=\iota_h:U^h\longrightarrow U.
 \tag{1.1}
\]

Assume an actual carrier \(T\Subset U\) is a nondegenerate full
continuum satisfying

\[
 c\in T\subset K,\qquad F(T)\subset T,
 \tag{1.2}
\]

where \(c\) is the physical critical point. Define

\[
 T_h=P_h^{-1}(T),\qquad
 X=U\setminus T,\qquad X_h=U^h\setminus T_h.
 \tag{1.3}
\]

The result is:

> Both \(X\) and \(X_h\) are genuine finite-modulus annuli.
> The immersion \(I_h\) maps all of \(X_h\) into \(X\).
> For every proper target path in \(X\), every maximal parameterized
> immersion lift in \(X_h\) has a single ideal endpoint at both ends
> of its maximal lifetime interval.

For a simple parent, these lifts are the actual simple maximal proper
restriction components. This includes lifetimes ending at the original
parent ideal endpoints, as well as lifetimes ending at an interior
parent time. No local connectivity or physical Jordan-boundary
assumption is imposed on \(T\) or \(T_h\).

The assertion concerns the full pulled carrier \(P_h^{-1}(T)\).
Replacing it by the disconnected small-Julia cycle would give a
different, generally multiply connected surface.

## 2. Source inputs

The finite disk domains are supplied by Kahn,
[*A priori bounds for some infinitely renormalizable quadratics:
I. Bounded primitive combinatorics*, arXiv:math/0609045v3](https://arxiv.org/abs/math/0609045v3),
Definition 7.1, the paragraph preceding Lemma 7.11, and Lemma 7.11.
The latter construction iterates the connected disk pullback.
The repository source alignment is
[Kahn iterate complementary-component alignment](../../mlc_unified/kahn_iterate_complementary_component_alignment.md).

The full filled-set identities are proved in
[PQL iterate filled-graph naturality, Lemma 3.1](../../mlc_unified/pql_iterate_filled_graph_naturality.md):

\[
 I_h^{-1}(K)=P_h^{-1}(K)=K^h,\qquad
 I_h|_{K^h}:K^h\longrightarrow K\text{ is a homeomorphism},
 \qquad P_h=F^h\circ I_h\text{ on }K^h.
 \tag{2.1}
\]

The critical-value calculation in
[MONODROMY_COLLISION.md, Lemma 3.1](MONODROMY_COLLISION.md) gives

\[
 \operatorname{CV}(P_h)
 \subset\{F(c),F^2(c),\ldots,F^h(c)\}.
 \tag{2.2}
\]

The full inverse-filled-set axiom is essential to that calculation;
local injectivity near the filled set alone would not suffice.
By (1.2), every value in (2.2) lies in \(T\).

The analytic endpoint inputs are the classical Fatou and F. and M.
Riesz theorems, in the forms stated as Theorems A and B on p. 1147 of
A. Danielyan,
[*The radial limits and boundary uniqueness*, Comptes Rendus
Mathématique 362 (2024), 1147--1153](https://doi.org/10.5802/crmath.609).
Theorem A explicitly supplies non-tangential limits almost everywhere.
Section 4 below explains their local use at an annular circle.

## 3. The pulled carrier is one full continuum

### Lemma 3.1 — complete pullback of a full critical-value carrier

Let \(P:S\to U\) be a proper holomorphic map of degree \(d\) between
hyperbolic conformal disks. Let \(T\Subset U\) be a nondegenerate full
continuum containing every critical value of \(P\). Then
\(P^{-1}(T)\) is a nondegenerate full continuum compactly contained
in \(S\).

#### Proof

Work in disk coordinates. A proper degree-\(d\) map between disks has
total critical multiplicity \(d-1\), by the disk Riemann--Hurwitz
formula. Equivalently, after uniformization it is a finite Blaschke
product of degree \(d\), giving the same count.

Choose nested analytic Jordan disks \(V_n\Subset U\) with

\[
 T\subset V_{n+1}\Subset V_n,\qquad
 \bigcap_n\overline{V_n}=T.
 \tag{3.1}
\]

Such a basis exists for every full continuum, using level curves
of its exterior Riemann map. All critical values belong to \(T\),
so every boundary \(\partial V_n\) avoids them.

Each component \(W_j\) of \(P^{-1}(V_n)\) is a disk. To see this
without assuming its topology, take any Jordan curve
\(\gamma\subset W_j\). Its bounded interior \(D_\gamma\) lies in
the source disk \(S\). For \(w\in U\setminus V_n\), the winding
number of \(P(\gamma)\) about \(w\) is zero, since the entire
image curve lies in the simply connected disk \(V_n\).
The argument principle gives no solution of \(P(z)=w\) in
\(D_\gamma\). Thus \(P(D_\gamma)\subset V_n\), and connectedness
places \(D_\gamma\) in \(W_j\). Every such Jordan curve fills in
its component, proving simple connectivity.

Properness gives finitely many components, each mapping properly
onto \(V_n\). Since the target boundary avoids critical values,
their compact boundaries are analytic. The simply connected
components are therefore Jordan disks. Write their degrees as
\(d_1,\ldots,d_k\), so that \(\sum_j d_j=d\).

Every critical point of \(P\) lies in \(P^{-1}(T)\), hence in
\(P^{-1}(V_n)\). Applying Riemann--Hurwitz to the component disks
therefore gives

\[
 d-1=\sum_{j=1}^k(d_j-1)=d-k.
 \tag{3.2}
\]

It follows that \(k=1\). Thus every full pullback \(P^{-1}(V_n)\)
is one disk, and its closure is one closed Jordan disk.

Their nested compact intersection is exactly \(P^{-1}(T)\).
It is connected and full: the complements of the nested closed
Jordan disks form an increasing union of connected complements.
Properness makes the intersection compactly contained in \(S\).
Finally \(P(P^{-1}(T))=T\), so the pullback cannot be a singleton
when \(T\) is nondegenerate. \(\square\)

### Corollary 3.2 — the actual two annuli and immersion

Under (1.1)--(1.3), \(T_h\) is a nondegenerate full continuum, and
\(X\), \(X_h\) are conformally equivalent to round annuli

\[
 A=\{r<|z|<1\},\qquad
 A_h=\{r_h<|z|<1\},\qquad 0<r,r_h<1.
 \tag{3.3}
\]

Moreover \(P_h:X_h\to X\) is an unbranched degree-\(2^h\) cover,
and \(I_h:X_h\to X\) is a holomorphic immersion.

#### Proof

Apply Lemma 3.1 using (2.2). The complements are doubly connected
domains with two nondegenerate complementary components, so annulus
uniformization gives (3.3). The compact inner continua are disjoint
from the outer ends. Removing \(T\) and its full preimage removes
all branching and retains the full covering degree.

For the immersion, let \(z\in I_h^{-1}(T)\). Since \(T\subset K\),
(2.1) gives \(z\in K^h\), and then

\[
 P_h(z)=F^h(I_h(z))\in F^h(T)\subset T.
 \tag{3.4}
\]

Thus

\[
 I_h^{-1}(T)\subset P_h^{-1}(T)=T_h.
 \tag{3.5}
\]

Taking complements proves that \(I_h\) maps all of \(X_h\) into
\(X\). No equality in (3.5) is claimed: added source carrier
pieces may map to target interior. \(\square\)

## 4. A bounded annular map detects a single boundary limit

### Lemma 4.1

Let \(A'=\{\rho<|z|<1\}\), where \(0<\rho<1\), and let
\(H:A'\to\mathbb C\) be bounded, holomorphic, and nonconstant.
Suppose a continuous curve \(z:[0,1)\to A'\) escapes every compact
subset of \(A'\) and \(H(z(t))\) has a finite limit as \(t\to1\).
Then \(z(t)\) converges to one point of one boundary circle.

#### Proof

The cluster set of \(z(t)\) in the compact closed annulus is a
nonempty connected compact set: it is the nested intersection
of closures of connected tails. Escape places it on the union
of the two disjoint boundary circles, hence on just one of them.
The radial coordinate therefore tends to either \(\rho\) or \(1\).

Suppose the angular limit is not a single point. On a late tail
choose a continuous real argument \(\theta(t)\).
If that argument is bounded and fails to converge, every angle
in a nonempty interval between its liminf and limsup is crossed
arbitrarily late. If it is unbounded on every late tail,
continuity gives arbitrarily late crossings of
\(\theta+2\pi k\) for every fixed angle \(\theta\), along a
suitable sequence of integers \(k\). Thus there is a boundary
arc of positive angular length such that at each angle on it
there are radial approach points \(z(t_n)\), \(t_n\to1\), and

\[
 H(z(t_n))\longrightarrow w
 \tag{4.1}
\]

for the stipulated common limit \(w\).

Fatou's almost-everywhere boundary-limit theorem holds locally
at either analytic annular circle. Explicitly, choose a small
Jordan lens inside the annulus whose boundary contains a
subarc of that circle. Its Riemann map extends conformally
across that analytic boundary subarc. Theorem A of the cited
Danielyan paper then gives non-tangential limits almost
everywhere on the subarc; annular radial approaches are
non-tangential in this chart. At those angles, (4.1) forces the
boundary value of \(H\) to equal \(w\).

The same analytic boundary chart preserves positive measure
on a compact subarc. Theorem B applied on that lens forces
\(H-w\) to vanish identically there, and the identity theorem
forces \(H\) to be constant on the annulus. This contradicts
the hypothesis. The boundary cluster set must therefore be a
singleton, proving convergence. \(\square\)

This is the annular counterpart of the disk argument in
[the exit-transfer note, Lemma 6.2](../maximal_exit_transfer_20261123/NOTE.md).
The positive-measure argument proves a statement about **every**
curve with the asserted image limit; no exceptional curve family
is discarded.

## 5. Every maximal lift of a proper path is proper

### Theorem 5.1 — maximal restriction properness

Let \(X'\) and \(X\) be finite-modulus annuli, and let
\(i:X'\to X\) be a holomorphic immersion. Let
\(\alpha:(0,1)\to X\) extend continuously to its two ideal
endpoints. Every maximal lift

\[
 \sigma:(a,b)\longrightarrow X',\qquad
 i\circ\sigma=\alpha|_{(a,b)},\qquad 0\le a<b\le1,
 \tag{5.1}
\]

converges to a single source ideal point at each end.

#### Proof

Consider the right endpoint \(b\). If \(b<1\) and
\(\sigma(t_n)\to x\in X'\) for a sequence \(t_n\uparrow b\),
then \(i(x)=\alpha(b)\). Choose a local inverse chart for \(i\)
at \(x\). A sufficiently late target segment, continuing beyond
\(b\), lies in the target chart. Its chart lift agrees with
\(\sigma\) by uniqueness and extends it past \(b\), contrary to
maximality.

If \(b=1\), a compact source accumulation would instead give an
interior target accumulation at \(i(x)\), contradicting the
specified proper ideal limit of \(\alpha\). Consequently
\(\sigma\) escapes every compact subset of \(X'\) in either
case.

Choose conformal annular coordinates
\(\phi:X\to A\) and \(\psi:X'\to A'\), and put

\[
 z(t)=\psi(\sigma(t)),\qquad
 H=\phi\circ i\circ\psi^{-1}.
 \tag{5.2}
\]

The function \(H\) is bounded and nonconstant. If \(b<1\),
its value along the lift converges to
\(\phi(\alpha(b))\in A\). If \(b=1\), it converges to the
specified target ideal endpoint on a round boundary circle.
Lemma 4.1 therefore gives a single boundary-circle limit of
\(z(t)\), which is the asserted source ideal endpoint.
The same argument at \(a\) proves the other endpoint.
\(\square\)

### Corollary 5.2 — native full-carrier restrictions

Under (1.1)--(1.3), every maximal lift of a proper parent path
under \(I_h:X_h\to X\) is ideal-proper in the **actual**
surface \(X_h=U^h\setminus P_h^{-1}(T)\).

If the parent is simple, every such lift is simple, because two
equal lift points would project to a repeated parent point.
The maximal lifted paths are then precisely the maximal
proper restriction components of the parameterized inverse
trace. No separate proper-landing assumption is needed for
an already existing local germ and its maximal continuation.

The theorem does not identify which of the two source ideal
circles receives an endpoint, or which physical point or
impression belongs to it. A contact germ already anchored
at a canonical filled-graph point retains that anchor by
local uniqueness, but the theorem does not construct such
a contact germ from combinatorial incidence.

## 6. Exact change to the occurrence obligations

For the displayed finite annular package, the former chain

\[
 \text{actual local lift germ}
 \ \longrightarrow\ \text{maximal continuation}
 \ \dashrightarrow\ \text{proper ideal endpoints}
\]

now has no missing last implication: Theorem 5.1 proves it.
The result covers both an interior-time stop and arrival
at an original parent ideal endpoint.

The following are still separate:

* two correctly positioned local germs must actually exist;
* their contact endpoints must be the named canonical graph
  points in the same selected physical component;
* the desired two occurrences must remain distinct as source
  occurrences with the required order;
* their native fine-marking and single-inclusion-block filters
  must be checked at every sequential stage;
* their terminal projections and further selected Wave
  outputs must meet the hypotheses of the connected-carrier
  noncollision theorem.

Thus this result removes the properness premise for actual
maximal restrictions on these annuli; it does not assert that
every raw proper restriction survives a dynamical filter.
It also does not replace two local germs by two complete
routes with particular far endpoints.

The hyperbolic disk and nondegenerate carrier hypotheses
are part of the theorem. No finite-annulus assertion is
made here for a puncture or a parabolic plane domain.
Kahn's separate plane/isomorphism case is described in
the exit-transfer note, Section 6.5.

The constructed carrier in CUTPOINT_PRUNING.md supplies
connectedness, forward invariance, and containment of the
critical point. Its fullness follows because it is a
subcontinuum of the full empty-interior physical filled set,
as proved in CONNECTED_CARRIER_NONCOLLISION.md, Lemma 2.1.
Applying this package to the independently named native
KKL carrier retains the stated identification requirement.
