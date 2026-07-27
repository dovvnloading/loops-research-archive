# Access-seeded maximal lifts: continuity, Borel landing, and the reduced stationary gate

## 1. Purpose and status

The fixed-Freudenthal-end route is not presently available on the
stationary tree complement for the source-locked reason proved in
`kkl_stationary_fixed_end_topological_obstruction.md`: KKL's
\(BL_0\) and \(L_0^h\) data are marked accesses, whereas the imported
fixed-end theorem is stated for Freudenthal ends.  The sharper
one-inner-end/nonproperness obstruction is conditional on the
physical-carrier and inclusion hypotheses
\(\mathrm{TWO}_h\wedge\mathrm{INC}_h\).

This note proves the descriptive-topological replacement that is
available once one actual marked-access germ has been selected.
It resolves the abstract continuation-time and landing-measurability
parts of RLS\(_h\); it does **not** construct the KKL access germ,
prove prime-end landing for every leaf, prove the line-2097 filters,
or give a width bound.

The proved implication is

\[
\boxed{
\begin{array}{c}
\text{continuous product family of embedded target paths}\\
+\text{ one continuous access-local inverse seed}\\
\Downarrow\\
\text{unique maximal lift field on an open domain,}\\
\text{lower-semicontinuous exit time, Borel landing set,}\\
\text{Borel landing map, and Borel finite-horizon first-exit code.}
\end{array}}
\tag{1.1}
\]

Thus no independent measurable-selection theorem is needed for the
continuation on a **supplied continuous product piece**, after a
canonical access seed on that piece is supplied.  A merely Borel
KL06 lamination is not automatically such a product family.  The
product presentation, its seeds, and the analytic KKL
survival/response clauses remain genuine gates.

No MLC-related global obligation is promoted.

## 2. Abstract setting

Let \(X,Y\) be second-countable locally compact metric spaces and let

\[
 I:X\longrightarrow Y
\tag{2.1}
\]

be a local homeomorphism.  A holomorphic immersion between Riemann
surfaces satisfies these hypotheses.

Let \(\Lambda\) be a second-countable metric transversal and fix
\(0<t_0<1\).  Suppose

\[
 \Phi:\Lambda\times(0,1)\longrightarrow Y
\tag{2.2}
\]

is continuous and every

\[
 \phi_\lambda(t):=\Phi(\lambda,t)
\tag{2.3}
\]

is an embedded path.  Assume different path images are disjoint:

\[
 \lambda\ne\lambda'
 \quad\Longrightarrow\quad
 |\phi_\lambda|\cap|\phi_{\lambda'}|=\varnothing.
\tag{2.4}
\]

This is the product-rectangle model for one foliated piece of a valid
target WAD.  Nothing in the KL06 definition of a valid lamination
automatically supplies this joint continuity.  Applying the theorem
to a finite or countable WAD decomposition therefore requires, as an
additional hypothesis, a Borel partition into continuous product
pieces, together with a separate audit of seams and any excluded or
null leaf set.

An **access seed** consists of a continuous map

\[
 s:\Lambda\longrightarrow X,
\qquad
 I(s(\lambda))=\Phi(\lambda,t_0),
\tag{2.5}
\]

together with a continuous lift

\[
 \widehat\Phi_0:
\Lambda\times(0,t_0]\longrightarrow X
\tag{2.6}
\]

satisfying

\[
 I\widehat\Phi_0(\lambda,t)=\Phi(\lambda,t),
\qquad
\widehat\Phi_0(\lambda,t_0)=s(\lambda).
\tag{2.7}
\]

In the stationary application, (2.6) is what a univalent collar at
one marked \(BL_0\) access must supply.  It is strictly finer than
properness at a Freudenthal end.

The word “access” here records the intended application, not an
extra conclusion of the abstract hypotheses.  Equations (2.5)--(2.7)
give a continuous lifted segment on \(0<t\le t_0\), but do not assert
that it leaves every compact subset of \(X\) as \(t\downarrow0\), or
that it lands at a KKL ideal access.  Seed-side access properness must
be proved separately in the analytic application.

For each \(\lambda\), let

\[
 \widehat\phi_\lambda:(0,\tau(\lambda))\longrightarrow X
\tag{2.8}
\]

be the maximal continuation of (2.6), with

\[
 t_0<\tau(\lambda)\le1.
\tag{2.9}
\]

Existence and uniqueness follow by continuing through local inverse
charts.  The next theorem supplies the family-level regularity.

## 3. The open continuation domain

Define

\[
 \mathcal D
 =
 \{(\lambda,t)\in\Lambda\times(0,1):
      0<t<\tau(\lambda)\}.
\tag{3.1}
\]

### Theorem 3.1 (continuous maximal-lift field)

The set \(\mathcal D\) is open and there is a unique continuous map

\[
 \widehat\Phi:\mathcal D\longrightarrow X
\tag{3.2}
\]

which extends \(\widehat\Phi_0\) and satisfies

\[
 I\widehat\Phi(\lambda,t)=\Phi(\lambda,t).
\tag{3.3}
\]

Consequently,

\[
 \tau:\Lambda\longrightarrow(t_0,1]
\tag{3.4}
\]

is lower semicontinuous and hence Borel.

#### Proof

Fix \(\lambda_0\).  Starting at \(s(\lambda_0)\), ordinary path
lifting through a local inverse chart gives a lift on a nontrivial
interval about \(t_0\).  Two lifts which agree at one time agree on
their common connected parameter interval: the equality set is
nonempty, open by local injectivity, and closed by continuity.
Therefore all successive local continuations glue uniquely.  Their
union is the maximal interval \((0,\tau(\lambda_0))\).

We prove simultaneous continuity locally.  Fix

\[
 (\lambda_0,t_1)\in\mathcal D.
\tag{3.5}
\]

If \(t_1<t_0\), the assertion follows directly from the assumed
continuity of \(\widehat\Phi_0\) on
\(\Lambda\times(0,t_0]\).  At \(t_1=t_0\), use that seed on the
backward side and the first inverse chart below on the forward side;
the two formulas agree at \(t_0\) by (2.7).  It remains to treat
\(t_1>t_0\).

The compact target segment

\[
 K=
 \Phi\bigl(\{\lambda_0\}\times[t_0,t_1]\bigr)
\tag{3.6}
\]

has a lifted compact segment

\[
 \widehat K=
 \widehat\phi_{\lambda_0}([t_0,t_1]).
\tag{3.7}
\]

Cover \(\widehat K\) by finitely many open sets

\[
 W_1,\ldots,W_r
\tag{3.8}
\]

on each of which \(I\) is a homeomorphism onto an open subset of
\(Y\).  Using local compactness, choose smaller inverse
neighborhoods compactly contained in those charts.  Subdivide
\([t_0,t_1]\) so that each closed lifted subsegment is contained in
one smaller neighborhood.  At every subdivision point choose one
still smaller inverse neighborhood whose closure lies in
\(W_j\cap W_{j+1}\).  Thus choose

\[
 t_0=u_0<u_1<\cdots<u_r=t_1
\tag{3.9}
\]

so that the lift of the \(j\)-th closed subsegment has compact
closure in \(W_j\), its target image has compact closure in
\(I(W_j)\), and the lifted transition point has a compactly
contained inverse neighborhood in \(W_j\cap W_{j+1}\).

Continuity of \(\Phi\) and of the seed \(s\) now gives a neighborhood
\(N\ni\lambda_0\) such that, for every \(\lambda\in N\), the first
target subsegment lies in \(I(W_1)\) and its initial lift lies in
\(W_1\).  Apply \((I|_{W_1})^{-1}\).  At \(u_1\), compact containment
and continuity put the computed endpoint in the prescribed smaller
neighborhood in \(W_1\cap W_2\), uniformly after shrinking \(N\).
The \(W_1\)- and \(W_2\)-inverse formulas therefore agree there and,
by uniqueness, throughout their common parameter interval.  Repeat
this argument through the finite chain.

Finally choose one more inverse chart at
\(\widehat\phi_{\lambda_0}(t_1)\).  Since \(t_1<1\), continuity of
\(\Phi\) puts \(\Phi(\lambda,t)\) in its image for \(\lambda\) near
\(\lambda_0\) and
\(t_1-\varepsilon<t<t_1+\varepsilon<1\).  Consequently the nearby
lifts exist slightly beyond \(t_1\), and all formulas are
compositions of continuous maps.  Hence \(\mathcal D\) is open at
\((\lambda_0,t_1)\) and the joint lift is continuous there.

The same construction applies at every point already reached by the
maximal lift.  Its union is the map (3.2), and it proves that
\(\mathcal D\) is open.

For \(a<1\),

\[
 \{\lambda:\tau(\lambda)>a\}
\tag{3.10}
\]

is the projection to \(\Lambda\) of a neighborhood obtained by the
preceding finite-chart argument at every
\((\lambda,a)\in\mathcal D\).  More directly, if
\(a\le t_0\), then \(\{\lambda:\tau(\lambda)>a\}=\Lambda\).
If \(t_0<a<1\) and \(\tau(\lambda_0)>a\), repeat the argument on
\([t_0,a]\) to obtain a neighborhood \(N\) on which every lift exists
past \(a\).  Thus (3.10) is open.  This is lower
semicontinuity. \(\square\)

### Corollary 3.2 (finite-time failure is escape)

If \(\tau(\lambda)<1\), then

\[
 \widehat\phi_\lambda(t)
\text{ leaves every compact subset of }X
\quad(t\uparrow\tau(\lambda)).
\tag{3.11}
\]

#### Proof

If a sequence \(t_n\uparrow\tau(\lambda)\) remained in one compact
set, pass to a subsequence with
\(\widehat\phi_\lambda(t_n)\to x\in X\).  Choose an inverse chart
\(W\ni x\).  Since \(\tau(\lambda)<1\), continuity of the target path
puts its entire sufficiently late segment, including a short segment
past \(\tau(\lambda)\), inside \(I(W)\).  For a sufficiently late
\(t_n\), the inverse branch on \(W\) agrees with the existing lift at
\(t_n\); uniqueness makes it agree up to \(\tau(\lambda)\) and then
continue beyond it, a contradiction.  This is the argument of
`kkl_stationary_route_exit_conductance_reduction.md`, Lemma 4.2.
\(\square\)

## 4. Borel ideal landing

Assume now that \(X\) has a metrizable compactification

\[
 X\subset\widehat X
\tag{4.1}
\]

with \(X\) open and dense.  For KKL, one works chartwise in the
universal-cover ideal closure and then quotients by the fixed deck
data selected by the access seed.

Fix a compatible bounded metric \(d_{\widehat X}\) on \(\widehat X\).
Extend \(\widehat\Phi\) to a Borel map on
\(\Lambda\times(0,1)\) by assigning one dummy point outside
\(\mathcal D\).  This extension is Borel because \(\mathcal D\) is
open.

For \(n\ge1\), define the terminal oscillation

\[
\begin{split}
 \operatorname{osc}_n(\lambda)
 =
 \sup\{&
 d_{\widehat X}(
   \widehat\Phi(\lambda,q),
   \widehat\Phi(\lambda,r)):
 q,r\in\mathbb Q,\\
 &\max(t_0,\tau(\lambda)-1/n)<q,r<\tau(\lambda)\}.
\end{split}
\tag{4.2}
\]

The supremum over an empty set is \(0\).

### Lemma 4.1 (Borel oscillation)

Every \(\operatorname{osc}_n\) is Borel.

#### Proof

For fixed rationals \(q,r\), the condition

\[
 \max(t_0,\tau(\lambda)-1/n)<q,r<\tau(\lambda)
\tag{4.3}
\]

is Borel because \(\tau\) is Borel.  On that set, the displayed
distance in (4.2) is Borel.  Extend it by \(0\) off the set.
Equation (4.2) is the supremum of countably many Borel functions,
and is therefore Borel. \(\square\)

Define the landing set

\[
 \Lambda_{\mathrm{land}}
 =
 \left\{
  \lambda:
  \lim_{n\to\infty}\operatorname{osc}_n(\lambda)=0
 \right\}.
\tag{4.4}
\]

### Theorem 4.2 (Borel landing map)

The set \(\Lambda_{\mathrm{land}}\) is Borel.  For every
\(\lambda\in\Lambda_{\mathrm{land}}\), the limit

\[
 \ell(\lambda)
 =
 \lim_{t\uparrow\tau(\lambda)}
 \widehat\phi_\lambda(t)
\tag{4.5}
\]

exists in \(\widehat X\), and

\[
 \ell:\Lambda_{\mathrm{land}}\longrightarrow\widehat X
\tag{4.6}
\]

is Borel.

#### Proof

By Lemma 4.1,

\[
\Lambda_{\mathrm{land}}
=
\bigcap_{k\ge1}
\bigcup_{N\ge1}
\bigcap_{n\ge N}
\{\lambda:\operatorname{osc}_n(\lambda)<1/k\}
\tag{4.7}
\]

is Borel.

For a fixed \(\lambda\), continuity in \(t\) implies that the diameter
of the entire terminal image

\[
 \widehat\phi_\lambda
 \bigl((\max(t_0,\tau(\lambda)-1/n),\tau(\lambda))\bigr)
\tag{4.8}
\]

equals the supremum over rational parameter pairs in (4.2).  Hence
(4.4) is the Cauchy criterion for the full terminal path, not merely
for one chosen sequence.  Compactness of \(\widehat X\) gives the
unique limit (4.5).

Choose the Borel times

\[
 q_j(\lambda)
 =
 t_0+
 \bigl(\tau(\lambda)-t_0\bigr)
 \left(1-\frac1j\right),
\qquad j\ge2.
\tag{4.9}
\]

They satisfy \(t_0<q_j(\lambda)<\tau(\lambda)\), so

\[
 \lambda\longmapsto
 \widehat\Phi(\lambda,q_j(\lambda))
\tag{4.10}
\]

is Borel.  On \(\Lambda_{\mathrm{land}}\), these maps converge
pointwise to \(\ell\).  A pointwise limit of Borel maps into a compact
metric space is Borel, proving (4.6). \(\square\)

### Lemma 4.3 (when the landing point is on the boundary)

If \(\lambda\in\Lambda_{\mathrm{land}}\) and
\(\tau(\lambda)<1\), then

\[
 \ell(\lambda)\in\widehat X\setminus X.
\tag{4.10a}
\]

The same conclusion holds when \(\tau(\lambda)=1\) provided the
target path \(\phi_\lambda(t)\) leaves every compact subset of \(Y\)
as \(t\uparrow1\).

#### Proof

If \(\tau(\lambda)<1\) and \(\ell(\lambda)\in X\), choose a local
inverse chart for \(I\) at \(\ell(\lambda)\).  Since

\[
 I(\ell(\lambda))
 =
 \lim_{t\uparrow\tau(\lambda)}\phi_\lambda(t)
 =
 \phi_\lambda(\tau(\lambda)),
\tag{4.10b}
\]

that chart extends the lift beyond \(\tau(\lambda)\), contradicting
maximality.

If \(\tau(\lambda)=1\) and \(\ell(\lambda)\in X\), continuity of \(I\)
puts the terminal target path in a compact neighborhood of
\(I(\ell(\lambda))\), contradicting target properness. \(\square\)

### Corollary 4.4 (Borel boundary code)

Let

\[
 \widehat X\setminus X
 =
 Z_1\sqcup Z_2\sqcup\cdots
\tag{4.11}
\]

be a finite or countable Borel partition into proof-used boundary
strata, including all access, obstacle, outer-boundary, and marking
codes.  Restrict to the Borel part of
\(\Lambda_{\mathrm{land}}\) covered by Lemma 4.3.  Then

\[
 \Lambda_j
 =
 \{\lambda\in\Lambda_{\mathrm{land}}:
      \ell(\lambda)\in Z_j\}
\tag{4.12}
\]

is Borel for every \(j\).  The nonlanding set

\[
 \Lambda_{\mathrm{nl}}
 =
 \Lambda\setminus\Lambda_{\mathrm{land}}
\tag{4.13}
\]

is Borel as well.

#### Proof

Take the Borel preimages under (4.6), and use (4.4). \(\square\)

## 5. Embeddedness and noncrossing

### Proposition 5.1 (canonical seeded traces)

For each \(\lambda\), the maximal trace
\(\widehat\phi_\lambda\) is embedded.  Traces belonging to distinct
parameters are disjoint.

#### Proof

If

\[
 \widehat\phi_\lambda(t)
 =
 \widehat\phi_\lambda(u),
\tag{5.1}
\]

then applying \(I\) gives

\[
 \phi_\lambda(t)=\phi_\lambda(u).
\tag{5.2}
\]

The target path is embedded, so \(t=u\).

If traces for \(\lambda\ne\lambda'\) met, their images under \(I\)
would give an intersection of the two target leaves, contradicting
(2.4). \(\square\)

Thus the seed eliminates the sheet-selection ambiguity: one target
leaf has exactly one continuation attached to the chosen access
germ.  This does not say that another access seed cannot produce a
different trace with the same untagged terminal image.

## 6. First failure over a finite Wave horizon

Suppose the proof supplies finitely many access-seeded route systems
on one common standard-Borel leaf domain \(\Lambda\), indexed by

\[
 1\le h\le m.
\tag{6.1}
\]

If a native route system is defined only on a Borel subset
\(R_h\subset\Lambda\), extend its record to \(\Lambda\) with an
explicit `NO_ROUTE` value and declared Borel values of
\(\tau_h,Q_h\) on \(\Lambda\setminus R_h\).  The application must
state whether route absence counts as a failure.  The Borel nature of
\(R_h\) and this convention are application hypotheses, not
consequences of the abstract lifting theorem.  When every route is
defined everywhere, take \(R_h=\Lambda\).

For each \(h\), let \(\tau_h\) be obtained above.  Let \(L_h\) be the
Borel subset of the stage-\(h\) transversal on which the terminal
limit exists and lies in the boundary part covered by Lemma 4.3.
Let

\[
 \ell_h:L_h\longrightarrow\widehat X_h,
 \qquad
 c_h:L_h\longrightarrow C_h
\tag{6.2a}
\]

be respectively the Borel landing map and its Borel code in a finite
or countable discrete code space \(C_h\).  Enlarge \(C_h\) by the
three symbols

\[
 \{\mathtt{NONLANDING},
   \mathtt{NO\_BOUNDARY\_CODE},
   \mathtt{NO\_ROUTE}\}
\tag{6.2c}
\]

and extend \(c_h\) to a total Borel code
\(\bar c_h:\Lambda\to\bar C_h\): use `NO_ROUTE` first on
\(\Lambda\setminus R_h\); on \(R_h\), use \(c_h\) on \(L_h\),
`NONLANDING` when the terminal oscillation does not vanish, and
`NO_BOUNDARY_CODE` when a terminal limit exists but is outside the
boundary strata covered by Lemma 4.3.  These four cases form a Borel
partition under the stated hypotheses.  Let \(Q_h\) be any additional
Borel predicate recording a full-path marked-state failure, as
opposed to a geometric continuation failure.

Define

\[
 h_*(\lambda)
 =
 \min\{h:
   \tau_h(\lambda)<1
   \text{ or }Q_h(\lambda)=1\},
\tag{6.2}
\]

on the set where the displayed set is nonempty.

Define the landing part of the first-failure domain by

\[
 D_{\mathrm{first,land}}
 =
 \bigcup_{h=1}^m
 \bigl(\{h_*=h\}\cap L_h\bigr).
\tag{6.2b}
\]

### Proposition 6.1 (Borel first-horizon code)

The failure domain is Borel, \(h_*\) is Borel, and the tuple

\[
 \bigl(
 h_*,\tau_{h_*},\ell_{h_*},c_{h_*},Q_{h_*}
 \bigr)
\tag{6.3}
\]

is a Borel record on the explicitly defined Borel domain
\(D_{\mathrm{first,land}}\).  Its complement in the first-failure
domain is recorded by the total Borel code
\((h_*,\bar c_{h_*})\) with values in the tagged countable disjoint
union
\(\bigsqcup_{h=1}^m(\{h\}\times\bar C_h)\).

#### Proof

For each \(h\), the set

\[
 D_h^{\mathrm{fail}}
 =
 \{\tau_h<1\}\cup\{Q_h=1\}
\tag{6.4}
\]

is Borel.  The first-index fiber is

\[
 \{h_*=h\}
 =
 D_h^{\mathrm{fail}}
 \setminus
 \bigcup_{r<h}D_r^{\mathrm{fail}},
\tag{6.5}
\]

so it is Borel.  A map into a finite discrete set is Borel when its
fibers are Borel.  Equation (6.2b) is a finite union of Borel sets.
Restricting the Borel maps \(\ell_h,c_h,\tau_h,Q_h\) to
\(\{h_*=h\}\cap L_h\), and gluing across the finite Borel partition,
proves the landing assertion.  Gluing the total codes
\(\bar c_h\) over the same first-index fibers proves the complementary
record. \(\square\)

For the native stationary horizon,

\[
 m=N-1=b+2.
\tag{6.6}
\]

The index horizon in Proposition 6.1 is \(b+2\).  This is only a
uniform bound on the supplied stage list.  No claim is made here that
the number of access seeds or route systems required at one stage is
independent of satellite period.

## 7. Exact effect on RLS\(_h\)

RLS\(_h\) in
`kkl_stationary_route_exit_conductance_reduction.md` required:

1. a Borel target leaf space;
2. a complete single-valued selector;
3. a Borel field of initial germs;
4. a Borel maximal continuation time;
5. a compatible compactification;
6. a Borel landing map;
7. a Borel first-boundary code; and
8. transverse-measure compatibility.

Theorems 3.1, 4.2, and Proposition 6.1 prove clauses 4, 6, and 7
only after clauses 1, 3, and 5 are strengthened by the following
product hypothesis:

\[
\begin{split}
\mathrm{RLS\!-\!A^+}:\quad&
\text{the proof-used leaf family has a finite or countable Borel}\\
&\text{partition into continuous product pieces of the form
  (2.2)--(2.4),}\\
&\text{each product parametrization is a Borel isomorphism onto its
  ambient leaf piece,}\\
&\text{each piece has a continuous seed (2.5)--(2.7), and}\\
&\text{the seams and any excluded/null leaves have explicit
  Borel codes.}
\end{split}
\tag{7.0}
\]

On each supplied product piece the theorems remove the arbitrary
part of clause 2 for geometric continuation: the chosen access germ
has one and only one maximal continuation.  A merely Borel leaf space
plus a Borel germ field does not imply \(\mathrm{RLS\!-\!A^+}\).

What remains is:

\[
\boxed{
\begin{array}{ll}
\text{RLS-A}&\text{construct the actual KKL product pieces, their
                 continuous access seeds, the complete proof-used
                 leaf domain, and the seam/null-set codes;}\\
\text{RLS-B}&\text{prove the selected KKL ideal compactification and
                 its strata satisfy the stated Borel model;}\\
\text{RLS-C}&\text{prove full-path fine marking, coarse-filter
                 survival, and marked-state predicates;}\\
\text{RLS-D}&\text{prove seed-side access properness and that the
                 Borel landing traces assemble into the source-valid
                 proper lamination required by domination;}\\
\text{RLS-E}&\text{prove transverse-width accounting and bounded
                 occurrence multiplicity;}\\
\text{RLS-F}&\text{charge or respond to the nonlanding and
                 \(BL_0\)-ending residuals.}
\end{array}}
\tag{7.1}
\]

The three abstract Borel conclusions are therefore no longer an
independent research mystery **on supplied
\(\mathrm{RLS\!-\!A^+}\) product pieces**.  Constructing those pieces
and proving that they exhaust the native KKL WAD remain analytic
carrier/marking tasks.

## 8. Why no width theorem is claimed here

Pairwise-disjoint landing traces are necessary candidates for a
source lamination.  After seed-side access properness is separately
proved they become proper-trace candidates, but even then they do not
by themselves prove:

- that every trace is a KKL path in the refined marking;
- that no trace is subordinate to one interval of the pulled coarse
  marking;
- that an arbitrary Borel union is a source-valid partial proper
  foliation in the exact source convention;
- that occurrence multiplicity is one after different access seeds
  are combined; or
- that the source extremal width equals, dominates, or is dominated
  by a named target width.

Once RLS-C--E are proved, KKL's domination lemma is the correct tool
for the inequality

\[
 \mathcal W(\text{target class})
 \le
 \mathcal W(\text{source trace class}).
\tag{8.1}
\]

Equation (8.1) is not inferred merely from the Borel continuation
theorem.

## 9. Adversarial audit

1. A local inverse seed is assumed, not inferred from a route label.
2. The maximal lift is continued on the full source surface, not
   stopped at an artificial collar boundary.
3. Lower semicontinuity, not continuity, is claimed for exit time.
   Exit times can jump upward under perturbation.
4. The landing criterion controls the full terminal oscillation, not
   one favorable subsequence.
5. A compact metric ideal model is an explicit hypothesis.
6. A Freudenthal-end limit is not silently promoted to a KKL marked
   prime-end access.
7. Nonlanding is retained as a Borel residual.
8. Different access seeds may still yield colliding terminal images.
9. Borel continuation is not called a valid WAD or a width estimate.
10. The finite horizon is \(b+2\), while ambient unbreakability is
    retained through \(N=b+3\).
11. No period-dependent finite-end count is used.
12. MLC, UPTCR, VAAPC-I, and the native stationary repair remain open.

## 10. Immediate analytic target

The next proof must instantiate (2.6) on the actual \(BL_0\) access
collar and then prove RLS-C--F.  The first falsifiable failure record
is

\[
\begin{split}
(&h,\lambda,\text{access},\text{sheet},
  \tau_h,\ell_h,\text{boundary stratum};\\
 &\text{first fine/coarse filter failure},
  \text{terminal image and properness flag},
  \text{response class}).
\end{split}
\tag{10.1}
\]

If the landing lies on the outer end, the terminal segment is a
vertical candidate; it becomes a proper vertical path only after
seed-side access properness is proved.  If it lands on a prescribed
small-Julia end, it is an \(R\)-charge candidate subject to the same
properness and marking checks.  If it lands at a different access of
the inner tree end and its output is a Wave ending at \(BL_0\), it is
the exact critical residual which still requires a noncircular
response theorem.
