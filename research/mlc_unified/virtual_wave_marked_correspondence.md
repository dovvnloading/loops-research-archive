# Virtual Wave Marked Correspondence: Return Language, Boundary Action, and Enlargement

## 1. Status and exact result

This note attacks `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`.

The pass proves four statements that were previously implicit:

1. a horizon-independent branch graph has a canonical prefix-closed path
   language;
2. a forward-invariant full carrier containing the critical values of a
   polynomial return produces an actual covering/inclusion pair on its
   complement;
3. marking refinement is equivalent to an exact containment relation between
   the two pulled endpoint sets on the prime-end boundary; and
4. this endpoint relation is natural under a root enlargement precisely when
   the analytic and prime-end squares commute.

It also gives an exact countermodel showing that carrier, degree, covering,
prime-end-circle, and relative-cover existence data do **not** determine the
marked action: a residual boundary phase of the immersion can change a valid
marking into an invalid one.

Consequently:

- `RETURN_PATH_LANGUAGE` is proved;
- `FORWARD_COHERENT_COMPLEMENT_PAIR` is proved;
- `PRIME_END_MARKING_ACTION_CRITERION` is proved;
- `MARKED_PAIR_ENLARGEMENT_NATURALITY` is proved;
- `VIRTUAL_RETURN_BRANCH_LANGUAGE` is open;
- `VIRTUAL_PROVISIONAL_COMPLEMENT_PAIR` is open;
- `VIRTUAL_ACCESS_ACTION_CERTIFICATE` is open; and
- `VIRTUAL_WAVE_MARKED_CORRESPONDENCE` remains open.

The first source-facing missing datum is now sharper than “a marked
complement”: it is an actual virtual return graph together with a normalized
prime-end access action for its provisional carrier pairs.

`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, `VAAPC-I`, UPTCR, and MLC remain open.

## 2. Source boundary

The source locks are unchanged:

1. Dzmitry Dudko, *The decoration theorem for the Mandelbrot set and
   applications*, arXiv:2512.24171v1, source file `main.tex`, SHA-256
   `FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454`;
2. Jeremy Kahn, Artem Kapiamba, and Mikhail Lyubich,
   *A priori bounds for Feigenbaum quadratics*, arXiv:2606.27272v1, source
   file `waves-with-Misha.tex`, SHA-256
   `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`.

Dudko lines 875--892 define the nested satellite-copy chain and propose
partially invariant connected hulls of the corresponding Cantor small Julia
sets carrying the critical orbit through an “appropriate number” of first
returns.  They do not define the return branches, their localizations, their
prime-end markings, or the appropriate stopping number.

KKL lines 2062--2141 define a pair
\[
  (g,\iota):V'\rightrightarrows V
\tag{2.1}
\]
with \(g\) a holomorphic covering and \(\iota\) a holomorphic immersion.
For an ideal marking \(I\) of \(V\), the pair acts only when
\[
  g^*I\quad\text{refines}\quad \iota^*I.
\tag{2.2}
\]
KKL lines 1707--1709 verify this structure for their native pulled Hubbard
tree complements.  No theorem in the checked sources constructs (2.1)--(2.2)
for Dudko's virtual carrier.

All results below that are not quotations are proved directly.  No unpublished
virtual-renormalization result is imported.

## 3. Horizon-independent return languages

### 3.1 Typed branch graph

A **typed return graph** for a block \(B\) is a directed graph
\[
  \mathcal G_B=(\mathcal V_B,\mathcal E_B,v_B)
\tag{3.1}
\]
with distinguished initial vertex \(v_B\).  Every edge \(e:u\to v\) carries:

1. an actual source localization \(U_e^-\);
2. an actual target localization \(U_e^+\);
3. a specified holomorphic branch
   \(F_e:U_e^-\to U_e^+\);
4. a positive iterate length \(s(e)\);
5. the complete critical and degree words;
6. the selected source and target components;
7. the parent route and selected sheet;
8. the absorbed-or-separated obstacle record; and
9. the protected source and target access records.

“Actual” means that the domains, map, and components occur in the dynamical
plane of the specified polynomial.  A symbol standing for an as-yet
unconstructed branch is not an edge of \(\mathcal G_B\).

A finite directed path
\[
  r=(e_1,\ldots,e_k),
  \qquad
  t(e_j)=o(e_{j+1}),
\tag{3.2}
\]
starting at \(v_B\) is a **return word**.  The empty path is denoted
\(\varnothing\).  Define
\[
  \mathscr R(\mathcal G_B)
  =
  \{\varnothing\}
  \cup
  \{(e_1,\ldots,e_k):k\geq1,\ o(e_1)=v_B\}.
\tag{3.3}
\]
No Wave stopping rule occurs in (3.1)--(3.3).

### Theorem 3.1 (return-path language)

For every typed return graph, \(\mathscr R(\mathcal G_B)\) is prefix closed.
For each \(r=(e_1,\ldots,e_k)\), its total iterate
\[
  s(r)=\sum_{j=1}^k s(e_j)
\tag{3.4}
\]
is finite and every intermediate branch and critical encounter is retained.

#### Proof

Let \(r=(e_1,\ldots,e_k)\) be a path.  For \(0\leq j\leq k\), the sequence
\((e_1,\ldots,e_j)\) starts at \(v_B\), and every adjacent pair remains
composable.  It is therefore in (3.3).  This proves prefix closure.

The path contains finitely many edges and every \(s(e_j)\) is a positive
integer, so (3.4) is a finite integer.  Items 4--9 in the edge definition are
stored edgewise.  Reading the first \(j\) edge records gives the complete
intermediate data of the length-\(j\) prefix.  Nothing is inferred from the
terminal edge alone. \(\square\)

### 3.2 Source-facing qualification

Theorem 3.1 is a compiler theorem, not a virtual realization theorem.  To
instantiate it, one must construct \(\mathcal G_B\) from an actual
virtual-Molecule block before the Wave algorithm runs and prove that every
branch the Wave proof may request occurs in the graph.

Call that assertion `VIRTUAL_RETURN_BRANCH_LANGUAGE`.  Dudko's “appropriate
number of first returns” does not provide Items 1--9 above.  KKL's native
graph cannot be substituted without the typed component-and-access bridge
already isolated in Proposition 7.1 of `vaapc_inventory_source_audit.md`.

## 4. The unmarked polynomial complement pair

This section separates existence of an analytic pair from existence of a
marking on which it acts.

### Theorem 4.1 (forward-coherent complement pair)

Let \(R\) be a polynomial of degree \(d\geq2\), and let
\(H\subset\mathbb C\) be a nondegenerate full continuum.  Assume:

`C1.` \(H\) contains every finite critical value of \(R\); and

`C2.` \(R(H)\subset H\).

Set
\[
  H'=R^{-1}(H),\qquad
  V=\mathbb C\setminus H,\qquad
  V'=\mathbb C\setminus H'.
\tag{4.1}
\]
Then:

1. \(H'\) is a nondegenerate full continuum;
2. \(H\subset H'\), hence the identity restricts to a holomorphic embedding
   \[
     \iota:V'\hookrightarrow V;
   \tag{4.2}
   \]
3. the restriction
   \[
     g=R|_{V'}:V'\longrightarrow V
   \tag{4.3}
   \]
   is a connected unbranched covering of degree \(d\); and
4. \((g,\iota):V'\rightrightarrows V\) is an actual unmarked analytic pair.

#### Proof

Put
\[
  \Omega=\widehat{\mathbb C}\setminus H.
\]
Because \(H\) is a nondegenerate full continuum, \(\Omega\) is a simply
connected proper domain containing \(\infty\).  Assumption `C1` implies that
every finite critical point of \(R\) lies in \(H'\): if \(R'(z)=0\), then
\(R(z)\in H\), hence \(z\in R^{-1}(H)\).

We now justify both connectedness and fullness of \(H'\); neither follows
from the degree count alone.  Let \(\Omega_\infty\) be the component of
\(R^{-1}(\Omega)\) containing \(\infty\).  Choose a regular value \(y\in
\Omega\) sufficiently close to \(\infty\).  All \(d\) solutions of
\(R(z)=y\), counted with multiplicity, lie near \(\infty\), hence in
\(\Omega_\infty\).  Thus the proper restriction
\[
  R:\Omega_\infty\longrightarrow\Omega
\]
has degree \(d\).  Every other component of \(R^{-1}(\Omega)\), if present,
would map properly and surjectively to \(\Omega\) with positive degree.
Since the sum of the component degrees is \(d\), no such component exists:
\[
  R^{-1}(\Omega)=\Omega_\infty.
\tag{4.4a}
\]

Remove the unique preimage \(\infty\) of \(\infty\).  There are no remaining
critical points, so
\[
  R:\Omega_\infty\setminus\{\infty\}
  \longrightarrow
  \Omega\setminus\{\infty\}.
\tag{4.4b}
\]
is a connected unbranched cover of degree \(d\).  A Riemann map
\(\Omega\to\mathbb D\) sending \(\infty\) to \(0\) identifies the target in
(4.5) with \(\mathbb D^*\).  Connected finite covers of
\(\mathbb D^*\) correspond to the subgroups
\(d\mathbb Z<\pi_1(\mathbb D^*)\cong\mathbb Z\), and are again punctured
disks.  Filling the unique puncture therefore makes
\(\Omega_\infty\) simply connected.

The complement
\[
  H'=\widehat{\mathbb C}\setminus\Omega_\infty
\]
is consequently connected; it is compact and nonempty, and (4.4) gives
\(\mathbb C\setminus H'=\Omega_\infty\setminus\{\infty\}\), which is
connected.  Hence \(H'\) is a full continuum.  It is nondegenerate because
the proper map \(R:H'\to H\) is onto and \(H\) is nondegenerate.

Assumption `C2` is equivalent to
\[
  H\subset R^{-1}(H)=H'.
\tag{4.4}
\]
Taking complements in \(\mathbb C\) reverses the inclusion and gives
\(V'\subset V\), proving (4.2).

The restriction (4.3) has no critical point by the first paragraph.  It is
proper: if \(K\Subset V\), polynomial properness makes \(R^{-1}(K)\) compact
in \(\mathbb C\), and \(R^{-1}(K)\cap H'=\varnothing\), so it is compact in
\(V'\).  If \(y\in V\), none of its \(d\) preimages, counted with
multiplicity, belongs to \(H'\); moreover \(y\) is not a critical value by
`C1`.  Thus it has exactly \(d\) distinct preimages in \(V'\).  Therefore
\(g\) is an unbranched degree-\(d\) covering.  Connectedness was proved
above.  Together with (4.2), this gives Item 4. \(\square\)

### Corollary 4.2 (finite return word)

For \(R=f_c^n\), Assumption `C1` is discharged if \(H\) contains
\[
  f_c(0),f_c^2(0),\ldots,f_c^n(0),
\tag{4.5}
\]
because every finite critical value of \(f_c^n\) occurs in this list.
Assumption `C2` remains a separate entire-carrier assertion; partial
invariance of selected atoms does not imply it.

### Localization warning

The surfaces in (4.1) have the end at infinity.  A cusp-free KKL surface is
obtained only after selecting compatible outer localizations.  Theorem 10.2
of `finite_horizon_inflation.md` supplies qualitative Jordan localizations
after the complete selected pullback itinerary and separated obstacles are
given.  It does not prove uniform modulus, properness of a selected
relative-cover lift, or access completeness.  None of those properties is
included in Theorem 4.1.

The actual virtual assertion that constructs an \(H\) satisfying `C1`--`C2`,
all protected-access conditions, the authorized localization, and the
selected component itinerary for every finite provisional package and
compatible return word is named `VIRTUAL_PROVISIONAL_COMPLEMENT_PAIR`.

## 5. Exact prime-end marking criterion

### 5.1 Markings determined by endpoint sets

Let \(S\) be an oriented topological circle.  If \(E\subset S\) is closed
and nowhere dense, define
\[
  \mathcal I(E)=\pi_0(S\setminus E).
\tag{5.1}
\]
The components are pairwise disjoint open intervals.  There are at most
countably many because each contains a distinct member of a fixed countable
dense subset of \(S\).  Since \(E\) has empty interior,
\(\bigcup\mathcal I(E)\) is dense in \(S\).  Hence (5.1) is an ideal marking
in the sense used by KKL.

### Lemma 5.1 (endpoint refinement)

For closed nowhere-dense sets \(E_1,E_2\subset S\),
\[
  \mathcal I(E_1)\ \text{refines}\ \mathcal I(E_2)
  \quad\Longleftrightarrow\quad
  E_2\subset E_1.
\tag{5.2}
\]

#### Proof

Suppose \(E_2\subset E_1\).  Each component \(J\) of \(S\setminus E_2\) is
the union of the components of \(S\setminus E_1\) lying in \(J\), together
with the points of \(E_1\cap J\).  This is exactly a multi-interval in
\(\mathcal I(E_1)\), so \(\mathcal I(E_1)\) refines
\(\mathcal I(E_2)\).

Conversely, suppose \(x\in E_2\setminus E_1\).  Since \(S\setminus E_1\) is
open, \(x\) lies in one interval \(J_1\in\mathcal I(E_1)\).  The point \(x\)
separates the two local sides of \(S\setminus E_2\), so \(J_1\) crosses an
endpoint of \(\mathcal I(E_2)\).  An interval of the proposed finer marking
therefore is not contained in a single interval or endpoint of the proposed
coarser marking.  A coarser interval cannot be a union of whole
\(\mathcal I(E_1)\)-intervals and their endpoints.  Refinement fails.  This
proves the reverse implication. \(\square\)

### 5.2 Pullback endpoint sets

Let \(V,V'\) be hyperbolic planar surfaces with selected prime-end boundary
circles \(S,S'\).  Let
\[
  (g,\iota):V'\rightrightarrows V
\tag{5.3}
\]
be an analytic pair.  Assume:

`M1.` \(g\) extends on \(S'\) to a finite-degree covering
\(g_\partial:S'\to S\);

`M2.` for the complete protected marking under consideration, the immersion
pullback is defined and has endpoint pullback set
\[
  E_\iota=\iota_\partial^{-1}(E)\subset S';
\tag{5.4}
\]
and

`M3.` \(E_g=g_\partial^{-1}(E)\) and \(E_\iota\) are closed and nowhere
dense.

In `M2`, \(\iota_\partial^{-1}(E)\) denotes the endpoint set determined by
the protected prime-end pullback.  A global continuous boundary extension
of \(\iota\) is sufficient but is not silently assumed.

### Theorem 5.2 (prime-end marking action criterion)

Under `M1`--`M3`, the pair (5.3) acts on
\((V,\mathcal I(E))\) if and only if
\[
  E_\iota\subset E_g.
\tag{5.5}
\]
Equivalently, every endpoint pulled back by the immersion is also an
endpoint pulled back by the covering.

#### Proof

The endpoint set of \(g^*\mathcal I(E)\) is \(E_g\), while the endpoint set
of \(\iota^*\mathcal I(E)\) is \(E_\iota\).  By the definition of action,
\(g^*\mathcal I(E)\) must refine
\(\iota^*\mathcal I(E)\).  Apply Lemma 5.1 on \(S'\). \(\square\)

### 5.3 Boundary-transition form

If \(\iota_\partial:S'\to S\) is an orientation-preserving homeomorphism,
define
\[
  \beta
  =
  g_\partial\circ\iota_\partial^{-1}:S\to S.
\tag{5.6}
\]
Then (5.5) is equivalent to
\[
  \beta(E)\subset E.
\tag{5.7}
\]
Indeed, apply \(\iota_\partial\) to
\(\iota_\partial^{-1}(E)\subset g_\partial^{-1}(E)\).

Let \(A\subset S\) be the finite set of endpoints required by the protected
access inventory, and put
\[
  E_A
  =
  \overline{\bigcup_{n\geq0}\beta^n(A)}.
\tag{5.8}
\]

### Proposition 5.3 (minimal access-orbit closure)

There exists a closed nowhere-dense set \(E\) satisfying
\[
  A\subset E,\qquad \beta(E)\subset E
\tag{5.9}
\]
if and only if \(E_A\) in (5.8) is nowhere dense.  In that case \(E_A\) is
the unique least closed set satisfying (5.9).  There exists a finite such
\(E\) if and only if every point of \(A\) has a finite forward orbit under
\(\beta\).

#### Proof

The set \(E_A\) is closed and contains \(A\).  Continuity gives
\[
  \beta(E_A)
  \subset
  \overline{\bigcup_{n\geq1}\beta^n(A)}
  \subset E_A,
\]
so it is forward invariant.  If it is nowhere dense, it itself satisfies
(5.9).

Conversely, let \(E\) be closed and satisfy (5.9).  Induction gives
\(\beta^n(A)\subset E\) for every \(n\), hence \(E_A\subset E\).  If \(E\)
is nowhere dense, every closed subset of \(E\), including \(E_A\), is
nowhere dense.  This proves the equivalence and leastness.

If every point of finite \(A\) has finite forward orbit, their union is a
finite forward-invariant set.  Conversely, a finite forward-invariant set
containing \(A\) contains the entire forward orbit of every point of \(A\),
so each such orbit is finite. \(\square\)

The invariant
\[
  \chi_{\rm mark}(A,\beta)
  =
  \mathbf 1_{\operatorname{int}(E_A)\neq\varnothing}
\tag{5.10}
\]
detects a genuine obstruction to a marking that retains every access in
\(A\) as an endpoint.  It is not a width invariant and cannot be removed by
relabelling a finite ribbon tree.

## 6. Naturality under final-root enlargement

Let \(P\preceq Q\) be two provisional packages.  Suppose their analytic
pairs are
\[
  (g_P,\iota_P):V'_P\rightrightarrows V_P,
  \qquad
  (g_Q,\iota_Q):V'_Q\rightrightarrows V_Q.
\tag{6.1}
\]
An **analytic enlargement square** consists of holomorphic embeddings
\[
  a:V_Q\hookrightarrow V_P,
  \qquad
  a':V'_Q\hookrightarrow V'_P
\tag{6.2}
\]
such that
\[
  a\circ g_Q=g_P\circ a',
  \qquad
  a\circ\iota_Q=\iota_P\circ a'.
\tag{6.3}
\]
Assume on every protected prime-end interval that \(a,a'\) extend
injectively and preserve cyclic order.  Let the endpoint sets satisfy
\[
  E_Q=a_\partial^{-1}(E_P),
  \qquad
  E_{\iota,Q}=a_\partial'{}^{-1}(E_{\iota,P}),
  \qquad
  E_{g,Q}=a_\partial'{}^{-1}(E_{g,P}).
\tag{6.4}
\]
The equalities in (6.4), rather than one-sided containment, express that no
new endpoint is silently born and no old endpoint is identified.

### Theorem 6.1 (marked-pair enlargement naturality)

Under (6.1)--(6.4), if the \(P\)-pair satisfies the endpoint condition
(5.5), then the \(Q\)-pair satisfies it.  The exact marked action commutes
with enlargement on every protected interval.  Finite compositions of such
enlargements preserve the conclusion.

#### Proof

The \(P\)-endpoint condition and the exact inverse-image equalities give
\[
  E_{\iota,Q}
  =
  a_\partial'{}^{-1}(E_{\iota,P})
  \subset
  a_\partial'{}^{-1}(E_{g,P})
  =
  E_{g,Q}.
\]
This is the \(Q\)-endpoint condition (5.5).

The commuting equalities (6.3) identify the image interval of every
component of the marked boundary complement.  Cyclic-order preservation
prevents a swap.  Hence the interval action, not merely its label, commutes.
Composition of commuting squares is a commuting square, and inverse images
in (6.4) compose.  Induction proves the finite-composition assertion.
\(\square\)

### Limitation 6.2

Theorem 6.1 does not construct (6.2)--(6.4).  A root enlargement may:

- merge selected pullback components;
- destroy a protected access;
- change a relative-cover subgroup or deck phase;
- introduce a critical value into a declared degree-one corridor;
- create a new improper ideal interval; or
- leave the authorized localization.

Each possibility must be excluded by an actual enlargement certificate.
The fixed-point closure theorem for finite records cannot prove any of these
analytic assertions.

## 7. Exact phase countermodel

The following model proves that the boundary action is indispensable.

### Proposition 7.1 (carrier data do not determine marked action)

Let
\[
  H=\{z:|z|\leq1\},
  \qquad
  V=\mathbb C\setminus H.
\]
For \(\alpha\in\mathbb R\), set
\[
  g(z)=z^2,
  \qquad
  \iota_\alpha(z)=e^{i\alpha}z.
\tag{7.1}
\]
Then \(g:V\to V\) is an unbranched proper degree-two holomorphic covering and
\(\iota_\alpha:V\to V\) is a conformal automorphism.  They have the same
carrier, degree, and component data for every \(\alpha\).

Let \(E=\{1\}\) on the prime-end circle.  The pair
\((g,\iota_\alpha)\) acts on \(\mathcal I(E)\) if and only if
\[
  \alpha\equiv0\ \text{or}\ \pi\pmod{2\pi}.
\tag{7.2}
\]

#### Proof

On the unit circle,
\[
  E_g=g_\partial^{-1}(E)=\{1,-1\},
  \qquad
  E_{\iota_\alpha}
  =\iota_{\alpha,\partial}^{-1}(E)
  =\{e^{-i\alpha}\}.
\tag{7.3}
\]
By Theorem 5.2, the pair acts exactly when
\(\{e^{-i\alpha}\}\subset\{1,-1\}\), which is equivalent to (7.2).
\(\square\)

In angular coordinates \(t\in\mathbb R/\mathbb Z\), with
\(a=\alpha/(2\pi)\), the boundary transition is
\[
  \beta_a(t)=2t-2a\pmod1.
\tag{7.4}
\]
The translation \(h_a(t)=t-2a\) conjugates (7.4) to doubling:
\[
  h_a\circ\beta_a=2h_a\pmod1.
\tag{7.5}
\]
Choose \(a\) so that \(-2a\) has dense orbit under doubling.  Then the orbit
closure (5.8) of the protected endpoint \(0\) is the entire circle.  By
Proposition 5.3, no closed nowhere-dense forward-invariant endpoint set can
retain that access.

Such an \(a\) exists explicitly.  Let \(x\in[0,1)\) have binary expansion
obtained by concatenating, in lexicographic order, every finite binary word
(with a separator convention chosen once to avoid the two expansions of a
dyadic rational).  Every finite binary word occurs in this expansion.
Multiplication by \(2\) shifts the binary expansion, so the forward orbit of
\(x\) meets every binary cylinder and is dense in the circle.  Taking
\(a=-x/2\pmod1\) gives \(-2a=x\).

This is not a counterexample to the virtual theorem: it does not assert that
the offending phase occurs in an actual virtual-Molecule block.  It is a
counterexample to the implication from the previously listed generic
prerequisites to exact marked action.  A basepoint, deck phase, and
access-transition record are necessary.

## 8. Replacement invariant and source-facing certificates

For every provisional package \(P\) and word \(r\), the required boundary
record is
\[
  \mathfrak M(P,r)
  =
  \left(
    E_{P,r},
    E^\iota_{P,r},
    E^g_{P,r},
    \beta_{P,r},
    \theta_{P,r},
    [G'_{P,r}\xrightarrow{\iota_*}G_{P,r}],
    \mathsf{Prop}_{P,r}
  \right).
\tag{8.1}
\]
Here:

1. \(E_{P,r}\) is the complete target endpoint set;
2. \(E^\iota_{P,r}\) and \(E^g_{P,r}\) are the two actual pulled endpoint
   sets;
3. \(\beta_{P,r}\) is the boundary transition wherever the immersion
   pullback is single-valued;
4. \(\theta_{P,r}\) is the normalized deck/phase choice;
5. the subgroup arrow records the relative-cover lifting condition;
6. \(\mathsf{Prop}_{P,r}\) records proper, end-proper, and improper
   intervals separately; and
7. the certificate requires
   \[
     E^\iota_{P,r}\subset E^g_{P,r}
   \tag{8.2}
   \]
   together with (6.3)--(6.4) under enlargement.

Three source-facing obligations remain.

### `VIRTUAL_RETURN_BRANCH_LANGUAGE` (open)

For every actual virtual-Molecule block, construct the typed graph (3.1)
before the Wave horizon, prove that its actual path language contains every
branch that any admissible Wave continuation can request, and prove complete
critical, component, obstacle, localization, and access metadata for every
edge.

### `VIRTUAL_PROVISIONAL_COMPLEMENT_PAIR` (open)

For every finite provisional root package and compatible path, construct a
nondegenerate full carrier satisfying the forward-coherence and
critical-value hypotheses of Theorem 4.1, construct compatible cusp-free
localizations, and verify the selected component itinerary and
absorb-or-separate ledger.

### `VIRTUAL_ACCESS_ACTION_CERTIFICATE` (open)

For every pair above, construct (8.1), prove (8.2), prove every required
proper/end-proper assertion, and prove (6.3)--(6.4) for every certified
collision-free enlargement.  The phase \(\theta_{P,r}\) must be fixed by an
actual base access or equivalent normalization; existence of an unbased
relative-cover lift is insufficient.

These obligations are independent of a completed Wave horizon.  Once they
are proved, Theorems 3.1, 4.1, 5.2, and 6.1 assemble the actual marked
correspondence, after which the resolved Wave-horizon compiler can run.

## 9. Dependency correction

The previous ledger listed only:

- `ROOT_PULLBACK_FOREST_EQUIVALENCE`;
- `RELATIVE_COVER_LIFT`;
- `PRIME_END_RETURN`;
- `FINITE_LOCAL_SATURATION`;
- `PROTECTED_REGULATED_CONNECTOR_REALIZATION`; and
- `CRITICAL_VALUE_CORRIDOR_CRITERION`.

Those theorems are necessary but not sufficient.  Proposition 7.1 satisfies
the generic carrier, covering, and prime-end requirements while changing
only the immersion phase; the marking action changes.  Therefore an
inference from those six nodes directly to
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE` is invalid.

The corrected dependency is:
\[
\begin{split}
 &\texttt{VIRTUAL\_RETURN\_BRANCH\_LANGUAGE}\\
 {}\land{}&
 \texttt{VIRTUAL\_PROVISIONAL\_COMPLEMENT\_PAIR}\\
 {}\land{}&
 \texttt{VIRTUAL\_ACCESS\_ACTION\_CERTIFICATE}\\
 {}\land{}&
 \texttt{MARKED\_PAIR\_ENLARGEMENT\_NATURALITY}\\
 &\Longrightarrow
 \texttt{VIRTUAL\_WAVE\_MARKED\_CORRESPONDENCE}.
\end{split}
\tag{9.1}
\]

Equation (9.1) is not circular: all three virtual inputs are quantified over
finite provisional packages and finite return paths defined before the Wave
stopping execution.

## 10. Skeptic audit

1. **A graph is not a branch.**  Every edge in (3.1) must carry an actual
   holomorphic map and actual components.
2. **A finite number of calls is not an iterate bound.**  Equation (3.4)
   stores the exact sum.
3. **Atom invariance is not carrier invariance.**  Theorem 4.1 explicitly
   assumes \(R(H)\subset H\).
4. **Critical-orbit containment is typed.**  Corollary 4.2 retains every
   critical value of the full iterate, not only the terminal critical
   value.
5. **Infinity is not hidden.**  The global plane complement has an outer
   end; cusp-free localization is a separate obligation.
6. **Prime-end circles do not imply marked action.**  Theorem 5.2 requires
   the endpoint containment (5.5).
7. **A relative-cover lift is not normalized.**  Proposition 7.1 detects the
   missing phase.
8. **Countable markings are not automatic.**  The orbit closure must be
   nowhere dense; a dense access orbit is fatal for this endpoint marking.
9. **Labels do not prove naturality.**  The analytic squares (6.3) and exact
   endpoint pullbacks (6.4) are required.
10. **Root monotonicity is insufficient.**  It does not exclude sheet
    mergers, access loss, or critical intrusion.
11. **No local connectivity is assumed.**  All boundary statements are in
    prime-end coordinates.
12. **No numerical test proves an analytic clause.**  Finite regressions
    check only the algebraic implications and countermodel arithmetic.
13. **No downstream conclusion is imported.**  No a priori bound,
    compactness, rigidity, parameter shrinking, UPTCR, or MLC assertion is
    used.

## 11. Promotion decision and immediate next construction

The four generic theorems listed in Section 1 are proved.  The actual virtual
marked correspondence is not.

The next construction is `VIRTUAL_RETURN_BRANCH_LANGUAGE`: choose one actual
virtual-Molecule block, define its horizon-independent selected branch graph
from its puzzle/renormalization localizations, and prove the edge inventory
in Items 1--9 of Section 3.  Simultaneously, each edge must record the base
access that normalizes the phase in (8.1); otherwise the language cannot feed
the marked-pair theorem.

No status of `VIRTUAL_WAVE_HORIZON_CERTIFICATE`, `VAAPC-I`, UPTCR, or MLC is
changed by this pass.

## 12. Return-atlas refinement

The subsequent pass in `virtual_return_branch_language.md` resolves the
generic analytic-composition issue left implicit in Theorem 3.1.

A directed path of edge labels is not by itself an analytic composite.
For a certified prefix
\[
 \Phi_\nu=f^{S_\nu}|_{D_\nu}:D_\nu\to Y_{\sigma_\nu}
\]
and an atomic branch \(F_b=f^{q_b}|_{A_b}\), the next child must be selected
on an actual nonempty component
\[
 C\in\pi_0\bigl(\Phi_\nu^{-1}(A_b)\bigr).
\]
Only then is the composite exactly
\[
 F_b\circ\Phi_\nu|_C=f^{S_\nu+q_b}|_C.
\]

The demand-closed analytic return-atlas compiler and its exact enlargement
naturality theorem are proved.  Complete no-birth/no-loss stability requires
a bijection on demanded branch-component pairs at every prefix; an injective
ambient embedding proves only persistence of old words.

The source-facing construction remains open and is now divided into:

1. `VIRTUAL_RETURN_BASE_ATLAS`, which supplies the actual open return
   localizations and atomic analytic branches; and
2. `VIRTUAL_WAVE_DEMAND_SCHEMA`, which supplies the frozen, proof-complete
   continuation relation before the stopping execution.

The need for the first input is exact.  For \(f(z)=z^2-1\) and compact seed
\(\{-1\}\), the return times to \(D(-1,1/4)\) and
\(D(-1/2,3/4)\) are two and one.  Thus the compact seed does not determine
the return branch.

These two open inputs feed `VIRTUAL_RETURN_BRANCH_LANGUAGE`; no later
virtual obligation is promoted.

## 13. Native return-base positive control and selector refinement

The next source pass proves `NATIVE_PRINCIPAL_NEST_RETURN_ATLAS` from
Lyubich's Markov-puzzle and principal-nest return theory.  For a specified
returning native level \(n\ge2\), the open base
\(\operatorname{int}V^{n-1}\) is nice and has actual proper return
components with exact iterate and degree words, together with Jordan
prime-end markings.

This does not discharge `VIRTUAL_RETURN_BASE_ATLAS`.  The missing bridge is
now recorded as `VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`: at every intermediate
virtual copy index it must select the embedded nice base, place the
completed virtual carrier and retained orbit inside it, match every frozen
Wave access and obstacle, and provide exact provisional-to-final
enlargement maps.  A neighborhood given only up to isotopy is insufficient;
the concentric \(z^2-1\) disk example changes return time inside one
explicit relative-isotopy class.

Thus the refined order is

\[
\texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}
\longrightarrow
\texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}
\longrightarrow
\texttt{VIRTUAL\_RETURN\_BRANCH\_LANGUAGE}.
\]

The selector and both source-facing consequences remain open.

## 12. Direct-decoration multi-base update

The first direct-decoration pass now supplies the exact initial analytic
chain

\[
A_0\to A_1\to\cdots\to A_{P-1}\to B,
\qquad A_0\hookrightarrow B,
\]

with one quadratic step and all later steps univalent.  This is stronger
than a component-label action and is the correct analytic skeleton for a
marked correspondence.

The marked correspondence still cannot be promoted.  The primitive
little Julia sets \(K_i\subset A_i\) are pairwise disjoint, and the source
does not construct the continuum in \(J(f)\) joining them.  In particular,
the first attachment access of the first excluded component \(K_1\) is
undefined, so the endpoint pullback/refinement criterion cannot yet be
checked.  The raw decoration fan also has \(2^n\) accesses.  Protected
connector realization and either a bounded proof-complete access selection
or future-faithful compression of the demanded subset are now the two
explicit first-scale inputs before any full Wave-horizon transport.
