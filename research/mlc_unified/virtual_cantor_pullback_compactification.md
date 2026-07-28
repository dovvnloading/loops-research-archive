# Direct-decoration pullback compactification and the scale-two marking gate

## 1. Result and logical status

This pass makes the first analytic construction downstream of
`virtual_cantor_package_interface.md`.  It works in the directly attached
non-principal-decoration category of Kahn--Lyubich.  It does **not** solve
virtual renormalization at every intermediate satellite scale.

The source supplies an actual puzzle disk \(P\), an actual iterate

\[
g=f^q,
\]

and two actual univalent pullbacks

\[
g:Q_0\longrightarrow P,
\qquad
g:Q_1\longrightarrow P,
\qquad
Q_0,Q_1\subset P.
\tag{1.1}
\]

Starting with the terminal primitive small filled Julia set \(K_0\) in
the escape gap, these branches construct:

1. a rooted binary family of actual preterminal Julia continua
   \(K_w\), \(w\in\{0,1\}^{<\mathbb N}\);
2. a compact end space \(\{0,1\}^{\mathbb N}\);
3. an actual connected nested puzzle fiber \(E_\omega\) at every end;
4. a compact planar union whose connected components are precisely the
   finite pullbacks and end fibers;
5. exact branch, nesting-parent, shift, sheet, time, and root-transition
   data; and
6. exact naturality for every root enlargement that remains in the
   same puzzle gap.

This proves the narrow obligation

```text
DIRECT_DECORATION_PULLBACK_COMPACTIFICATION
```

and the abstract enlargement result

```text
PULLBACK_GAP_ENLARGEMENT_NATURALITY.
```

The construction does not identify every \(E_\omega\) as a small Julia
set, does not transfer the satellite marking of
\(\mathcal M^{(2)}\) to these fibers, and does not show that the final
terminal Hubbard carrier remains in the root gap.  The first undefined
scale-two field is now the **disconnected marking-transfer map**, not the
outer address space.  The corresponding obligation

```text
VIRTUAL_DISCONNECTED_MARKING_TRANSFER
```

is open.  `VIRTUAL_CANTOR_PACKAGE_REALIZATION`, VAAPC-I, UPTCR, and MLC
remain open.

## 2. Source lock

### 2.1 Decoration puzzle

The source is J. Kahn and M. Lyubich,
*A priori bounds for some infinitely renormalizable quadratics. II.
Decorations*, arXiv:math/0609046.  The checked file is

```text
source-lock/KL08/
  kingdom.tex
SHA-256:
5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
```

The proof uses the following exact ranges.

| Lines | Imported statement |
|---|---|
| 21--60 | the marked Yoccoz puzzle and connected puzzle traces \(K(f)\cap Y\) |
| 68--86 | the candidate satellite quadratic-like map \(f^q\) and its non-escaping set |
| 90--107 | the least escape number \(n\), escape route, and \(V^0=Y^{nq+1}\) |
| 116--130 | the separator \(P=Y^{(n-1)q+1}\) and dyadic pullback labels |
| 133--155 | the two univalent \(f^q\)-pullbacks \(Q_0,Q_1\subset P\) and their iterates |
| 181--233 | the modified nest, the terminal primitive map, and analytic extensions |

The source constructs the maps in (1.1).  No symbolic word is used to
invent a branch.

### 2.2 Generalized return source

The auxiliary source is J. Kahn and M. Lyubich,
*Local connectivity of Julia sets for unicritical polynomials*,
arXiv:math/0505194.  The checked file is

```text
source-lock/KL09/
  kingdom.tex
SHA-256:
2DF0B51CB7DC8BB421AD72684F187D3502A7CA8599F10CDF9DAC9A7E844253BA
```

Lines 7--54 define actual generalized polynomial-like first returns.
Lines 183--223 give the modified nest by actual iterates.  Lines
227--280 place the first kingdom and terminal primitive
renormalization.

### 2.3 Virtual source boundary

Dudko's arXiv:2512.24171, lines 875--892 of the locked source, supplies
the satellite-copy chain and proposes connected hulls of corresponding
Cantor small Julia sets.  KKL arXiv:2606.27272, lines 299--303 and
326--390 of the locked source, classifies the virtually-satellite
regime and explicitly defers virtual renormalization to separate work.

Neither source proves that the end fibers constructed below are the
intended scale-\(s\) small Julia sets.  Neither transfers the next
satellite marking through a disconnected intermediate map.  Those facts
are not imported.

## 3. Analytic datum

Fix a quadratic polynomial

\[
f(z)=z^2+c
\]

in the direct-decoration setting of
`FIRST_DECORATION_SCALE_ESCAPE_ATLAS`.  Assume:

1. the marked satellite rotation is \(p/q\), \(q>1\);
2. \(n\) is the least escape number;
3. \(V^0=Y^{nq+1}\) is the escape piece;
4. \(P=Y^{(n-1)q+1}\), so \(V^0\subset P\);
5. \(K_0\Subset\operatorname{int}V^0\) is the small filled Julia set of
   the terminal primitive renormalization;
6. \(K(f)=J(f)\).

Assumption 6 is stated explicitly so that no Fatou classification is
hidden in the argument.  It holds in the periodically repelling
polynomial category used by the later KKL interface.  The construction
through Section 7 remains valid in \(K(f)\) without Assumption 6; that
assumption is used only to place every resulting continuum literally in
\(J(f)\), as required by Dudko's proposal.

By the decoration source, \(P,Q_0,Q_1\) are closed Jordan puzzle pieces,
\(Q_0,Q_1\subset P\) are pairwise disjoint, and \(g=f^q\) maps each
\(Q_a\) univalently and properly onto \(P\).  In particular, these
degree-one proper maps are homeomorphisms of the closed Jordan pieces.  Let

\[
\phi_a:P\longrightarrow Q_a,
\qquad a\in\{0,1\},
\tag{3.1}
\]

be the inverse branches.  Thus

\[
g\circ\phi_a=\operatorname{id}_P.
\tag{3.2}
\]

These closed-piece and boundary-homeomorphism assertions are hypotheses of
every result below; disjoint interiors alone would not suffice.  The
source also places the interiors of \(Q_0,Q_1\) away from the escape piece,
with only the declared boundary-ray contacts.  Since
\(K_0\Subset\operatorname{int}V^0\), we have

\[
K_0\cap(Q_0\cup Q_1)=\varnothing.
\tag{3.3}
\]

Equation (3.3), rather than a drawing of the puzzle, is the root-gap
hypothesis used below.

The closed-piece separation deserves an explicit check.  The source
defines puzzle pieces as closed Jordan disks and \(Q_0,Q_1\) as two
distinct univalent pullback components.  If their closures met at \(z\),
then \(z\) would be a regular point of \(g\) on the pullback locus.  A
sufficiently small Jordan half-neighborhood of \(g(z)\) in \(P\) has a
unique inverse under the local homeomorphism at \(z\).  Both alleged
pullback components would contain that same inverse half-neighborhood,
contradicting their being distinct components.  Hence the closed pieces
are disjoint.  Moreover, each proper degree-one continuous map
\(g:Q_a\to P\) is a continuous bijection from a compact space to a
Hausdorff space and therefore a homeomorphism, including on the boundary.
These are the boundary facts used in every sibling-cylinder separation.

## 4. Address compactification

Let \(A=\{0,1\}\).  Write \(A^{<\mathbb N}\) for finite words, including
the empty word \(\varnothing\), and \(A^{\mathbb N}\) for one-sided
infinite words.

Introduce a terminal symbol \(\#\notin A\) and define

\[
\Omega_\partial
=
\{w\#^\infty:w\in A^{<\mathbb N}\}
\cup
A^{\mathbb N}
\subset
\{0,1,\#\}^{\mathbb N}.
\tag{4.1}
\]

The ambient product has the discrete topology on
\(\{0,1,\#\}\).

### Lemma 4.1 (compact rooted-end address space)

\(\Omega_\partial\) is compact and metrizable.  Every finite word is an
isolated point.  A sequence of finite words \(w_j\), with
\(|w_j|\to\infty\), converges to
\(\omega\in A^{\mathbb N}\) exactly when every fixed prefix of
\(\omega\) is eventually a prefix of \(w_j\).

#### Proof

The product \(\{0,1,\#\}^{\mathbb N}\) is compact and metrizable.  A
sequence belongs to \(\Omega_\partial\) precisely when either it never
contains \(\#\), or its first \(\#\) is followed only by \(\#\)'s.
The complement is the union of cylinders containing a symbol \(0\) or
\(1\) after a previous \(\#\), and is therefore open.  Hence
\(\Omega_\partial\) is closed and compact.

The cylinder determined by \(w\#\) contains only \(w\#^\infty\) in
\(\Omega_\partial\), so finite words are isolated.  Product convergence
to an infinite binary sequence is exactly eventual agreement on every
finite prefix. \(\square\)

## 5. Actual cylinders and component fibers

For a finite word \(w=a_1\ldots a_m\), put

\[
\phi_w=\phi_{a_1}\circ\cdots\circ\phi_{a_m},
\qquad
Q_w=\phi_w(P),
\tag{5.1}
\]

with \(\phi_\varnothing=\operatorname{id}\) and
\(Q_\varnothing=P\).

Define the finite pullback continuum

\[
K_w=\phi_w(K_0).
\tag{5.2}
\]

For an infinite address
\(\omega=a_1a_2\ldots\), define

\[
E_\omega
=
\bigcap_{m\ge1}Q_{\omega|m},
\tag{5.3}
\]

where \(\omega|m=a_1\ldots a_m\).

### Lemma 5.1 (cylinder properties)

For every finite word \(w\):

1. \(Q_w\) is a compact connected puzzle disk;
2. \(g^{|w|}:Q_w\to P\) is univalent;
3. \(K_w\) is a nonempty compact connected subset of \(J(f)\);
4. if \(a\in A\), then \(Q_{wa}\subset Q_w\);
5. if neither of \(u,v\) is a prefix of the other, then
   \(Q_u\cap Q_v=\varnothing\).

#### Proof

Items 1--2 follow by induction from (3.1).  A univalent inverse image of
a compact connected set is compact and connected, proving the first
part of Item 3.  Since \(K_0\subset J(f)\) and Julia sets are completely
invariant,

\[
K_w\subset f^{-q|w|}(J(f))=J(f).
\]

For Item 4,
\[
Q_{wa}=\phi_w(\phi_a(P))\subset\phi_w(P)=Q_w.
\]

For Item 5, let \(r\) be the longest common prefix and write
\(u=ra u'\), \(v=rb v'\), \(a\ne b\).  Then

\[
Q_u\subset\phi_r(Q_a),
\qquad
Q_v\subset\phi_r(Q_b).
\]

The sets \(Q_a,Q_b\) are disjoint, and \(\phi_r\) is injective.
Therefore \(Q_u\cap Q_v=\varnothing\). \(\square\)

### Lemma 5.2 (end fibers)

For every \(\omega\in A^{\mathbb N}\), \(E_\omega\) is a nonempty compact
connected subset of \(J(f)\).  If \(\omega\ne\nu\), then

\[
E_\omega\cap E_\nu=\varnothing.
\tag{5.4}
\]

#### Proof

The sequence

\[
Q_{\omega|1}\supset Q_{\omega|2}\supset\cdots
\]

is nested and consists of nonempty compact connected sets.  Its
intersection is therefore nonempty, compact, and connected.

Every point \(z\in E_\omega\) has

\[
g^m(z)\in P
\qquad(m\ge0).
\]

The finitely many intermediate images
\(f^r(P)\), \(0\le r<q\), form a bounded set.  Hence the full
\(f\)-orbit of \(z\) is bounded, so \(z\in K(f)=J(f)\).

For distinct \(\omega,\nu\), choose their first differing symbol.
Their corresponding cylinders at that finite depth are disjoint by
Lemma 5.1, and contain \(E_\omega,E_\nu\), respectively.  This proves
(5.4). \(\square\)

## 6. Root-gap separation

The finite and infinite fibers must also be separated from their
ancestors.  This is where (3.3) is used.

### Lemma 6.1 (finite-fiber disjointness)

The continua \(K_w\), \(w\in A^{<\mathbb N}\), are pairwise disjoint.
Every \(K_w\) is disjoint from every end fiber \(E_\omega\).

#### Proof

Let \(u\ne v\).

If neither word is a prefix of the other, Lemma 5.1 places \(K_u\) and
\(K_v\) in disjoint cylinders.

Suppose \(v=ua v'\) for \(a\in A\).  Then

\[
K_u=\phi_u(K_0),
\qquad
K_v\subset\phi_u(Q_a).
\]

Equation (3.3) and injectivity of \(\phi_u\) imply
\(K_u\cap K_v=\varnothing\).

For \(K_w\) and \(E_\omega\), either \(\omega\) differs from \(w\) before
\(|w|\), in which case disjoint cylinders separate them, or \(w\) is a
prefix of \(\omega\).  In the latter case, writing the next symbol as
\(a\),

\[
E_\omega\subset\phi_w(Q_a),
\qquad
K_w=\phi_w(K_0),
\]

and (3.3) again gives disjointness. \(\square\)

## 7. Compact planar component package

Define

\[
\mathcal H_\partial
=
\bigcup_{w\in A^{<\mathbb N}}K_w
\ \cup\
\bigcup_{\omega\in A^{\mathbb N}}E_\omega.
\tag{7.1}
\]

Define the set-valued realization

\[
\Xi_\partial:\Omega_\partial
\longrightarrow
\{\text{nonempty compact connected subsets of }J(f)\}
\tag{7.2}
\]

by

\[
\Xi_\partial(w\#^\infty)=K_w,
\qquad
\Xi_\partial(\omega)=E_\omega.
\tag{7.3}
\]

### Theorem 7.1 (`DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`)

In the analytic setting of Section 3:

1. \(\mathcal H_\partial\) is compact;
2. the connected components of \(\mathcal H_\partial\) are exactly the
   sets in (7.3);
3. \(\Xi_\partial\) has closed graph, hence is upper
   semicontinuous in the Hausdorff hyperspace;
4. on the domain consisting of non-root finite addresses and all infinite
   addresses, the partial dynamical shift
   \(\sigma_{\rm pre}\) is given by deletion of the first symbol, and for
   \(a\in A\),

   \[
   g(K_{aw})=K_w,
   \qquad
   g(E_{a\omega})=E_\omega;
   \tag{7.4}
   \]

5. every arrow in (7.4) is an actual univalent branch of \(f^q\);
6. the exact nesting-parent, dynamical-shift, sheet, and time data are

   \[
   \operatorname{gpar}(wa)=w,\qquad
   \sigma_{\rm pre}(aw)=w,\qquad
   \operatorname{sheet}(aw)=a,\qquad
   r(aw\to w)=q;
   \tag{7.5}
   \]

7. \(\sigma_{\rm pre}\) is undefined at the empty word.  The empty word is
   the declared critical root, and its separate forward transition is

   \[
   g(K_\varnothing)=f^q(K_0)
   =K^{\rm term}_{q\bmod P_{\rm term}}
   \tag{7.6}
   \]

   in the terminal primitive cycle; this root transition is recorded by a
   separate arrow \(\tau_{\rm root}\), not by extending the deletion shift;
8. the construction is determined by the fixed marked puzzle, its
   actual pullback components, and \(K_0\); changing only the verbal
   presentation changes none of the embedded sets or maps.

The theorem constructs a compact rooted pre-Julia component package.  It
does not assert that the end fibers are renormalization Julia sets.

#### Proof

##### Step 1: compactness

Every set in (7.1) lies in the compact disk \(P\).  It is enough to prove
that \(\mathcal H_\partial\) is closed.

Let \(x_j\in\mathcal H_\partial\) and \(x_j\to x\in P\).  Choose labels
\(\xi_j\in\Omega_\partial\) with
\(x_j\in\Xi_\partial(\xi_j)\).  Compactness of \(\Omega_\partial\)
gives a subsequence \(\xi_j\to\xi\).

If \(\xi=w\#^\infty\) is finite, Lemma 4.1 makes it isolated.  Hence
\(\xi_j=\xi\) eventually and
\(x\in K_w\).

If \(\xi=\omega\in A^{\mathbb N}\), then for every fixed \(m\), all
sufficiently large labels \(\xi_j\) extend \(\omega|m\).  Therefore

\[
x_j\in Q_{\omega|m}
\]

for all sufficiently large \(j\).  Since \(Q_{\omega|m}\) is closed,
\(x\in Q_{\omega|m}\).  This holds for every \(m\), so
\(x\in E_\omega\).  Thus \(\mathcal H_\partial\) is closed and compact.

The same argument proves that the graph of \(\Xi_\partial\) is closed.
For compact-valued maps from a compact metric space to a compact metric
hyperspace, the closed-graph condition is the sequential form of upper
semicontinuity.  This proves Items 1 and 3.

##### Step 2: connected components

Lemmas 5.2 and 6.1 show that all sets in (7.3) are pairwise disjoint
continua.

We verify that no connected subset of \(\mathcal H_\partial\) meets two
of them.  Two distinct end fibers are separated by disjoint cylinders at
their first differing symbol.  A finite fiber and a label outside its
cylinder are separated at the first differing symbol.  If a finite
fiber \(K_w\) and another label share prefix \(w\), then \(K_w\) lies in
\(\phi_w(K_0)\), while every strict descendant lies in
\(\phi_w(Q_0\cup Q_1)\).  These are disjoint compact sets by (3.3).
Their inverse images under the injective \(\phi_w\) give disjoint
relative neighborhoods in \(\mathcal H_\partial\).

Thus each set in (7.3) is a maximal connected subset of
\(\mathcal H_\partial\), proving Item 2.

##### Step 3: branch action

For a finite word \(w\),

\[
g(K_{aw})
=g(\phi_a(\phi_w(K_0)))
=\phi_w(K_0)
=K_w
\]

by (3.2).

For an end,

\[
E_{a\omega}
=
\bigcap_{m\ge1}Q_{(a\omega)|m}
\subset Q_a.
\]

The restriction \(g:Q_a\to P\) is a homeomorphism.  A homeomorphism
commutes with intersections, and deleting the first cylinder gives

\[
g(E_{a\omega})
=
\bigcap_{m\ge1}Q_{\omega|m}
=E_\omega.
\]

This proves (7.4).  The branch lies in \(Q_a\), which avoids the unique
critical point because it is a univalent pullback.  Deleting the first
symbol gives the dynamical shift, while deleting the last symbol gives
the geometric cylinder parent.  Reading the deleted first symbol gives
the inverse sheet.  This proves (7.5).

At the empty word there is no inverse symbol to delete, so
\(\sigma_{\rm pre}\) is genuinely partial.  The root is \(K_0\), and the
actual iterate is \(f^q\).  Since
\(\{K_i^{\rm term}=f^i(K_0)\}_{i\in\mathbb Z/P_{\rm term}\mathbb Z}\) is
the terminal cycle, (7.6) follows.  Equation (7.6) is the separately typed
root arrow \(\tau_{\rm root}\), not an extension of the symbol-deletion
rule.  It is not an assertion that the planar set
\(K^{\rm term}_{q\bmod P_{\rm term}}\) never re-enters another selected
cylinder.
That is a separate return test.  The root is the only selected component
containing the critical point.

##### Step 4: fixed-map invariance

Equations (5.1)--(5.3) recover every field from the embedded puzzle
piece \(P\), the two connected pullback components of \(g^{-1}(P)\)
inside \(P\), and the embedded terminal set \(K_0\).  A different name
for the same marked objects changes no equation.  This proves Item 8.
\(\square\)

## 8. What “Cantor” has and has not been proved

The end-label set \(A^{\mathbb N}\) is the standard binary Cantor space.
Theorem 7.1 proves a pairwise-disjoint family of actual connected end
fibers indexed by it.  It also proves a countable rooted family of actual
univalent pullbacks of the terminal small filled Julia set.

It does **not** prove any of the following.

1. Every \(E_\omega\) is the filled Julia set of a quadratic-like or
   generalized polynomial-like return.
2. Every \(E_\omega\) is a point.
3. The set-valued map \(\omega\mapsto E_\omega\) is Hausdorff
   continuous.  Upper semicontinuity is all that Step 1 proves.
4. Dudko's phrase “corresponding Cantor small Julia sets” refers exactly
   to \(\{K_w\}\), exactly to \(\{E_\omega\}\), or to their union.
5. The package contains the proof-complete critical-orbit segment.

Consequently, Theorem 7.1 fills an actual component substrate but does
not promote `VIRTUAL_CANTOR_PACKAGE_REALIZATION`.

## 9. Root-enlargement naturality

Let

\[
G_{\rm gap}=P\setminus(Q_0\cup Q_1).
\tag{9.1}
\]

Let \(S\subset G_{\rm gap}\) be a nonempty compact connected set.  Define

\[
S_w=\phi_w(S)
\tag{9.2}
\]

and retain the same end fibers \(E_\omega\).

### Theorem 9.1 (`PULLBACK_GAP_ENLARGEMENT_NATURALITY`)

Suppose

\[
K_0\subset S\subset S^+\subset G_{\rm gap},
\tag{9.3}
\]

where \(S,S^+\) are compact and connected.  Then:

1. the construction of Theorem 7.1 applies to both roots;
2. \(S_w\subset S_w^+\) for every finite word \(w\);
3. the end fibers are unchanged;
4. for every \(a\in A\),

   \[
   g(S_{aw})=S_w,
   \qquad
   g(S^+_{aw})=S^+_w;
   \tag{9.4}
   \]

5. all inclusion squares commute:

   \[
   \begin{CD}
   S_{aw} @>>> S^+_{aw}\\
   @V g VV @VV g V\\
   S_w @>>> S^+_w;
   \end{CD}
   \tag{9.5}
   \]

6. sheets, parent words, branch times, and end actions are identical.

#### Proof

The proof of Theorem 7.1 used the seed only through compactness,
connectedness, and disjointness from \(Q_0\cup Q_1\).  These properties
hold for both \(S\) and \(S^+\) by (9.3).

Injectivity of \(\phi_w\) gives

\[
S_w=\phi_w(S)\subset\phi_w(S^+)=S_w^+.
\]

The end fibers depend only on \(P,Q_0,Q_1\), so they are unchanged.
Equation (9.4) follows from \(g\circ\phi_a=\operatorname{id}\), and
(9.5) follows by applying the same equality to the inclusion
\(S\hookrightarrow S^+\).  No branch or word changes, so Item 6 follows.
\(\square\)

### Exact limit of Theorem 9.1

The theorem is a topological finite-fiber safe-chamber statement.  It does
not prove that \(S\) or \(S^+\) is full, dynamically protected,
access-complete, or admissible as an analytic virtual carrier.  It also
does not prove that the
final terminal Hubbard carrier \(T_{\rm term}\) satisfies

\[
T_{\rm term}\subset G_{\rm gap}.
\tag{9.6}
\]

For an arbitrary enlargement \(S^+\subset P\), define the actual
collision ledger

\[
\begin{aligned}
\mathscr C(S^+)
= {}&
\{(u,v):u\ne v,\ \phi_u(S^+)\cap\phi_v(S^+)\ne\varnothing\}\\
&\cup
\{(u,\omega):\phi_u(S^+)\cap E_\omega\ne\varnothing\}.
\end{aligned}
\tag{9.7}
\]

If \(\mathscr C(S^+)\ne\varnothing\), order it first by
\(\max\{|u|,|v|\}\), then lexicographically.  Its first entry is the
first actual component/address collision.  If
\(S^+\not\subset G_{\rm gap}\) but \(\mathscr C(S^+)=\varnothing\), the
gap proof no longer applies, but collision has not been proved.  These
two cases must not be conflated.

Thus final-root enlargement is resolved for (9.3) and remains open
outside the gap.

## 10. Attempted scale-two marking

Now assume the parameter copy chain contains

\[
\mathcal M^{(0)}
\supsetneq
\mathcal M^{(1)}
\supsetneq
\mathcal M^{(2)}.
\tag{10.1}
\]

The first satellite rotation selects \(q\), hence the actual outer map
\(g=f^q\) and the package of Theorem 7.1.  The second inclusion in
(10.1) supplies a satellite combinatorial type relative to
\(\mathcal M^{(1)}\).  To turn it into a scale-two analytic row, one
would need a map

\[
\mu_2:
\text{the marked second-copy combinatorics}
\longrightarrow
\left\{
\begin{array}{c}
\text{actual bases inside the cylinders or end fibers,}\\
\text{actual polynomial iterates between them,}\\
\text{actual access and sheet markings}
\end{array}
\right\}.
\tag{10.2}
\]

The checked sources do not define (10.2).  The obstruction is not that
the first-level branches are symbolic: they are the actual branches
(3.1).  The obstruction is that the parameter belongs outside the first
satellite copy, so the candidate first intermediate renormalization has
escaping critical point.  The usual instruction “straighten and repeat”
does not canonically transport the second satellite portrait to every
component or end of a disconnected map.

The exact first unresolved record is

\[
\mathfrak X^{\rm mark}_2
=
\left(
\begin{array}{c}
\mathcal M^{(0)},\mathcal M^{(1)},\mathcal M^{(2)},\\
\Omega_\partial,\Xi_\partial,g,\operatorname{gpar},
\sigma_{\rm pre},\tau_{\rm root},
\operatorname{sheet},r,\\
\mu_2=\bot,\quad
\{B_{2,\xi}\}=\bot,\quad
\mathcal R_2=\bot,\quad
\chi_{\rm mark}=\bot
\end{array}
\right).
\tag{10.3}
\]

Unlike the earlier type certificate, (10.3) has an actual outer address
space, actual embedded continua, a partial pre-root shift, and a separately
typed root transition.  The bottom
symbol has moved to the first second-scale marking field.

### Open Problem 10.1 (`VIRTUAL_DISCONNECTED_MARKING_TRANSFER`)

For every admissible chain (10.1), construct (10.2) and prove:

1. every selected base is an actual puzzle or generalized
   polynomial-like domain in the original \(f\)-plane;
2. every arrow is an actual iterate of \(f\);
3. on a non-root finite cylinder, the marking is equivariant under the
   univalent partial shift in (7.4), while the root obeys its separately
   declared terminal-cycle transition;
4. at an end fiber, the marking has a well-defined limiting analytic
   realization, not merely a limiting label;
5. the critical encounter occurs only at the declared root stage;
6. the construction is compatible with the terminal primitive return;
7. all proof-used accesses and obstacles are recorded;
8. the transfer is natural under every authorized final-root
   enlargement; and
9. equivalent marked presentations give the same embedded package or a
   proved canonical conjugacy.

Only after this theorem can the second-scale “small Julia” status of the
relevant fibers be asserted.

## 11. Adversarial audit

1. **Binary words treated as branches.** Rejected.  The branches
   \(\phi_a\) are first selected as the actual connected pullbacks
   \(Q_a\) of \(P\); words only record their compositions.
2. **Nested nonempty sets called connected without proof.** Rejected.
   Every \(Q_{\omega|m}\) is connected and the family is decreasing, so
   the intersection theorem applies.
3. **Bounded orbit called Julia without a hypothesis.** Rejected.
   Assumption \(K(f)=J(f)\) is explicit.
4. **Different end addresses declared disjoint from labels alone.**
   Rejected.  The proof uses disjoint actual cylinders at the first
   differing symbol.
5. **Ancestor pullbacks assumed disjoint from descendants.** Rejected.
   This uses the separate root-gap equation (3.3).
6. **Upper semicontinuity promoted to Hausdorff continuity.** Rejected.
   The theorem proves only closed graph/upper semicontinuity.
7. **End fibers called small Julia sets.** Rejected.  Their
   renormalization return remains open.
8. **The terminal cycle claimed to lie in one outer base.** Rejected.
   The root action has the explicit separately typed exit (7.6);
   \(\sigma_{\rm pre}\) is not extended through the root.
9. **Gap enlargement promoted to arbitrary enlargement.** Rejected.
   The theorem is topological finite-fiber naturality only, and Equation
   (9.7) is mandatory outside the safe chamber.
10. **A gap breach called a collision.** Rejected.  A collision requires
    an actual nonempty intersection in (9.7).
11. **The second parameter copy called an embedded second base.**
    Rejected.  The missing map is exactly (10.2).
12. **Disconnected straightening assumed canonical.** Rejected.  Open
    Problem 10.1 asks for an original-plane construction or a proved
    marked conjugacy.
13. **One direct-decoration block promoted uniformly.** Rejected.
    The theorem has the explicit hypotheses of Section 3.
14. **A computational tree picture used as analytic evidence.**
    Rejected.  Regressions test only the address and collision bookkeeping.

## 12. Promotion decision

The justified statuses after this pass are:

```text
KL_DECORATION_ESCAPE_PUZZLE                 imported
FIRST_DECORATION_SCALE_ESCAPE_ATLAS         proved
DIRECT_DECORATION_PULLBACK_COMPACTIFICATION proved
PULLBACK_GAP_ENLARGEMENT_NATURALITY         proved
VIRTUAL_DISCONNECTED_MARKING_TRANSFER       open
VIRTUAL_CANTOR_PACKAGE_REALIZATION           open
VIRTUAL_PROOF_USE_TRACE_SELECTOR             proved (conditional interface)
VIRTUAL_VERTEX_PACKAGE_SELECTOR              open
VIRTUAL_SCALE_TO_PUZZLE_SELECTOR             open
VIRTUAL_WAVE_HORIZON_CERTIFICATE             open
VAAPC-I                                     open
UPTCR                                       open
MLC                                         open
```

The immediate next analytic task is no longer to guess
\(\Omega_2\).  It is to construct the first actual second-scale base
\(B_{2,\xi}\) and iterate for a finite outer cylinder, prove equivariance
under (7.4), and then decide whether this construction converges to an
analytic base on every end fiber.  Failure must identify the first
cylinder, return time, access, or end at which the marking ceases to be
defined.

## 13. Full-fiber and protected-cell strengthening

The co-agent research push recorded and audited in
`research_push_1_assessment_and_integration.md` yields the following
strengthening of the already realized direct-decoration package.  Every
statement in this section retains the exact hypotheses of Section 3.  It
does not apply to an unconstructed deeper virtual scale.

### Theorem 13.1 (`DIRECT_DECORATION_FULL_FIBERS`)

Every finite pullback \(K_w\) and every end fiber \(E_\omega\) is a full
continuum.

#### Proof

The terminal filled Julia set \(K_0\) is full.  Every homeomorphism
\(\phi_w:P\to Q_w\) of closed Jordan disks extends to a sphere
homeomorphism by extending its boundary map across the complementary
Jordan disks.  Thus \(K_w=\phi_w(K_0)\) is full.

For an end address, the complements of the nested closed Jordan disks
\(Q_{\omega|m}\) are connected, increase with \(m\), and contain
infinity.  Hence
\[
  \widehat{\mathbb C}\setminus E_\omega
  =
  \bigcup_m
  \left(\widehat{\mathbb C}\setminus Q_{\omega|m}\right)
\]
is connected. \(\square\)

### Theorem 13.2 (`DIRECT_DECORATION_GLOBAL_NONSEPARATION`)

The complete rooted-end compactum \(\mathcal H_\partial\) has connected
sphere complement.

#### Proof

For \(m\ge0\), set
\[
  \mathcal H_m
  =
  \bigcup_{|u|<m}K_u
  \ \cup\
  \bigcup_{|w|=m}Q_w.
\tag{13.1}
\]
Every term is full.  Equal-depth cylinders are disjoint.  Distinct finite
fibers are disjoint by Lemma 6.1.  If \(u\) is a strict prefix of \(w\),
then \(K_u\) lies outside both children of \(Q_u\), whereas \(Q_w\) lies
in one of them.  Thus (13.1) is a finite union of pairwise-disjoint full
continua, so its complement is connected.

The sets (13.1) decrease.  Their intersection is exactly
\(\mathcal H_\partial\): a point not in an explicit finite fiber must lie
at each depth in one unique compatible cylinder and therefore in the
corresponding end fiber.  The complement of the intersection is the
increasing union of the connected complements of (13.1), all containing
infinity. \(\square\)

### Lemma 13.3 (full-continuum Jordan neighborhood)

If a nondegenerate full continuum \(K\) is compactly contained in an open
set \(G\), then there is a closed Jordan disk \(D\) with
\[
  K\subset\operatorname{int}D\subset D\Subset G.
\tag{13.2}
\]

#### Proof

Uniformize the simply connected exterior of \(K\) by
\(\psi:\{|z|>1\}\to\widehat{\mathbb C}\setminus K\).  The images of the
circles \(|z|=R\), \(R>1\), are Jordan curves.  Their filled interiors
decrease to \(K\) as \(R\downarrow1\).  If none were contained in \(G\),
compactness would put a point of the closed set
\(\widehat{\mathbb C}\setminus G\) in their intersection \(K\), a
contradiction. \(\square\)

Let \(G_0\) be the component of
\(\operatorname{int}P\setminus(Q_0\cup Q_1)\) containing \(K_0\).
Equation (3.3) gives \(K_0\Subset G_0\).  Choose \(D\) by Lemma 13.3 and
put \(D_w=\phi_w(D)\).

### Theorem 13.4 (`DIRECT_DECORATION_GAP_CELL_ATLAS`)

The closed Jordan cells \(D_w\) satisfy
\[
  K_w\subset\operatorname{int}D_w,\qquad
  D_w\Subset
  \operatorname{int}Q_w\setminus(Q_{w0}\cup Q_{w1}),
\tag{13.3}
\]
are pairwise disjoint even for ancestor--descendant words, and obey
\[
  D_w\cap\mathcal H_\partial=K_w,\qquad
  g(D_{aw})=D_w.
\tag{13.4}
\]
For every compact connected
\(S_w\Subset\operatorname{int}D_w\),
\[
  \operatorname{Fill}(S_w)
  \Subset\operatorname{int}D_w.
\tag{13.5}
\]

#### Proof

Equation (13.3) is the pullback of the root cell.  Incomparable words have
disjoint cylinders.  If \(v=uat\), the descendant cell lies in
\(Q_{ua}\), while \(D_u\) lies outside both child cylinders of \(Q_u\).
This proves cell disjointness.  The same dichotomy shows that every other
finite or end fiber misses \(D_w\), proving the first identity in (13.4).
The second follows from \(g\circ\phi_a=\operatorname{id}\).

A collar of \(\partial D_w\), joined to the exterior of \(D_w\), lies in
the unbounded component of \(\mathbb C\setminus S_w\).  Every bounded
complementary component of \(S_w\) therefore lies away from that collar,
which proves (13.5). \(\square\)

### Theorem 13.5 (`DIRECT_DECORATION_FINITE_PACKET_REPLACEMENT`)

Let \(F\subset A^{<\mathbb N}\) be finite and let each \(L_w\),
\(w\in F\), be a full continuum satisfying
\[
  K_w\subset L_w\Subset\operatorname{int}D_w.
\tag{13.6}
\]
Replacing the selected \(K_w\) by \(L_w\) in
\(\mathcal H_\partial\) gives a compact set with connected sphere
complement.

#### Proof

The isolation identity in (13.4) makes each selected \(K_w\) clopen in
\(\mathcal H_\partial\), so the replacement is compact.  For
\(m>\max_{w\in F}|w|\), make the same replacements in (13.1).  The
modified approximants remain decreasing finite unions of pairwise-disjoint
full continua and intersect in the modified rooted-end compactum.  Their
connected complements increase and share infinity. \(\square\)

### Lemma 13.6 (`PROPER_PROTECTED_IMPRESSION_EXPOSURE`)

Let \(K\Subset D^\circ\) be a nondegenerate full continuum in a closed
Jordan disk, and let \(P_{\rm prot}\subsetneq\partial K\) be compact.
There are \(x\in\partial K\setminus P_{\rm prot}\) and a Jordan arc
\(\alpha\) from \(x\) to \(\partial D\) whose interior misses \(K\).
For finitely many protected crosscut chains whose impressions have union
in \(P_{\rm prot}\), sufficiently deep collar tails miss \(\alpha\), and
if \(S\) is their connected union with \(K\), then
\[
  \alpha\cap\operatorname{Fill}(S)=\{x\}.
\tag{13.7}
\]

#### Proof

Choose \(y\in\partial K\setminus P_{\rm prot}\), let
\(\delta=\operatorname{dist}(y,P_{\rm prot})\), and choose
\(z\in D^\circ\setminus K\) with \(|z-y|<\delta/4\).  If \(x\in K\)
minimizes distance to \(z\), the segment \((x,z]\) misses \(K\), and
\[
  |x-y|\le2|z-y|<\delta/2,
\]
so \(x\notin P_{\rm prot}\).  The connected open complement of the full
continuum is arcwise connected; joining \(z\) to the exterior, extracting
a simple subarc, and stopping at the first boundary hit gives \(\alpha\).

The compact arc is disjoint from \(P_{\rm prot}\).  Nested compact
crosscut-chain closures converge setwise to their impressions, so
sufficiently deep tails lie in prescribed neighborhoods of those
impressions, chosen away from \(\alpha\).  Extending \(\alpha\) outside
\(D\) to infinity puts every point except \(x\) in the unbounded
complementary component of \(S\), proving (13.7). \(\square\)

### Theorem 13.7 (`DIRECT_DECORATION_FINITE_PROTECTED_CARRIER`)

Fix finitely many finite direct-decoration addresses and finitely many
actual protected root prime-end chains whose total impression is a proper
subset of \(\partial K_0\).  Transport sufficiently deep collar tails and
the free root port through the inverse branches.  Their packet seeds
fullify inside the pairwise-disjoint cells \(D_w\), remain isolated from
every unselected finite fiber and every end fiber, and retain their free
ports.  All ports lie in one complementary component, so the protected
regulated-connector theorem gives a carrier preserving the transported
prime ends and cyclic order.

#### Proof

Apply Lemma 13.6 at the root and transport by the
orientation-preserving \(\phi_w\).  Theorem 13.4 supplies exact
localization, isolation, and transport; Theorem 13.5 supplies a common
complement after packet fullification.  The protected free-component
criterion and protected regulated-connector theorem complete the
construction. \(\square\)

Theorem 13.7 is finite and direct-scale only.  It does not construct the
second satellite portrait, a virtual return on an end fiber, a uniform
access-incidence bound, or future fjord, dam, and attachment data.
