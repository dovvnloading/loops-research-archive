# KL canonical localization: forced excess-component collision

## 1. Result, scope, and status

This note resolves the first actual Kahn localization question left open in
`kl_localization_subgroup_reflection_gate.md`.

Let

\[
 f:U^1\longrightarrow U^0
\]

be an ordinary quadratic-like restriction of a quadratic polynomial, and
suppose that it is primitively renormalizable of period \(p>1\).  Put

\[
 F=f^p:U^p\longrightarrow U^0,\qquad
 A=K_p,\qquad
 B=\mathcal K_p=\bigcup_{j=0}^{p-1}K_p(j).
\]

Kahn's canonical renormalization is the dynamical localization of
\((i^p,F)\) at \(A\), with removal of \(B\).  Here \(i^p:U^p\hookrightarrow
U^0\) is the physical inclusion.  The source and target marked surfaces
before localization are

\[
 T'=(U^p\setminus F^{-1}B)\cup A,
 \qquad
 T=(U^0\setminus B)\cup A.                 \tag{1.1}
\]

The main theorem is:

> **Forced-collision theorem.**  The localized inclusion
> \[
>   \widehat i:T'_A\longrightarrow T_A
> \]
> is not injective.  More precisely, there is a component
> \(X\ne A\) of \(F^{-1}A\), a based loop
> \(\gamma\subset U^p\setminus F^{-1}B\), and localization subgroups
> \(H_s,H_t\) such that
> \[
>  [\gamma]\notin H_s,\qquad
>  (i^p)_*[\gamma]=1\in H_t.                \tag{1.2}
> \]
> The lift of \(\gamma\) has distinct source endpoints which
> \(\widehat i\) identifies.

This is an actual collision in Kahn's canonical-localization construction,
not an abstract annulus or abstract \(\psi\)-quadratic-like counterexample.
It uses only an ordinary primitive polynomial stage and the localization
defined in Kahn I.

The theorem also propagates through Kahn's exact pullback iteration.  If the
same canonical seed has KL direct-decoration data

\[
 P=Y^{(\nu-1)q+1},\qquad
 Q_a\subset P,\qquad a\in\{L,R\},
\]

then the bold ambient annulus map at the exact direct-decoration depths

\[
 m=\nu q+1,\qquad n=(\nu-1)q+1
\]

is noninjective.  Every induced full universal-cover tile map and the full
glued pseudo-piece inclusion are consequently noninjective.  Section 8
states the realization quantifier separately; no empty-class or
stage-alignment inference is hidden in the theorem.

This result does **not** prove VAAPC-I, UPTCR, rigidity, or MLC.  Those
statements remain open.  Its value is corrective: the full embedded
pseudo-piece cannot be the universal carrier invariant.  A valid
replacement must retain localization cosets/sheets or synchronize the
removed obstacle packet.

## 2. Source lock

The proof uses the following statements from the checked TeX source of
Jeremy Kahn, *A priori bounds for some infinitely renormalizable
quadratics. I. Bounded primitive combinatorics*,
arXiv:math/0609045.

1. `pullback.tex`, lines 2--7:
   \[
    U^r=f^{-r}(U^0),\qquad U^{r+1}\subset U^r,
   \]
   and every \(f:U^{r+1}\to U^r\) is quadratic-like.  Hence
   \(F=f^p:U^p\to U^0\) is proper of degree \(2^p\), while \(i^p\) is the
   physical inclusion.
2. `intro.tex`, lines 22--44, defines
   \[
    K_p(j)=f^j(K_p),\qquad
    \mathcal K_p=\bigcup_{j=0}^{p-1}K_p(j),
   \]
   and defines primitive renormalization by pairwise disjointness of the
   \(K_p(j)\).
3. `psiql2.tex`, lines 434--505, constructs localization.  The connected
   complement cover is the cover corresponding to the image of the
   fundamental group of a local neighborhood of the marked full
   continuum.  A morphism has a unique commuting localized lift; the
   source asserts preservation of immersion, not preservation of
   embedding.
4. `psiql2.tex`, lines 510--542, defines dynamical localization with
   \[
    T=(U\setminus B)\cup A,\qquad
    T'=(U'\setminus f^{-1}B)\cup A',
   \]
   and states that the localized \(i\)-leg is an immersion.
5. `psiql2.tex`, lines 549--558, takes
   \[
    A=K_p,\qquad B=\mathcal K_p
   \]
   after replacing \((i,f)\) by \((i^p,f^p)\).  The resulting canonical
   renormalization has local degree two at the central component.
6. `psiql2.tex`, lines 350--416, realizes the later pullback stages as the
   exact equalizers
   \[
    \mathbf U^{r+2}
    =
    \{(x,y):i_r(x)=f_r(y)\},
    \quad
    i_{r+1}(x,y)=y,\quad
    f_{r+1}(x,y)=x.                         \tag{2.1}
   \]
7. `psiql2.tex`, lines 612--619, gives the path model for canonical
   localization and proves only that source-equivalent paths become
   target-equivalent.

For the direct-decoration depth calculation, KL II,
`kingdom.tex`, lines 116--155, gives

\[
 P=Y^{(\nu-1)q+1},\qquad
 \operatorname{depth}Q_a=\nu q+1,
\]

and the univalent physical branches
\(f^q:Q_a\to P\).  KL II, `psiql.tex`, lines 169--207, treats the
dynamical pseudo-piece arrow as a covering but the inclusion pseudo-piece
arrow as an immersion.

No claim below is inferred from an abstract, title, or numerical
experiment.

## 3. The finite full-pullback lemma

The collision loop must surround an actual isolated component.  Merely
knowing that two compacta are disjoint would not be enough if infinitely
many other components accumulated on the selected one.  We therefore
prove the required finiteness and fullness first.

### Lemma 3.1 (Jordan-neighborhood basis)

Let \(K\Subset U\subset\mathbb C\) be a nonempty full continuum and let
\(\mathcal O\) be any neighborhood of \(K\) compactly contained in \(U\).
There is a Jordan domain \(V\) such that

\[
 K\subset V\subset\overline V\subset\mathcal O.             \tag{3.1}
\]

There is moreover a nested sequence of such domains satisfying

\[
 K\subset V_{r+1},\qquad
 \overline V_{r+1}\subset V_r,\qquad
 \bigcap_{r\ge1}\overline V_r=K.                            \tag{3.2}
\]

#### Proof

If \(K\) is a singleton, take round disks.  Otherwise, fullness and
connectedness make

\[
 \widehat{\mathbb C}\setminus K
\]

a simply connected domain containing infinity.  Uniformize it by the
exterior unit disk, normalized at infinity.  The inverse images of circles
\(|w|=r\), with regular radii \(r\downarrow1\), are Jordan curves in the
complement of \(K\).  Their bounded sides contain \(K\).  Choosing the
radii sufficiently close to \(1\) gives (3.1), and choosing them
monotonically gives (3.2).  The intersection is \(K\), since every point
of the complement has uniformizing modulus strictly greater than \(1\).
\(\square\)

### Lemma 3.2 (one quadratic pullback)

Let

\[
 q:U'\longrightarrow U
\]

be a proper holomorphic map of degree two between plane topological disks,
and let \(K\Subset U\) be a nonempty full continuum.  Let \(c\) be the
unique critical point and \(v=q(c)\).

1. If \(v\in K\), then \(q^{-1}K\) is one full continuum and the local
   degree on it is two.
2. If \(v\notin K\), then \(q^{-1}K\) is the disjoint union of two full
   continua, each mapped homeomorphically onto \(K\).

#### Proof

Choose the nested basis \(V_r\) from Lemma 3.1, with
\(\partial V_r\) avoiding \(v\).  If \(v\notin K\), choose
\(\overline V_1\) disjoint from \(v\).

Suppose first that \(v\notin V_r\).  Then

\[
 q:q^{-1}(V_r)\longrightarrow V_r
\]

is an unbranched proper cover of total degree two.  Since \(V_r\) is
simply connected, its inverse image has exactly two components
\(W_r^0,W_r^1\), and both restrictions are biholomorphisms.  The two
inverse branches on \(V_1\) label the components coherently, and

\[
 \overline W_{r+1}^k\subset W_r^k,\qquad k=0,1.
\]

Set

\[
 L_k=\bigcap_{r\ge1}\overline W_r^k.
\]

Each \(L_k\) is nonempty, compact, and connected.  It is full because

\[
 \mathbb C\setminus L_k
 =
 \bigcup_{r\ge1}
 \bigl(\mathbb C\setminus\overline W_r^k\bigr)
\]

is an increasing union of connected sets.  The inverse branches identify
\(L_k\) homeomorphically with \(K\), and
\(q^{-1}K=L_0\sqcup L_1\).

Now suppose that \(v\in K\).  Every \(V_r\) contains \(v\).  The component
\(W_r\) of \(q^{-1}(V_r)\) containing \(c\) already has degree at least two,
so it has degree exactly two and exhausts \(q^{-1}(V_r)\).
Riemann--Hurwitz gives

\[
 \chi(W_r)=2\chi(V_r)-1=1.
\]

Thus \(W_r\) is a disk.  Because \(\partial V_r\) contains no critical
value, \(\partial W_r\) is a regular Jordan curve.  The compact Jordan
disks \(\overline W_r\) are nested, and

\[
 q^{-1}K=\bigcap_{r\ge1}\overline W_r.
\]

The same increasing-complement argument proves that this intersection is
connected and full.

For completeness, the bordered Riemann--Hurwitz step can be obtained by
doubling \(W_r\) and \(V_r\) across their regular boundaries.  The doubled
degree-two map has the critical point and its mirror, so

\[
 2-2g=2\cdot2-2=2.
\]

Hence \(g=0\).  The double of a planar domain with \(b\) boundary
components has genus \(b-1\), so \(b=1\).  \(\square\)

### Corollary 3.3 (finite full \(p\)-fold pullback)

Under a chain of \(p\) quadratic-like pullbacks, the inverse image of one
full continuum is a union of at most \(2^p\) pairwise disjoint full
continua.  Every resulting component maps onto its parent continuum, with
positive integer degree.  The inverse image of a finite pairwise-disjoint
family of full continua is again a finite pairwise-disjoint family of full
continua.

#### Proof

Apply Lemma 3.2 successively.  Each parent has either one degree-two child
or two degree-one children, and every child is mapped onto its parent.
Children of different parents are disjoint because their images lie in
disjoint parent continua.  Induction gives the bound \(2^p\), the stated
surjectivity, and a positive product degree for every terminal component.
Applying this separately to the members of the finite family proves the
last statement.  \(\square\)

### Corollary 3.4 (isolating Jordan disks)

Let \(C_1,\ldots,C_N\Subset U\) be pairwise disjoint full continua.  For
each \(i\), there is a Jordan domain \(D_i\Subset U\) such that

\[
 C_i\subset D_i,\qquad
 \overline D_i\cap C_j=\varnothing\quad(j\ne i).             \tag{3.3}
\]

The \(D_i\) may be chosen pairwise disjoint.

#### Proof

The finite family has positive minimum pairwise distance and positive
distance from \(\partial U\).  Apply Lemma 3.1 inside pairwise-disjoint
metric neighborhoods of the \(C_i\).  \(\square\)

### Lemma 3.5 (connectivity after finitely many full deletions)

Let \(U\) be a plane topological disk and let
\(C_1,\ldots,C_N\Subset U\) be pairwise disjoint full continua.  Then

\[
 U\setminus\bigcup_{i=1}^N C_i
\]

is path connected.

#### Proof

Choose pairwise-disjoint Jordan domains

\[
 C_i\subset D_i^-,\qquad
 \overline{D_i^-}\subset D_i^+,\qquad
 \overline{D_i^+}\subset U,
\]

by applying Lemma 3.1 twice inside the disjoint neighborhoods used in
Corollary 3.4.  The finitely connected plane domain

\[
 U_0=U\setminus\bigcup_{i=1}^N\overline {D_i^-}
\]

is connected: after a homeomorphism \(U\cong\mathbb D\), removing finitely
many pairwise-disjoint closed Jordan disks compactly contained in
\(\mathbb D\) leaves a disk with finitely many holes.  As an open connected
subset of the plane, \(U_0\) is path connected.

For each \(i\), the open set \(D_i^+\setminus C_i\) is connected.  Indeed,
\(\mathbb C\setminus C_i\) is connected by fullness, and its intersection
with the Jordan disk \(D_i^+\) cannot have a component separated from the
outer collar of \(\partial D_i^+\): such a component would be a bounded
complementary component of \(C_i\).  Hence
\(D_i^+\setminus C_i\) is path connected.  It
contains the nonempty annulus
\(D_i^+\setminus\overline{D_i^-}\), which is also contained in \(U_0\).
Thus every \(D_i^+\setminus C_i\) has nonempty connected overlap with
\(U_0\).  Their union is path connected and equals

\[
 U_0\cup\bigcup_i(D_i^+\setminus C_i)
 =U\setminus\bigcup_i C_i.
\]

\(\square\)

## 4. Existence and itinerary of an excess component

### Proposition 4.1 (excess central pullback)

There is a component

\[
 X\subset F^{-1}A,\qquad X\ne A.                            \tag{4.1}
\]

Every such component satisfies

\[
 X\cap B=\varnothing.                                       \tag{4.2}
\]

#### Proof

The global map \(F:U^p\to U^0\) has degree \(2^p\).  By the definition of
the primitive quadratic-like renormalization, the central component
\(A\) has local degree two under \(F\).

Choose a sufficiently small Jordan neighborhood \(V\) of \(A\) inside
the range of the quadratic-like renormalization.  The central component
of \(F^{-1}(V)\) maps onto \(V\) with degree two.  The degrees of all
components of \(F^{-1}(V)\) sum to \(2^p\).  Since \(p>1\),

\[
 2^p-2>0,
\]

so another component \(W\) exists.  The proper map \(F:W\to V\) is onto.
It therefore contains a point of \(F^{-1}(A)\).  The component \(X\) of
\(F^{-1}(A)\) containing that point is not the central component \(A\).
This proves (4.1).

For \(0\le j<p\), write \(K_j=K_p(j)=f^j(A)\).  Since \(F=f^p\) commutes
with \(f^j\) on these sets,

\[
 F(K_j)=f^j(F(A))=f^j(A)=K_j.                               \tag{4.3}
\]

Suppose \(X\cap K_j\ne\varnothing\).  If \(j\ne0\), a point of the
intersection maps by \(F\) into both \(A\) and \(K_j\), contradicting
primitive disjointness \(A\cap K_j=\varnothing\).  If \(j=0\), then
\(X\cap A\ne\varnothing\); the two connected subsets of \(F^{-1}A\)
therefore belong to the same component, giving \(X=A\), again a
contradiction.  Hence (4.2) holds.  \(\square\)

### Complete component certificate

Corollary 3.3 makes the family of excess components finite.  Fix any
deterministic order on the finite pulled-component inventory and choose
the first \(X\).  No theorem depends on this choice.  Its complete
finite itinerary is

\[
 \tau(X)
 =
 \bigl(
   X,\ f(X),\ldots,f^p(X)=A;
   \varsigma_0,\ldots,\varsigma_{p-1}
 \bigr),                                                     \tag{4.4}
\]

where \(\varsigma_r\) records the actual component/sheet of
\(f^{-1}(f^{r+1}X)\) containing \(f^rX\).  If a stage already has external
or puzzle markings, those markings order the \(\varsigma_r\); otherwise
(4.4) is a geometric component itinerary, not an invented symbolic word.

By Corollaries 3.3--3.4, there is a Jordan domain \(D_X\Subset U^p\) with

\[
 X\subset D_X,\qquad
 \overline D_X\cap
 \bigl((F^{-1}B\setminus X)\cup B\bigr)=\varnothing.          \tag{4.5}
\]

The peripheral access used in the collision is the based homotopy class
of \(\partial D_X\).  This is a genuine access in the complement of the
actual pulled obstacle family; it is not a ribbon-tree label.

## 5. The localization subgroup defect

Set

\[
 \Omega_s=T'\setminus A=U^p\setminus F^{-1}B,
 \qquad
 \Omega_t=T\setminus A=U^0\setminus B.                       \tag{5.1}
\]

The inclusion \(a=i^p\) maps \(\Omega_s\) into \(\Omega_t\).  Indeed, if
\(z\in B\), then \(F(z)\in B\) by (4.3), so
\(z\in F^{-1}B\).

Choose a Jordan local neighborhood \(D_A\Subset T'\) of \(A\), disjoint
from every other component of \(F^{-1}B\), and choose a basepoint

\[
 z_*\in D_A\setminus A.
\]

Kahn's localization cover of \(\Omega_s\) corresponds to

\[
 H_s
 =
 \operatorname{im}\!
 \left[
  \pi_1(D_A\setminus A,z_*)\longrightarrow
  \pi_1(\Omega_s,z_*)
 \right].                                                    \tag{5.2}
\]

The target subgroup \(H_t\) is defined analogously from a local
neighborhood of \(A\) in \(T\).

The complement of the finite family \(F^{-1}B\) is path connected by
Corollary 3.3 and Lemma 3.5.
Choose a path \(\eta\subset\Omega_s\) from \(z_*\) to
\partial D_X\), and let

\[
 \gamma
 =
 \eta\cdot\partial D_X\cdot\overline\eta.                    \tag{5.3}
\]

Fix \(x\in X\).  Winding number about \(x\) gives a homomorphism on
\(\pi_1(\Omega_s,z_*)\).  Every loop representing an element of \(H_s\)
lies, before inclusion, in \(D_A\setminus A\), and \(x\notin D_A\).
Consequently

\[
 \operatorname{Ind}_x(H_s)=0.                               \tag{5.4}
\]

On the other hand, the path and reverse path in (5.3) cancel in winding
number, while \(\partial D_X\) has positive winding one about \(x\).
Thus

\[
 \operatorname{Ind}_x(\gamma)=1,
 \qquad
 [\gamma]\notin H_s.                                        \tag{5.5}
\]

Equation (4.5) gives \(D_X\cap B=\varnothing\).  Hence
\(\partial D_X\) contracts across \(D_X\) in \(\Omega_t\), and therefore

\[
 a_*[\gamma]=1\in H_t.                                      \tag{5.6}
\]

Combining (5.5)--(5.6),

\[
 a_*^{-1}(H_t)\supsetneq H_s.                               \tag{5.7}
\]

This is the exact failure of the subgroup-reflection equality, on the
actual canonical-localization data.

## 6. Point collision in the localized annulus

Let

\[
 \pi_s:\widehat\Omega_s\longrightarrow\Omega_s,
 \qquad
 \pi_t:\widehat\Omega_t\longrightarrow\Omega_t
\]

be the localization covers, and let

\[
 \widehat a:\widehat\Omega_s\longrightarrow\widehat\Omega_t
\]

be the lift of \(a\).  Choose a source lift \(\widehat z_*\) and lift
\(\gamma\) from it.  Write \(\widehat z_*'\) for the other endpoint.
By the covering-subgroup endpoint criterion and (5.5),

\[
 \widehat z_*'\ne\widehat z_*.                              \tag{6.1}
\]

The image path is the target lift of \(a\gamma\).  Equation (5.6) says
that this target lift is closed.  Therefore

\[
 \widehat a(\widehat z_*')
 =
 \widehat a(\widehat z_*).                                  \tag{6.2}
\]

Both points lie in the complementary annulus.  Adding the marked
continuum \(A\) to complete the localized marked surfaces does not
identify distinct complement-cover points.  Thus (6.1)--(6.2) are an
actual point collision of Kahn's localized inclusion

\[
 \widehat i:T'_A\longrightarrow T_A.
\]

In path language, if \(\alpha\) is any source path from the marked
base access to \(z_*\), the two classes

\[
 [\alpha],
 \qquad
 [\alpha\cdot\gamma]
\]

are distinct in the source localization and equal after target
localization.  Kahn's forward path-equivalence statement is respected;
the missing converse fails.

The collision certificate is

\[
 \mathfrak C_{\rm can}
 =
 \left(
  X,\ D_X,\ [\gamma],\ \tau(X),\
  H_s,\ H_t,\
  H_s,\ H_s[\gamma],\
  \widehat z_*,\widehat z_*',
  \widehat a(\widehat z_*)
 \right).                                                    \tag{6.3}
\]

It records the first excess component, peripheral access, complete
\(p\)-step component itinerary, source and target subgroups, distinct
source sheets, and common target point.  In the project's collision
language, at least the sheet and localization coordinates are nonzero.
No critical-value crossing or numerical approximation is used to create
the collision.

## 7. Exact propagation through Kahn's pullback dynasty

Let

\[
 (i_r,f_r):
 (\mathbf U^{r+1},K^{r+1})
 \longrightarrow
 (\mathbf U^r,K^r)
\]

be the pullback iteration of the canonical seed
\((i_0,f_0)=(\widehat i,\widehat f)\), and set

\[
 A_r=\mathbf U^r\setminus K^r.
\]

The collision (6.2) gives

\[
 x_0^+\ne x_0^-\in A_1,
 \qquad
 i_0(x_0^+)=i_0(x_0^-)=v_0\in A_0.                          \tag{7.1}
\]

Suppose inductively that

\[
 x_r^+\ne x_r^-\in A_{r+1},
 \qquad
 i_r(x_r^+)=i_r(x_r^-)=v_r\in A_r.                          \tag{7.2}
\]

The restriction

\[
 f_r:A_{r+1}\longrightarrow A_r
\]

is an unbranched surjective covering, because
\(f_r^{-1}(K^r)=K^{r+1}\).  Choose
\(y_r\in A_{r+1}\) with \(f_r(y_r)=v_r\).  In the exact equalizer (2.1),
put

\[
 x_{r+1}^{\pm}=(x_r^\pm,y_r).
\]

Then

\[
 x_{r+1}^+\ne x_{r+1}^-,
 \qquad
 i_{r+1}(x_{r+1}^{\pm})=y_r=:v_{r+1}.                       \tag{7.3}
\]

Thus a complement collision propagates to every \(i_r\).  The choices of
the \(y_r\) give the complete inverse-sheet word

\[
 \omega=(\epsilon_0,\epsilon_1,\ldots),
\]

which is appended to (6.3); no unlabeled existence step is used.

For \(m>n\), define

\[
 I_{m,n}
 =
 i_n\circ i_{n+1}\circ\cdots\circ i_{m-1}:A_m\to A_n.       \tag{7.4}
\]

At \(r=m-1\), (7.3) gives two distinct points in \(A_m\) with the same
\(i_{m-1}\)-image.  Applying the remaining factors yields

\[
 I_{m,n}(u)=I_{m,n}(v),\qquad u\ne v.                        \tag{7.5}
\]

For KL's direct-decoration pair,

\[
 m=\nu q+1,\qquad n=(\nu-1)q+1,
\]

so (7.5) is at the exact source and target depths used by
\(Q_L,Q_R\subset P\), not at an unrelated pullback depth.

Finally, \(I_{m,n}\) has annular degree \(+1\).  Let \(L\) be a compatible
universal-cover tile lift and let \(\widetilde u,\widetilde v\) lift
\(u,v\).  For a unique integer \(k\),

\[
 L(\widetilde v)=T_t^kL(\widetilde u).
\]

Degree-one equivariance gives

\[
 L(T_s^{-k}\widetilde v)=L(\widetilde u),                   \tag{7.6}
\]

at two distinct source points.  KL's construction embeds each source tile
in its source pseudo-piece, so (7.6) survives the source gluing.  It is a
same-tile collision of the full inclusion-induced pseudo-piece
immersion.

## 8. Alignment and realization quantifiers

The statements proved without further hypotheses are:

1. every first canonical localization of an ordinary primitively
   \(p\)-renormalizable quadratic polynomial, \(p>1\), has the collision
   (6.3);
2. that collision propagates through every pullback depth of that same
   seed;
3. whenever that same seed has KL direct-decoration data, the exact
   direct-decoration maps \(I_{m,n}\), their full tile lifts, and their
   full glued pseudo-piece inclusions are noninjective.

The third item is an implication about an aligned realized stage.  It does
not infer that an arbitrary abstract canonical seed has a particular
decoration.  A separate realization statement may be supplied either by:

- a named quadratic parameter whose primitive renormalization straightens
  to a non-satellite KL decoration germ; or
- the standard primitive-tuning theorem, applied to a primitive
  postcritically finite quadratic base and a non-satellite quadratic germ.

Until that realization is source-locked in the ledger, this note does not
use it to change an existential statement about a narrower parameter
subclass.  It already settles the actual canonical-localization map and
invalidates any proof that treats localization as embedding-preserving.

## 9. Replacement invariant

The failure is structural.  The source removes \(X\) because

\[
 X\subset F^{-1}B,
\]

while the target does not remove it because

\[
 X\cap B=\varnothing.
\]

Localization therefore distinguishes the two source cosets

\[
 H_s,\qquad H_s[\gamma],
\]

but target localization merges them.  A full embedded carrier cannot
forget this distinction.

Any replacement must perform at least one of the following exact
operations.

1. **Sheet retention.**  Retain the source coset and path-groupoid state
   through the immersed target instead of quotienting it to a single
   target sheet.
2. **Obstacle synchronization.**  Remove \(X\), and the finite
   forward/backward packet forced by the proof, on the target side as well;
   then recompute both localization subgroups and prove reflection.
3. **Collar truncation.**  Restrict to Kahn's embedded inner collar and
   carry every omitted outer sheet, access, and width contribution in an
   explicit defect state.
4. **Block retiming/localization revision.**  Move the interface until the
   source and target removal packets have matching peripheral components,
   then rerun the complete Wave horizon and final-root audit.

The minimal replacement state for the present collision is

\[
 \mathfrak S_{\rm loc}
 =
 \left(
  \operatorname{Comp}(F^{-1}B),\
  \{\tau(X)\},\
  H_s,H_t,\
  H_s\backslash\pi_1(\Omega_s),\
  a_*^{-1}(H_t)/H_s
 \right).                                                    \tag{9.1}
\]

The last factor is nontrivial by (5.7), and in fact infinite.  Winding
about \(x\in X\) gives a homomorphism \(w\) with
\[
 w(H_s)=0,\qquad w(\gamma)=1,\qquad\gamma\in a_*^{-1}(H_t).
\]
Hence the cosets \(\gamma^nH_s\), \(n\in\mathbb Z\), are pairwise
distinct.  A ribbon tree that identifies them to a point hides the
analytic obstruction and is not proof-faithful.  Here
\(a_*^{-1}(H_t)/H_s\) denotes the pointed set of left cosets of \(H_s\)
inside \(a_*^{-1}(H_t)\); it is not asserted to be a quotient group unless
normality of \(H_s\) is separately proved.

The follow-up theorem
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION` constructs the exact
interior carrier for the first replacement route.  With
\(K=a_*^{-1}(H_t)\), the localized lift factors uniquely as
\[
 \widehat X_s\xrightarrow qP_K\xrightarrow e\widehat X_t,
 \qquad A=e\circ q,
\]
where \(q\) is the \(H_s\)-to-\(K\) covering, \(e\) is embedded, and
the kernel pair of \(A\) is exactly the kernel pair of \(q\).  The category
of elements of the monodromy functor of this infinite cover is the required
sheet groupoid.
Exact base change propagates it through full, unselected Kahn equalizers on
the complementary-cover locus; filled completion, selected
direct-decoration component alignment, and prime-end realization remain
open.

## 10. Skeptic audit

1. **Degree-count shortcut.**  Global degree \(2^p\) is not by itself a
   component theorem.  Lemmas 3.1--3.2 first prove finite full
   pullbacks; Proposition 4.1 then uses the central local degree two.
2. **Disjoint compacta shortcut.**  Pairwise disjoint compact sets can
   have zero separation in an infinite family.  Corollary 3.3 proves that
   the relevant family is finite before Corollary 3.4 isolates \(X\).
3. **Primitive-label shortcut.**  Equation (4.2) uses actual invariance
   \(F(K_j)=K_j\) and pairwise disjoint actual continua, not equality of
   component labels.
4. **Wrong removed set.**  The source removal is
   \(F^{-1}B=f^{-p}B\), not \(B\).  The target removal is \(B\).  Their
   mismatch is the mechanism.
5. **Confusing \(A'\) and \(X\).**  For the physical inclusion,
   \(A'=(i^p)^{-1}A=A\).  The selected \(X\) is a different component of
   \(F^{-1}A\).
6. **Unbased loop shortcut.**  Equation (5.3) conjugates
   \(\partial D_X\) to the localization basepoint.  Winding is unchanged.
7. **Homology-only shortcut.**  Winding is used only to prove
   \([\gamma]\notin H_s\).  The point collision follows from the exact
   covering endpoint criterion.
8. **Filling shortcut.**  Filling the marked continuum adds \(A\); it does
   not identify two distinct points of the complement cover.
9. **Iteration shortcut.**  Propagation is performed in Kahn's exact
   equalizer (2.1), and surjectivity is used at every step.
10. **Depth mismatch.**  Section 7 substitutes KL's actual depths
    \(m=\nu q+1\) and \(n=(\nu-1)q+1\).
11. **Dynamical/inclusion-arrow conflation.**  The collision belongs to
    the inclusion arrow.  It says nothing against KL's separate
    degree-\(k\) dynamical covering arrow.
12. **Parameter-existence overreach.**  Section 8 separates the
    unconditional canonical theorem, the aligned-stage implication, and
    the still-to-be-source-locked realization witness.
13. **MLC overpromotion.**  The theorem rejects one proposed embedding
    route.  It supplies no Master Transition inequality, coercive
    compactness, rigidity, or parameter shrinking.

## 11. Ledger consequence

The following theorem may be promoted:

- `KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`.

The proposed universal full-embedding route must not remain a dependency
of the direct-decoration footprint and contact-closure chain.  Those
obligations must be restated for a sheet-sensitive immersed carrier, with
the coset defect (9.1) retained.

The following remain open:

- an aligned, source-locked parameter realization if an existential
  direct-decoration counterexample is required;
- the sheet-sensitive \(O\)- and \(J\)-side accessible-footprint theorem;
- complete path-lift exhaustion and proper/end-proper interval action;
- full Wave-horizon transport under synchronized obstacle or sheet state;
- VAAPC-I;
- UPTCR;
- MLC.
