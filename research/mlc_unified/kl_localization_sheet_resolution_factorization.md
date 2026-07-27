# KL localization: canonical sheet resolution and enlargement criteria

## 1. Result, scope, and status

This note proves the covering-space theorem needed immediately after
`KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`.

The forced-collision theorem shows that the full canonical localized
inclusion

\[
 A:\widehat X_s\longrightarrow \widehat X_t
\]

cannot be used as an embedded carrier.  The replacement is not an
informal list of duplicate labels.  There is a canonical factorization

\[
 \widehat X_s
 \xrightarrow{\ q\ }
 P_K
 \xrightarrow{\ e\ }
 \widehat X_t                                      \tag{1.1}
\]

in which:

- \(q\) is a connected covering and contains **all** localization-sheet
  identifications;
- \(e\) is an actual topological embedding;
- the fibers of \(q\) are exactly the fibers of \(A\);
- the based fiber is the pointed coset set
  \(K/H_s\), where \(K=a_*^{-1}(H_t)\);
- path lifting for \(q\) gives a transport functor whose category of
  elements is the required sheet groupoid; and
- under a change of interface, two explicit subgroup conditions are
  necessary and sufficient for bijectivity of the induced **based coset
  map**.  They do not by themselves preserve the full groupoid or geometric
  state.

The theorem is elementary covering theory, but it is proved here in full
because later prime-end, proper-path, and width arguments must use the
correct direction of every subgroup inclusion.

The theorem does **not** prove:

- that \(P_K\) has the filled pseudo-piece disk structure required by KL;
- that \(e\) extends to the complete KL prime-end marking;
- the actual \(O\)-, \(\xi\)-, or \(\eta\)-side complement footprints;
- finiteness or a uniform bound for \(K/H_s\);
- properness or end-properness on a complete ideal interval;
- stability for an actual final-root enlargement before its induced
  subgroup diagram has been constructed; or
- any width, transition, compactness, rigidity, or MLC conclusion.

Accordingly
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`,
`DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`,
`DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE`, VAAPC-I, UPTCR, and MLC
remain open.

## 2. Conventions

All spaces in Sections 3--8 are Hausdorff, connected, locally
path-connected, and semilocally simply connected.  Covers are connected and
based.  These hypotheses are satisfied by the planar complementary surfaces
used in the canonical KL localization.

For a based cover

\[
 p:(\widehat X,\widehat x)\longrightarrow(X,x),
\]

its subgroup is

\[
 H=p_*\pi_1(\widehat X,\widehat x)\leq\pi_1(X,x).
\]

For \(H\leq K\), the notation

\[
 K/H=\{kH:k\in K\}                                \tag{2.1}
\]

means only the pointed set of cosets with distinguished point \(H\).
No multiplication on (2.1) is asserted unless \(H\triangleleft K\).
With the usual path-endpoint convention, a cover fiber is naturally
\(H\backslash K\); inversion gives the canonical pointed bijection

\[
 Hk\longmapsto k^{-1}H
\]

with (2.1).  Thus the project notation \(K/H\) does not silently assume
normality.

Path products and induced fundamental-group maps are based.  Every
statement involving an unbased cover or subgroup is to be read after the
displayed basepoints have been fixed.

For composable paths, \(\delta_2\cdot\delta_1\) means: first traverse
\(\delta_1\), then traverse \(\delta_2\).  In the usual endpoint
description, continuing the endpoint labelled \(H_sk\) by a based loop
\(g\) gives \(H_skg\).  Under the inversion identification

\[
 H_sk\longmapsto k^{-1}H_s
\]

used in this project, that transport is therefore

\[
 k^{-1}H_s\longmapsto g^{-1}k^{-1}H_s.             \tag{2.2}
\]

This explicit formula replaces any naive multiplication on \(K/H_s\)
and remains valid when \(H_s\) is not normal.

## 3. Canonical pullback component

Let

\[
 a:(X_s,x_s)\hookrightarrow(X_t,x_t)               \tag{3.1}
\]

be a based topological embedding.  Let

\[
 p_s:(\widehat X_s,\widehat x_s)\to(X_s,x_s),
 \qquad
 p_t:(\widehat X_t,\widehat x_t)\to(X_t,x_t)        \tag{3.2}
\]

be connected based covers with subgroups \(H_s,H_t\).  Suppose that a
based lift

\[
 A:(\widehat X_s,\widehat x_s)
   \longrightarrow(\widehat X_t,\widehat x_t),
 \qquad
 p_tA=ap_s                                             \tag{3.3}
\]

exists.  The lifting criterion gives

\[
 a_*(H_s)\leq H_t.                                  \tag{3.4}
\]

Define

\[
 K:=a_*^{-1}(H_t)\leq\pi_1(X_s,x_s).                \tag{3.5}
\]

Equation (3.4) implies

\[
 H_s\leq K.                                         \tag{3.6}
\]

Form the pullback

\[
 P=
 X_s\times_{X_t}\widehat X_t
 =
 \{(x,\widehat y):
      a(x)=p_t(\widehat y)\}.                        \tag{3.7}
\]

Let \(P_K\) be the path component of
\((x_s,\widehat x_t)\).  Write

\[
 r:P_K\to X_s,\quad r(x,\widehat y)=x,
 \qquad
 e:P_K\to\widehat X_t,\quad e(x,\widehat y)=\widehat y.
\tag{3.8}
\]

### Lemma 3.1 -- subgroup of the pullback component

The map \(r:P_K\to X_s\) is the connected based cover corresponding to
\(K\).

#### Proof

The pullback of a covering is a covering.  The pullback is locally path
connected, so its path components are open.  Moreover, the selected
component maps onto \(X_s\): because connected and locally path-connected
spaces are path connected, for any \(x\in X_s\) choose a path from
\(x_s\) to \(x\); its lift to the pullback from
\((x_s,\widehat x_t)\) stays in \(P_K\) and ends over \(x\).  Hence the
restriction \(r:P_K\to X_s\) is itself a connected covering.

It remains to compute its subgroup.

Let \(\gamma\) be a based loop in \(X_s\).  Its lift to \(P_K\) from
\((x_s,\widehat x_t)\) is

\[
 t\longmapsto
 \bigl(\gamma(t),\widehat{a\gamma}(t)\bigr),         \tag{3.9}
\]

where \(\widehat{a\gamma}\) is the lift of \(a\gamma\) to
\(\widehat X_t\) from \(\widehat x_t\).  The lift (3.9) is closed if and
only if \(\widehat{a\gamma}\) is closed.  By the cover-subgroup
criterion, this is equivalent to

\[
 a_*[\gamma]\in H_t,
\]

which, by (3.5), is equivalent to \([\gamma]\in K\).  Therefore

\[
 r_*\pi_1(P_K,(x_s,\widehat x_t))=K.
\]

This also proves that the selected path component is precisely the based
connected cover classified by \(K\). \(\square\)

### Lemma 3.2 -- the resolved leg is embedded

The second projection

\[
 e:P_K\hookrightarrow\widehat X_t                  \tag{3.10}
\]

is a topological embedding.

#### Proof

First consider the second projection on the entire pullback \(P\).
Its image is

\[
 p_t^{-1}(a(X_s)).
\]

Because \(a\) is an embedding, the formula

\[
 \widehat y\longmapsto
 \bigl(a^{-1}(p_t(\widehat y)),\widehat y\bigr)      \tag{3.11}
\]

is a continuous inverse on this image.  Thus the second projection
identifies \(P\) homeomorphically with
\(p_t^{-1}(a(X_s))\).  Restricting this homeomorphism to \(P_K\) proves
(3.10). \(\square\)

The embedding hypothesis in (3.1) is essential.  If \(a\) has a
base-space self-intersection, equality of the second coordinates in
(3.7) need not determine the first coordinate, so Lemma 3.2 can fail
before any subgroup collision is considered.

## 4. Exact collision-resolution factorization

### Theorem 4.1 -- canonical sheet resolution

Under the hypotheses of Section 3, define

\[
 q:\widehat X_s\longrightarrow P_K,\qquad
 q(\widehat u)=\bigl(p_s(\widehat u),A(\widehat u)\bigr).
\tag{4.1}
\]

Then:

1. \(q\) is the unique based map over \(X_s\) from the \(H_s\)-cover to
   the \(K\)-cover;
2. \(q\) is a surjective covering map;
3. the original lift factors exactly as
   \[
   A=e\circ q;                                      \tag{4.2}
   \]
4. for all \(\widehat u,\widehat v\in\widehat X_s\),
   \[
   A(\widehat u)=A(\widehat v)
   \quad\Longleftrightarrow\quad
   q(\widehat u)=q(\widehat v);                     \tag{4.3}
   \]
5. equivalently, the kernel pairs agree:
   \[
   \widehat X_s\times_{P_K}\widehat X_s
   =
   \widehat X_s\times_{\widehat X_t}\widehat X_s;   \tag{4.4}
   \]
6. the fiber of \(q\) over the based point is the pointed coset set
   \[
   \mathscr S_{\rm loc}=K/H_s;                     \tag{4.5}
   \]
7. \(q\) is injective if and only if \(K=H_s\); and
8. if \([K:H_s]<\infty\), then \(q\) has exactly \([K:H_s]\) sheets.
   No finiteness is asserted when the index is infinite.

#### Proof

The formula (4.1) lands in the pullback (3.7) because (3.3) gives

\[
 a(p_s(\widehat u))=p_t(A(\widehat u)).
\]

It lands in \(P_K\) because \(\widehat X_s\) is path connected and sends
the basepoint to \((x_s,\widehat x_t)\).  Moreover,

\[
 r q=p_s.                                          \tag{4.6}
\]

By (3.6), the lifting criterion for covers over the common base \(X_s\)
gives a unique based map from the \(H_s\)-cover to the \(K\)-cover.
Thus (4.1) is that map.

We verify surjectivity rather than hiding it in cover classification.
Let \(z\in P_K\), and choose a path \(\delta\) in \(P_K\) from the based
point to \(z\).  Lift \(r\delta\) to \(\widehat X_s\) from
\(\widehat x_s\), obtaining a path \(\widehat\delta\).  Both
\(\delta\) and \(q\widehat\delta\) are lifts of \(r\delta\) to \(P_K\)
from the same initial point.  Uniqueness of path lifting gives

\[
 q(\widehat\delta(1))=\delta(1)=z.
\]

Hence \(q\) is onto.  Choose a path-connected neighborhood
\(U\subset X_s\) evenly covered by both \(p_s\) and \(r\).  Each
component of \(p_s^{-1}(U)\) is mapped by \(q\) into one component of
\(r^{-1}(U)\); because both projections to \(U\) are homeomorphisms and
\(rq=p_s\), this restriction of \(q\) is a homeomorphism onto that target
sheet.  Surjectivity of \(q\) ensures that every target sheet is met.
Therefore \(q\) is a covering map.

The second coordinate in (4.1) is \(A(\widehat u)\), so (4.2) is
immediate.  Since \(e\) is injective by Lemma 3.2,

\[
 A(\widehat u)=A(\widehat v)
 \iff
 e(q(\widehat u))=e(q(\widehat v))
 \iff
 q(\widehat u)=q(\widehat v),
\]

which proves (4.3) and (4.4).

The standard fiber classification for the map from an \(H_s\)-cover to a
\(K\)-cover identifies its based fiber with
\(H_s\backslash K\).  The inversion convention in Section 2 identifies
that pointed set with \(K/H_s\), proving (4.5).  The map is one-sheeted
exactly when the two subgroups agree; in finite index its sheet number is
\([K:H_s]\). \(\square\)

### Corollary 4.2 -- exact meaning of the forced KL collision

For an ordinary primitive KL canonical localization,
`KL_CANONICAL_LOCALIZATION_FORCED_COLLISION` proves

\[
 H_s\subsetneq K=(i^p)_*^{-1}(H_t).                \tag{4.7}
\]

Consequently \(q\) in (4.1) is a nontrivial covering and \(e\) is an
embedded resolved pullback component.  The peripheral loop around the
proved excess component gives a non-base point of the fiber (4.5).
All point collisions of the full localized inclusion occur in fibers of
this same \(q\); none is left unexplained by the factorization.

This corollary is unconditional at the canonical primitive seed.  Its
transport to a named KL direct-decoration depth still has the same-seed
alignment qualification recorded in the forced-collision theorem.

### Corollary 4.3 -- the canonical sheet defect is infinite

At every ordinary primitive canonical seed,

\[
 [K:H_s]=\infty.                                   \tag{4.8}
\]

Consequently \(q\) is an infinite-sheeted cover, and for every
\(z\in P_K\),

\[
 A^{-1}(e(z))=q^{-1}(z)
\]

is infinite.  In particular, no finite enumeration of the raw
localization sheets can be complete.

#### Proof

Use the excess component \(X\), point \(x\in X\), and peripheral class
\([\gamma]\) from the forced-collision theorem.  Winding about \(x\)
defines a homomorphism

\[
 w:\pi_1(\Omega_s,x_s)\longrightarrow\mathbb Z.
\]

Every source-local loop is supported in the chosen neighborhood of the
central component \(A\), which misses \(x\), so

\[
 w(H_s)=0.
\]

The peripheral class satisfies

\[
 w([\gamma])=1,
\qquad
 [\gamma]\in K.
\]

Because \(K\) is a subgroup, \([\gamma]^n\in K\) for every
\(n\in\mathbb Z\).  If two cosets were equal,

\[
 [\gamma]^mH_s=[\gamma]^nH_s,
\]

then \([\gamma]^{m-n}\in H_s\).  Applying \(w\) would give

\[
 m-n=0.
\]

Thus the cosets \([\gamma]^nH_s\) are pairwise distinct, proving (4.8).
Theorem 4.1 identifies the fiber cardinality of \(q\) with this index and
identifies the \(A\)-fibers with the \(q\)-fibers. \(\square\)

## 5. Canonicality and optimality

The factorization (1.1) is not one arbitrary way of recording a
collision.

### Theorem 5.1 -- unique embedded intermediate factor

Suppose \(C\to X_s\) is a connected based intermediate cover and

\[
 \widehat X_s\xrightarrow{q_C}C
 \xrightarrow{e_C}\widehat X_t                    \tag{5.1}
\]

satisfies, with \(q_C\) and \(e_C\) based:

\[
 r_Cq_C=p_s,\qquad
 p_te_C=ar_C,\qquad
 A=e_Cq_C,                                         \tag{5.2}
\]

and \(e_C\) is injective.  Then the subgroup of \(C\to X_s\) is exactly
\(K\), and there is a unique based isomorphism of covers

\[
 C\cong P_K                                       \tag{5.3}
\]

which identifies (5.1) with (1.1).

#### Proof

Let

\[
 L=(r_C)_*\pi_1(C)\leq\pi_1(X_s).
\]

Existence of \(q_C\) gives \(H_s\leq L\).  Existence of \(e_C\) gives

\[
 a_*(L)\leq H_t,
\]

so \(L\leq K\).

Apply the proved subgroup-reflection criterion to the lift
\(e_C:C\to\widehat X_t\) of the physical embedding \(a\).  Since \(e_C\)
is injective, that criterion gives

\[
 a_*^{-1}(H_t)=L.
\]

The left side is \(K\), hence \(L=K\).  The classification of connected
based covers now gives the unique based isomorphism (5.3), and uniqueness
of based lifts identifies both factor maps. \(\square\)

Thus \(P_K\) is the unique connected intermediate cover on which the
remaining leg is embedded.  Replacing \(K/H_s\) by a coarser finite label
set without proving that the corresponding factor remains injective
would destroy this optimality statement.

## 6. The sheet-transport groupoid

The coset set (4.5) records the based fiber, but a path argument needs
transport between fibers over different points.

For every path

\[
 \delta:[0,1]\to P_K
\]

and every

\[
 \widehat u\in q^{-1}(\delta(0)),
\]

let \(\widetilde\delta_{\widehat u}\) be the unique \(q\)-lift beginning
at \(\widehat u\), and define

\[
 M_\delta(\widehat u)
 =
 \widetilde\delta_{\widehat u}(1)
 \in q^{-1}(\delta(1)).                             \tag{6.1}
\]

### Proposition 6.1 -- exact sheet transport

The maps (6.1) satisfy:

1. \(M_\delta\) is a bijection, with inverse \(M_{\delta^{-1}}\);
2. \(M_\delta\) depends only on the homotopy class of \(\delta\) relative
   to its endpoints;
3. for composable paths,
   \[
   M_{\delta_2\cdot\delta_1}
   =
   M_{\delta_2}\circ M_{\delta_1};                  \tag{6.2}
   \]
4. the constant path induces the identity; and
5. at the based point these transports give the monodromy action on the
   pointed fiber \(K/H_s\).

Hence

\[
 \Pi_1(P_K)\longrightarrow\mathbf{Set}_{\rm bij},
 \qquad
 z\longmapsto q^{-1}(z),\quad
 [\delta]\longmapsto M_\delta                       \tag{6.3}
\]

is a functor.  Its category of elements is the canonical
sheet-transport groupoid \(\mathscr G_q\).  Its full object set is

\[
 \{(z,\widehat u):z\in P_K,\ \widehat u\in q^{-1}(z)\},
\]

canonically the point set of \(\widehat X_s\).  The pointed coset set
\(K/H_s\) is only its based fiber (or, equivalently, the object set after
restricting (6.3) to the based action groupoid).

#### Proof

Every assertion is forced by uniqueness and homotopy invariance of lifts.
Lifting \(\delta\) and then \(\delta^{-1}\) returns to the initial point,
which proves bijectivity.  A homotopy relative endpoints lifts after an
initial sheet is fixed, so the terminal sheet is constant through the
homotopy.  The lift of a concatenation is the concatenation of the two
successive lifts, proving (6.2).  Constant paths lift to constant paths.
Restricting (6.3) to the based fundamental group gives the usual
monodromy action on the cover fiber, identified with \(K/H_s\) by the
convention of Section 2. \(\square\)

No regularity is used.  If \(H_s\) is not normal in \(K\), the based
fiber \(K/H_s\) is not a quotient group, but the groupoid (6.3) still
gives complete path transport.  Under the inversion convention of
Section 2, continuation by \(g\) acts by the explicit formula (2.2), not
by a silently assumed quotient-group multiplication.

### Proposition 6.2 -- compact-segment lifting classification

Let

\[
 \gamma:[0,1]\to\widehat X_t
\]

have image in the embedded resolved component \(e(P_K)\), and put

\[
 \delta=e^{-1}\gamma.
\]

Then the source paths

\[
 \widehat\delta:[0,1]\to\widehat X_s
\quad\text{such that}\quad
 A\widehat\delta=\gamma                             \tag{6.4}
\]

are exactly the \(q\)-lifts of \(\delta\).  There is one and only one such
path for each initial sheet in \(q^{-1}(\delta(0))\), and its final sheet
is given by \(M_\delta\).

The same statement applies separately on every compact parameter interval
on which a target path lies in \(e(P_K)\).

#### Proof

If \(q\widehat\delta=\delta\), then

\[
 A\widehat\delta=e q\widehat\delta=e\delta=\gamma.
\]

Conversely, if (6.4) holds, then

\[
 e(q\widehat\delta)=A\widehat\delta
=\gamma=e\delta.
\]

Injectivity of \(e\) gives \(q\widehat\delta=\delta\).  Covering path
lifting supplies exactly one lift from each initial sheet, and
Proposition 6.1 computes its endpoint. \(\square\)

Proposition 6.2 is the precise compact-segment replacement for treating
\(A\) as an embedding.  It does not classify a target path which leaves
and re-enters \(e(P_K)\), glue choices over nested intervals, prove
convergence to declared prime ends, or prove the KKL unique-proper-lift
predicate.

### Proposition 6.3 -- topological properness, with its exact boundary

Let

\[
 \delta:(0,1)\to P_K
\]

be topologically proper.  Every \(q\)-lift
\(\widehat\delta:(0,1)\to\widehat X_s\) is topologically proper.

If, in addition, \(a(X_s)\) is open in \(X_t\), then \(e(P_K)\) is open
in \(\widehat X_t\).  Let

\[
 \gamma:(0,1)\to\widehat X_t
\]

be topologically proper and let \(J\) be a component of
\(\gamma^{-1}(e(P_K))\).  After parametrizing \(J\) as an open interval,

\[
 \delta_J=e^{-1}\gamma|_J
\]

is topologically proper, and so are all of its \(q\)-lifts.

#### Proof

For compact \(C\subset\widehat X_s\), the set \(q(C)\) is compact.
Therefore

\[
 \widehat\delta^{-1}(C)
 \subset
 \delta^{-1}(q(C)).
\]

The right side is compact in \((0,1)\).  Since
\(\widehat X_s\) is Hausdorff, \(C\) is closed, so
\(\widehat\delta^{-1}(C)\) is closed in \((0,1)\), hence closed in the
right side.  It is therefore compact.  This proves properness of the lift.

If \(a(X_s)\) is open, then

\[
 p_t^{-1}(a(X_s))
\]

is open.  Lemma 3.2 identifies the selected component \(e(P_K)\) with an
open component of that preimage.  For compact \(C\subset P_K\),

\[
 \delta_J^{-1}(C)
 =
 J\cap\gamma^{-1}(e(C)).
\]

The set
\[
 S=\gamma^{-1}(e(C))
\]
is compact because \(e(C)\) is compact and \(\gamma\) is proper.  Moreover
\(S\subset\gamma^{-1}(e(P_K))\).  The latter set is open in \((0,1)\), and
its components are open intervals which are also closed relative to that
open set.  Hence \(J\cap S\) is closed in \(S\), and is compact.  The
definition \(\delta_J=e^{-1}\gamma|_J\) identifies \(J\cap S\) with
\(\delta_J^{-1}(C)\).  Thus
\(\delta_J\) is proper.  Apply the first paragraph to every \(q\)-lift.
\(\square\)

Topological properness means escape from compact subsets.  It does not
give convergence to a declared prime end, subordination to one marked
ideal interval, or uniqueness among the infinitely many possible proper
sheet lifts.

### Proposition 6.4 -- base-change propagation through exact equalizers

Let

\[
 X\xrightarrow{i}Z\xleftarrow{f}Y
\]

be continuous maps, and suppose

\[
 i=e\circ q,\qquad
 X\xrightarrow{q}P\xrightarrow{e}Z,
\]

where \(q\) is a covering and \(e\) is an embedding.  Form

\[
 E=X\times_ZY,\qquad
 R=P\times_ZY.
\]

Define

\[
 q':E\to R,\quad q'(x,y)=(q(x),y),
\]

\[
 e':R\to Y,\quad e'(p,y)=y,
\qquad
 i':E\to Y,\quad i'(x,y)=y.                        \tag{6.5}
\]

Then:

1. \(q'\) is the pullback covering of \(q\);
2. \(e'\) is a topological embedding;
3. \(i'=e'\circ q'\);
4. \(i'\) and \(q'\) have the same kernel pair; and
5. for every \((p,y)\in R\),
   \[
   (q')^{-1}(p,y)
   =
   \{(x,y):q(x)=p\}
   \cong q^{-1}(p).                                \tag{6.6}
   \]

Hence infinite collision fibers remain infinite under the full
base-change equalizer.

#### Proof

The square

\[
\begin{array}{ccc}
E&\xrightarrow{q'}&R\\
\downarrow&&\downarrow\\
X&\xrightarrow{q}&P
\end{array}
\]

is a pullback by direct substitution in the definitions, so \(q'\) is a
covering.

If \(e'(p_1,y_1)=e'(p_2,y_2)\), then \(y_1=y_2=y\).  Membership in \(R\)
gives

\[
 e(p_1)=f(y)=e(p_2).
\]

Injectivity of \(e\) gives \(p_1=p_2\).  The inverse on the image is

\[
 y\longmapsto(e^{-1}(f(y)),y),
\]

so \(e'\) is an embedding.  Formula (6.5) gives \(i'=e'q'\);
injectivity of \(e'\) gives equality of kernel pairs.  Formula (6.6) is
immediate. \(\square\)

Kahn's recursion is exactly such a base change:

\[
 \mathbf U^{r+2}
 =
 \{(x,y):i_r(x)=f_r(y)\},
\qquad
 i_{r+1}(x,y)=y.
\]

Thus, if \(i_r=e_rq_r\), Proposition 6.4 constructs

\[
 P_{r+1}=P_r\times_{\mathbf U^r}\mathbf U^{r+1},
\quad
 q_{r+1}(x,y)=(q_r(x),y),
\quad
 e_{r+1}(p,y)=y,
\]

and proves \(i_{r+1}=e_{r+1}q_{r+1}\).  Iteration propagates the resolved
factorization and its infinite full fibers through every **full,
unselected exact Kahn equalizer on the complementary-cover locus**.
It does not extend the factorization across a filled or prime-end
completion.  Nor does it identify one selected connected component with
the proof-used direct-decoration \(O\)-side, prove that all required sheets
lie in that component, or discharge the same-seed alignment hypothesis
by itself.  The later
`KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT` theorem proves connected
ambient and tilewise interior alignment for one fixed eligible seed.  It
still constructs no intermediate ideal boundary or \(O\)-side.

## 7. Exact based-coset merger and birth tests

The phrase "the old sheet labels survive enlargement" has no content
until the induced subgroup map is checked.  The following algebraic
criterion is exact for the induced **based coset map**.  It is not a
complete geometric final-root criterion.

Let

\[
 H\leq K\leq G,\qquad
 H^+\leq K^+\leq G^+,
\]

and let

\[
 \varphi:G\to G^+
\]

be a homomorphism such that

\[
 \varphi(H)\leq H^+,\qquad
 \varphi(K)\leq K^+.                               \tag{7.1}
\]

Then

\[
 \overline\varphi:K/H\longrightarrow K^+/H^+,
\qquad
 kH\longmapsto\varphi(k)H^+                        \tag{7.2}
\]

is well-defined.

### Theorem 7.1 -- based-coset no-merger/no-birth criterion

For (7.2):

\[
 \boxed{
 \overline\varphi\text{ is injective}
 \iff
 K\cap\varphi^{-1}(H^+)=H;
 }                                                  \tag{7.3}
\]

\[
 \boxed{
 \overline\varphi\text{ is surjective}
 \iff
 K^+=\varphi(K)H^+;
 }                                                  \tag{7.4}
\]

and therefore

\[
 \boxed{
 \overline\varphi\text{ is bijective}
 \iff
 \begin{cases}
 K\cap\varphi^{-1}(H^+)=H,\\
 K^+=\varphi(K)H^+.
 \end{cases}
 }                                                  \tag{7.5}
\]

If (7.3) fails, every

\[
 k\in
 \bigl(K\cap\varphi^{-1}(H^+)\bigr)\setminus H      \tag{7.6}
\]

is an exact **based-coset merger certificate**: the non-base coset \(kH\)
maps to the base coset \(H^+\).

If (7.4) fails, every

\[
 k^+\in K^+\setminus\varphi(K)H^+                  \tag{7.7}
\]

is an exact **based-coset birth certificate**: its coset has no old
preimage.

#### Proof

Suppose

\[
 \overline\varphi(k_1H)
 =
 \overline\varphi(k_2H).
\]

By (7.2), this is equivalent to

\[
 \varphi(k_2^{-1}k_1)\in H^+.
\]

Since \(k_2^{-1}k_1\in K\), injectivity holds exactly when this implication
forces \(k_2^{-1}k_1\in H\), which is precisely (7.3).  Taking \(k_2=1\)
gives the explicit certificate (7.6).

A coset \(k^+H^+\) lies in the image of (7.2) exactly when there is
\(k\in K\) with

\[
 k^+H^+=\varphi(k)H^+,
\]

equivalently

\[
 k^+\in\varphi(K)H^+.
\]

Every target coset has a preimage exactly when (7.4) holds.  Its failure
is witnessed by (7.7).  Combining (7.3) and (7.4) proves (7.5).
\(\square\)

### Corollary 7.2 -- subgroup diagram for the enlarged based fiber

Suppose an old and enlarged localization give a commutative group diagram

\[
\begin{CD}
G_s @>{a_*}>> G_t\\
@V{\varphi_s}VV @VV{\varphi_t}V\\
G_s^+ @>{a_*^+}>> G_t^+
\end{CD}                                            \tag{7.8}
\]

with

\[
\varphi_s(H_s)\leq H_s^+,\qquad
\varphi_t(H_t)\leq H_t^+.
\]

Put

\[
 K=a_*^{-1}(H_t),\qquad
 K^+=(a_*^+)^{-1}(H_t^+).
\]

Then commutativity gives

\[
 \varphi_s(K)\leq K^+,
\]

so the old-to-new based-coset map exists.  It has no coset mergers and no
coset births if and only if

\[
 K\cap\varphi_s^{-1}(H_s^+)=H_s,
\qquad
 K^+=\varphi_s(K)H_s^+.                            \tag{7.9}
\]

#### Proof

If \(k\in K\), then \(a_*(k)\in H_t\).  Hence

\[
 a_*^+(\varphi_s(k))
 =
 \varphi_t(a_*(k))
 \in
 \varphi_t(H_t)
 \subseteq H_t^+.
\]

Thus \(\varphi_s(k)\in K^+\).  Apply Theorem 7.1 with
\(\varphi=\varphi_s\). \(\square\)

The first condition in (7.9) is reflection: no old non-base sheet becomes
new-base.  The second is exhaustion: every new sheet is represented by
an old sheet.  Commutation alone proves neither.

### 7.3 Why the coset test is not geometric no-birth

Equations (7.9) are necessary and sufficient only for bijectivity of the
based coset map.  They do not classify new geometric components, path
restrictions, obstacle bridges, or prime-end accesses.

For an exact countermodel, take all four fundamental groups and all four
subgroups in (7.8) to be trivial.  Then both equalities in (7.9) hold
automatically.  Enlarge a simply connected source localization by
attaching a new simply connected collar lobe along an interval, and
enlarge the target interval so that the lobe contains one new proof-used
path or access component.  Fundamental groups and based coset sets remain
singletons, but the new geometric component has no old representative.

Therefore full final-root no-birth additionally requires:

1. an actual cover diagram over the complete enlarged proof-used domain;
2. a Cartesian component/path fiber-product square;
3. bijection of all retained and omitted proof-used components with
   multiplicity;
4. preservation of obstacles, proper/nonproper status, deck phase,
   itinerary, and cyclic order;
5. no new nonproper bridge; and
6. the required prime-end or direct proper-path endpoint compatibility.

The coset test detects algebraic sheet mergers and births that this
geometric audit must include.  It cannot replace the geometric audit.

## 8. Presentation invariance

### Proposition 8.1 -- invariance under equivalent based presentations

Suppose two based presentations of (3.1)--(3.3) are related by based
homeomorphisms of source and target spaces and based isomorphisms of the
covers, with every square commuting.  Then:

1. the induced fundamental-group isomorphism sends \(K\) to the
   corresponding subgroup \(K'\);
2. it induces a pointed bijection \(K/H_s\to K'/H_s'\);
3. the two pullback components \(P_K,P_{K'}\) are uniquely isomorphic as
   based covers;
4. that isomorphism conjugates the maps \(q,e\); and
5. it conjugates the transport functors (6.3).

#### Proof

Commutativity sends the predicate

\[
 a_*(k)\in H_t
\]

to the corresponding predicate

\[
 a_*'(k')\in H_t'.
\]

Therefore \(K\) maps to \(K'\), and \(H_s\) maps to \(H_s'\), giving the
pointed coset bijection.  Lemma 3.1 and based-cover classification give
the unique isomorphism of pullback components.  Uniqueness of based lifts
conjugates \(q\) and \(e\), and uniqueness of path lifts conjugates every
transport map \(M_\delta\). \(\square\)

This is the valid presentation-independence statement.  It does not say
that changing an obstacle packet, localization subgroup, root, or proof
horizon is an equivalent presentation.  Such a change must pass the
based-coset test (7.9) and the geometric no-birth audit of Section 7.3.

## 9. Application boundary for the KL \(O\)-footprint

At the canonical primitive seed the proved data now have the exact form

\[
\widehat\Omega_s
\xrightarrow{\ q\ }
P_K
\xrightarrow{\ e\ }
\widehat\Omega_t,
\qquad
K=(i^p)_*^{-1}(H_t),\quad H_s\subsetneq K.           \tag{9.1}
\]

Thus, within the canonical interior, if the full-canonical
**sheet-retention route** is used, its state must use the pair

\[
\bigl(e(P_K),\mathscr G_q\bigr),                    \tag{9.2}
\]

not the noninjective image \(A(\widehat\Omega_s)\) with sheet labels
forgotten.  This internal state does not itself identify \(P_K\) with an
actual KL tile.  Proposition 6.4 propagates this factorization through the
full, unselected exact Kahn equalizers on the complementary-cover locus,
not through filled or prime-end completion.  The later Kahn-iterate
alignment theorem proves connected ambient resolved interiors and gives a
conditional tilewise base-change theorem when the annular base map has the
stated \(q/e\) factorization.  The still later
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY` theorem proves that the
canonical infinite cover cannot be identified with a whole actual KL
tile covering factorization: KL's wrapping-end extension forces every
such actual whole-tile factorization to be one-sheeted.  The still later
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO` theorem closes the
five-clause end-compatible whole-tile comparison square negatively for
the nontrivial canonical kernel.  It does not prove the actual KL
immersion injective.  The subsequent
`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION` constructs the
non-covering relation span and tagged maximal interior restrictions for
each supplied fixed labeled same-source datum.  The first unresolved
object is therefore its complete Wave-stage alignment and
proper/end-proper response, or a separately authorized collar, retimed,
or revised interface, with complete proof-use exhaustion or a universal
Value-observable omitted-family charge.  Its full relative ideal
incidence and actual \(O\)-side remain open.

This is not the only logically possible replacement.  One may instead
synchronize the source and target obstacle packets, use a proved embedded
collar while charging every omitted sheet, or retime and revise the
interface.  Each alternative must rebuild its own localization,
component, path, end, and enlargement certificates.

For every compact target-path segment contained in \(e(P_K)\),
Proposition 6.2 already gives the complete canonical source restriction
list and its multiplicity.  For a supplied fixed labeled same-source
datum, the later restricted classification gives an admissible
**interior relation** from (9.1) to the actual direct-decoration tile.
It cannot be compressed to the ruled-out nontrivial whole-tile
covering/embedding comparison.  Once realized on the complete Wave
horizon, this relation, or any separately authorized collared, retimed,
or relocalized interface, must supply:

1. a conformal-disk or authorized collared localization of \(P_K\);
2. either continuous extensions of \(q,e\) on every complete proof-used
   \(O,\xi,\eta\) interval in an authorized compactification, or a direct
   proper-path endpoint groupoid; no global prime-end extension of an
   infinite cover is assumed;
3. enumeration of every component of the target complement landing on
   each resolved sheet;
4. the full ideal footprint of each landing component;
5. classification of every competing sheet lift as KKL-proper or
   nonproper, with singleton proper-lift isolation for each absorption or
   exclusion witness and explicit deck/coset certificates for all other
   live lifts;
6. properness or end-properness on every complete proof-used interval;
7. family-level disjointness and covering-endpoint refinement;
8. a finite or future-faithfully compact representation of the infinite
   groupoid state; and
9. both equalities (7.9) **and** the geometric component/path/prime-end
   no-birth audit of Section 7.3 at final-root enlargement.

These nine items are the exact analytic content still required by
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT` and
`DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`.

### Theorem 9.1 -- conditional sheet-isolated footprint criterion

Let \(E\) be a resolved source ideal set, let \(J\) be the target ideal
set, and let

\[
 \Phi:E\longrightarrow 2^J
\]

be a proposed complete sheet-resolved access footprint.  For every target
proper path \(\Gamma\), let

\[
 \operatorname{PropRes}_{\mathscr G_q}(\Gamma)
\]

denote its full set of KKL-proper source restrictions, with coset and deck
phase retained.  Assume:

1. **endpoint necessity:** if
   \[
   \operatorname{PropRes}_{\mathscr G_q}(\Gamma)=\{\delta\}
   \]
   and the source ideal endpoints of \(\delta\) are \(p_-,p_+\), then the
   target ideal endpoints of \(\Gamma\) lie respectively in
   \(\Phi(p_-)\) and \(\Phi(p_+)\);
2. **sheet-isolated realization:** for every \(p\in E\) and every
   \(\xi\in\Phi(p)\), there is a target proper hairpin
   \(\Gamma_{p,\xi}\), with \(\xi\) as a target endpoint, such that
   \(\operatorname{PropRes}_{\mathscr G_q}(\Gamma_{p,\xi})\) consists of
   exactly one source hairpin whose two source ideal endpoints are \(p\);
3. **boundary-subordination axioms:** the declared source and target ideal
   compactifications have the following endpoint rules for connected
   \(C\subset E\) and \(I\subset J\):
   - a source proper path subordinate to \(C\) has both source endpoints in
     \(C\);
   - a source hairpin with both endpoints equal to \(p\in C\) is
     subordinate to \(C\); and
   - a target proper path is subordinate to \(I\) if and only if both of
     its target endpoints lie in \(I\).

These are hypotheses on the authorized ideal-boundary model.  In the
intended disk case they are the standard endpoint rules on the conformal
ideal circles; they are not inferred here from a ribbon-tree marking or
from local connectivity of a carrier.

Then, for every connected target ideal set \(I\subset J\), a connected
source ideal set \(C\subset E\) satisfies the KKL universal
unique-proper-restriction implication for \(I\) if and only if

\[
 C\subset
 \operatorname{Safe}_{\mathscr G_q}(I)
 :=
 \{p\in E:\Phi(p)\subset I\}.                       \tag{9.3}
\]

Consequently the maximal connected admissible candidates are exactly the
connected components of the safe set (9.3).  A unique maximum requires a
separate connectedness or distinguished-seed theorem.

#### Proof

Assume first that \(C\) contains
\(p\notin\operatorname{Safe}_{\mathscr G_q}(I)\).  Choose

\[
 \xi\in\Phi(p)\setminus I.
\]

By sheet-isolated realization,
\(\Gamma_{p,\xi}\) has exactly one KKL-proper source restriction, a
hairpin with both source endpoints \(p\).  The second
boundary-subordination axiom makes that hairpin subordinate to \(C\).
Since its target endpoint \(\xi\) is outside \(I\), the third axiom says
that the target hairpin is not subordinate to \(I\).  Thus \(C\) violates
the KKL implication.

Conversely, let \(C\) be contained in the safe set and let \(\Gamma\) be
a target proper path whose full proper restriction set is the singleton
\(\{\delta\}\), with \(\delta\) subordinate to \(C\).  The first
boundary-subordination axiom puts its source endpoints \(p_-,p_+\) in
\(C\).  Endpoint necessity gives target
endpoints in

\[
 \Phi(p_-)\cup\Phi(p_+)\subset I.
\]

The third boundary-subordination axiom therefore makes \(\Gamma\)
subordinate to \(I\), and the universal implication holds.  This proves
(9.3) and the maximal-component statement. \(\square\)

The theorem is a proved conditional reduction, not the actual KL
footprint theorem.  At the canonical seed the raw \(q\)-fiber is infinite,
so sheet-isolated realization must prove that every competing lift is
nonproper or otherwise excluded; it cannot be inferred from a pointwise
target access picture.

## 10. Adversarial audit

### 10.1 Quotient-group shortcut

Rejected.  If \(H_s\) is not normal in \(K\), \(K/H_s\) has no canonical
group law.  The transport functor (6.3), not multiplication of cosets, is
the valid object.

### 10.2 Finite-state shortcut

Rejected more strongly at the canonical primitive seed.  Corollary 4.3
proves \([K:H_s]=\infty\) there.  A finite response state can therefore
exist only after a proved future-faithful compactification or sufficient
quotient that preserves every proof-used path, access, and Value
observable; raw sheet enumeration is impossible.

### 10.3 Embedded-image shortcut

Rejected.  The embedded object is \(e(P_K)\) together with the covering
\(q\).  Replacing it by \(A(\widehat X_s)\) and forgetting \(q\) erases
exactly the collision fibers in (4.3).

### 10.4 Immersion shortcut

Rejected.  Lemma 3.2 uses injectivity of the physical base map \(a\).
For a later bold map known only to be an immersion, a base self-collision
can remain after subgroup resolution.

### 10.5 Compact-path to proper-end shortcut

Rejected.  Proposition 6.3 proves topological properness for a proper
resolved open path and its lifts, but neither Proposition 6.2 nor 6.3
proves convergence to declared prime ends, marked subordination,
end-properness, or singleton proper-lift isolation.

### 10.6 Commuting enlargement shortcut

Rejected twice.  A commuting square gives only
\(\varphi_s(K)\leq K^+\), not either equality in (7.9).  Even when both
equalities hold, the simply connected lobe countermodel of Section 7.3
can create a new geometric access invisible to fundamental groups.

### 10.7 Root equivalence shortcut

Rejected.  Proposition 8.1 applies only to genuinely equivalent based
presentations.  Late root enlargement generally changes the spaces or
subgroups and must pass both Corollary 7.2 and Section 7.3.

### 10.8 Prime-end shortcut

Rejected.  An embedding of open complementary surfaces need not by itself
supply the complete continuous boundary extension required by the KL
marking.  An infinite cover need not extend continuously at a full ideal
boundary at all; authorized interval extensions or a direct proper-path
endpoint groupoid must be proved.

### 10.9 Unique-proper-lift shortcut

Rejected.  The canonical \(q\)-fiber is infinite.  A pointwise access
footprint does not by itself show that a target witness has one KKL-proper
source restriction.  Each witness must isolate one proper coset or
classify and exclude every competing proper lift.

### 10.10 MLC shortcut

Rejected.  The theorem canonically resolves one covering-space
obstruction.  It supplies no uniform width estimate, backward transition,
coercive compactness, rigidity, or parameter-fiber theorem.

## 11. Promotion record

This note proves one narrow obligation:

```text
KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION
```

Its dependencies are:

```text
KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION
KL_CANONICAL_LOCALIZATION_FORCED_COLLISION
```

The first dependency supplies the exact subgroup-reflection theorem and
the second supplies the KL peripheral loop and winding separation.
Sections 3--8 prove the general factorization, infinite-index consequence,
equalizer base change, topological properness boundary, and based-coset
enlargement criteria internally.

The following obligations remain open:

```text
DIRECT_DECORATION_OUTER_CAP_FOOTPRINT
DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION
DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE
VIRTUAL_WAVE_MARKED_CORRESPONDENCE
VIRTUAL_WAVE_HORIZON_CERTIFICATE
VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE
UNIVERSAL_PROTECTED_TOWER_CLOSURE
MLC
```

The proved advance is exact: the sheet-sensitive replacement carrier is
now canonical, its path groupoid is constructed, every compact resolved
path lift is classified, the raw canonical sheet defect is proved
infinite, and final-root **based-coset** stability has a
necessary-and-sufficient algebraic test.  Full geometric root stability
remains open.
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO` excludes identification of
this infinite resolved carrier with the complete actual KL tile.
`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION` supplies the
label-preserving interior relation span.  The next unresolved datum is
its canonical/KL proper-end response on every complete proof-used
interval, with uniform omitted-family control and Cartesian final-root
no-birth.  Only after that response is typed may the actual
sheet-indexed \(O\)-side complement and access footprint be constructed
on its authorized relative boundary.
