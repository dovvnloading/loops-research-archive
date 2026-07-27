# Filled-set graph naturality for pseudo-quadratic-like iterates

## 1. Result and exact scope

This note proves the finite-level graph construction that was missing from
the stationary-Wave audit:

```text
PQL_ITERATE_FILLED_GRAPH_NATURALITY
KKL_STATIONARY_FINAL_COMPONENT_REALIZATION
```

For every finite fiber-product iterate of a pseudo-quadratic-like map, the
iterated immersion is a homeomorphism on the filled set.  Consequently
every connected base-filled-set package has one canonical connected graph
lift.  Applied at KKL's stationary level \(m=N-1=b+2\), this constructs
the two lifts of \(K_0^b\) and \(K_0^{b+1}\), proves the correctly typed
\(f^m\)-projection formulas, and proves that the components of
\((f^m)^{-1}(\mathcal K)\) containing them are distinct.

This does **not** prove that a source-language KKL pass-through occurrence
survives as a proper leaf of the final immersion restriction.  It also
does not prove that the two shallower pass-through predicates occur in
one component of that restriction.  The immediate native-source gate is

```text
KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION
```

and the first stronger fixed-pair gate is

```text
KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT
```

VAAPC-I, UPTCR, and MLC remain open.

## 2. Source locks and convention

The analytic source is Jeremy Kahn, *A priori bounds for some infinitely
renormalizable quadratics: I. Bounded primitive combinatorics*,
arXiv:math/0609045.  The locked source file is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The proof-used clauses are:

- lines 20--41: a \(\psi\)-polynomial-like map and the fact that the
  immersion maps its pulled filled set bijectively to the target filled
  set;
- lines 60--77 and 155--178: an embedded polynomial-like restriction on
  a neighborhood of the same filled set;
- lines 188--265: the topological pullback and preservation of
  homeomorphisms under base change;
- lines 350--399: the fiber-product pullback, including
  \(i_1:K''\to K'\) being a homeomorphism and the explicit coordinate
  convention
  \[
    U''=\{(x,y):i(x)=f(y)\},\qquad i_1(x,y)=y,\quad f_1(x,y)=x;
  \]
- lines 410--416: the complete finite iterate tower and the commuting
  identities
  \[
    i_n\circ f_{n+1}=f_n\circ i_{n+1}.
  \tag{2.1}
  \]

The KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

Its proof-used clauses are lines 439--461, 478--490, 497--504,
1547--1548, 1591--1605, and 2060--2090.
Kahn writes a correspondence as \((i,f)\); KKL write it as
\((f,\iota)\).  In this note \(i\) always denotes the immersion and
\(f\) the proper branched covering.

## 3. The finite fiber-product tower

Let
\[
 (i_n,f_n):(U^{n+1},K^{n+1})\longrightarrow(U^n,K^n),
 \qquad n\geq0,
\tag{3.1}
\]
be Kahn's iterated pullback tower.  Thus:

1. \(i_n\) is a holomorphic immersion;
2. \(f_n\) is proper of the fixed degree \(d\);
3. \(i_n^{-1}(K^n)=f_n^{-1}(K^n)=K^{n+1}\);
4. \(i_n|_{K^{n+1}}:K^{n+1}\to K^n\) is a homeomorphism; and
5. the squares commute as in (2.1).

For \(m\geq1\), define the two level maps
\[
 I_m=i_0\circ i_1\circ\cdots\circ i_{m-1},
 \qquad
 P_m=f_0\circ f_1\circ\cdots\circ f_{m-1}.
\tag{3.2}
\]
Both maps have domain \(U^m\) and target \(U^0\).  KKL denote them by
\(\iota_m\) and \(f^m\), respectively.

Define the single-valued filled-set dynamics
\[
 F
 =
 f_0\circ
 \bigl(i_0|_{K^1}\bigr)^{-1}
 :
 K^0\longrightarrow K^0.
\tag{3.3}
\]
This definition uses only the homeomorphism on the filled set.  Kahn's
embedded polynomial-like neighborhood shows that it agrees with the
usual holomorphic quadratic-like germ near \(K^0\).

### Lemma 3.1 (iterated filled-set coordinate)

For every \(m\geq1\):

\[
 I_m|_{K^m}:K^m\longrightarrow K^0
 \quad\hbox{is a homeomorphism},
\tag{3.4}
\]

\[
 I_m^{-1}(K^0)=P_m^{-1}(K^0)=K^m,
\tag{3.5}
\]
and, on \(K^m\),
\[
 P_m=F^m\circ I_m.
\tag{3.6}
\]

#### Proof

Each factor \(i_n|_{K^{n+1}}\) in (3.2) is a homeomorphism.  Their finite
composition is a homeomorphism, proving (3.4).

For (3.5), use induction separately for the two maps.  At \(m=1\), the
defining equality is
\[
 i_0^{-1}(K^0)=f_0^{-1}(K^0)=K^1.
\]
If the covering identity holds for \(m\), then
\[
\begin{aligned}
 P_{m+1}^{-1}(K^0)
 &=
 f_m^{-1}\!\left(P_m^{-1}(K^0)\right)\\
 &=
 f_m^{-1}(K^m)
 =
 K^{m+1}.
\end{aligned}
\tag{3.7}
\]
The same calculation with \(I_{m+1}=I_m\circ i_m\) and
\(i_m^{-1}(K^m)=K^{m+1}\) proves the immersion identity.

It remains to prove (3.6).  On \(K^1\), the definition (3.3) gives
\[
 f_0=F\circ i_0.
\tag{3.8}
\]
Repeated use of (2.1) gives the telescoping identity
\[
 I_m\circ f_m
 =
 f_0\circ i_1\circ\cdots\circ i_m
 =
 F\circ I_{m+1}
\quad\hbox{on }K^{m+1}.
\tag{3.9}
\]
The first equality follows by moving \(f_m\) left through
\(i_{m-1},\ldots,i_0\), one commuting square at a time; the second uses
(3.8).

Now induct on \(m\).  Formula (3.8) is (3.6) for \(m=1\).  Assuming
(3.6) at \(m\), equations (3.2) and (3.9) give, on \(K^{m+1}\),
\[
\begin{aligned}
 P_{m+1}
 &=
 P_m\circ f_m\\
 &=
 F^m\circ I_m\circ f_m\\
 &=
 F^{m+1}\circ I_{m+1}.
\end{aligned}
\tag{3.10}
\]
This proves (3.6). \(\square\)

### Theorem 3.2 (canonical filled graph)
(`PQL_ITERATE_FILLED_GRAPH_NATURALITY`)

Let \(A\subset K^0\) be compact and connected.  For every finite
\(m\geq1\), set
\[
 \widehat A^{\,m}
 =
 \bigl(I_m|_{K^m}\bigr)^{-1}(A).
\tag{3.11}
\]
Then:

1. \(\widehat A^{\,m}\) is compact and connected;
2. \(I_m(\widehat A^{\,m})=A\);
3. it is the unique subset of \(K^m\) with this image;
4. for every \(B\subset K^0\),
   \[
     A\subset F^{-m}(B)
     \quad\Longrightarrow\quad
     \widehat A^{\,m}\subset P_m^{-1}(B);
   \tag{3.12}
   \]
5. more precisely,
   \[
     P_m(\widehat A^{\,m})=F^m(A).
   \tag{3.13}
   \]

If \(B\subset K^0\) and \(A\) is a component of \(F^{-m}(B)\), then
\(\widehat A^{\,m}\) is a component of \(P_m^{-1}(B)\).

#### Proof

Items 1--3 follow from the homeomorphism (3.4).  Formula (3.13) is
(3.6) applied to (3.11), and (3.12) follows immediately.

For the last assertion, first observe from (3.5) that, when
\(B\subset K^0\),
\[
 P_m^{-1}(B)\subset K^m.
\tag{3.14}
\]
Equations (3.6) and (3.14) therefore give the exact equality
\[
 P_m^{-1}(B)
 =
 \bigl(I_m|_{K^m}\bigr)^{-1}\!\left(F^{-m}(B)\right).
\tag{3.15}
\]
A homeomorphism carries connected components bijectively to connected
components.  Apply this to (3.15). \(\square\)

No local-connectivity statement is used: all maps in (3.4) are
homeomorphisms of compact filled sets supplied by the
\(\psi\)-polynomial-like pullback construction.

### Lemma 3.3 (confluence and component composition)

Let \(h:X\to Y\) be a finite proper branched covering between Riemann
surfaces.

1. If \(A\subset Y\) is a continuum and \(C\) is a component of
   \(h^{-1}(A)\), then
   \[
      h(C)=A.
   \tag{3.16}
   \]
2. If \(g:Y\to Z\) is continuous, \(B\subset Z\), \(A\) is a component
   of \(g^{-1}(B)\), and \(C\) is a component of \(h^{-1}(A)\), then
   \(C\) is a component of
   \[
      (g\circ h)^{-1}(B).
   \tag{3.17}
   \]

#### Proof

For the first assertion, fix a complete auxiliary metric on \(Y\).
Because \(A\) is compact and connected, there are connected relatively
compact open neighborhoods \(V_k\) such that
\[
 A\subset V_{k+1},\qquad
 \overline{V_{k+1}}\subset V_k,\qquad
 \bigcap_{k\geq1}\overline{V_k}=A.
\tag{3.18}
\]
For example, after working in a relatively compact metric neighborhood
of \(A\), take successively smaller connected metric neighborhoods of
\(A\).  Their connectedness follows because each is the union of balls
meeting the connected set \(A\).

Let \(W_k\) be the component of \(h^{-1}(V_k)\) containing \(C\).
The set \(C\) is connected and is contained in \(h^{-1}(V_k)\), so
\(W_k\) exists and is unique.  The restriction
\[
 h|_{W_k}:W_k\longrightarrow V_k
\tag{3.19}
\]
is proper: if \(L\Subset V_k\), then \(h^{-1}(L)\) is compact and
\(W_k\cap h^{-1}(L)\) is closed in it.  A branched covering is open, so
\(h(W_k)\) is open in \(V_k\); properness makes the same image closed in
\(V_k\).  Since \(V_k\) is connected, (3.19) is onto.

The nesting in (3.18) gives
\[
 \overline{W_{k+1}}\subset W_k.
\tag{3.20}
\]
Indeed, \(\overline{W_{k+1}}\) is a connected subset of
\(h^{-1}(V_k)\) meeting \(C\), and hence lies in the component \(W_k\).
Consequently
\[
 E:=\bigcap_{k\geq1}\overline{W_k}
\tag{3.21}
\]
is a compact connected subset of \(h^{-1}(A)\) containing \(C\).
Maximality of the component \(C\) gives \(E=C\).

Now fix \(y\in A\).  Surjectivity of (3.19) makes each compact set
\[
 \overline{W_k}\cap h^{-1}(y)
\tag{3.22}
\]
nonempty.  These sets are nested by (3.20), so compactness gives a point
in their intersection.  By (3.21) that point belongs to \(C\), and
therefore \(y\in h(C)\).  This proves (3.16).

For the second assertion, let \(D\) be a connected subset of
\((g\circ h)^{-1}(B)\) that contains \(C\).  Its image \(h(D)\) is a
connected subset of \(g^{-1}(B)\) meeting the component \(A\), so
\(h(D)\subset A\).  Hence \(D\subset h^{-1}(A)\), and maximality of
the component \(C\) gives \(D\subset C\).  Thus \(C\) is a component
of (3.17). \(\square\)

### Lemma 3.4 (analytic graph neighborhood and end degree)

For every finite \(m\geq1\), there are an open neighborhood
\(V_m\subset U^0\) of \(K^0\), an open neighborhood
\(W_m\subset U^m\) of \(K^m\), and a biholomorphism
\[
 \Gamma_m:V_m\longrightarrow W_m
\tag{3.23}
\]
such that
\[
 I_m\circ\Gamma_m=\operatorname{id}_{V_m},
\qquad
 P_m\circ\Gamma_m=F^m|_{V_m}.
\tag{3.24}
\]
In particular, \(I_m|_{W_m}=\Gamma_m^{-1}\), and the set-theoretic
graph in Theorem 3.2 is the restriction of an actual holomorphic graph.

An **isolating Jordan restriction of \(F^m\) at \(A\) over \(B\)** means
Jordan disks \(E,D\Subset V_m\) such that
\[
 A\subset E,\quad B\subset D,\quad
 F^m:E\to D\text{ is proper},\quad
 (F^m)^{-1}(B)\cap E=A,
\tag{3.25}
\]
and every critical value of this restriction lies in \(B\).
Suppose, moreover, that \(A\subset K^0\) is a component of
\((F^m)^{-1}(B)\), where \(A\) and \(B\) are nondegenerate full
continua, and that an isolating Jordan restriction has degree \(e\).
Then the corresponding isolating restriction of \(P_m\) at
\(\widehat A^{\,m}\) has the same degree \(e\).  The induced covering of
the ideal-boundary component belonging to \(\widehat A^{\,m}\) also has
degree \(e\).

#### Proof

Kahn's embedded restriction theorem gives neighborhoods
\(E_1\subset U^1\) of \(K^1\) and \(D_1=i_0(E_1)\subset U^0\) of
\(K^0\) such that \(i_0:E_1\to D_1\) is biholomorphic and
\[
 F=f_0\circ i_0^{-1}:D_1\longrightarrow D_0
\tag{3.26}
\]
is a genuine polynomial-like map.  Here and below \(i_0^{-1}\) means
only the inverse of this selected embedded restriction; the immersion
may have other remote preimages of points of \(D_1\).  For fixed \(m\),
put
\[
 D^{[m]}
 =
 \{z\in D_1:F^j(z)\in D_1\text{ for }0\leq j<m\}
\tag{3.27}
\]
and let \(V_m\) be the component of \(D^{[m]}\) containing \(K^0\).
It is an open neighborhood of \(K^0\), because \(F(K^0)=K^0\) and
\(K^0\Subset D_1\).

Write \(a=(i_0|_{E_1})^{-1}:D_1\to E_1\).  Kahn's fiber-product
description identifies a level-\(m\) point with a length-\(m\) relation
chain.  Define explicitly
\[
\Gamma_m(z)
=
\bigl(a(F^{m-1}z),a(F^{m-2}z),\ldots,a(Fz),a(z)\bigr).
\tag{3.28}
\]
For adjacent entries,
\[
 i_0(a(F^{j+1}z))
 =
 F^{j+1}z
 =
 f_0(a(F^jz)),
\tag{3.29}
\]
so (3.28) lies in the iterated fiber product.  Equivalently,
\(\Gamma_1=a\), and
\(\Gamma_{m+1}(z)\) is obtained from \(\Gamma_m(z)\) by adjoining
\(a(F^mz)\); equation (3.29) is the pullback equality at that induction
step.  Kahn's locked lines 259--265 identify the analytic pullback with
the set-theoretic pullback whenever one leg is an immersion, while
lines 372--392 prove that the filled-set pullback used here is connected.
Thus the chain is an actual point of \(U^m\), with no normalization or
component choice left implicit, and depends holomorphically on \(z\).
Induction through the last and first coordinate projections gives,
respectively,
\[
 I_m\Gamma_m(z)=z,
\qquad
 P_m\Gamma_m(z)=F^m(z),
\]
which is (3.24).  The first identity implies that
\(\Gamma_m\) is injective with nonzero derivative.  It is therefore a
biholomorphism onto the open set \(W_m:=\Gamma_m(V_m)\).  The set
\(W_m\) contains \(K^m\): for \(x\in K^m\), the point
\(z=I_m(x)\in K^0\) has the relation chain \(\Gamma_m(z)\), while the
identity \(I_m^{-1}(K^0)=K^m\) in (3.5) puts
\(\Gamma_m(z)\) in \(K^m\), and the filled-set injectivity of \(I_m\)
in (3.4) forces
\(x=\Gamma_m(z)\).

For the degree assertion, start with the assumed isolating Jordan
restriction
\[
 F^m:E\longrightarrow D.
\tag{3.30}
\]
Set \(\widehat E=\Gamma_m(E)\).  Equations (3.24) conjugate
\[
 P_m:\widehat E\longrightarrow D
\tag{3.31}
\]
to (3.30), so (3.31) is proper of the same degree \(e\) and its
preimage of \(B\) in \(\widehat E\) is
\(\widehat A^{\,m}\).  Because all critical values of (3.30) in \(D\)
lie in \(B\), deleting the two full continua gives a degree-\(e\)
covering of annular collars.  Nondegeneracy excludes a puncture/cusp,
so uniformization extends the covering to their inner prime-end circles
with topological degree \(e\).

For the KKL application, \(A\) and \(B\) belong to finite pairwise
disjoint full obstacle packages, and the isolating disks are chosen to
meet no other obstacle.  The local collar inclusion then identifies its
inner prime-end circle canonically with the corresponding component of
the ambient KKL ideal boundary: any smaller obstacle-free collar is
cofinal at exactly the same complementary end.  The same applies in the
source.  This, rather than an appeal to local connectivity, identifies
the transferred degree with KKL's ambient ideal-boundary degree.
\(\square\)

### Lemma 3.5 (fullness of selected pullback components)

Let \(h:D'\to D\) be a proper holomorphic map between planar disks,
let \(A\Subset D\) be a full continuum, and let \(C\) be a component of
\(h^{-1}(A)\).  Then \(C\) is full.  Consequently every selected KKL
continuum \(K_0^r\) admits a nested basis of Jordan neighborhoods.

#### Proof

Suppose that \(H\) were a bounded component of
\(\mathbb C\setminus C\).  Since \(C\Subset D'\) and \(D'\) is a disk,
such a bounded complementary component lies in \(D'\), and
\(\partial H\subset C\).  Choose \(x\in H\setminus h^{-1}(A)\); such a
point exists because otherwise \(H\) would be a connected subset of
\(h^{-1}(A)\) attached to \(C\), contrary to maximality of the component
\(C\).

The holomorphic map \(h\) is open.  It is also proper on
\(\overline H\), and therefore
\[
 \partial h(H)\subset h(\partial H)\subset A.
\tag{3.32}
\]
Indeed, if \(h(x_n)\to y\in\partial h(H)\) with \(x_n\in H\),
compactness gives a limit \(x\in\overline H\); the open mapping theorem
excludes \(x\in H\), so \(x\in\partial H\).

Let \(O\) be the component of \(\mathbb C\setminus A\) containing
\(h(x)\).  Relation (3.32) implies \(O\subset h(H)\): the nonempty set
\(O\cap h(H)\) is both open and closed in \(O\), since any relative
boundary point would lie in \(\partial h(H)\subset A\).  But \(h(H)\)
is bounded, whereas fullness of \(A\) makes
\(\mathbb C\setminus A=O\) connected and unbounded.  This
contradiction proves that \(C\) is full.

The central small Julia set is full.  Applying the first assertion
inductively to the proper inverse components in KKL line 1597 makes
every \(K_0^r\) full.  The standard planar cellularity theorem says
that a compact nonseparating continuum in the plane has a neighborhood
basis of Jordan disks.  A full planar continuum is nonseparating, so
the final statement follows.  This use of cellularity is purely
topological and makes no assertion that the continuum itself is locally
connected. \(\square\)

## 4. Application to the KKL stationary pair

Use KKL's notation.  Let \(b\) be the parabolic bound,
\[
 N=b+3,
 \qquad
 m=N-1=b+2.
\tag{4.1}
\]
Let \(\mathcal K\subset K^0\) be the primitive cycle of small filled
Julia sets and let \(K_0^r\), \(r\geq0\), be the selected successive
pullback continua in KKL line 1597.  By construction,
\[
 F^r(K_0^r)=K_0^0.
\tag{4.2}
\]

Equation (4.2) follows by applying Lemma 3.3 successively to KKL's
selected proper-preimage components.

Define the actual final graph lifts
\[
 \widehat K_r
 =
 \bigl(I_m|_{K^m}\bigr)^{-1}(K_0^r),
 \qquad
 r\in\{b,b+1\}.
\tag{4.4}
\]

### Lemma 4.A (primitive small-Julia pullback)

Let \(p>1\) be the primitive renormalization period, put
\[
 K_j=F^j(K_0^0)\qquad (j\in\mathbb Z/p\mathbb Z),
\tag{4.A.1}
\]
and interpret inverse images in the source disk of the embedded
quadratic-like representative of \(F\).  Then
\[
 F^{-1}(K_1)=K_0^0,
\tag{4.A.2}
\]
and, for \(1\leq j<p\),
\[
 K_j\in\operatorname{Comp}F^{-1}(K_{j+1}).
\tag{4.A.3}
\]
Moreover, the first restriction in the cyclic return has degree two,
all remaining restrictions have degree one, and each restriction admits
an isolating Jordan representative of that degree.

#### Proof

By the definition of \(\psi\)-ql renormalizability in KKL lines
478--490, an embedded quadratic-like representative of \(F\) has a
quadratic-like return
\[
 G=F^p:D_0\longrightarrow D_p
\tag{4.A.4}
\]
of degree two whose connected filled set is \(K_0^0\) and contains the
unique simple critical point \(c\) of \(F\).  Choose the representative
with Jordan source and target disks.  The proved
`QL_RETURN_FACTORIZATION` constructs disks \(D_j\), \(0\leq j\leq p\),
such that
\[
 F:D_j\longrightarrow D_{j+1}
\tag{4.A.5}
\]
is proper, \(K_j\Subset D_j\), and the product of the stage degrees is
\(\deg G=2\).  Its proof is not polynomial-specific: define \(D_j\) as
the component of \(F^{-(p-j)}(D_p)\) containing \(F^j(D_0)\).
Properness of \(G\) makes \(D_0\) the selected \(p\)-fold preimage
component; induction makes every \(F:D_j\to D_{j+1}\) proper, and the
composition is \(G\).  This argument applies verbatim to the embedded
quadratic-like germ used here.

The first disk contains \(c\), so its stage degree is at
least two.  The product is two; consequently the first stage has degree
exactly two and every later stage has degree one.  A proper degree-one
map between disks is a conformal isomorphism.

The defining filled-set identity for \(G\) is
\[
 G^{-1}(K_0^0)\cap D_0=K_0^0.
\tag{4.A.6}
\]
If \(x\in D_0\) and \(F(x)\in K_1\), choose \(y\in K_0^0\) with
\(F(y)=F(x)\).  Then
\[
 G(x)
 =F^{p-1}(F(x))
 =F^{p-1}(F(y))
 =G(y)\in K_0^0.
\tag{4.A.7}
\]
Equation (4.A.6) gives \(x\in K_0^0\).  The reverse inclusion follows
from the definition of \(K_1\), hence
\[
 F^{-1}(K_1)\cap D_0=K_0^0.
\tag{4.A.8}
\]
The proper restriction \(F:D_0\to D_1\) has degree two, equal to the
total degree of the ambient quadratic-like map \(F\).  It therefore
contains, with multiplicity, every ambient preimage of every point of
\(D_1\).  No further preimage of \(K_1\) exists outside \(D_0\).
This upgrades (4.A.8) to the actual equality (4.A.2), including at the
critical value.

For \(j\geq1\), the conformal isomorphism in (4.A.5) gives
\[
 F^{-1}(K_{j+1})\cap D_j=K_j.
\tag{4.A.9}
\]
The factorization constructs \(D_j\) as a whole component of
\(F^{-1}(D_{j+1})\).  Since \(K_{j+1}\Subset D_{j+1}\), a connected
subset of \(F^{-1}(K_{j+1})\) meeting \(K_j\) cannot leave \(D_j\).
Thus (4.A.9) proves the component assertion (4.A.3).

Finally, primitivity makes the finitely many \(K_j\) pairwise disjoint.
Choose each terminal Jordan boundary inside its disjoint cycle-member
localization and away from the finite set of critical values, then pull
it back through (4.A.5).  The resulting Jordan pairs isolate
\(K_j\to K_{j+1}\), meet no other member of \(\mathcal K\), and have
precisely the stage degrees just computed. \(\square\)

### Theorem 4.1 (stationary final-component realization)
(`KKL_STATIONARY_FINAL_COMPONENT_REALIZATION`)

The sets in (4.4) satisfy:

\[
 I_m(\widehat K_r)=K_0^r,
\qquad
 \widehat K_r\subset P_m^{-1}(\mathcal K)
 =\mathcal K^m,
\tag{4.6}
\]

\[
 P_m(\widehat K_r)
 =
 F^{m-r}(K_0^0),
\tag{4.7}
\]
and
\[
 \widehat K_b\ne \widehat K_{b+1}.
\tag{4.8}
\]
More precisely,
\[
 \widehat K_b
 \in
 \operatorname{Comp}P_m^{-1}\!\left(F^2(K_0^0)\right),
 \qquad
 \widehat K_{b+1}
 \in
 \operatorname{Comp}P_m^{-1}\!\left(F(K_0^0)\right),
\tag{4.9}
\]
and both are components of
\(\mathcal K^m=P_m^{-1}(\mathcal K)\).
In particular,
\[
 P_m(\widehat K_b)=F^2(K_0^0),
 \qquad
 P_m(\widehat K_{b+1})=F(K_0^0).
\tag{4.10}
\]

#### Proof

The graph identity in (4.6) is Theorem 3.2.  Equations (3.13), (4.1),
and (4.2) give
\[
\begin{aligned}
 P_m(\widehat K_r)
 &=
 F^m(K_0^r)\\
 &=
 F^{m-r}\!\left(F^r(K_0^r)\right)\\
 &=
 F^{m-r}(K_0^0),
\end{aligned}
\tag{4.11}
\]
which proves (4.7) and (4.10).  Both sets in (4.10) are members of the
forward-invariant cycle \(\mathcal K\), so (4.6) follows from (3.12).

Write \(K_j=F^j(K_0^0)\).  Lemma 4.A gives
\[
 F^{-1}(K_1)=K_0^0,
\qquad
 K_1\in\operatorname{Comp}F^{-1}(K_2).
\tag{4.12}
\]
These two statements and the component-composition clause of
Lemma 3.3 give
\[
 K_0^0\in\operatorname{Comp}F^{-2}(K_2).
\tag{4.13}
\]

Repeated component composition in KKL's recursive definition gives
\[
 K_0^r\in\operatorname{Comp}F^{-r}(K_0^0)
 \quad(r\geq1).
\tag{4.14}
\]
Combining (4.12)--(4.14), with \(m=b+2\), yields
\[
\begin{aligned}
 K_0^{b+1}
 &\in\operatorname{Comp}F^{-m}(K_1),\\
 K_0^b
 &\in\operatorname{Comp}F^{-m}(K_2).
\end{aligned}
\tag{4.15}
\]
The component clause of Theorem 3.2 now proves (4.9).

Finally, a connected subset of \(P_m^{-1}(\mathcal K)\) meeting either
component in (4.9) has connected \(P_m\)-image in the finite pairwise
disjoint union \(\mathcal K\).  Its image must remain in the same
cycle member, so maximality in (4.9) makes each graph a component of
\(P_m^{-1}(\mathcal K)\).  The two target members \(K_1,K_2\) are
distinct because the primitive period is greater than one.  Hence the
two graph components are distinct, proving (4.8). \(\square\)

## 5. The stationary degree-one clause is false

The graph coordinate also exposes a separate source error in KKL's
stationary-alignment lemma.  KKL lines 1592--1593 assert that the selected
component \(K\) has degree one under \(f^{N-1}\), and line 1605 identifies
it with \(K_0^b\).  Under the only canonical filled-set realization of
that label, the degree is two.

### Lemma 5.1 (degrees along the selected critical-limb pull)

Let \(c\) and \(v=F(c)\) be the critical point and critical value.  For
every \(s\geq1\), the selected map
\[
 F:K_0^s\longrightarrow K_0^{s-1}
\tag{5.1}
\]
has degree one.  The map
\[
 F:K_0^0\longrightarrow F(K_0^0)
\tag{5.2}
\]
has degree two, while
\[
 F:F(K_0^0)\longrightarrow F^2(K_0^0)
\tag{5.3}
\]
has degree one.

#### Proof

KKL line 501 places \(c\) in the critical limb \(\mathfrak L_0\), places
\(v\) in \(\mathfrak L_p\), and has \(p\ne0\pmod q\) because
\((p,q)=1\) and \(q\geq2\).  The limbs are disjoint.  KKL line 1597
places every \(K_0^{s-1}\), for \(s\geq2\), in
\(\mathfrak L_0\).

For \(s=1\), the target \(K_0^0\) is disjoint from the
critical-value cycle member \(K_1=F(K_0^0)\), by primitivity, while
\(v\in K_1\).  For \(s\geq2\), the target
\(K_0^{s-1}\subset\mathfrak L_0\) is disjoint from
\(v\in\mathfrak L_p\).  Thus, in every case,
\[
 v\notin K_0^{s-1}.
\tag{5.4}
\]
Choose a Jordan neighborhood of \(K_0^{s-1}\) avoiding \(v\).
Every component of its inverse image is an unbranched cover of a simply
connected disk, hence maps biholomorphically to that disk.  The
component containing \(K_0^s\) therefore has degree one.  This
simply-connected-neighborhood argument is essential: absence of a
critical point alone would not rule out a higher-degree unbranched
cover of a multiply connected target.

The central small Julia set \(K_0^0\) contains \(c\) by the definition
of quadratic-like renormalization (KKL line 478).  On an isolating
Jordan neighborhood, Riemann--Hurwitz makes (5.2) a degree-two proper
restriction.  This equals the total quadratic degree.  Finally,
\(F(K_0^0)=K_1\) is disjoint from \(K_0^0\), and its target \(K_2\)
is disjoint from the critical value \(v\in K_1\).  The same
Jordan-neighborhood argument makes (5.3) degree one. \(\square\)

### Theorem 5.2 (stationary degree correction)
(`KKL_STATIONARY_DEGREE_TWO_CORRECTION`)

For \(m=b+2\), the two canonical graph restrictions satisfy
\[
 \deg\!\left(P_m:\widehat K_b\to F^2(K_0^0)\right)=2,
\tag{5.5}
\]
and
\[
 \deg\!\left(P_m:\widehat K_{b+1}\to F(K_0^0)\right)=2.
\tag{5.6}
\]
In particular, KKL's printed degree-one conclusion for
\(K=K_0^b\) cannot hold under the canonical filled-set graph
identification.

#### Proof

We first construct, rather than assume, the isolating restrictions.
For each selected arrow
\[
 K_0^s\longrightarrow K_0^{s-1}\qquad(s\geq1),
\]
the proof of Lemma 5.1 supplies a Jordan target avoiding the critical
value and a univalent selected preimage disk.  Lemma 4.A supplies the
central degree-two Jordan restriction
\(K_0^0\to F(K_0^0)\) and the following univalent restriction
\(F(K_0^0)\to F^2(K_0^0)\).  There are only finitely many arrows.
Starting at the terminal target and shrinking successively, if needed,
makes the selected Jordan restrictions composable.  Their composition
is a proper Jordan restriction of \(F^m\).  Because \(V_m\) is an open
neighborhood of the compact invariant set \(K^0\), all finitely many
source, intermediate, and target disks can be chosen inside the
corresponding proof-used part of \(V_m\).  Its inverse image of the
terminal small Julia set is exactly the component in (4.15).

There is exactly one critical encounter.  For \(r=b+1\), its composite
critical value is \(F(c)\in K_1\); for \(r=b\), the final univalent
cycle step makes it \(F^2(c)\in K_2\).  Thus every critical value of
each composed restriction lies in its terminal continuum, exactly as
required in (3.25).  Lemma 3.5 makes every continuum involved full, and
the disjoint localizations from Lemma 4.A exclude all other cycle
members.  Hence all hypotheses of Lemma 3.4 hold at both graph
components in (4.9).

Lemma 3.4 now identifies the analytic and ideal-boundary degrees of the
graph restrictions with the corresponding local degrees of \(F^m\).
For \(r=b\),
\[
 F^m|_{K_0^b}
 =
 \left(F|_{F(K_0^0)}\right)
 \circ
 \left(F|_{K_0^0}\right)
 \circ
 \left(F^b|_{K_0^b}\right).
\tag{5.7}
\]
Lemma 5.1 gives degrees \(1,2,1\), read from right to left, so the
product is \(2\).  For \(r=b+1\),
\[
 F^m|_{K_0^{b+1}}
 =
 \left(F|_{K_0^0}\right)
 \circ
 \left(F^{b+1}|_{K_0^{b+1}}\right),
\tag{5.8}
\]
whose degrees are \(2\) and \(1\).  This proves (5.5)--(5.6).
\(\square\)

There is an exhaustive interpretive dichotomy:

1. if KKL's \(K_0^b\subset\mathcal K^m\) means the canonical graph lift,
   the degree-one sentence is contradicted by (5.5);
2. if it means a different final component, the source proof does not
   construct that component or relate it to the line-1603
   pass-through predicate.

### Corollary 5.3 (quantitative repair conditional on a typed lamination)

Fix one \(r_*\in\{b,b+1\}\).  Suppose the final immersion restriction
supplies an occurrence-tagged lamination
\[
 B\subset I_m^*A_m
\tag{5.9}
\]
in \(U^m\setminus\mathcal K^m\) such that:

1. for every leaf \(\alpha\in A_m\), the retained restriction
   \(I_m^*\alpha\) contains a leaf of \(B\);
2. every leaf of \(B\) is a proper path with one end on the fixed graph
   component \(\widehat K_{r_*}\) and its other end on
   \(\mathcal K^m\setminus\widehat K_{r_*}\); and
3. \(B\) is a measurable lamination in KKL's final ideal marking, not
   merely an independently selected path for each leaf.

Put
\[
 \mathscr V=U^0\setminus\mathcal K,\qquad
 \mathscr V'=U^m\setminus\mathcal K^m,
\tag{5.C.1}
\]
and let
\[
 X'
 =
 \partial_{\!I}\widehat K_{r_*}
 \subset\partial_{\!I}\mathscr V'
\tag{5.C.2}
\]
be the corresponding inner prime-end boundary component.  Then
\[
 P_m:\mathscr V'\longrightarrow\mathscr V
\tag{5.C.3}
\]
is a holomorphic covering, is proper on \(X'\), and has degree exactly
two on \(X'\).

Here is the required verification.  The map \(P_m\) is proper and
\(\mathcal K^m=P_m^{-1}(\mathcal K)\), so the restriction (5.C.3) is
proper.  If \(x\) is critical for
\[
 P_m=f_0\circ f_1\circ\cdots\circ f_{m-1},
\]
then for some \(j\) the point
\[
 x_j=(f_{j+1}\circ\cdots\circ f_{m-1})(x)
\]
is critical for \(f_j\).  Kahn's pullback calculation (locked source
lines 382--385), iterated from level \(j\), puts \(x_j\in K^{j+1}\).
The exact preimage identities of Lemma 3.1 then put \(x\in K^m\).
Write \(x=\Gamma_m(z)\).  The analytic graph identity
\(P_m\Gamma_m=F^m\) shows that \(z\) is critical for \(F^m\).  Hence
\(F^\ell(z)=c\) for some \(0\leq\ell<m\), and
\[
 P_m(x)=F^m(z)=F^{m-\ell}(c)\in\mathcal K,
\tag{5.C.4}
\]
because \(c\in K_0^0\) and the small-Julia cycle is forward invariant.
Thus every critical point of \(P_m\) belongs to
\(P_m^{-1}(\mathcal K)=\mathcal K^m\).  The restriction (5.C.3) is
therefore unbranched, and properness makes it a covering.

Finally, Theorem 5.2 and the annular-collar/prime-end clause of
Lemma 3.4 give degree two and proper prime-end action on \(X'\).  Every
leaf of \(B\) ends at \(X'\) by clause 2, so all
hypotheses of KKL's pushforward-lamination lemma are now explicitly
typed.

KKL's domination lemma then gives
\[
 \mathcal W(A_m)\leq\mathcal W(B).
\tag{5.10}
\]
Their pushforward-lamination lemma must be used with \(d=2\), giving a
target lamination \(C\) with
\[
 \mathcal W(B)
 \leq
 2\mathcal W(C)+4.
\tag{5.11}
\]
For a lamination ending at one fixed small-Julia component, KKL's
subsequent single-component bound gives
\[
 \mathcal W(C)\leq2\mathcal W(\mathcal RF)
\tag{5.12}
\]
and hence
\[
 \mathcal W(A_m)
 \leq
 \mathcal W(B)
 \leq
 4\mathcal W(\mathcal RF)+4.
\tag{5.13}
\]
Thus the degree error changes a universal coefficient and additive
constant, but not the \(O(\mathcal W(\mathcal RF))\) conclusion in KKL's
high-type near-degenerate regime.  The word “conditional” is essential:
the occurrence-tagged proper-path lamination is the next gate.

### Proposition 5.4 (conditional native stationary repair)

The one-component conclusion needed in KKL's native stationary estimate
has the following exact repair template, which does not use the
two-incidence refinement.
Put
\[
 m=N-1=b+2,
 \qquad
 Q=K_0^{m-1}=K_0^{b+1},
\tag{5.14}
\]
and let
\[
 \widehat Q
 =
 \bigl(I_m|_{K^m}\bigr)^{-1}(Q).
\tag{5.15}
\]
Assume, in addition to KKL line 1603, the following typed extraction
clause:

> The retained final restriction contains an occurrence-tagged
> measurable lamination \(B\subset I_m^*A_m\) satisfying all three
> clauses of Corollary 5.3 with distinguished end \(\widehat Q\).

Then:

1. \(\widehat Q\) is a component of
   \(\mathcal K^m=P_m^{-1}(\mathcal K)\);
2. \(B\) gives a retained proper leaf incident to \(\widehat Q\) for
   every source leaf of \(A_m=A_{N-1}\);
3. \(P_m\) has degree exactly two on \(\widehat Q\); and
4. the stationary lamination satisfies
   \[
   \mathcal W(A_m)
   \leq
   \mathcal W(B)
   \leq
   4\mathcal W(\mathcal RF)+4.
   \tag{5.16}
   \]

Consequently, **conditional on that extraction clause**, KKL's
\(O(\mathcal W(\mathcal RF))\) stationary estimate is valid after
changing the selected pull from \(K_0^b\) to \(K_0^{b+1}\) and changing
the asserted degree from one to two.

#### Proof

**Component.**  Put \(K_1=F(K_0^0)\).  Lemma 4.A gives the actual
ambient equality
\[
 F^{-1}(K_1)=K_0^0.
\tag{5.17}
\]
By KKL's recursive definition, \(Q\) is a component of
\(F^{-(m-1)}(K_0^0)\).  Equation (5.17) gives
\[
 F^{-m}(K_1)
 =
 F^{-(m-1)}(K_0^0),
\tag{5.18}
\]
so \(Q\) is a component of \(F^{-m}(K_1)\).  The members of the finite
primitive cycle \(\mathcal K\) are pairwise-disjoint compacta, and
preimages over different cycle members are disjoint.  A connected set
in \(F^{-m}(\mathcal K)\) meeting \(Q\) must therefore remain over
\(K_1\).  Thus \(Q\) is a component of \(F^{-m}(\mathcal K)\), and
the component clause of Theorem 3.2 makes \(\widehat Q\) a component
of \(P_m^{-1}(\mathcal K)\).

**Source pass-through and the remaining bridge.**  Apply KKL line 1603 with
\[
 n=m-1=b+1.
\tag{5.19}
\]
This is within its declared range \(n\geq b\), and its wave is
\[
 A_{n+1}=A_m=A_{N-1},
\tag{5.20}
\]
which is defined.  Thus no \(A_N\) is invoked.  This proves the
source-language pass-through of \(Q\) at the final depth.

It does **not**, by itself, prove the typed extraction clause.  KKL lines
2081--2097 define immersion restriction as a set of proper preimage
paths, allow the restriction to split, and discard subordinate or
non-marked components.  Lines 1600 and 1602 supply the restricted path
and the separator, but the source does not prove that the two relevant
ideal tails lie in one retained component after \(\mathcal K^m\) is
removed.  The extraction clause is therefore a genuine hypothesis, not
a paraphrase of “passes through.”

**Degree and width.**  Formula (5.6), with \(b+1=m-1\), gives
\[
 \deg(P_m|\widehat Q)=2.
\tag{5.21}
\]
The extraction clause and KKL's domination lemma first give
\(\mathcal W(A_m)\leq\mathcal W(B)\).  Applying KKL's
pushforward-lamination lemma with \(d=2\) then gives
\[
 \mathcal W(B)\leq2\mathcal W(C)+4.
\tag{5.22}
\]
KKL's unchanged terminal comparison gives
\(\mathcal W(C)\leq2\mathcal W(\mathcal RF)\).  Combining it with
KKL's restriction domination
\(\mathcal W(A_m)\leq\mathcal W(B)\) proves (5.16). \(\square\)

This conditional repair is deliberately one-component-valued.  The component on the
other end of the proper subpath may depend on the leaf occurrence.  Thus
even after its extraction hypothesis is discharged it will repair only
the native KKL estimate; it will not select the fixed pair
\(C_b,C_{b+1}\) needed by the project's KL binder.

## 6. Exact residual incidence gate

The graph problem and the path-refinement problem are different.
Theorem 4.1 gives two actual, distinct components of the single final
fiber-product obstacle package.  The proved conditional off-by-one
reduction says only that, **if** the two-sided noncollision theorem
validates KKL line 1603, then every occurrence in \(A_m\) has both
source-language pass-through predicates at \(K_0^b\) and
\(K_0^{b+1}\).  The actual ledger node
`KKL_STATIONARY_TWO_PULLBACK_PASS_THROUGH` remains open.  Before either
source predicate can be combined with the graph components, one must
prove the two-occurrence binder, retained-path realization, and
terminal noncollision.  After those gates, one must still prove:

> for every retained occurrence \(\alpha\in A_m\), one component (or one
> source-faithful finite ordered chain of components) of the actual
> restriction
> \[
>   I_m^{-1}(\alpha)\setminus\mathcal K^m
> \tag{6.1}
> \]
> has terminal incidences on both \(\widehat K_b\) and
> \(\widehat K_{b+1}\), with all
> intervening component encounters retained.

The first, weaker gate is
`KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION`: prove the typed
extraction clause in Proposition 5.4 for \(Q=K_0^{m-1}\).

The stronger fixed-pair gate is
`KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT`.  It cannot be
deduced from Theorem 4.1 alone: two graph lifts can exist while the two
separately selected shallower restriction components refine to different
components at the final level.  KKL's \(m\)-unbreakability is the
candidate input for excluding that split, but the required transitivity
statement for occurrence-tagged restrictions must be written and proved.

## 7. Adversarial audit

1. **Map typing.**  The final projection is \(P_m=f^m\), not \(F^m\).
   The latter appears only on the base filled set in (3.6).
2. **No invented inverse branch.**  The graph is the inverse of the
   proved homeomorphism \(I_m|_{K^m}\), not a symbolic return word.
3. **No local connectivity.**  Compact filled-set homeomorphisms replace
   any boundary landing argument.
4. **No component shortcut.**  Whole-component status is proved through
   Lemma 4.A, (4.12)--(4.15), and Theorem 3.2, not inferred from set
   containment.
5. **Distinctness is typed.**  It is proved from the two different
   \(P_m\)-images in the finite disjoint cycle.
6. **Degree is not inferred from graph existence.**  The complete
   critical itinerary is counted in Lemma 5.1; it gives degree two.
7. **No order from separation.**  Equation (4.8) says only
   \(\widehat K_b\ne\widehat K_{b+1}\).
8. **No refinement from nesting.**  The final occurrence-level
   restriction remains open in Section 6.
9. **No unconditional width repair.**  Equation (5.13) still requires
   the missing occurrence-tagged incidence lamination.
10. **No width claim from existence.**  Existence of two components carries no extremal
   width by itself.
11. **No KL relabeling.**  Neither component has yet been realized as
   \(S_Y^v\) for a KL puzzle vertex.
12. **Global status.**  VAAPC-I, UPTCR, all global closure gates, and MLC
    remain open.
