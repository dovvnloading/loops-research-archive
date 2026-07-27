# Embedded-disk accessible-footprint theorem

## 1. Purpose and status

This note proves the abstract analytic theorem needed to turn geometric
complement footprints into KKL immersion pullbacks.

The theorem applies to a holomorphic embedding of conformal disks only
after the embedding has been shown to extend continuously to the two
conformal ideal closures.  That hypothesis is denoted `(PE)`.  It is not a
consequence of interior injectivity.

For the fixed Kahn--Lyubich direct-decoration pair, `(PE)` is now
source-locked rather than assumed.  Kahn defines the ideal boundary by
uniformization, and Kahn--Lyubich call the named
\(\lambda,\xi,\eta\) arcs a tiling of that same ideal boundary and state
that the inclusion immersion extends continuously to it.  The
pseudo-pieces are hyperbolic conformal disks, so the deck group is
trivial and Kahn's ideal closure is literally the closed uniformizing
disk.  No local connectivity of the physical Julia set enters this
identification.

The continuous ideal extension `(PE)` is therefore source-locked for the
fixed direct-decoration **immersion**.  Application of the present theorem
to that map is still conditional on global interior injectivity, which KL
do not state and the previous project proof did not establish.  Once an
embedding is available, this theorem converts any independently
established complement-access footprint into an exact KKL pullback
criterion.  It does not itself prove the horizontal outer-cap geometry,
compute the source \(\xi,\eta\) footprints, or prove that the resulting
pullbacks form a partial marking.

No statement here proves VAAPC-I, UPTCR, or MLC.

## 2. Source-locked KKL definitions

The audited KKL source is:

```text
.tmp_wave_audit/waves-with-Misha.tex
  AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The proof uses:

- line 406: a proper path extends continuously to two points of the ideal
  boundary;
- lines 1844--1868: ideal closure, connected ideal sets, and
  subordination;
- lines 2081--2094: restriction of a target proper path by an immersion
  and the universal definition of \(\iota^*X\).

The direct-decoration specialization also uses the following two locked
primary sources.

```text
.tmp_kl06_source/wad.tex
  B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580

.tmp_kl08_source/psiql.tex
  6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
```

The exact source chain is:

1. Kahn I, `wad.tex`, lines 169--175, defines the ideal closure of a
   hyperbolic surface \(S\) from a universal cover
   \(\pi:\mathbb D\to S\), its deck group, and its limit set
   \(\Lambda\):
   \[
      \widehat S=(\overline{\mathbb D}\setminus\Lambda)/\Gamma.
   \]
2. KL II, `psiql.tex`, line 6, refers to Kahn I for the general and
   detailed pseudo-quadratic-like framework.
3. The physical puzzle pieces are closed Jordan domains
   (`kingdom.tex`, lines 28, 32, and 273--278), so the central closed
   copy may not simply be declared an open member of a van Kampen cover.
   Use instead the central interior
   \(U_0=\operatorname{int}Y\) and the open tile images \(T_i\).
   These sets cover the pseudo-piece.  Indeed, `kingdom.tex`, lines
   56--62, says that \(K_Y\) meets \(\partial Y\) only at the finitely
   many vertices; `psiql.tex`, lines 139--144, puts every such vertex in
   \(S_Y\), so no vertex is a point of the path surface.  Every other
   central-boundary point lies in one \(Y_i\), hence in its tile by
   lines 146--160.  The sets \(U_0,T_i\) are open disks, distinct tiles
   are disjoint, and
   \(U_0\cap T_i=\operatorname{int}Y\cap Y_i\) is path-connected.
   For the last assertion, join two points first by a path in the
   source-locked simply connected set \(Y_i\).  The set \(Y_i\) is
   relatively open in the closed Jordan disk \(Y\), so the compact path
   image has positive distance from \(Y\setminus Y_i\).  A sufficiently
   small Schoenflies-collar isotopy of \(\partial Y\), fixed at the two
   interior endpoints, pushes every boundary contact of the path into
   \(\operatorname{int}Y\) while remaining in \(Y_i\).  Hence the path
   can be chosen in \(U_0\cap T_i\).  Thus \(\{U_0,T_i\}\) is a
   finite open cover with star nerve, all vertex spaces are simply
   connected, and all nonempty edge intersections are path-connected.
   Repeated van Kampen gives trivial fundamental group.
4. The bold domain \(\mathbf U^m\) is itself a noncompact simply
   connected disk, hence uniformizes as \(\mathbb D\) or \(\mathbb C\).
   The pseudo-piece projection
   \(\pi_Y:\mathbf Y\to\mathbf U^m\) is a nonconstant holomorphic
   immersion (`psiql.tex`, lines 107--112), and its image omits \(S_Y\)
   by the path definition in lines 97--107.  If
   \(\mathbf U^m\cong\mathbb D\), a hypothetical
   \(\mathbf Y\cong\mathbb C\) would give a bounded nonconstant entire
   map, contradicting Liouville.  If
   \(\mathbf U^m\cong\mathbb C\), the same hypothetical entire map omits
   at least two points for the two audited direct-decoration pieces
   \(P,Q_a\): \(P\) has \(2^n\geq2\) distinct vertices
   (`kingdom.tex`, lines 116--118), every boundary vertex belongs to
   \(S_Y\) (`psiql.tex`, lines 139--144), and the univalent branch
   preserves the corresponding distinct vertices for \(Q_a\).  Little
   Picard is then a contradiction.  The source cannot be compact:
   otherwise its nonconstant open projection would have compact, hence
   closed, image in the connected noncompact target while also having
   nonempty open image.  The sphere is therefore excluded.  Hence
   \(\mathbf P,\mathbf Q_a\cong\mathbb D\).  No broader pseudo-piece
   class is asserted without a separate omitted-value audit.
5. For a disk the deck group is trivial and \(\Lambda=\varnothing\).
   Thus Kahn's ideal closure is the closed uniformizing disk.  The nearby
   generic sentence in Kahn I that \(\Lambda\) is Cantor is not used in
   this trivial-group specialization.
6. KL II, `psiql.tex`, lines 231--244, explicitly calls
   \(\lambda_i,\xi_i,\eta_i\) a tiling of *the ideal boundary* of the
   pseudo-piece, and lines 248--253 state that the inclusion immersion
   extends continuously to that boundary.  No second symbolic
   compactification is introduced.

Items 1--6 prove `(PE)` for the fixed KL inclusion and identify the named
boundary with the conformal ideal circle.  The unsafe alternative
argument that a proper curve must eventually remain in one tile is not
used: a curve can approach a shared ideal vertex through alternating
adjacent sectors.

For a holomorphic immersion \(\iota:U\to V\), a source ideal subset
\(C\) is **admissible for** a connected target ideal set \(I\) if

\[
 \forall\gamma\text{ proper in }V,\qquad
 \left[
    \iota^*\gamma=\{\delta\},
    \quad
    \delta\preceq C
 \right]
 \Longrightarrow
 \gamma\preceq I.
\tag{2.1}
\]

Here \(\preceq\) denotes subordination.

## 3. Disk subordination

Let \(W\cong\mathbb D\) be a conformal disk and
\(\widehat W=W\sqcup S_W\) its conformal ideal closure.

### Lemma 3.1

Let \(A\subset S_W\) be connected, and let \(\gamma\) be a proper path in
\(W\).  Then

\[
 \gamma\preceq A
 \quad\Longleftrightarrow\quad
 \gamma(-),\gamma(+)\in A.
\tag{3.1}
\]

### Proof

If one endpoint, say \(\gamma(-)\), does not belong to \(A\), the compact
Hausdorff circle \(S_W\) has a neighborhood of \(A\) whose closure omits
\(\gamma(-)\).  No homotopy relative to ideal endpoints can move
\(\gamma(-)\), so \(\gamma\) is not subordinate to \(A\).

Conversely, a connected subset of a circle is a point, an arc, or the
whole circle.  If both endpoints lie in \(A\), any path between them in
the disk is homotopic relative to its endpoints to a path in an
arbitrarily thin one-sided collar of the subarc of \(A\) joining the
endpoints.  If the endpoints coincide, use a hairpin in an arbitrarily
small collar of that point.  Therefore the proper homotopy class has a
representative in every neighborhood of \(A\).  \(\square\)

### Lemma 3.2

Let \(A\subset S_W\) be arbitrary.

1. If a proper path is subordinate to \(A\), both of its ideal endpoints
   belong to \(A\).
2. If \(p\in A\), a proper hairpin with both ideal endpoints equal to
   \(p\) is subordinate to \(A\).

### Proof

If \(p\notin A\), the open set
\(\widehat W\setminus\{p\}\) is a neighborhood of \(A\).  A path whose
endpoint is \(p\) cannot be homotoped relative to its ideal endpoints
into that neighborhood.  This proves the first assertion.

For the second, every neighborhood \(N\) of \(A\) is in particular a
neighborhood of \(p\).  In a disk coordinate centered at the prime end
\(p\), a sufficiently small one-sided hairpin is contained in \(N\).
All such hairpins represent the same proper homotopy class relative to
the repeated endpoint \(p\).  Hence that class has a representative in
every \(N\).  \(\square\)

## 4. Boundary fibers of a disk embedding are light

Let \(U,V\) be conformal disks and let

\[
 \iota:U\longrightarrow V
\]

be a holomorphic embedding.  Write
\(\Omega=\iota(U)\).  Assume:

\[
 \tag{PE}
 \iota\text{ extends continuously to }
 \overline\iota:\widehat U\longrightarrow\widehat V.
\]

After disk uniformizations, write the same map as

\[
 F:\mathbb D\longrightarrow\mathbb D,
 \qquad
 \overline F:\overline{\mathbb D}\longrightarrow
 \overline{\mathbb D}.
\]

### Lemma 4.1

For every \(w\in\overline{\mathbb D}\), every connected subset of

\[
 \overline F^{-1}(w)\cap S^1
\]

is a singleton.

### Proof

Suppose a connected fiber subset contains at least two points.  A
nondegenerate connected subset of a circle contains a nondegenerate
circular arc \(J\).  The function

\[
 H(z)=F(z)-w
\]

is holomorphic and nonconstant in \(\mathbb D\), continuous on \(J\), and
has boundary value \(0\) on \(J\).

Here is a self-contained bounded-holomorphic uniqueness argument.  If
\(H\not\equiv0\), precompose with a disk automorphism so that
\(H(0)\ne0\).  A disk automorphism is a smooth circle diffeomorphism, so
the preimage of \(J\) still has positive arclength; relabel it \(J\).
Put

\[
 M=\max(1,\|H\|_\infty),\qquad
 u_r(t)=\log M-\log|H(re^{it})|\geq0.
\]

Jensen's formula gives

\[
 \frac1{2\pi}\int_0^{2\pi}\log|H(re^{it})|\,dt
 \geq \log|H(0)|,
\]

and therefore

\[
 \int_0^{2\pi}u_r(t)\,dt
 \leq 2\pi\bigl(\log M-\log|H(0)|\bigr)
 \tag{4.1}
\]

uniformly for \(0<r<1\).  For every \(e^{it}\in J\), continuity of the
boundary extension and \(H|_J=0\) give
\(u_r(t)\to+\infty\) as \(r\uparrow1\).  Since \(J\) has positive
measure, Fatou's lemma says

\[
 \liminf_{r\uparrow1}\int_0^{2\pi}u_r(t)\,dt=+\infty,
\]

contradicting (4.1).  Hence \(H\equiv0\), contrary to nonconstancy of
\(F\).  No nondegenerate connected boundary-fiber subset exists.
\(\square\)

## 5. Every intersection component acquires prime-end limits

Let

\[
 \gamma:(0,1)\longrightarrow V
\]

be a target proper path, with continuous extension to
\([0,1]\to\widehat V\).  Let \(A=(a,b)\) be a parameter component of

\[
 \gamma^{-1}(\Omega).
\]

Define

\[
 \beta
 =
 \iota^{-1}\circ\gamma|_A:A\longrightarrow U.
\tag{5.1}
\]

### Lemma 5.1

\(\beta\) is topologically proper: for every compact \(K\Subset U\),

\[
 \beta^{-1}(K)
\]

is compact in \(A\).

### Proof

The set \(\iota(K)\) is compact in \(V\), so
\(\gamma^{-1}(\iota(K))\) is compact in \((0,1)\).
Moreover,

\[
 \beta^{-1}(K)
 =
 A\cap\gamma^{-1}(\iota(K)).
\]

This intersection is closed in
\(\gamma^{-1}(\iota(K))\).  Indeed, if points of it converge to a finite
endpoint \(a\in(0,1)\), then continuity gives
\(\gamma(a)\in\iota(K)\subset\Omega\), contradicting maximality of the
component \(A\).  If they converge to \(0\) or \(1\), properness of
\(\gamma\) gives an ideal target limit, whereas every point of
\(\iota(K)\) is interior.  The same argument applies at \(b\).
Thus \(\beta^{-1}(K)\) is a closed subset of a compact set.  \(\square\)

For the left end of \(A\), define

\[
 \mathcal C_a
 =
 \bigcap_{\epsilon>0}
 \overline{
   \beta\bigl(A\cap(a,a+\epsilon)\bigr)
 }^{\,\widehat U}.
\tag{5.2}
\]

Define \(\mathcal C_b\) analogously.

### Lemma 5.2

Each of \(\mathcal C_a,\mathcal C_b\) is a singleton in \(S_U\).
Consequently, \(\beta\) extends continuously to

\[
 \overline\beta:[a,b]\longrightarrow\widehat U
\]

with both endpoint values in \(S_U\).  Thus \(\beta\) is a KKL proper
path.

### Proof

The tail closures in (5.2) are nested nonempty compact connected sets.
Their intersection is therefore nonempty, compact, and connected.
Lemma 5.1 forces the intersection into \(S_U\).

Continuity of \(\gamma\) and `(PE)` gives

\[
 \overline\iota(\mathcal C_a)=\{\overline\gamma(a)\}.
\]

Hence \(\mathcal C_a\) is a connected subset of one boundary fiber of
\(\overline\iota\).  Lemma 4.1 makes it a singleton.  The same proof
applies to \(\mathcal C_b\).

A curve in a compact Hausdorff space extends continuously to an endpoint
when its endpoint cluster set is a singleton.  This gives the asserted
extension.  \(\square\)

### Corollary 5.3

Under `(PE)`, every parameter component of
\(\gamma^{-1}(\Omega)\) produces, by (5.1), a KKL proper source path.
Consequently, if the **entire geometric restriction**
\(\iota^*\gamma\) contains a unique proper path \(\delta\), then every
parameter traversal traces \(\delta\).  The uniqueness assumption also
excludes any additional proper path obtained by switching branches at a
self-intersection or retraced portion of the target trace.

No canonical bijection with all geometric restriction paths is asserted:
for a self-intersecting target trace, its full preimage can contain a
branch-switching path that is not the lift of any one parameter
component.  Lemma 5.2, rather than such a bijection, is the fact used
below.

## 6. Full access footprint

For \(p\in S_U\), define its complement-access footprint
\(\Phi_\iota(p)\subset S_V\) as follows.

If \(\overline\iota(p)\in S_V\), put

\[
 \Phi_\iota(p)=\{\overline\iota(p)\}.
\tag{6.1}
\]

If \(\overline\iota(p)\in V\), put

\[
 \Phi_\iota(p)
 =
 \left\{
 \xi\in S_V:
 \begin{array}{l}
 \text{there is a path }
 a:[0,1]\to\widehat V,\\
 a(0)=\xi,\quad
 a(1)=\overline\iota(p),\\
 a((0,1))\subset V\setminus\Omega
 \end{array}
 \right\}.
\tag{6.2}
\]

If more than one complement component lands at
\(\overline\iota(p)\), formula (6.2) takes their union.  A refined record
may retain the components separately; the union is the correct datum for
the universal KKL implication.

Notice that

\[
 \overline\iota(p)\notin\Omega
 \quad\text{for every }p\in S_U.
\tag{6.3}
\]

Indeed, if
\(\overline\iota(p)=\iota(u)\in\Omega\), take \(z_n\to p\) in \(U\).
Then \(\iota(z_n)\to\iota(u)\), and continuity of the inverse
\(\iota^{-1}:\Omega\to U\) gives \(z_n\to u\).  This contradicts
uniqueness of limits in the Hausdorff compactification
\(\widehat U\), because \(p\ne u\).

For arbitrary \(C\subset S_U\), define the endpoint shadow

\[
 \operatorname{Sh}_\iota(C)
 =
 \bigcup
 \left\{
 \{\gamma(-),\gamma(+)\}:
 \begin{array}{l}
 \gamma\text{ is target proper},\\
 \iota^*\gamma=\{\delta\},\\
 \delta\preceq C
 \end{array}
 \right\}.
\tag{6.4}
\]

### Theorem 6.1: accessible-footprint characterization

Under `(PE)`,

\[
 \boxed{
 \operatorname{Sh}_\iota(C)
 =
 \bigcup_{p\in C}\Phi_\iota(p)
 }
\tag{6.5}
\]

for every \(C\subset S_U\), with no connectedness assumption on \(C\).

Consequently, for every connected \(I\subset S_V\),

\[
 \boxed{
 C\text{ is KKL-admissible for }I
 \quad\Longleftrightarrow\quad
 \Phi_\iota(p)\subset I
 \text{ for every }p\in C.
 }
\tag{6.6}
\]

### Proof

Let \(\gamma\) occur in the definition of
\(\operatorname{Sh}_\iota(C)\).  By Lemma 5.2, every parameter component
of \(\gamma^{-1}(\Omega)\) is a KKL proper path.

If the entire geometric restriction contains the unique proper path
\(\delta\), then every source traversal represents that same path and no
branch-switching proper path is available.  There can be only finitely
many traversals.  Otherwise choose an interior point \(x\) of
\(\delta\).  Infinitely many traversals give infinitely many points of
the closed set
\(\overline\gamma^{-1}(\iota(x))\subset[0,1]\), hence an accumulation
parameter \(t_*\).  It cannot be \(0\) or \(1\), because the two endpoint
values of the target proper path lie in \(S_V\), whereas
\(\iota(x)\in V\).  Thus \(t_*\in(0,1)\).  But
\(\gamma(t_*)=\iota(x)\in\Omega\), so openness of \(\Omega\) puts a
parameter neighborhood of \(t_*\) in one component of
\(\gamma^{-1}(\Omega)\), contradicting accumulation from distinct
components.

Take the first and last source traversals.  The initial target tail lies
in \(V\setminus\Omega\) until it reaches one source endpoint \(p_-\) of
\(\delta\), and the terminal tail similarly leaves from \(p_+\).  Thus

\[
 \gamma(-)\in\Phi_\iota(p_-),\qquad
 \gamma(+)\in\Phi_\iota(p_+).
\]

Subordination \(\delta\preceq C\) implies
\(p_-,p_+\in C\) by Lemma 3.2.  This proves

\[
 \operatorname{Sh}_\iota(C)
 \subset
 \bigcup_{p\in C}\Phi_\iota(p).
\]

Conversely, take \(p\in C\) and
\(\xi\in\Phi_\iota(p)\).  Choose a simple source hairpin with both ideal
ends at \(p\), subordinate to \(C\) by Lemma 3.2.

If \(\overline\iota(p)=\xi\in S_V\), its image is already a target
proper hairpin and has exactly the chosen source hairpin as its
restriction.

Otherwise put \(x=\overline\iota(p)\in V\setminus\Omega\), where the
set difference follows from (6.3), and let
\(a:[0,1]\to\widehat V\) witness
\(\xi\in\Phi_\iota(p)\).  Concatenate \(a\), the image of the source
hairpin, and the reverse of \(a\).  Repetition of the same access path is
allowed because KKL proper paths need not be simple.  The open part of
both access traversals lies in \(V\setminus\Omega\), while the middle
part lies in \(\Omega\).  Hence the target path has exactly the chosen
source hairpin as its unique proper restriction and has both target
endpoints equal to \(\xi\).  Therefore

\[
 \xi\in\operatorname{Sh}_\iota(C).
\]

This proves (6.5).  By Lemma 3.1, the universal implication (2.1) holds
exactly when every possible target endpoint in (6.5) lies in \(I\).
This is (6.6).  \(\square\)

### Repetition audit

If KKL restrictions are treated with parametrized multiplicity, uniqueness
immediately means one parameter component.  If repeated traversals with
the same image are identified, the first/last argument above gives the
same endpoint conclusion.  No conclusion depends on deleting a compact
loop without proof.

## 7. Exact safe-set formula

For connected target \(I\subset S_V\), define

\[
 S_I
 =
 \{p\in S_U:\Phi_\iota(p)\subset I\}.
\tag{7.1}
\]

Theorem 6.1 gives:

\[
 C\text{ is \(I\)-admissible}
 \quad\Longleftrightarrow\quad
 C\subset S_I.
\tag{7.2}
\]

In particular \(S_I\) itself is admissible, and every admissible subset
is contained in it.  Therefore the maximal set in KKL's definition
exists uniquely and

\[
 \boxed{\iota^*I=S_I.}
\tag{7.3}
\]

This is a maximum, not merely a choice among incomparable maximal
subsets.  Its connected components are exactly the maximal connected
admissible subsets.

If internal source ideal points are partitioned into complement-access
classes \(E_G\) with constant footprint \(\Phi(G)\), then

\[
 S_I
 =
 P_I
 \cup
 \bigcup_{\Phi(G)\subset I}E_G,
\tag{7.4}
\]

where

\[
 P_I
 =
 \{p\in S_U:
       \overline\iota(p)\in I\}.
\tag{7.5}
\]

The criterion is full footprint containment

\[
 \Phi(G)\subset I,
\]

not nonempty contact, equality of finite labels, or containment in
\(\overline I\).

Equations (7.1)--(7.5) do not automatically prove:

- that pullbacks of several target intervals are pairwise disjoint;
- that they form a partial ideal marking;
- that covering endpoints refine immersion endpoints;
- properness or end-properness; or
- stability under root enlargement.

## 8. Conditional direct-decoration specialization

Let

\[
 \boldsymbol\iota:\mathbf Q_a\longrightarrow\mathbf P
\]

be either fixed degree-one direct-decoration immersion.  Section 2 proves
that both pseudo-pieces are conformal disks, that their named KL
boundaries are their conformal ideal boundaries, and that
\(\boldsymbol\iota\) satisfies `(PE)`.

Assume additionally that \(\boldsymbol\iota\) is globally injective.  This
is an open source-specific obligation for a general KL \(\psi\)-ql stage,
not a conclusion of `(PE)`.

The formulas in this section are conditional on a separate geometric
input:

\[
 \tag{OFP}
 \Phi_{\boldsymbol\iota}(p)
 =
 \overline{\lambda}_{t,j(i)}
 \quad
 \text{for every }
 p\in\operatorname{relint}\lambda_{s,i}.
\]

`(OFP)` holds in the literal common-coordinate nested-annulus model, but
it has not been derived from the general KL degree-one annulus immersion.
In particular, degree one and continuous boundary extension alone do not
force a universal-cover lift to be a translation.

Assume `(OFP)`.  For a point

\[
 p\in\operatorname{relint}\lambda_{s,i}
\]

of a source \(O\)-side, the footprint hypothesis gives

\[
 \Phi_{\boldsymbol\iota}(p)
 =
 \overline{\lambda}_{t,j(i)}.
\tag{8.1}
\]

The right-hand side is the complete closed target \(O\)-port, including
both wrapping corners, and is independent of \(p\) along the open source
\(O\)-side.  At a source wrapping endpoint itself the boundary image is
the corresponding target wrapping endpoint, so (6.1), rather than
(8.1), applies.

Theorem 6.1 and (7.3) now give the exact equivalence

\[
 \boxed{
 \operatorname{relint}\lambda_{s,i}
 \subset \boldsymbol\iota^*I
 \quad\Longleftrightarrow\quad
 \overline{\lambda}_{t,j(i)}\subset I
 }
\tag{8.2}
\]

for every connected target ideal set \(I\).

The footprint formula supplies the negative direction for the open target
port:

\[
 E\not\subset
 \boldsymbol\iota^*(\lambda_{t,j(i)})
\tag{8.3}
\]

for every nondegenerate source
\(E\Subset\operatorname{relint}\lambda_{s,i}\), because the target
\(O\)-interval is open while (8.1) contains both wrapping corners.
The abstract converse realizes an excluded corner by a repeated-access
target proper path; it need not be a simple crosscut.  The explicit simple
crosscut belongs only to the additional horizontal-cap geometry of the
`(CI)` model.

The smallest native open candidate is the tile-star

\[
 I^\star_{t,j}
 =
 \operatorname{relint}\xi_{t,j}
 \cup\{p_j^-\}
 \cup\operatorname{relint}\lambda_{t,j}
 \cup\{p_j^+\}
 \cup\operatorname{relint}\eta_{t,j},
\tag{8.4}
\]

understood as the unique open ideal interval between the two neighboring
target Julia vertices that contains \(\lambda_{t,j}\); the two far
vertices are excluded.  It contains the closed \(O\)-port.  Formula
(8.2) proves

\[
 \operatorname{relint}\lambda_{s,i}
 \subset
 \boldsymbol\iota^*I^\star_{t,j(i)}.
\tag{8.5}
\]

The tile-star has native combinatorial length three: it contains the
target \(O\)-interval and the two adjacent \(J\)-intervals.  This bound is
independent of the satellite period and the corridor length.

This does not determine the footprints of the source \(\xi,\eta\) sides,
determine the rest of the exact set
\(\boldsymbol\iota^*I^\star_{t,j(i)}\), prove pairwise disjointness for
the family of tile-star pullbacks, or establish a partial action marking.

## 9. Exact remaining geometric gate

The prime-end identification is closed, and component properness is proved
abstractly for embeddings.  The first remaining direct-decoration task is
to prove global injectivity of the actual KL tile immersions.  The second
is to prove `(OFP)` for that map, without replacing it by a literal
inclusion.  After that, the next task is:

> **Central \(J\)-seam footprint computation.**  For every point on every
> nonproper source \(\xi_i\)- or \(\eta_i\)-portion, enumerate the
> component or components of
> \(\mathbf P\setminus\boldsymbol\iota(\mathbf Q_a)\) landing there and
> compute the complete target ideal access set
> \(\Phi_{\boldsymbol\iota}(p)\).  Then apply (7.3) to every proof-used
> target marking, check pairwise disjointness, and verify covering
> endpoint refinement and proper/end-proper action on complete
> end-intervals.

The finite label hull does not compute these footprints.  In particular,
one must not infer the answer from the adjacent \(\xi/\eta\) label, and
one must not assume that a path approaching a shared vertex eventually
remains in a single tile sector.

## 10. Promotion boundary

This note proves:

- `KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY`;
- `EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM`.

The first statement is source-specific.  The second is an abstract
theorem with `(PE)` as an explicit hypothesis.  Section 8 records the
exact consequence of `(OFP)` but does not promote `(OFP)` for a general
KL \(\psi\)-ql immersion.

They do not promote:

- `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`;
- `DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`;
- `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`;
- `DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE`;
- `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`;
- VAAPC-I;
- UPTCR; or
- MLC.
