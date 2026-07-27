# Critical chronology, retimed cylinders, and the protected-spine boundary

## 1. Status and purpose

This document records the independently checked mathematical content of
Research Push II.  Its purpose is separation, not compression:

- the elementary degree identities and several finite analytic compiler
  lemmas are proved below;
- the existence and authorization of the virtual scale-two root portrait
  are not proved;
- relative-cover realization, protected carrier-complement prime ends,
  end-properness, and final-root stability are not consequences of the
  planar compiler;
- `MAPPING_TELESCOPE`, `FINITE_HORIZON_ASSEMBLY`,
  `VIRTUAL_DISCONNECTED_MARKING_TRANSFER`, VAAPC-I, UPTCR, and MLC remain
  open.

The decisive distinction is between the following two assertions.

1. **Conditional pullback.**  Given an already realized branch
   \(F=f^r:A\to B\) and one of the already realized univalent decoration
   cylinders, a retimed covering/embedding pair can be written down and
   checked exactly.
2. **Virtual realization.**  The satellite-copy chain itself selects such
   an \(F\), identifies it with the required next portrait, supplies every
   proof-used marking, and preserves the resulting simultaneous family
   under the authorized final-root enlargement.

Only the first assertion is proved here.  Treating it as the second would
assume the present virtual marking gate.

## 2. Source and evidence boundary

The direct-decoration input is the proved theorem
`DIRECT_DECORATION_PULLBACK_COMPACTIFICATION` in
[virtual_cantor_pullback_compactification.md](virtual_cantor_pullback_compactification.md).
It supplies closed Jordan puzzle pieces \(P,Q_0,Q_1\), actual degree-one
restrictions of \(f^q\), their inverse-word cylinders \(Q_w\), and closed
piece homeomorphisms

\[
 h_w=f^{N_w}|_{Q_w}:Q_w\longrightarrow P,
 \qquad N_w=q|w|.
\tag{2.1}
\]

The enlargement input is only
`PULLBACK_GAP_ENLARGEMENT_NATURALITY`: the root enlargement must stay in
the certified safe gap, or an actual collision ledger must replace that
hypothesis.  Merely staying inside \(P\) is insufficient.

The public virtual sources do not supply the missing scale-two map.  In
particular, Dudko's virtual-Molecule paragraph describes a strategy using
connected hulls of Cantor small Julia sets and finitely many critical-orbit
returns; it is not a theorem constructing \(F,A,B\), its protected marking,
or a Wave-complete branch catalog.  KKL likewise places virtual
renormalization in its future perspective rather than using it as an
established construction.

The supplied Push II artifacts were treated as a research proposal, not as
an imported source.  Their exact hashes and the claim-by-claim disposition
are recorded in
[research_push_2_assessment_and_integration.md](research_push_2_assessment_and_integration.md).

### Jordan-domain convention

The source puzzle pieces \(P,Q_w\) are closed Jordan disks.  When a
holomorphic restriction is written between Jordan disks below, its source
and target are the corresponding bounded open Jordan domains.  The maps
\(h_w\) are used both for their conformal interior restrictions and for
their stated homeomorphic extensions between the closed puzzle pieces.
Thus a compact-containment statement such as \(A\Subset B\) means
\(\overline A\) is a compact subset of the open domain \(B\).

## 3. Local degree and chronology

For a nonconstant holomorphic map \(H\), write \(e_H(z)\) for its local
degree at \(z\).  The chain rule for local degree is

\[
 e_{G\circ H}(z)=e_H(z)e_G(H(z)).
\tag{3.1}
\]

For the quadratic polynomial \(f(z)=z^2+c\), define the pointwise
length-\(k\) orbit word

\[
 \mathbf d_k(z)
 =
 \bigl(e_f(z),e_f(fz),\ldots,e_f(f^{k-1}z)\bigr).
\tag{3.2}
\]

Every entry is \(1\) or \(2\).  This is a pointwise orbit word.  A global
word attached to a branch additionally requires specified intermediate
branch domains on which the one-step maps are proper.

### Theorem 3.1 (`CRITICAL_CUT_POINTWISE_CONSERVATION`)

Let \(f\) be holomorphic and \(N,r\geq 1\).  At every point where the
iterates are defined,

\[
 e_{f^r}(z)e_{f^N}(f^r z)
 =
 e_{f^N}(z)e_{f^r}(f^N z).
\tag{3.3}
\]

For a quadratic polynomial,

\[
 \mathbf d_r(z)\star\mathbf d_N(f^r z)
 =
 \mathbf d_N(z)\star\mathbf d_r(f^N z)
 =
 \mathbf d_{N+r}(z),
\tag{3.4}
\]

where \(\star\) denotes concatenation.

#### Proof

The equality \(f^N\circ f^r=f^r\circ f^N=f^{N+r}\) and (3.1) give
(3.3) from the two factorizations.  The first word in (3.4) lists the
one-step local degrees at absolute times

\[
 0,\ldots,r-1,r,\ldots,r+N-1,
\]

and the second lists the same absolute-time sequence with the cut after
time \(N\).  Both are precisely (3.2) for \(k=N+r\). \(\square\)

### Corollary 3.2 (critical-count transfer)

Put

\[
 m_k(z)=\#\{0\leq j<k:f^j(z)=0\}.
\tag{3.5}
\]

If \(f^N\) is locally univalent at \(z\), then

\[
 m_N(f^r z)=m_r(f^N z)-m_r(z).
\tag{3.6}
\]

#### Proof

For a quadratic polynomial,
\(e_{f^k}(z)=2^{m_k(z)}\).  Substitute this identity into (3.3), use
\(m_N(z)=0\), and compare exponents. \(\square\)

### Warning 3.3

Equation (3.3) preserves the product of the local degrees.  It does not
say at which time the quadratic factor occurs.  Chronology requires the
intermediate squares of Section 8.

## 4. Proper commuting squares

### Theorem 4.1 (`PROPER_COMMUTING_SQUARE_DEGREE_LAW`)

Consider a commuting square

\[
\begin{array}{ccc}
U&\xrightarrow{H}&V\\
\scriptstyle h_0\downarrow&&\downarrow\scriptstyle h_1\\
A&\xrightarrow{F}&B
\end{array}
\qquad
h_1\circ H=F\circ h_0,
\tag{4.1}
\]

in which all four maps are finite-degree proper holomorphic maps between
connected bordered Riemann surfaces.  Then

\[
 \deg(H)\deg(h_1)=\deg(h_0)\deg(F)
\tag{4.2}
\]

and, for every \(x\in U\),

\[
 e_H(x)e_{h_1}(H(x))
 =
 e_{h_0}(x)e_F(h_0(x)).
\tag{4.3}
\]

If \(h_0\) is univalent and \(\deg F=2\), exactly one of

\[
 (\deg H,\deg h_1)=(2,1),
 \qquad
 (\deg H,\deg h_1)=(1,2)
\tag{4.4}
\]

occurs.

#### Proof

A nonconstant proper holomorphic map has a finite positive topological
degree, and degrees multiply under composition.  Apply this to the two
equal compositions in (4.1), proving (4.2).  Formula (4.3) is (3.1)
applied pointwise.  Under \(\deg h_0=1\) and \(\deg F=2\), (4.2) says
that two positive integers have product two, giving exactly the two
possibilities in (4.4). \(\square\)

The alternatives in (4.4) locate the obstruction exactly.  Either the
lifted branch retains the quadratic factor, or the transverse target
projection stores it.

## 5. The local off-critical square

### Theorem 5.1 (`LOCAL_OFF_CRITICAL_CYLINDER_SQUARE`)

Let \(f\) be a polynomial.  Suppose

\[
 h_0=f^N|_U:U\longrightarrow A,
 \qquad
 F=f^r|_A:A\longrightarrow B
\tag{5.1}
\]

are conformal isomorphisms of plane domains.  Define

\[
 H=f^r|_U,\qquad V=H(U),\qquad h_1=f^N|_V.
\tag{5.2}
\]

Then \(H:U\to V\) and \(h_1:V\to B\) are conformal isomorphisms and

\[
 h_1\circ H=F\circ h_0.
\tag{5.3}
\]

Consequently, any already defined prime-end marking supported in these
four charts transports by the induced prime-end homeomorphisms.  This
conclusion neither declares \(V\) to be an authorized virtual target nor
constructs a protected marking.

If one additionally knows that \(H:\overline U\to\overline V\) is a
homeomorphism and that \(U\) is a Jordan disk, then \(V\) is a Jordan disk
and the square extends to the ordinary closures.

#### Proof

If \(H(x_1)=H(x_2)\), apply \(f^N\) and use commutation:

\[
 F(h_0(x_1))
 =
 f^r(f^N(x_1))
 =
 f^N(f^r(x_1))
 =
 f^N(f^r(x_2))
 =
 F(h_0(x_2)).
\]

The injectivity of \(F\) and \(h_0\) gives \(x_1=x_2\).  Thus \(H\) is
a conformal isomorphism onto \(V\).  For \(y=H(x)\),

\[
 h_1(y)=F(h_0(x)).
\tag{5.4}
\]

As \(x\) runs through \(U\), the right side runs bijectively through
\(B\).  Hence \(h_1\) is a conformal isomorphism and (5.3) holds.
Conformal isomorphisms induce homeomorphisms of prime-end
compactifications.  The last assertion follows from the additional
closure homeomorphism. \(\square\)

### Adversarial correction 5.2

The extra closure hypothesis cannot be deleted.  The map \(z\mapsto z^2\)
is injective on the open right half-disk, but it identifies the two sides
of the imaginary diameter on the boundary.  Its image is a slit disk,
not a Jordan disk.  Interior univalence plus continuous extension is
therefore insufficient to infer a Jordan image.

## 6. Retiming an independently realized root pair

### Theorem 6.1 (`RETIMED_FINITE_CYLINDER_PAIR`)

Assume the following data have already been constructed.

1. \(P\) is a closed Jordan disk, \(A,B\) are bounded open Jordan domains,
   and
   \[
   \overline A\Subset B,\qquad
   \overline B\Subset\operatorname{int}P.
   \tag{6.1}
   \]
2. \(F=f^r|_A:A\to B\) is proper.
3. \(h_w=f^{N_w}|_{Q_w}:Q_w\to P\) is one of the closed-piece
   homeomorphisms in (2.1).

Put

\[
 U_w=h_w^{-1}(A)
\tag{6.2}
\]

and define maps with common source \(U_w\) and common target \(B\):

\[
 g_w=f^{N_w+r}|_{U_w}=F\circ h_w:U_w\longrightarrow B,
\tag{6.3}
\]

\[
 \iota_w=
 \operatorname{incl}_{A\hookrightarrow B}\circ h_w:
 U_w\longrightarrow B.
\tag{6.4}
\]

Then:

1. \(g_w\) is proper and \(\deg g_w=\deg F\);
2. \(\iota_w\) is a conformal embedding with image \(A\);
3. on \(A\),
   \[
   g_w\circ\iota_w^{-1}=F;
   \tag{6.5}
   \]
4. the pointwise \(N_w\)-step prehistory contributes only degree-one
   entries, so the relative critical chronology of
   \((g_w,\iota_w)\) is exactly the chronology of \(F\);
5. if \(K\Subset A\) is compact and full and satisfies
   \[
   F^{-1}(K)=K=F(K)
   \tag{6.6}
   \]
   within this restriction, then
   \[
   K_w=h_w^{-1}(K)
   \tag{6.7}
   \]
   is compact and full and
   \[
   g_w^{-1}(K)=\iota_w^{-1}(K)=K_w,
   \qquad
   g_w(K_w)=\iota_w(K_w)=K;
   \tag{6.8}
   \]
6. any root marking, obstacle representative, or label already certified
   inside the root charts transports by \(h_w^{-1}\), with exactly the
   same incidence and cyclic order;
7. if \(s=f^q:Q_{aw}\to Q_w\) is a direct-decoration shift branch, then
   on the corresponding pulled domains
   \[
   g_{aw}=g_w\circ s,\qquad
   \iota_{aw}=\iota_w\circ s.
   \tag{6.9}
   \]

No assertion is made here that \(F\) is the scale-two virtual portrait,
that an arbitrary finite root marking satisfies the required
covering-versus-immersion action, that different words have a simultaneous
authorized ownership relation, or that an arbitrary enlargement inside
\(P\) is safe.

#### Proof

Equation (6.3) follows from commutation of polynomial iterates.  Since
\(h_w:U_w\to A\) is conformal and \(F\) is proper, their composition is
proper and has degree \(\deg F\).  Equation (6.4) is a conformal embedding
onto \(A\), and (6.5) follows by cancellation of \(h_w\).

Because \(h_w=f^{N_w}|_{Q_w}\) is injective, every prefix
\(f^k|_{Q_w}\), \(0\leq k\leq N_w\), is injective: equality after a prefix
would imply equality after applying the remaining iterate.  Thus no
critical encounter occurs in the cylinder prehistory.  Both entries of
the pair contain this same prehistory, and (6.5) leaves precisely the
root chronology.

For (6.8),

\[
 g_w^{-1}(K)
 =
 h_w^{-1}(F^{-1}(K))
 =
 h_w^{-1}(K)
 =
 \iota_w^{-1}(K),
\]

and the forward equalities are immediate from (6.6).  The homeomorphism
of closed Jordan disks \(h_w\) extends to a sphere homeomorphism by the
Schoenflies theorem, so it preserves connectedness of the complement;
hence \(K_w\) is full.

Every already certified chart-supported record is transported by the
same homeomorphism.  This preserves incidence and cyclic order but does
not certify that the record was dynamically admissible in the first
place.  Finally, the inverse-word identity
\(h_{aw}=h_w\circ s\) gives (6.9). \(\square\)

### Countercheck 6.2 (an arbitrary finite marking need not act)

For the disk pair \((z^2,\operatorname{id})\), mark only the boundary
angle \(1/3\).  The immersion pullback contains \(1/3\), whereas the
covering pullback contains the angles \(1/6\) and \(2/3\).  The endpoint
containment required by `PRIME_END_MARKING_ACTION_CRITERION` fails.
Therefore “freeze any finite marking” must be replaced by “freeze an
already certified marking.”

### Countercheck 6.3 (inside \(P\) is not an enlargement certificate)

A connected root enlargement can remain inside \(P\) while meeting a
first pullback cylinder.  At that first meeting, the root and child
components can merge and their sheet labels cease to be disjoint.  The
valid conclusion is only the safe-gap theorem already proved in
`PULLBACK_GAP_ENLARGEMENT_NATURALITY`, or an explicit collision-free
replacement with exact endpoint inverse-image identities.

There is also a type distinction that must remain visible.  In KKL's
\(\psi\)-ql notation the target carrier \(K\), not the pulled source
carrier \(K_w\), is called the filled Julia set of the pair.  Formula
(6.8) constructs the source filled carrier \(K_w\) feeding the same
normalized target pair.  It does not construct a self-return whose target
carrier is \(K_w\).

## 7. Exact chronology counterexamples

### Proposition 7.1 (`CRITICALITY_LOCATION_SWAP_NO_GO`)

Let \(f(z)=z^2-1\), choose \(0<\rho<1\), and put

\[
 A=\mathbb D(0,\rho),
 \qquad
 B=\mathbb D(-1,\rho^2).
\tag{7.1}
\]

Let \(U\) be the component of \(f^{-1}(A)\) containing \(1\).  Then

\[
 h_0=f|_U:U\to A
\]

is conformal, while

\[
 F=f|_A:A\to B
\]

is proper of degree two.  With

\[
 H=f|_U,\quad V=A,\quad h_1=f|_A,
\]

the square (4.1) commutes and

\[
 (\deg H,\deg h_1)=(1,2).
\tag{7.2}
\]

Thus a univalent source projection and a quadratic root branch do not
force a univalent target projection.

#### Proof

The disk \(A\) omits the critical value \(-1\), so each component of
\(f^{-1}(A)\) maps conformally onto \(A\).  The centered disk \(A\)
contains the critical point, and \(z\mapsto z^2-1\) maps it properly with
degree two onto \(B\).  Both compositions in the square equal
\(f^2|_U\). \(\square\)

### Proposition 7.2 (`CRITICAL_TIME_SHEAR_NO_GO`)

For the same polynomial, choose \(0<\rho<1/2\) and let

\[
 A_0=\mathbb D(0,\rho),\qquad
 A_1=f(A_0)=\mathbb D(-1,\rho^2),\qquad
 A_2=f(A_1).
\tag{7.3}
\]

Let \(U_0\) be the component of \(f^{-1}(A_0)\) containing \(1\), and set

\[
 h_0=f|_{U_0},\qquad
 F=f^2|_{A_0},\qquad
 H=f^2|_{U_0},\qquad
 h_2=f|_{A_1}.
\tag{7.4}
\]

For sufficiently small \(\rho\), \(h_0\) and \(h_2\) are conformal,
\(F\) and \(H\) are proper of degree two, and

\[
 h_2\circ H=F\circ h_0.
\tag{7.5}
\]

Nevertheless, their chronological words are

\[
 \operatorname{word}(F)=(2,1),
 \qquad
 \operatorname{word}(H)=(1,2).
\tag{7.6}
\]

#### Proof

The first factor of \(F\) is the quadratic map
\(f:A_0\to A_1\); for small \(\rho\), the next factor is univalent near
\(-1\).  Thus its word is \((2,1)\).  For \(H\), the first factor
\(f:U_0\to A_0\) is univalent and the next is quadratic, giving
\((1,2)\).  More explicitly,
\(\overline{A_1}\subset\{\operatorname{Re}z<0\}\) and
\(-\overline{A_1}\subset\{\operatorname{Re}z>0\}\).  Since
\(f(z)=f(z')\) implies \(z'=\pm z\), \(f\) is injective on
\(\overline{A_1}\).  Hence \(A_2=f(A_1)\) is a Jordan domain and
\(h_2:A_1\to A_2\) is a proper conformal isomorphism.  Both sides of
(7.5) equal \(f^3|_{U_0}\). \(\square\)

Endpoint degree and endpoint conjugacy therefore do not determine
critical time.

## 8. The stagewise degree ladder

Suppose a root branch is represented by proper one-step restrictions

\[
 f:A_j\longrightarrow A_{j+1},
 \qquad 0\leq j<r,
\tag{8.1}
\]

between connected Jordan disks.  Suppose a lifted chain has proper
one-step restrictions

\[
 f:U_j\longrightarrow U_{j+1}
\tag{8.2}
\]

and proper onto transverse maps

\[
 h_j=f^N|_{U_j}:U_j\longrightarrow A_j
\tag{8.3}
\]

such that every one-step square commutes.  Put

\[
 d_j=\deg(f:A_j\to A_{j+1}),\quad
 \widetilde d_j=\deg(f:U_j\to U_{j+1}),\quad
 e_j=\deg h_j.
\tag{8.4}
\]

### Theorem 8.1 (`STAGEWISE_CRITICAL_WORD_LADDER`)

For every \(j\),

\[
 \widetilde d_j e_{j+1}=e_jd_j.
\tag{8.5}
\]

If \(e_0=1\), the following are equivalent:

1. \(e_j=1\) for every \(j\);
2. \(d_j=\widetilde d_j\) for every \(j\);
3. the two proper branch chains have the same chronological degree word
   and no criticality is stored in a transverse projection.

Endpoint univalence \(e_r=1\) implies equality of total branch degrees,
but not equality of chronological words.

#### Proof

Apply Theorem 4.1 to every one-step square, proving (8.5).  If all
\(e_j=1\), then (8.5) gives \(d_j=\widetilde d_j\).  Conversely,
if the one-step degrees agree, (8.5) and \(e_0=1\) inductively give
\(e_j=1\) for all \(j\).  This is precisely equality of the ordered
proper one-step degree words.  Multiplication of (8.5) over \(j\)
cancels all intermediate \(e_j\); hence \(e_0=e_r=1\) controls only the
product.  Proposition 7.2 shows that the ordered words can still differ.
\(\square\)

### Corollary 8.2 (critical-set test, with the necessary topology)

Under the hypotheses above, \(h_j\) is univalent exactly when

\[
 \operatorname{Crit}(f^N)\cap U_j=\varnothing.
\tag{8.6}
\]

Equivalently,

\[
 0\notin f^k(U_j)
 \quad(0\leq k<N).
\tag{8.7}
\]

#### Proof

One direction is immediate.  Conversely, absence of critical points
makes the proper map \(h_j\) an unbranched finite cover of the simply
connected Jordan disk \(A_j\).  Such a connected cover has degree one.
The description (8.7) is the chain rule characterization of the critical
set of an iterate of a quadratic polynomial. \(\square\)

The simply connected target cannot be omitted: \(z^2\) is an unbranched
degree-two cover on a suitable annulus.

## 9. Quadratic Jordan base change

### Theorem 9.1 (`QUADRATIC_JORDAN_BASE_CHANGE_DICHOTOMY`)

Let

\[
 p:X\longrightarrow Y
\tag{9.1}
\]

be a proper degree-two holomorphic map between Jordan disks, with unique
critical point \(c\) and critical value \(v=p(c)\).  Let
\(E\Subset Y\) be a Jordan disk with \(v\notin\partial E\).

1. If \(v\in E\), then \(p^{-1}(E)\) is one Jordan disk containing
   \(c\), and \(p|_{p^{-1}(E)}:p^{-1}(E)\to E\) is proper of degree two.
2. If \(v\notin\overline E\), then \(p^{-1}(E)\) is the disjoint union
   of exactly two Jordan disks, each mapped conformally onto \(E\).

#### Proof

If \(v\in E\), let \(C\) be the preimage component containing \(c\).
Its degree is at least the local degree two.  Since the total degree is
two, \(C\) has the full degree and there can be no other component.
The restriction \(p:C\to E\) has exactly one simple branch point.
Riemann--Hurwitz for compact bordered surfaces gives

\[
 \chi(C)=2\chi(E)-1=1.
\tag{9.2}
\]

The surface \(C\) is planar, so \(\chi(C)=2-b\), where \(b\) is its number
of boundary components.  Hence \(b=1\).

If \(v\notin\overline E\), the restriction over \(E\) is unbranched.
Every connected preimage component is an unbranched finite cover of the
simply connected disk \(E\), hence has degree one.  Total degree two gives
exactly two components.

In both cases, \(E\Subset Y\) and \(v\notin\partial E\) give an unbranched
annular neighborhood of the Jordan boundary.  Its lifted boundary
components are Jordan curves.  In the branched case the
Riemann--Hurwitz calculation gives exactly one such component; in the
unbranched case each degree-one inverse branch extends across the collar.
The corresponding preimage components are therefore Jordan disks.
\(\square\)

### Corollary 9.2 (degree-loss certificate)

At a base change of a quadratic partial covering, a connected selected
component retains degree two exactly when the embedded next Jordan disk
contains the propagated critical value.  If it omits the critical value,
the full preimage splits into two degree-one components.

This is a specialization of the existing full-continuum pullback
dichotomy, but its Jordan-disk form is the exact input needed below.

## 10. Embedded-Jordan critical-spine telescope

### Definition 10.1 (authorized planar stage system)

Fix Jordan disks \(Y_0,\ldots,Y_m\) with \(Y_m=Y_0\).  For
\(0\leq j<m\), let:

- \(X_j\) be a Jordan disk;
- \(g_j:X_j\to Y_{j+1}\) be proper holomorphic;
- \(\iota_j:\overline X_j\to Y_j\) be a topological embedding whose
  interior restriction is conformal and whose image
  \[
  A_j=\iota_j(X_j)\Subset Y_j
  \tag{10.1}
  \]
  is a Jordan disk.

Starting with

\[
 T_1=X_0,\qquad G_1=g_0,\qquad I_1=\iota_0,
\tag{10.2}
\]

suppose \(G_k:T_k\to Y_k\) and \(I_k:T_k\to Y_0\) have been defined.
Set

\[
 D_k=G_k^{-1}(A_k),
\qquad
 q_k=\iota_k^{-1}\circ G_k|_{D_k},
\tag{10.3}
\]

and, when \(D_k\) is connected, define

\[
 T_{k+1}=D_k,\qquad
 G_{k+1}=g_k\circ q_k,\qquad
 I_{k+1}=I_k|_{D_k}.
\tag{10.4}
\]

This is the planar form of selecting the connected fiber-product
component.

### Theorem 10.2 (`PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER`)

Assume an authorized planar stage system satisfies:

1. exactly one \(g_j\) has degree two and every other \(g_j\) has degree
   one;
2. before that quadratic stage, the recursion (10.3)--(10.4) is used on
   the unique preimage of \(A_k\);
3. after the quadratic stage, whenever \(G_k\) has degree two with
   critical value \(v_k\),
   \[
   v_k\in A_k;
   \tag{10.5}
   \]
4. every stated compact containment lies in the authorized planar
   localization.

Then every \(D_k\) is a connected Jordan disk.  The recursion is unique,
and the endpoint pair

\[
 (G_m,I_m):T_m\rightrightarrows Y_0
\tag{10.6}
\]

satisfies:

- \(I_m\) is a conformal embedding;
- \(G_m\) is proper of degree two;
- the stage-degree word contains exactly one quadratic factor; and
- the target route closes because \(Y_m=Y_0\).

If (10.5) first fails at a post-quadratic stage \(k\) with
\(v_k\notin\overline{A_k}\), then \(D_k\) has exactly two separated Jordan
components, each gives a degree-one continuation, and no connected
continuation through that base change retains degree two.  If instead
\(v_k\in\partial A_k\), the stage is a boundary-critical collision: the
compiler stops and makes no two-sheet separation or Jordan-collar claim.

#### Proof

If \(g_0\) is quadratic, then \(G_1=g_0\) is the initial proper
degree-two covering.  Otherwise, before the quadratic stage \(G_k\) is a
conformal isomorphism onto \(Y_k\).  Hence \(G_k^{-1}(A_k)\) is one Jordan
disk and the restriction to it is conformal.  Composing with the next
degree-one \(g_k\) preserves degree one.  When the unique later
quadratic \(g_k\) is reached, the current base-change map is conformal, so
the new partial covering has degree two and one critical value.

Now assume inductively that \(G_k:T_k\to Y_k\) is proper of degree two.
By (10.5), the embedded Jordan disk \(A_k\Subset Y_k\) contains its
critical value.  Theorem 9.1 shows that
\(D_k=G_k^{-1}(A_k)\) is one Jordan disk and that
\(G_k|_{D_k}:D_k\to A_k\) retains degree two.  Since every later
\(g_k\) is conformal, (10.4) remains proper of degree two.  Its critical
value is

\[
 v_{k+1}=g_k(\iota_k^{-1}(v_k)).
\tag{10.7}
\]

This proves existence, uniqueness, the Jordan property, and degree
retention at every remaining step.  Each restriction of the injective
\(I_k\) remains injective, so \(I_m\) is a conformal embedding.  The
single quadratic stage and the equality \(Y_m=Y_0\) give the last two
claims.

If \(v_k\notin\overline{A_k}\), Theorem 9.1 gives exactly two separated
degree-one preimage components.  All later \(g_j\) have degree one, so no
chosen connected route can recover the lost quadratic degree.  The
boundary case \(v_k\in\partial A_k\) has no unbranched collar and is
therefore recorded as a boundary-critical collision rather than passed
through Theorem 9.1. \(\square\)

### Failure certificate 10.3

A critical-spine failure is not the statement “some fiber product did not
close.”  It is the finite record

\[
 (k,G_k,v_k,A_k,D_k^+,D_k^-,D_k^{\rm chosen})
\tag{10.8}
\]

with \(v_k\notin\overline{A_k}\), the two degree-one components
\(D_k^\pm\), and the selected continuation.

If \(v_k\in\partial A_k\), the first failure record is instead

\[
 (k,G_k,v_k,A_k,\text{boundary-critical collision}),
\tag{10.9}
\]

and no separated-sheet continuation is certified.

### Adversarial correction 10.4

A conformal embedding that merely extends to prime ends does not satisfy
Definition 10.1.  Take \(G(z)=z^2:\mathbb D\to\mathbb D\) and a relatively
compact simply connected slit domain \(E\) containing \(0\).  A Riemann
map \(\iota:\mathbb D\to E\) extends to prime-end compactifications and
the critical value is retained, but \(G^{-1}(E)\) has pulled slits and is
not a Jordan disk.  The closure embedding onto a relatively compact
Jordan subdisk is an essential hypothesis.

### Boundary of the theorem

Theorem 10.2 is a planar compiler.  It does not prove that a virtual stage
immersion has a relative-cover lift with the properties in Definition
10.1.  The basic subgroup lifting criterion supplies a lift only.  It
does not by itself supply:

- an embedding of the selected lift;
- properness or core-properness;
- a full compatible orbit of selected components;
- basepoint and deck-phase compatibility;
- lifting and containment of the propagated critical value; or
- protected carrier-complement prime-end action.

These are precisely why `MAPPING_TELESCOPE` remains open.

A second elementary counterexample blocks the proposed prime-end shortcut.
The embedding

\[
 \iota(z)=z/2:\mathbb D\hookrightarrow\mathbb D
\]

extends injectively to the closed disk, but its source prime-end circle
maps to the interior circle \(|z|=1/2\), not to the target prime-end circle
\(|z|=1\).  A conformal embedding therefore does not automatically give
the target-circle homeomorphism needed for a marked correspondence.
Protected prime-end maps must be separately defined on the relevant
carrier-complement ideal boundaries.

## 11. The exact finite planar telescope identity

### Proposition 11.1 (`FINITE_PLANAR_TELESCOPE_IDENTITY`)

In Theorem 10.2, define the relative stage maps

\[
 R_j=g_j\circ\iota_j^{-1}:A_j\longrightarrow Y_{j+1}.
\tag{11.1}
\]

As maps whose exact common domain is \(I_m(T_m)\),

\[
 \left.G_m\circ I_m^{-1}\right|_{I_m(T_m)}
 =
 \left.R_{m-1}\circ\cdots\circ R_0\right|_{I_m(T_m)}.
\tag{11.2}
\]

If every \(R_j\) is an actual restriction of \(f^{s_j}\) and the selected
route is contained in the chronological composition domain, then

\[
 G_m\circ I_m^{-1}=f^S,
\qquad
 S=\sum_{j=0}^{m-1}s_j.
\tag{11.3}
\]

The pointwise critical word is the chronological concatenation of the
stage words.  The intermediate component selected at every base change
is retained by the nested domains \(T_k\), so it need not be reconstructed
from the endpoint.

No relative-cover, protected marking, end-properness, or enlargement
claim is part of this proposition.

#### Proof

From (10.4),

\[
 G_{k+1}
 =
 g_k\circ\iota_k^{-1}\circ G_k
 =
 R_k\circ G_k
\tag{11.4}
\]

on \(T_{k+1}\), while \(I_{k+1}\) is the restriction of \(I_k\).
Induction gives

\[
 G_k=R_{k-1}\circ\cdots\circ R_0\circ I_k
\tag{11.5}
\]

on \(T_k\), proving (11.2).  Under the iterate hypothesis, polynomial
iterates compose by addition of exponents, proving (11.3).  The pointwise
word statement follows from Theorem 3.1 at each cut.  Finally,
\(T_{k+1}\subset T_k\) is the actual selected preimage domain, so the
entire route is present in the recursion. \(\square\)

This proposition is the valid algebraic core of the proposed marked
assembly theorem.  It does not prove the current
`FINITE_HORIZON_ASSEMBLY` obligation, which additionally requires actual
depth-\(q\) \(\psi\)-ql core identities, iterated covering embeddings,
protected carrier-complement markings, compatible relative covers,
proper/end-proper ideal intervals, and exact enlargement squares.

## 12. Planar end collapse

Retain the actual inverse-word maps

\[
 \Phi_m=\phi_{\omega|m}:
 \operatorname{int}P\longrightarrow
 \operatorname{int}Q_{\omega|m}
\tag{12.1}
\]

and the nested end fiber

\[
 E_\omega=\bigcap_{m\geq1}Q_{\omega|m}\subset J(f)
\tag{12.2}
\]

from `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`.

### Theorem 12.1 (`PLANAR_END_COLLAPSE_NO_GO`)

For every compact \(L\Subset\operatorname{int}P\),

\[
 \operatorname{diam}\Phi_m(L)\longrightarrow0.
\tag{12.3}
\]

Every locally uniform subsequential limit of \(\Phi_m\) is constant with
value in \(E_\omega\).  Hence no nonconstant analytic end chart is an
unrescaled planar limit of these inverse branches.

#### Proof

The maps \(\Phi_m\) have images in the fixed bounded disk \(P\), so they
form a normal family.  Let a subsequence converge locally uniformly to
\(\Phi\).  For every fixed \(n\), all sufficiently deep images lie in the
closed set \(Q_{\omega|n}\).  Therefore

\[
 \Phi(\operatorname{int}P)
 \subset
 \bigcap_{n\geq1}Q_{\omega|n}
 =
 E_\omega.
\tag{12.4}
\]

The continuum \(E_\omega\) lies in the Julia set and has empty interior.
The open mapping theorem forces \(\Phi\) to be constant.

If (12.3) failed for a compact \(L\), a subsequence would have image
diameter bounded below.  Normality would give a locally uniformly
convergent subsubsequence, and its constant limit would force uniform
diameter convergence to zero on \(L\), a contradiction. \(\square\)

### Corollary 12.2

For every compact root carrier \(K\Subset\operatorname{int}P\),

\[
 \operatorname{diam}\phi_{\omega|m}(K)\longrightarrow0.
\tag{12.5}
\]

This is a no-go theorem.  It does not construct an end fiber carrying a
nondegenerate virtual portrait.

## 13. Normalized retimed germ and projection collapse

### Theorem 13.1 (`NORMALIZED_RETIMED_GERM_CONSTANCY`)

Let \(F=f^r|_A:A\to B\) be the independently realized root pair in
Theorem 6.1, and let \(w_m=\omega|m\).  In the source coordinate

\[
 h_m=h_{w_m}|_{U_{w_m}}:U_{w_m}\longrightarrow A,
\]

the retimed pair satisfies the exact identity

\[
 \bigl(g_{w_m}\circ h_m^{-1},
       \iota_{w_m}\circ h_m^{-1}\bigr)
 =
 \bigl(F,\operatorname{incl}_{A\hookrightarrow B}\bigr)
\tag{13.1}
\]

for every \(m\).

#### Proof

Equations (6.3)--(6.4) are
\(g_{w_m}=F\circ h_m\) and
\(\iota_{w_m}=\operatorname{incl}\circ h_m\).  Cancel \(h_m\).
\(\square\)

This constancy is conditional on the root portrait.  It does not identify
that portrait with the source-facing virtual second scale and does not
attach the normalized germ to the planar end fiber.

### Theorem 13.2 (`END_BLOWUP_PROJECTION_NO_GO`)

Assume \(K\Subset A\) is a connected compact set with at least two points.
Suppose a Hausdorff space \(\mathcal X\) contains embeddings

\[
 j_m:K\to\mathcal X,\qquad j_\infty:K\to\mathcal X,
\tag{13.2}
\]

such that \(j_m(z)\to j_\infty(z)\) for every \(z\in K\).  Suppose there
is a continuous map

\[
 \pi:\mathcal X\to\overline P
\tag{13.3}
\]

with

\[
 \pi\circ j_m=\phi_{\omega|m}|_K.
\tag{13.4}
\]

Then \(\pi\circ j_\infty\) is constant.  In particular, \(\pi\) is not
locally injective at any point of \(j_\infty(K)\).

#### Proof

For \(z,z'\in K\), Corollary 12.2 gives

\[
 \left|
 \phi_{\omega|m}(z)-\phi_{\omega|m}(z')
 \right|\longrightarrow0.
\]

Use (13.4), pointwise convergence of the embeddings, and continuity of
\(\pi\) to obtain

\[
 \pi(j_\infty(z))=\pi(j_\infty(z')).
\]

Thus all of \(j_\infty(K)\) lies in one projection fiber.  The nondegenerate
connected compactum \(K\) has no isolated points, and \(j_\infty\) is an
embedding.  Therefore every neighborhood of every point of
\(j_\infty(K)\) contains a second point of that compactum with the same
\(\pi\)-image.  The projection is not locally injective at any point of
\(j_\infty(K)\). \(\square\)

The theorem forces a nontrivial projection fiber under its hypotheses.
It does not prove that a conformal prime-end blow-up exists, nor that every
possible realization must belong to one preferred category.

## 14. Fixed-iterate action on nested end fibers

### Theorem 14.1 (`FIXED_ITERATE_END_FIBER_EXTENSION`)

Let \(X,Y\) be Hausdorff spaces,
\(C_1\supset C_2\supset\cdots\) nonempty compact subsets of \(X\), and
\(D_1\supset D_2\supset\cdots\) nonempty compact subsets of \(Y\).  Let
\(F\) be one fixed continuous map from a neighborhood of \(C_1\) into
\(Y\).  If

\[
 F(C_n)\subset D_n\qquad(n\geq1),
\tag{14.1}
\]

then

\[
 F\left(\bigcap_{n\geq1}C_n\right)
 \subset
 \bigcap_{n\geq1}D_n.
\tag{14.2}
\]

If \(F(C_n)=D_n\) for every \(n\), then equality holds in (14.2).

#### Proof

The inclusion is immediate: a point in every \(C_n\) maps into every
\(D_n\).

For the reverse inclusion, fix \(y\in\bigcap_nD_n\) and define

\[
 A_n=C_n\cap F^{-1}(\{y\}).
\tag{14.3}
\]

Surjectivity \(F(C_n)=D_n\) makes every \(A_n\) nonempty.  These sets are
compact and nested, hence have nonempty intersection.  Any point in that
intersection belongs to \(\bigcap_nC_n\) and maps to \(y\). \(\square\)

The Hausdorff hypothesis is necessary for this abstract formulation.
On \(\mathbb N\) with the cofinite topology, the tails
\(C_n=\{n,n+1,\ldots\}\) are nested nonempty compact sets with empty
intersection.  For the constant map to \(Y=\{*\}\), one has
\(F(C_n)=D_n=\{*\}\) at every finite level, while
\(F(\bigcap_n C_n)=\varnothing\ne\{*\}=\bigcap_nD_n\).

Applied to direct-decoration cylinders, the theorem is formal only for
one fixed iterate and an already compatible nested target system.  It
does not apply directly to the retimed coverings
\(f^{N_w+r}\), whose exponents grow with \(|w|\).  A discrete finite
label passes to the intersection only when the parent system makes that
label eventually constant; continuous phases or protected accesses need
their own topology and compatibility proof.

## 15. Claims deliberately held open

### 15.1 Root localization

The standard polynomial-like equipotential restriction used in Push II is
plausible, but the supplied proof did not source-lock the external
coordinate theorem or choose the new target inside \(W\cap A_0\).
No separate `LOCALIZED_QL_RESTRICTION` ledger node is promoted in this
pass.  The retimed theorem instead assumes the required localized pair.

### 15.2 Prime-end impression equality

The direct-decoration angular inverse branches give a plausible limiting
external angle only after an additional sector check.  The root separator
can meet the basin of infinity in several ray sectors.  Univalence of one
plane branch does not by itself prove that every exterior boundary ray is
represented by one common affine lift

\[
 t\longmapsto\frac{t+k}{2^q}.
\]

Different exterior components can require different integers \(k\).
Thus even the proposed exact angular-diameter formula requires a
source-locked one-sector or compatible-multisector lemma.

After that lemma, angular-diameter contraction and convergence of
equipotential height still do not alone prove

\[
 E_\omega=\operatorname{Imp}(\theta_\omega).
\tag{15.1}
\]

One must prove that the actual exterior puzzle sectors form a fundamental
prime-end chain cofinal with a defining chain at \(\theta_\omega\), handle
addresses landing at sector endpoints, and then audit collars, obstacles,
and root enlargements before calling the access protected.  This is the
open `DIRECT_DECORATION_END_PRIME_END_COFINALITY` obligation.

### 15.3 Relative-cover and marked telescope

Theorem 10.2 cannot be applied in an abstract relative cover until the
selected lift is proved embedded and proper, its basepoint/deck phase and
critical lift are compatible across the entire cycle, and its embedded
core contains the propagated critical value.  Proposition 11.1 does not
supply protected carrier-complement prime ends or end-proper intervals.
Thus neither `MAPPING_TELESCOPE` nor `FINITE_HORIZON_ASSEMBLY` is promoted.

### 15.4 Final-root enlargement

Functorial restriction through \(h_w\) proves only a square for a fixed
root datum.  Complete final-root naturality requires:

1. the same source-defined root portrait after enlargement;
2. a collision-free safe gap or a complete component-intersection ledger;
3. exact inverse-image identities for all protected endpoints;
4. unchanged relative-cover subgroup, basepoint, deck phase, and critical
   lift;
5. a bijection, not merely an injection, on all demanded
   branch-component pairs; and
6. no new proof dependency reaching an earlier omitted record.

No Push II argument proves this list.

## 16. Exact source-facing residual

### Open Problem 16.1 (`VIRTUAL_FINITE_WORD_ROOT_PORTRAIT_AUTHORIZATION`)

For each actual two-step virtual satellite-copy chain:

1. construct and source-identify an actual root portrait
   \(F=f^r:A\to B\) for the required second scale;
2. prove \(A\Subset B\Subset\operatorname{int}P\) in the certified safe
   direct-decoration gap--in particular, construct a Jordan neighborhood
   of the target carrier compactly contained in
   \(\operatorname{int}P\setminus(Q_0\cup Q_1)\), not merely in
   \(\operatorname{int}P\);
3. construct a carrier satisfying the full inverse-image identities and
   containing every proof-used component and critical-orbit segment;
4. construct a root marking already satisfying the exact
   covering-versus-immersion prime-end criterion;
5. authorize every forced off-critical image domain and every simultaneous
   finite-word pullback with component, parent, sheet, obstacle, and
   localization ownership; and
6. prove exact naturality under the final-root enlargement and complete
   Wave demand schema.

Theorem 6.1 then compiles the central finite-word pairs.  It does not solve
this open problem.

### Open Problem 16.2 (`VIRTUAL_END_BLOWUP_REALIZATION`)

After Open Problem 16.1 and prime-end cofinality:

1. construct an analytic rescaled or nontrivial-fiber end space carrying
   the normalized root pair over every required infinite address;
2. define its continuous projection to the original plane;
3. realize all protected accesses, obstacles, sheets, critical chronology,
   and shift action;
4. prove compatibility with fixed-iterate end actions where applicable;
5. prove relative-cover, proper/end-proper, and final-root naturality; and
6. retain all data through the complete Wave horizon.

Theorem 13.2 is only a necessary projection-collapse constraint.

## 17. Dependency conclusion

The rigorous net advance is:

\[
\begin{gathered}
\text{pointwise chronology and proper-square degree laws}\\
\Downarrow\\
\text{conditional retimed finite-cylinder pair}\\
\Downarrow\\
\text{embedded-Jordan critical-spine compiler}\\
\quad+\quad
\text{planar end-collapse constraints}.
\end{gathered}
\tag{17.1}
\]

The remaining source-facing order is:

\[
\begin{gathered}
\texttt{VIRTUAL\_FINITE\_WORD\_ROOT\_PORTRAIT\_AUTHORIZATION}\\
\Downarrow\\
\texttt{DIRECT\_DECORATION\_END\_PRIME\_END\_COFINALITY}\\
\quad+\quad
\texttt{VIRTUAL\_END\_BLOWUP\_REALIZATION}\\
\Downarrow\\
\texttt{VIRTUAL\_DISCONNECTED\_MARKING\_TRANSFER}\\
\Downarrow\\
\text{actual return bases, Wave correspondence, and horizon}\\
\Downarrow\\
\text{VAAPC-I and the remaining UPTCR clauses}.
\end{gathered}
\tag{17.2}
\]

No arrow in (17.2) is promoted by a finite computation.  The chronology
regressions only protect the logical boundary established by the analytic
proofs above.
