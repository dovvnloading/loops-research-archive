# KKL stationary two-sided noncollision: source-specific reduction

## 1. Result and status

This note attacks the implication used at line 1603 of the locked
Kahn--Kapiamba--Lyubich (KKL) source:

\[
 \text{the two separator-side portions push forward to Waves}
 \quad\Longrightarrow\quad
 \text{the source leaf breaks under }F_*^{\,n+1}.
\tag{1.1}
\]

The attack gives a rigorous partial reduction, but not a proof of (1.1).
It proves the following.

1. Every selected small-Julia pull
   \[
     K_0^{s}\longrightarrow K_0^{s-1},
     \qquad s\geq1,
   \]
   is carried by a conformal branch.  The corresponding \(L_0^s\) pull
   is critical-value-free and locally univalent; a single global Jordan
   corridor around the whole limb pull is an additional localization
   predicate unless nonseparation of that whole limb continuum is
   proved.  On every realized conformal branch, the map preserves every
   realized separator-side prime-end access and its cyclic order; the
   existence of two distinct proof-used marked accesses is a separate
   predicate, not a consequence of continuum separation alone.
2. The next map
   \[
     K_0^0\longrightarrow K_1:=F(K_0^0)
   \]
   has degree two, not degree one.  After removing the two filled
   continua, it is a connected two-sheeted covering.
3. For portions certified to remain in the selected corridor, two
   distinct retained separator-side portions can have the same terminal
   geometric image only by the nontrivial deck involution of this one
   quadratic covering.  Such a collision forces the corresponding
   prime-end pairs to be deck-related, possibly after reversal.  The
   endpoint relation is only necessary: paths with the same endpoint
   pair can still differ by their relative homotopy or winding class.
4. KKL's Hubbard-tree component labels do not rule out this deck collision:
   the two distinguished sides of \(K_0^0\) both route to the
   \(\alpha_F\)-side component of \(K_1\).
5. The locked source does not bind the two portions to two complete
   retained fiber-product occurrences or record the prime-end side,
   sheet, and collar arc class needed to test the deck relation.  KKL's
   itinerary proposition is too coarse.  The definitions of \(A_n\)
   and \(N\)-unbreakability determine one untagged retained image path
   at every stage, but do not remember which restriction components
   produced it.

Thus the logically minimal repair is to prove directly that the two
line-1603 portions give two distinct retained terminal proper paths.
Sections 3, 7, and 8 give one source-specific sufficient factorization
of that assertion: retained realization (7.2), all-stage compatible
marked-access realization (3.3), selected-corridor confinement (7.3),
and the **selected-collar deck-noncollision predicate** (8.4).
Condition (8.5) is only a sufficient endpoint certificate for the last
predicate.  These four clauses are not claimed to be logically
necessary for every possible repair.

No global or gated conclusion is promoted.  The ledger records only the
local one-retained-chain lemma as proved and splits the remaining
line-1603 work into open clauses.  In particular,
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR`, VAAPC-I, UPTCR, and MLC
remain open.

## 2. Locked sources

The KKL source used here is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The relevant source clauses are:

- lines 478--490: the primitive quadratic-like renormalization and its
  critical small filled Julia set;
- lines 497--504 and 698: limb dynamics, the critical limb \(L_0\), the
  critical value in \(L_p\), and the proof-used rotation \(p/q=1/q\);
- lines 757--761 and 838--866: the ideal marking and the limb
  multi-intervals \(B L_j\);
- lines 1241--1274: identification of the pulled tree and the induced
  coarse interval action;
- lines 1547--1548: \(N=b+3\), the nested subwaves \(A_n\), and the
  terminal-Wave selection rule;
- lines 1597--1603: \(K_0^s,\alpha^s,L_0^s\), their separation
  relation, and the inference (1.1);
- lines 1839--1875: ideal boundary, markings, proper paths,
  subordination, laminations, and Waves;
- lines 2065--2078: proper covering pushforward;
- lines 2081--2108: immersion restriction, the retained-path filter,
  and the itinerary proposition;
- lines 2128--2167: \(F_*=f_*\iota^*\), breaking, and unbreakability.

The locked Kahn source is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

Its lines 60--77 and 155--178 give an embedded polynomial-like
neighborhood of the filled set.  All local branch arguments below are
made inside that embedded neighborhood.

Two already proved project lemmas are also used, with their native
hypotheses:

- `QL_RETURN_FACTORIZATION`, to obtain the cyclic Jordan restrictions
  and the central degree profile; and
- `PQL_ITERATE_FILLED_GRAPH_NATURALITY`, including its fullness lemma,
  to identify the selected filled continua and their Jordan
  neighborhood bases.

## 3. Notation and the two separator sides

In this note \(L_j\) denotes KKL's **tree limb**
\(\mathcal L_j=T\cap\mathfrak L_j\), while \(\mathfrak L_j\) denotes the
planar limb of the filled Julia set.  KKL work with rotation number
\(1/q\), so the critical value \(v=F(c)\) lies in
\(\mathfrak L_1\), while the critical point \(c\) lies in
\(\mathfrak L_0\).
Set

\[
 K_1=F(K_0^0).
\tag{3.1}
\]

For \(s\geq1\), KKL define \(K_0^s,\alpha^s,L_0^s\) as the selected
components in \(\mathfrak L_0\) of the inverse images of
\(K_0^{s-1},\alpha^{s-1},L_0^{s-1}\), respectively.  Hence

\[
 \begin{aligned}
 F(K_0^s)&=K_0^{s-1},\\
 F(\alpha^s)&=\alpha^{s-1},\\
 F(L_0^{s+1})&\subset L_0^s.
 \end{aligned}
\tag{3.2}
\]

Here \(F\) is the embedded quadratic-like representative supplied by
Kahn near the filled set.  The equality for \(K_0^s\) uses confluence
for a finite proper branched cover:
`PQL_ITERATE_FILLED_GRAPH_NATURALITY`, Lemma 3.3, proves that a selected
component of the inverse image of the compact connected target maps
onto that target, and that selected compact components compose.  The
point equality is immediate.  For the generally noncompact tree limb
\(L_0^s\), the definition gives only the displayed inclusion; no
unproved onto statement is used below.

KKL line 1602 says that \(K_0^s\) separates \(\alpha^s\) from
\(L_0^{s+1}\).  This is a continuum-separation statement.  It does not,
without an additional prime-end realization theorem, produce two
distinct single prime ends.  The precise access-realization predicate is

\[
\begin{split}
\operatorname{AR}(s):\quad&
\text{the root and deep parent routes determine nonempty disjoint}\\
&\text{marked prime-end sets at }K_0^s,\text{ each retained by the}\\
&\text{proof-used ideal marking and equipped with a cyclic side flag.}
\end{split}
\tag{3.3}
\]

When \(\operatorname{AR}(s)\) holds, choose proof-used access germs from
those two marked sets and denote them by

\[
 a_s^{\rm root}
 \quad\text{and}\quad
 a_s^{\rm deep}.
\tag{3.4}
\]

The first is approached through the component containing
\(\alpha^s\), and the second through the component containing
\(L_0^{s+1}\).  These are access germs, not merely component labels.
A Jordan localization has a prime-end boundary, but it does not by
itself prove that the two parent routes select distinct marked prime
ends, especially in the non-locally-connected case.  KKL do not prove
\(\operatorname{AR}(s)\) for these proof-used sides.

## 4. The selected pull chain is conformal

### Lemma 4.1 (critical-value-free selected pulls)

For every \(s\geq1\), the selected limb pull

\[
 F:L_0^s\longrightarrow L_0^{s-1}
\tag{4.1}
\]

contains no critical point and is locally univalent at every point.
If a proof-used simply connected Jordan corridor \(E_{s-1}\) around
the whole target \(L_0^{s-1}\), avoiding \(v\), has been constructed
with \(\overline E_{s-1}\) compactly contained in the range disk of the
embedded quadratic-like representative, then its selected preimage
component maps conformally to \(E_{s-1}\).

Independently of that extra whole-limb localization, the small-Julia
pull

\[
 F:K_0^s\longrightarrow K_0^{s-1}.
\tag{4.2}
\]

admits Jordan-disk localizations \(V_s,V_{s-1}\) on which
\(F:V_s\to V_{s-1}\) is conformal and
\[
F^{-1}(K_0^{s-1})\cap V_s=K_0^s.
\]

#### Proof

The unique critical value \(v\) lies in the planar limb
\(\mathfrak L_1\), whereas every target tree pull \(L_0^{s-1}\) lies in
the selected planar critical limb \(\mathfrak L_0\).  The planar limbs
are disjoint, and their closures meet only at \(\alpha_F\); the critical
value belongs to the limb rather than to \(\alpha_F\).  Therefore

\[
 v\notin \overline{L_0^{s-1}}.
\tag{4.3}
\]

The unique critical point maps to \(v\), so (4.3) proves local
univalence on
the selected limb pull.  If the stated Jordan corridor \(E_{s-1}\)
exists, the component \(E_s\) of its inverse image containing the
selected pull is a proper unbranched cover of a disk; properness here
uses \(\overline E_{s-1}\Subset\) the range disk.  Every connected
unbranched covering of a simply connected disk has degree one, so

\[
 F:E_s\longrightarrow E_{s-1}
\tag{4.4}
\]

is conformal.  Notice that avoidance of \(v\) alone does not prove the
existence of one simply connected neighborhood of an arbitrary
possibly separating limb continuum; this is why the whole-limb
statement is conditional.

For \(K_0^s\), the Jordan corridor exists.  The fullness lemma in
`PQL_ITERATE_FILLED_GRAPH_NATURALITY` proves that each \(K_0^{s-1}\) is
a full continuum: the central small Julia set is full, and a proper
inverse component of a full continuum is full.  A full planar continuum
has a basis of Jordan-disk neighborhoods.  When \(s\geq2\), its target
lies in \(\mathfrak L_0\), so (4.3) applies directly.  When \(s=1\), the target is
\(K_0^0\), while \(v\in K_1\); primitivity makes \(K_0^0\cap K_1\)
empty.  A Jordan localization of \(K_0^0\) can again be chosen to avoid
\(v\).  In either case take the selected component of the inverse
Jordan disk.  The resulting conformal isomorphism pulls the connected
target continuum back to one connected continuum, namely the selected
component \(K_0^s\); hence the stated relative preimage equality holds.
This proves (4.2). \(\square\)

### Corollary 4.2 (conditional exact access transport)

Assume \(\operatorname{AR}(s)\) and
\(\operatorname{AR}(s-1)\), with the access germs selected compatibly
from the small-Julia Jordan localizations in Lemma 4.1.  For \(s\geq1\),
the conformal branch transports them by

\[
 a_s^{\rm root}\longmapsto a_{s-1}^{\rm root},
 \qquad
 a_s^{\rm deep}\longmapsto a_{s-1}^{\rm deep},
\tag{4.5}
\]

and preserves their cyclic order.

#### Proof

Equation (3.2) sends the root parent \(\alpha^s\) to
\(\alpha^{s-1}\), and sends the deep parent \(L_0^{s+1}\) into
\(L_0^s\).  The biholomorphism of Jordan disks in Lemma 4.1 maps
\(K_0^s\) exactly onto \(K_0^{s-1}\), so it restricts to a
biholomorphism
\[
 V_s\setminus K_0^s\longrightarrow
 V_{s-1}\setminus K_0^{s-1}.
\]
Uniformize these doubly connected domains by annuli.  The
biholomorphism extends to the two annular prime-end circles and
preserves the inner component, the outer component, and their cyclic
orders.  Compatibility of the selected markings identifies the local
inner prime ends with the KKL proof-used accesses and therefore sends
the two named access germs as in (4.5).
\(\square\)

Thus, conditional on the access-realization and marking compatibility,
every possible identification of the two separator sides occurs after,
not during, the selected pull chain.

## 5. The unique nonunivalent stage

### Lemma 5.1 (one quadratic collar)

For every \(n\geq1\), there are Jordan localizations \(V_n\) of
\(K_0^n\) and \(W_1\) of \(K_1\) for which

\[
 G_n:=F^{n+1}:V_n\longrightarrow W_1
\tag{5.1}
\]

is proper of degree two and

\[
 G_n^{-1}(K_1)=K_0^n.
\tag{5.2}
\]

Consequently

\[
 G_n:
 V_n\setminus K_0^n
 \longrightarrow
 W_1\setminus K_1
\tag{5.3}
\]

is a connected two-sheeted unbranched covering.

#### Proof

For each \(1\leq s\leq n\), Lemma 4.1 supplies a conformal inverse germ
\(\phi_s\) taking a neighborhood of \(K_0^{s-1}\) to the selected
neighborhood of \(K_0^s\).  These pairwise germs must be made
simultaneously composable; this does not follow merely by naming their
domains.  Starting with \(\phi_1\), inductively shrink an open
neighborhood \(O\) of \(K_0^0\) so that
\[
 \Phi_s:=\phi_s\circ\cdots\circ\phi_1
\tag{5.4a}
\]
is defined and univalent on \(O\) for every \(1\leq s\leq n\).
At the \(s\)-th finite step this is possible because
\(\Phi_{s-1}(K_0^0)=K_0^{s-1}\) is compact and lies in the open domain
of \(\phi_s\).  A finite intersection leaves an open neighborhood of
\(K_0^0\).

The central small Julia set \(K_0^0\) contains the unique simple
critical point \(c\) by the definition of renormalization.  Lemma 4.A
of `PQL_ITERATE_FILLED_GRAPH_NATURALITY`, derived from
`QL_RETURN_FACTORIZATION`, gives an isolating degree-two Jordan
restriction
\[
 F:\widetilde V_0\longrightarrow\widetilde W_1,
 \qquad
 F^{-1}(K_1)\cap\widetilde V_0=K_0^0.
\tag{5.5a}
\]
Take a decreasing smooth Jordan basis \(W_1^{(k)}\) of the full
continuum \(K_1\), with
\(\overline{W_1^{(1)}}\Subset\widetilde W_1\) and boundaries avoiding
the critical value, and let \(V_0^{(k)}\) be the component of
\(F^{-1}(W_1^{(k)})\cap\widetilde V_0\) containing \(K_0^0\).  If no
\(\overline{V_0^{(k)}}\) lay in \(O\), choose
\(x_k\in\overline{V_0^{(k)}}\setminus O\).  Properness makes the preimage of
\(\overline{W_1^{(1)}}\) compact in \(\widetilde V_0\), so a subsequence
converges inside \(\widetilde V_0\).  Since
\(\bigcap_k\overline{W_1^{(k)}}=K_1\), its limit lies in
\[
 F^{-1}(K_1)\cap\widetilde V_0=K_0^0\subset O,
\]
a contradiction.  The selected component contains the unique simple
critical point, so its restriction has degree at least two.  The
ambient restriction has degree two, hence this component has degree
exactly two and exhausts the preimage of \(W_1^{(k)}\).
Riemann--Hurwitz gives Euler characteristic \(2\cdot1-1=1\), so the
connected planar source is a disk.  Its boundary contains no critical
point and is an unbranched finite cover of the smooth Jordan curve
\(\partial W_1^{(k)}\); consequently it too is a Jordan curve.  Choose
such a \(k\), rename its source and target \(V_0,W_1\), and obtain
\[
 F:V_0\longrightarrow W_1,
\qquad
 V_0\Subset O,
\tag{5.5}
\]
of degree two, with
\[
 F^{-1}(K_1)\cap V_0=K_0^0.
\tag{5.6}
\]

Now set
\[
 V_s=\Phi_s(V_0)\qquad(1\leq s\leq n).
\tag{5.4b}
\]
Every \(V_s\) is a Jordan disk, and the inverse-germ identities make
\[
 F:V_s\longrightarrow V_{s-1}\qquad(1\leq s\leq n)
\]
a conformal isomorphism.  Hence the restrictions are simultaneously
composable by construction and

\[
 H_n:=F^n:V_n\longrightarrow V_0
\tag{5.4}
\]

is conformal.  Equations (5.4)--(5.6) prove (5.1)--(5.2), with every
preimage equality understood relative to its displayed Jordan source.
The only critical point of
\(G_n\) is the pull of \(c\), and it lies in \(K_0^n\); its critical
value lies in \(K_1\).  Removing these filled continua therefore
removes all branching.  The source \(K_0^n\) is full by the fullness
lemma cited in Lemma 4.1, and \(K_1\) is a full small filled Julia
component in the primitive cycle.  Hence both complements are
connected.  A generic point of \(W_1\setminus K_1\) has exactly two
preimages in \(V_n\setminus K_0^n\), so the restriction has degree two
and is proper.  This proves (5.3). \(\square\)

### Lemma 5.2 (deck-collision classification)

Let \(\tau_n\) be the nontrivial deck involution of (5.3).  Suppose
\(\gamma^-\) and \(\gamma^+\) are two distinct retained proper paths
such that each
\[
 G_n|\gamma^\pm:\gamma^\pm\longrightarrow
 \delta^\pm:=G_n(\gamma^\pm)
\]
is a homeomorphism onto a simple proper target path.  Then

\[
 \delta^-=\delta^+
\tag{5.7}
\]

as unparametrized geometric paths if and only if, after a possible
reversal of path parameter,

\[
 \gamma^+=\tau_n\circ\gamma^-.
\tag{5.8}
\]

In particular, equality of the images forces the endpoint-access pair
of one path to be the deck transform of the endpoint-access pair of the
other, either in the same order or in the reversed order.

#### Proof

Every connected two-sheeted cover is regular.  Indeed, in each evenly
covered disk, exchange the two sheets.  These local exchanges agree on
overlaps and define the unique nontrivial deck involution \(\tau_n\).

Assume (5.7) and call the common simple path \(\delta\).  The
homeomorphism hypotheses make both source paths components of
\(G_n^{-1}(\delta)\).  Choose a common parametrization of \(\delta\),
allowing parameter reversal because the paths are being compared
unparametrized.  The two paths are lifts of that common path.
Uniqueness of path lifting says that two lifts agreeing at one point
are equal; otherwise their starting points are the two points of one
fiber, and applying \(\tau_n\) to one lift gives the other.  This proves
(5.8).  Conversely, the deck transform of one inverse component is the
other inverse component and has the same image because
\(G_n\circ\tau_n=G_n\).

For the endpoint statement, both complements in (5.3) are doubly
connected domains: each is a Jordan disk minus a full continuum.
Uniformize them by round annuli.  A finite unbranched annular cover is
conjugate to a power map, and its deck transformations extend to both
circles of the annular prime-end compactification.  Hence the relation
between the two lifted paths extends to their local collar prime-end
limits.  Identifying those local prime ends with KKL's proof-used ideal
intervals is not part of this lemma; it is exactly the later
marked-access and corridor-compatibility requirement. \(\square\)

Lemma 5.2 is stronger than the abstract observation that a degree-two
map may identify two paths: **inside the selected KKL collar** it shows
that there is exactly one possible collision mechanism and locates it
at the central quadratic stage.  It does not, by itself, prove that the
two complete portions named at line 1603 stay in that collar or cannot
leave and re-enter it on another fiber-product sheet.

## 6. The Hubbard-tree labels do not separate the deck pair

### Lemma 6.1 (central parent-route collapse)

The two distinguished sides of \(K_0^0\) in (3.3) have forward parent
routes in the same component of \(T\setminus K_1\).

#### Proof

The root-side parent maps to \(\alpha_F\).  The deep-side parent
\(L_0^1\) maps into \(L_0\), by (3.2).  The connected small Julia set
\(K_1\) contains the critical value \(v\in\mathfrak L_1\).  It cannot
contain \(\alpha_F\): since \(\alpha_F\) is fixed, that would put
\(\alpha_F\) in every forward member of the small-Julia cycle,
contradicting pairwise disjointness of the primitive cycle of period
\(>1\).  Because the open planar limbs are the components of
\(K(F)\setminus\{\alpha_F\}\), connectedness now gives
\(K_1\subset\mathfrak L_1\).

The tree limb \(L_0\) lies in the disjoint planar limb
\(\mathfrak L_0\), while \(\alpha_F\) belongs to neither open planar
limb.  Thus the connected tree set \(L_0\cup\{\alpha_F\}\) is disjoint
from \(K_1\).  Hence \(\alpha_F\) and \(L_0\) lie in the same component
of \(T\setminus K_1\). \(\square\)

Thus the coarse itinerary

\[
 \begin{array}{c|c|c|c}
 \text{stage}&\text{degree}&\text{root-side parent}&
 \text{deep-side parent}\\ \hline
 s\to s-1,\ s\geq1&1&
 \alpha^s\mapsto\alpha^{s-1}&
 L_0^{s+1}\mapsto\text{into }L_0^s\\
 0\to1&2&
 \alpha_F\mapsto\alpha_F&
 L_0^1\mapsto\text{into }L_0
 \end{array}
\tag{6.1}
\]

is complete through the component level.  It separates the two sides
at every conformal pull stage, but it merges their parent component at
the central degree-two stage.  A prime-end side flag finer than the
component route is therefore indispensable.

KKL line 1274 says only that the end intervals of the image of a side
of \(K\) are sides of \(F(K)\).  It does not say that two selected
sides have distinct images.  That distinction cannot be recovered from
(6.1).

### 6.2 Complete proof-use itinerary audit

The complete itinerary universe needed for line 1603, and the exact
state supplied by the locked source, is:

| itinerary field | selected stages \(s\to s-1\), \(s\geq1\) | central stage \(K_0^0\to K_1\) | certification |
|---|---|---|---|
| filled component | \(K_0^s\mapsto K_0^{s-1}\) | \(K_0^0\mapsto K_1\) | proved |
| local degree | \(1\) | \(2\) | proved |
| critical value in target corridor | absent | \(v\in K_1\) | proved |
| parent route | \(\alpha^s\mapsto\alpha^{s-1}\), \(F(L_0^{s+1})\subset L_0^s\) | both routes enter one component of \(T\setminus K_1\) | proved at component level |
| prime-end side/access | transported conformally if (3.3) is realized | two deck lifts must be distinguished | open marking predicate |
| complete fiber-product sheet word | selected local germ only | central deck phase unknown | open (7.3) |
| survival of line-2097 filter | not recorded occurrence by occurrence | not recorded | open (7.2) |
| outer endpoint interval | no complete parent/access word | terminal interval and deck mate unknown | open (8.2) |
| terminal geometric image | source says each is a Wave | equality versus distinctness not checked | open (8.4) |

This table is exhaustive for the proposed contradiction: component,
degree, critical, parent, access, sheet, filter, endpoint, and geometric
image are all recorded.  The first four rows are the proved reduction.
The last five rows are not derivable from the source's coarse interval
sequence.

Three source-supported partial realization facts must nevertheless be
retained:

1. \(A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}\), and
   \(A_{n+1}\subset A_0\).  Since the typed range below has
   \(n+1<N\), each selected occurrence is unbreakable through the
   required iterate.
2. By the definition of \(A_{n+1}\), the complete terminal family
   \(F_*^{\,n+1}A_{n+1}\) is a Wave ending at \(B L_0\).
3. KKL line 1600 asserts that every full leaf has an existential
   restriction path ending at \(L_0^{n+1}\).  It does not identify that
   restriction with the entire \(B L_0\)-to-\(L_0^{n+1}\) portion,
   anchor its occurrence window at the \(B L_0\) end, or provide a
   sequentially retained extension tower.  The separate proved
   one-retained-chain theorem supplies one retained untagged chain, but
   does not recover this missing portion provenance.

These facts do not split that one full-leaf occurrence into two
distinct retained restriction components.  Nor is a single leaf itself
a Wave: the precise missing assertion is that the two families of
portions form retained sublaminations whose terminal images are Waves,
while the two portions of each fixed \(\alpha\) determine two distinct
retained terminal proper paths.

## 7. The two actual portions and the earlier realization gap

Fix
\[
 b\leq n<N-1
\]
and \(\alpha\in A_{n+1}\), and assume, as in the contradiction at KKL
line 1603, that \(\alpha\) does not pass through \(K_0^n\).  This is the
entire typed range relevant to the proof: \(A_j\) was defined only for
\(j<N\), and the two applications use \(n=b,b+1\).  KKL name two
topological portions:

\[
 \begin{aligned}
 P^-_{n,\alpha}&:
 B L_0\longrightarrow L_0^{n+1},\\
 P^+_{n,\alpha}&:
 L_0^{n+1}\longrightarrow
 \partial_{\rm C}T\setminus B L_0.
\end{aligned}
\tag{7.1}
\]

Write
\[
 I_r=\iota_r:U^r\longrightarrow U,
 \qquad
 P_r=f^r:U^r\longrightarrow U
\tag{7.1a}
\]
for the immersion and covering projections of KKL's actual iterated
fiber product.  Thus
\[
 F_*^{\,r}=P_{r*}I_r^*
\]
on retained paths.  To use the Appendix definition of breaking, one
first needs:

\[
 \begin{split}
 \operatorname{RR}(n,\alpha):\quad&
 \text{the two }P^\pm_{n,\alpha}\text{ determine distinct proper}\\
 &\text{components }\gamma^\pm_{n,\alpha}
 \text{ of the full restriction }I_{n+1}^*\alpha;\\
 &\text{their compatible predecessor occurrences remain distinct}\\
 &\text{through every intermediate immersion restriction;}\\
 &\gamma^\pm_{n,\alpha}\text{ is a path in every pulled marking;}\\
 &\gamma^\pm_{n,\alpha}\text{ is never discarded as subordinate to}\\
 &\text{one pulled interval;}\\
 &P_{n+1}(\gamma^\pm_{n,\alpha})
 \text{ are two retained elements of }F_*^{\,n+1}\alpha;\\
 &\text{over the leaf family, each collection of such elements is a}\\
 &\text{retained sublamination whose terminal image is a Wave.}
 \end{split}
\tag{7.2}
\]

This is the **retained-realization predicate**.  KKL line 1603 asserts
its conclusion in prose, but the locked proof does not derive it.
In particular, Proposition 2099 permits a consecutive itinerary step
to be represented by adjacency alone, or by two intervals in one
pulled interval, rather than by an actual retained path.

The embedded collar and Lemma 4.1 explain why (7.2) is plausible near
the selected pull chain.  They do not prove that the two portions give
distinct full restriction components, have proper marked outer ends,
survive every filter, and remain actual paths through the full
fiber-product horizon.

By Lemma 3.4 of `PQL_ITERATE_FILLED_GRAPH_NATURALITY`, after shrinking
the base localization \(V_n\) if necessary, there is an actual
holomorphic graph
\[
 \Gamma_{n+1}:V_n\longrightarrow
 \widehat V_n\subset U^{n+1}
\]
with
\[
 I_{n+1}\circ\Gamma_{n+1}=\operatorname{id}_{V_n},
 \qquad
 P_{n+1}\circ\Gamma_{n+1}=G_n.
\tag{7.2a}
\]
Thus \(\widehat V_n\) is the correctly typed copy of the selected
planar collar in the final fiber-product surface.  Formula (7.2a)
realizes the local graph, but says nothing about which components of
\(I_{n+1}^*\alpha\) enter it or whether they later re-enter.

Even after (7.2), applying Lemma 5.2 to the complete portions therefore
requires the following additional predicate:

\[
\begin{split}
\operatorname{SC}(n,\alpha):\quad&
\text{each }\gamma^\pm_{n,\alpha}\text{ has exactly one retained}\\
&\text{connected crosscut }
\widehat\lambda^\pm_{n,\alpha}
\subset\widehat V_n\setminus\Gamma_{n+1}(K_0^n);\\
&\widehat\lambda^-_{n,\alpha}\text{ and }
\widehat\lambda^+_{n,\alpha}\text{ are distinct, and}\\
&\lambda^\pm_{n,\alpha}:=
\Gamma_{n+1}^{-1}(\widehat\lambda^\pm_{n,\alpha})
\subset V_n\setminus K_0^n;\\
&G_n|\lambda^\pm_{n,\alpha}\text{ is a homeomorphism onto a simple}\\
&\text{proper target-collar crosscut;}\\
&P_{n+1}(\gamma^\pm_{n,\alpha})\cap
 (W_1\setminus K_1)
=P_{n+1}(\widehat\lambda^\pm_{n,\alpha})
=G_n(\lambda^\pm_{n,\alpha});\\
&\text{there is no other retained entry, exit, re-entry, ambient-sheet}\\
&\text{change, or late enlargement over this target collar.}
\end{split}
\tag{7.3}
\]

This is the **selected-corridor confinement predicate**.  The last
displayed equality is an equality of the complete target-collar
occurrence, not merely containment of one local germ.  Without it,
equality of the two global terminal paths need not be classified by the
two-sheet deck involution in Lemma 5.2: another fiber-product sheet or a
later re-entry could participate.

KKL do not state (7.3).  Their definition of \(A_{n+1}\) gives the
untagged terminal Wave but no sheet word or no-reentry certificate.

## 8. The exact deck obstruction and an endpoint certificate

Assume \(\operatorname{RR}(n,\alpha)\),
\(\operatorname{SC}(n,\alpha)\), and
\(\operatorname{AR}(s)\) for every \(0\leq s\leq n\), with the
markings selected compatibly as in Corollary 4.2.  Orient \(\alpha\)
from its \(B L_0\)-end to its end in
\(\partial_{\rm C}T\setminus B L_0\), and give both portions the induced
orientation.  Transport the portions through the conformal prefix
\(H_n\) in (5.4).  Record the ordered prime-end access pairs

\[
 \mathbf e^\pm_{n,\alpha}
 =
 \left(
 e^\pm_{\rm in},
 e^\pm_{\rm out}
 \right)
\tag{8.1}
\]

in the central collar \(V_0\setminus K_0^0\), including:

\[
 \left(
 \text{source interval},
 \text{parent component},
 \text{side of the parent},
 \text{cyclic position},
 \text{orientation}
 \right)
\tag{8.2}
\]

at each endpoint.  Let \(\tau_0\) be the central deck involution,
conjugate to \(\tau_n\) by \(H_n\).

If the two terminal images collide, Lemma 5.2 gives the necessary
endpoint alternatives

\[
 \mathbf e^+_{n,\alpha}
 =
 \tau_0\mathbf e^-_{n,\alpha}
 \quad\text{or}\quad
 \mathbf e^+_{n,\alpha}
 =
 \operatorname{rev}
 \bigl(\tau_0\mathbf e^-_{n,\alpha}\bigr).
\tag{8.3}
\]

Relation (8.3) is necessary, not sufficient, for collision: two
different proper paths can have the same endpoint pair.  The exact
necessary-and-sufficient collar predicate is instead the geometric
deck noncollision

\[
 \boxed{
 [\lambda^+_{n,\alpha}]
 \neq
 [\tau_n(\lambda^-_{n,\alpha})],
 }
\tag{8.4}
\]

where brackets mean equality as unparametrized geometric paths and
therefore already allow reversal.  Call (8.4) the **selected-collar
deck-noncollision predicate**.

A complete endpoint computation can prove (8.4) by the stronger,
readily falsifiable certificate

\[
 \boxed{
 \left\{e^+_{\rm in},e^+_{\rm out}\right\}
 \neq
 \tau_0
 \left\{e^-_{\rm in},e^-_{\rm out}\right\}.
 }
\tag{8.5}
\]

because equality of the paths would force the endpoint relation in
(8.3).  Formula (8.5) is sufficient but not necessary.  In a realized
separator collar, the deck transformation preserves the inner and
outer boundary components, while the orientations induced by the
consecutive portions of \(\alpha\) are opposite; with those additional
endpoint-role flags, a collision is seen as a transposition of the
ordered endpoint pair.  KKL do not construct that collared
endpoint-role record.  Conversely, failure of (8.5) proves no
collision: paths can have deck-related endpoints but different relative
homotopy or winding classes.  In that case the full path predicate
(8.4), or an equivalent collar arc-class record, must still be
computed.

The exact path predicate (8.4), or the stronger sufficient endpoint
certificate (8.5), together with (7.2)--(7.3) and compatible all-stage
access transport from (3.3), proves the desired distinct-image
statement:

\[
 P_{n+1}(\gamma^-_{n,\alpha})
 \neq
 P_{n+1}(\gamma^+_{n,\alpha}).
\tag{8.6}
\]

Indeed, under the complete-occurrence equality in (7.3), equality in
(8.6) would imply the deck relation in Lemma 5.2 and hence contradict
(8.4); it would also imply (8.3), and therefore contradict (8.5)
whenever that sufficient certificate is used.  Thus
\(F_*^{n+1}\alpha\) would
contain at least two retained paths, contradicting the
\((n+1)\)-unbreakability inherited from
\(A_{n+1}\subset A^{N\text{-nbr}}\).

## 9. Why the locked source does not prove (8.4)

The source supplies only the following endpoint information.

1. Before pushing, one outer end lies in \(B L_0\), while the other lies
   in \(\partial_{\rm C}T\setminus B L_0\).
2. The selected complete pushforward is a Wave ending at \(B L_0\).
3. The coarse interval action has
   \[
     F_*B L_0=\partial_{\rm C}T.
   \tag{9.1}
   \]

Equation (9.1) destroys the proposed coarse distinction: an end that
starts in \(B L_0\) is not confined to a proper terminal
multi-interval.  The definition of \(A_{n+1}\) does not record which
terminal interval, parent side, or prime-end lift is used by either
portion.

The itinerary proposition at lines 2099--2108 does not repair this.
It gives a finite interval sequence, but an individual transition may
be:

- an actual restriction path;
- adjacency of two intervals; or
- membership of both intervals in one pulled target interval.

It therefore supplies neither the selected-corridor/no-reentry
certificate (7.3), the two complete ordered access tuples (8.2), nor
their deck phase under the unique degree-two stage.

Finally, the component route itself cannot prove even the endpoint
certificate (8.5), much less the path predicate (8.4), by Lemma 6.1.
The root and deep sides have the same terminal parent component.
Consequently the first genuinely missing bit is a two-valued
prime-end/deck flag at that component, together with the outer endpoint
flag needed to test the transposition.  If the endpoint test is
inconclusive, the complete path/deck phase in (8.4) is still required.

## 10. Push VII and Push VIII do not fill the predicate

The audited Push VII material proves a finite binary contact automaton
for one direct-decoration package.  It correctly identifies the
necessary refinement:

\[
 (\text{landing vertex},\text{incident side},\text{orientation})
\tag{10.1}
\]

rather than a bare endpoint.  But its assessment explicitly records
that the endpoint flags require a corrected incidence record and that
the construction is not instantiated on the actual KKL pulled surface.
It therefore gives the right data type for (8.2), not the values needed
to test (8.5) on the KKL block.

The audited Push VIII theorem is an abstract finite linear-label
enumerator.  Its own scope statement says that it does not prove that
the finite hull is an immersion pullback, that the endpoint map comes
from a covering, or that the labels are analytically realizable.  The
assessment also found that the proposed fixtures did not even enforce
atomwise endpoint consistency.  It cannot certify either the endpoint
condition (8.5) or the central path/deck phase in (8.4).

Thus neither research push supplies a source-specific proof of the
missing selected-collar path/deck inequality.

## 11. Adversarial checks

1. **The critical-value-free prefix is not confused with the full
   iterate.**  Lemma 4.1 proves degree one only for
   \(K_0^s\to K_0^{s-1}\), \(s\geq1\).  Lemma 5.1 explicitly retains
   the central degree-two map \(K_0^0\to K_1\).
2. **Absence of a critical point is used with a simply connected
   target.**  The degree-one conclusion is not inferred from
   unbranchedness on an arbitrary annulus.
3. **Non-local connectivity is not assumed.**  Whenever the open access
   predicate (3.3) is realized, its accesses are prime ends of Jordan
   localizations, not Euclidean landing points of the continua.
4. **Distinct source portions are not declared distinct after the
   cover.**  Under the simple-path and corridor hypotheses stated
   explicitly in Lemma 5.2 and (7.3), that lemma classifies exactly when
   their images collide.
5. **Coarse parent labels are tested and fail.**  Lemma 6.1 shows why
   the Hubbard-tree component route cannot distinguish the two central
   sheets.
6. **The retained-path filter and global sheet route are not
   bypassed.**  They are isolated as the earlier predicates (7.2) and
   (7.3).
7. **Orientation is not silently imported.**  Formula (8.4) compares
   unparametrized paths and (8.5) compares unordered endpoint sets.
   Orientation is used only for the optional finer diagnosis of the
   collision as an ordered transposition.
8. **No abstract countermodel is used as a KKL counterexample.**  The
   obstruction is derived from the actual KKL selected pull and its one
   central quadratic stage.
9. **No numerical or finite compiler output proves an analytic
   predicate.**
10. **No downstream conclusion is promoted.**  Even a proof of (8.4)
    would still leave the final retained component-to-component
    \(Q\)-exit extraction to be proved.

## 12. Exact next theorem

The logically minimal theorem completing the line-1603 inference is:

> **KKL stationary two-sided Wave noncollision.**  Under the complete
> hypotheses of the KKL stationary block, for every
> \(b\leq n<N-1\) and every \(\alpha\in A_{n+1}\) that avoids
> \(K_0^n\), the two portions in (7.1) give two distinct retained
> terminal proper paths under \(F_*^{\,n+1}\).

The following stronger theorem is the source-specific repair route
isolated in this note:

> **KKL stationary selected-collar repair.**  In the same range, both
> portions satisfy retained realization (7.2); the root and deep routes
> satisfy \(\operatorname{AR}(s)\) for every \(0\leq s\leq n\), with
> compatible pulled markings and cyclic-order transport; the two
> occurrences satisfy the exact graph-collar/no-reentry predicate
> (7.3); and their selected collar crosscuts satisfy the exact path
> deck-noncollision predicate (8.4).  It is sufficient, but not
> necessary, to replace the last clause by the endpoint certificate
> (8.5).

The first theorem is logically weaker.  The four clauses of the second
are a proof architecture, not a claim that every possible proof must
factor through them.

The locked source proves neither separate two-sided retention,
graph-collar confinement, complete access records, nor the path/deck
inequality.  A proof following this route must refine the minimal
Hubbard marking at the central \(K_1\)-side by the two lifts of the
quadratic collar, transport the flag through every selected conformal
pull, and compute the complete collar arc class of both portions.  A
deck-related endpoint pair merely makes (8.5) inconclusive.  Only an
actual deck relation between the two crosscut paths, as in the negation
of (8.4), certifies collision and forces an occurrence/deck-phase
replacement state; such a state may also need a relative-homotopy or
winding tag.

## 13. Binary certification and ledger recommendation

The binary theorem verdict is:

| assertion | verdict |
|---|---|
| selected \(K_0^s\)-pull degree-one profile | **proved** |
| one central degree-two collar | **proved** |
| two-sheet deck-collision classification for simple proper collar paths | **proved** |
| coarse central parent-route collapse | **proved** |
| one retained chain through the untagged action | **proved** |
| two-occurrence binder for the actual line-1603 portions | **open** |
| retained realization (7.2) for both bound portions | **open** |
| marked-access realization (3.3) through the full horizon | **open** |
| selected-corridor confinement/no-reentry (7.3) | **open** |
| selected-collar path deck-noncollision (8.4) | **open** |
| deck-separated endpoint pair (8.5), optional sufficient certificate | **open** |
| KKL line-1603 two-sided Wave noncollision | **open** |

Therefore `KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION` must remain
open.  The most direct evidence anchor is

```text
kkl_stationary_tsnc_source_reduction.md#12-exact-next-theorem
```

and the proved reduction is anchored at

```text
kkl_stationary_tsnc_source_reduction.md#5-the-unique-nonunivalent-stage
```

The machine ledger now records the following exact nonduplicative
clause-level split:

```text
KKL_STATIONARY_ONE_RETAINED_CHAIN                    proved
KKL_STATIONARY_TWO_OCCURRENCE_BINDER                 open  precursor to (7.2)
KKL_STATIONARY_RETAINED_PORTION_REALIZATION          open  Section 7, (7.2)
KKL_STATIONARY_MARKED_ACCESS_ITINERARY               open  Sections 3 and 8
KKL_STATIONARY_SELECTED_CORRIDOR_CONFINEMENT         open  Section 7, (7.3)
KKL_STATIONARY_SELECTED_COLLAR_DECK_NONCOLLISION     open  Section 8, (8.4)
```

The proved one-chain node feeds the open two-occurrence binder, which
feeds retained-portion realization.  The two-sided noncollision node
then depends on retained realization, marked access, corridor
confinement, selected-collar deck noncollision, and the previously
proved degree-two correction.  The selected-collar node is the exact
path predicate (8.4), not the merely sufficient endpoint predicate
(8.5).  No separate proved node is recommended for
Lemmas 4.1--6.1 because their degree content is already contained in
`KKL_STATIONARY_DEGREE_TWO_CORRECTION`; duplicating it would add ledger
surface without closing another gate.

Two ledger statements require the following typed reading.  In
`KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION`, “deck-separated endpoint
pairs” is shorthand for the exact selected-collar path predicate in its
dependency node; endpoint separation alone is only sufficient.  In
`KKL_STATIONARY_RETAINED_PORTION_REALIZATION`, “has a terminal image
that is a Wave” refers to the family of realized portions; for one
fixed leaf the terminal object is a retained proper path belonging to
that Wave.
