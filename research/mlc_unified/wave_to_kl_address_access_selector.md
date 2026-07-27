# Wave-to-KL address and carrier-access selector

## 1. Exact result and status boundary

This note separates two coordinates that were previously conflated:

1. the **component/address/finite chronological phase** coordinate; and
2. the **carrier-relative access/path-space** coordinate.

The first coordinate is constructed below.  At the terminal anchor the
second coordinate is advanced through a unique actual puzzle vertex,
two independently realized compact half-collars, and an exhaustive
proper-restriction/collar obstruction record.  This proves

```text
DIRECT_DECORATION_COMPONENT_ADDRESS_FINITE_PHASE_SKELETON
PUZZLE_VERTEX_EXTERIOR_COMPONENT_INJECTIVITY
TERMINAL_K1_UNIQUE_PUZZLE_VERTEX_ANCHOR
TERMINAL_ANCHOR_NOT_SMALL_JULIA_VERTEX
TERMINAL_ANCHOR_COMPACT_HALF_COLLARS
TERMINAL_SEAM_NORMALIZED_PATH_LIFT
TERMINAL_ANCHOR_COLLAR_OR_RESTRICTION_OBSTRUCTION
```

It leaves the actual value of the binder restriction record
\(\mathfrak r_*\), the common-access welding, and

```text
WAVE_TO_KL_ADDRESS_ACCESS_SELECTOR
DIRECT_DECORATION_CANONICAL_KL_STAGE_ALIGNMENT
DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER
VIRTUAL_WAVE_MARKED_CORRESPONDENCE
VAAPC-I
UPTCR
MLC
```

open.

No statement below identifies a Hubbard-tree side with a
Kahn--Lyubich (KL) puzzle-vertex boundary arc merely by label.  The KL
\(\lambda,\xi,\eta\) arcs belong to the conformal ideal boundary of a
pseudo-piece.  A KKL side belongs to the ideal marking of a
carrier-relative complement.  Moving between them is an analytic
prime-end/crosscut assertion.

## 2. Source lock and imported results

The construction uses the following already audited project theorems.

| Input | Exact imported content |
|---|---|
| `virtual_cantor_pullback_compactification.md`, Theorem 7.1 | Actual puzzle cylinders \(Q_w\), finite continua \(K_w\), end fibers \(E_\omega\), exact component classification, prefix dynamics, suffix parent data, and presentation invariance |
| `direct_decoration_bigraded_kl_stage_grid.md`, Proposition 4.2 and Theorem 5.2 | Unit phases \(Q_{w,r}\), univalent unit maps, the two commuting grid directions, and their intrinsic KL pseudo-piece lift |
| `terminal_hubbard_anchor.md`, Proposition 7.1 and Corollary 7.2 | The terminal carrier \(\mathcal T\), the actual native side \(I_{1\to0}\) at \(K_1\), its itinerary, \(\chi_{\rm ideal}=0\), and the still-missing protected analytic connector |
| KL Decorations `kingdom.tex`, SHA-256 `5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7`, lines 56--62 | Puzzle vertices and the exterior continua \(S_Y^v\) |
| `.tmp_kl08_source/psiql.tex`, lines 95--161, 169--207, 231--275 | Path-space/glued pseudo-pieces, naturality, KL ideal-boundary types, ordered horizontal multicurves, and the KL lifting lemma |

For the direct-decoration separator put

\[
 A=\{0,1\},\qquad g=f^q.
\]

The empty word is denoted by \(\varnothing\).

## 3. The constructed component/address/phase coordinate

### Definition 3.1

Let

\[
 \mathcal H_\partial
 =
 \bigcup_{w\in A^{<\mathbb N}}K_w
 \ \cup\
 \bigcup_{\omega\in A^{\mathbb N}}E_\omega
\]

be the compact pullback component package.  Define

\[
 \operatorname{Addr}_0:
 \pi_0(\mathcal H_\partial)
 \longrightarrow
 A^{<\mathbb N}\sqcup A^{\mathbb N}
\tag{3.1}
\]

by

\[
 \operatorname{Addr}_0(K_w)=w,
 \qquad
 \operatorname{Addr}_0(E_\omega)=\omega.
\tag{3.2}
\]

For the root set

\[
 \mathcal C(\varnothing,0)=(P,K_0).
\tag{3.3}
\]

For every nonempty finite word \(w\) and \(0\le r\le q\), set

\[
 Q_{w,r}=f^r(Q_w),\qquad
 K_{w,r}=f^r(K_w),\qquad
 \mathcal C(w,r)=(Q_{w,r},K_{w,r}).
\tag{3.4}
\]

The integer \(r\) is a chronological puzzle phase.  It is not a deck
coordinate in a chosen universal-cover chart.

### Theorem 3.2
(`DIRECT_DECORATION_COMPONENT_ADDRESS_FINITE_PHASE_SKELETON`)

In the fixed direct-decoration puzzle:

1. \(\operatorname{Addr}_0\) is a bijection.
2. For every nonempty \(w\) and every \(0\le r\le q\),
   \(K_{w,r}\subset Q_{w,r}\) is an actual nonempty compact connected
   subset of \(J(f)\).
3. For \(0\le r<q\),
   \[
   f:\mathcal C(w,r)\longrightarrow\mathcal C(w,r+1)
   \tag{3.5}
   \]
   is an actual degree-one pair map: its puzzle-disk restriction is a
   homeomorphism, holomorphic and univalent on the interior, and it maps
   \(K_{w,r}\) exactly onto \(K_{w,r+1}\).
4. If \(w=av\), then
   \[
   \mathcal C(w,q)=\mathcal C(v,0).
   \tag{3.6}
   \]
5. The geometric cell-parent inclusions
   \[
   Q_{wb,r}\subset Q_{w,r}
   \tag{3.7}
   \]
   commute with the unit dynamics.  No inclusion
   \(K_{wb,r}\subset K_{w,r}\) is asserted; those are distinct pullback
   components housed in nested cells.
6. The record is intrinsic to the marked puzzle and its actual pullback
   components.  No pseudo-piece \(\Psi(E_\omega)\), point landing of
   \(E_\omega\), or numerical deck origin is asserted.

#### Proof

The compactification theorem says that the connected components of
\(\mathcal H_\partial\) are exactly the pairwise distinct continua
\[
 \{K_w:w\in A^{<\mathbb N}\}
 \cup
 \{E_\omega:\omega\in A^{\mathbb N}\}.
\]
Equations (3.1)--(3.2) are therefore injective and surjective, proving
Item 1.

The construction gives \(K_w\subset Q_w\) and
\(K_w\subset J(f)\).  Applying \(f^r\) yields
\[
 K_{w,r}=f^r(K_w)\subset f^r(Q_w)=Q_{w,r}.
\]
Continuous images preserve nonemptiness, compactness, and connectedness,
and the Julia set is forward invariant.  This proves Item 2.

Fix \(0\le r\le q\).  If \(x,y\in Q_w\) and
\(f^r(x)=f^r(y)\), then applying \(f^{q-r}\) gives
\[
 g(x)=g(y).
\]
The restriction \(g|_{Q_w}\) is injective, hence \(x=y\).  Thus every
\(f^r|_{Q_w}\), and in particular every unit map
\[
 f:Q_{w,r}\longrightarrow Q_{w,r+1},
\]
is injective.  It is a continuous surjection from a compact disk to its
Hausdorff image, so it is a homeomorphism; its interior restriction is
holomorphic and univalent.  Equation (3.4) gives
\[
 f(K_{w,r})=K_{w,r+1},
\]
proving Item 3.

If \(w=av\), the prefix-shift formulas from the compactification theorem
and the grid theorem give
\[
 g(Q_{av})=Q_v,\qquad g(K_{av})=K_v.
\]
This is (3.6).  The cell inclusion and strict unit square in Item 5 are
Proposition 4.2 of the bigraded-grid note.  The finite continua are
pairwise disjoint by the compactification theorem, which is why (3.7)
must not be copied to the \(K\)-coordinate.

Finally, every entry was defined from the fixed marked puzzle, actual
inverse branches, and actual embedded continua.  Presentation
invariance is Item 8 of the compactification theorem.  Infinite
addresses supply only the planar continua \(E_\omega\); the finite
pseudo-piece source has no open geometric puzzle piece attached to
\(E_\omega\).  This proves Item 6. \(\square\)

### Corollary 3.3

Once an independent argument identifies a proof-used object with an
actual finite component \(K_w\), its finite address \(w\), chronological
phase object \(\mathcal C(w,r)\), and all unit transports are canonical.
The theorem does not perform that identification for a Wave trace.

## 4. Correct type of the still-open selector

A Wave row \(\mathcal Q\) is an intensional binder.  Consequently one
cannot attach one puzzle piece to the phrase “every wave” and call the
row aligned.  For a bound object

\[
 \gamma\in\operatorname{GTr}_{h,\mathcal Q},
\]

the desired selector must produce a binder-dependent compatible atlas

\[
 \operatorname{Sel}_{h,\mathcal Q}(\gamma)
 =
 \{\mathfrak s_\alpha(\gamma)\}_{\alpha\in A(\gamma)}.
\tag{4.1}
\]

Each chart record must contain

\[
\begin{split}
\mathfrak s_\alpha(\gamma)=(
&Y_\alpha,\Psi(Y_\alpha),H_\alpha,
\mathcal D_\alpha^{\rm cen},\mathcal D_\alpha^{\rm tile},
\rho_\alpha,\delta_\alpha,\\
&\theta_\alpha^{\rm rel},\theta_\alpha^{\rm KL},
j_\alpha,\widetilde z_\alpha,
H_{s,\alpha},H_{t,\alpha},\mathfrak E_\alpha).
\end{split}
\tag{4.2}
\]

The types are:

1. \(Y_\alpha\) is an actual authorized finite puzzle piece, such as
   \(P,V_{\rm esc},Q_{w,r}\), or a source-authorized first-return piece.
2. \(H_\alpha\) is the actual pulled or immersed full carrier in
   \(\Psi(Y_\alpha)\).  The carrier-relative marked surface is
   \[
   M_\alpha=\Psi(Y_\alpha)\setminus H_\alpha.
   \tag{4.3}
   \]
3. The related part of \(\gamma\) is cut at all declared
   central-copy/tile seams.  The central segments
   \(\mathcal D_\alpha^{\rm cen}\) have analytic charts
   \(\rho_\alpha\) into \(Y_\alpha\setminus H_\alpha\).  The complementary
   segments \(\mathcal D_\alpha^{\rm tile}\) are represented by actual
   authorized path classes \(\delta_\alpha\) in named KL tiles.
4. \(\theta_\alpha^{\rm rel}\) maps proof-used Hubbard-tree sides to the
   complete prime-end marking of \(M_\alpha\), preserving cyclic order.
   The separate field \(\theta_\alpha^{\rm KL}\) records a proved
   connector, if any, from those carrier-relative accesses to KL's outer
   or \(J\)-boundary arcs.  It may not be filled by label equality.
5. \(j_\alpha\) retains every competing tile/component incidence;
   \(\widetilde z_\alpha\) is present only when a based numerical deck
   phase is actually required.
6. \(H_{s,\alpha},H_{t,\alpha}\) are the localization subgroups, and
   \(\mathfrak E_\alpha\) contains the central/tile seam equalizers.

The atlas must reconstruct \(\gamma\) after gluing, with its original
order and multiplicity.  It must commute with both directions of the
bigraded grid, distinguish covering maps from inclusion immersions,
handle the declared root transition separately, and prove no-birth under
authorized final-root enlargement.

This definition does not assume that \(A(\gamma)\) is uniformly bounded
or even finite.  Finiteness or local finiteness is a theorem obligation,
not a consequence of the binder syntax.

## 5. What KL's lifting lemma actually supplies

For a KL puzzle piece \(Y\), let \(S_Y^v\) be the exterior Julia
continuum attached to a puzzle vertex \(v\), in the notation of the
Decorations source.  Let \(\partial^v\Psi(Y)\) be the corresponding
two-arc portion of the KL \(J\)-boundary.

### Lemma 5.1
(`CARRIER_ACCESS_TO_KL_MULTICURVE_BRIDGE`, conditional)

Let \(H\subset U^l\) be an actual carrier and let \(I^-,I^+\) be sides
in the complete ideal marking of \(U^l\setminus H\).  Let
\(Y\in\mathcal Y^m(l)\) be an authorized KL geometric puzzle piece with
vertices \(v^-,v^+\).  Assume a protected bridge certificate:

1. a curve \(\gamma:[0,1]\to U^l\) with
   \[
   \gamma(0)\in S_Y^{v^-},\qquad
   \gamma(1)\in S_Y^{v^+};
   \tag{5.1}
   \]
2. \(\gamma\) is a compact truncation of the declared carrier-relative
   Wave access, or is homotopic to it through the authorized complement,
   and its endpoint tails are subordinate to \(I^-,I^+\);
3. actual prime-end/crosscut collars identify \(I^\pm\) with the vertex
   accesses represented by \(S_Y^{v^\pm}\), injectively and with the
   declared cyclic order; and
4. the bridge and collars avoid every forbidden carrier and obstacle
   except at their declared endpoint impressions.

Then \(\gamma\) contains an ordered multicurve \(\gamma'\) which lifts
to a KL horizontal multicurve

\[
 \gamma^*\subset\Psi(Y)
\]

connecting
\(\partial^{v^-}\Psi(Y)\) to
\(\partial^{v^+}\Psi(Y)\).  With the endpoint tags transported through
the certified collars, \(\gamma^*\) represents the two declared
carrier-relative sides.

#### Proof

KL's lifting lemma assumes an authorized \(Y\), two puzzle vertices, and
a curve in \(U^l\) connecting \(S_Y^{v^-}\) to \(S_Y^{v^+}\).  Item 1
supplies exactly those source hypotheses.  The lemma produces an ordered
submulticurve \(\gamma'\) and a horizontal lift \(\gamma^*\) with the
stated KL endpoints.  Items 2--4 are additional to KL's lemma; they
justify transporting the Wave-side tags and cyclic order to that lift.
No other conclusion is used. \(\square\)

The lemma proves neither equality with the whole Wave leaf nor width
preservation, exhaustion of all lifts, proper/end-proper behavior, or
final-root stability.

## 6. Terminal anchor attempt and exact first obstruction

The terminal anchor supplies:

\[
 K_1,\qquad [\kappa_1,\kappa_0]_{\mathcal T},\qquad
 I_{1\to0},\qquad
 K_1\mapsto K_2\mapsto\cdots\mapsto K_0,
\tag{6.1}
\]

and proves

\[
 \chi_{\rm ideal}=0,\qquad
 \chi_{\rm protected\ analytic}=\bot.
\tag{6.2}
\]

### Theorem 6.1
(`TERMINAL_K1_EXTERIOR_PUZZLE_VERTEX_CANDIDATE_SET`)

Let
\[
 f^P:A_0\longrightarrow B,\qquad A_0\Subset B,\qquad P>1,
\tag{6.3}
\]
be the terminal primitive first-return branch, and write
\[
 K_i=f^i(K_0).
\]
Let
\[
 Y_B=\overline B=E^{\chi-1}
\tag{6.4}
\]
be the closed target puzzle piece of the terminal modified-principal-nest
map.  Let \(C_1\) be the connected component of
\[
 K(f)\setminus B
\tag{6.5}
\]
containing \(K_1\), and define
\[
 \mathcal V_1(Y_B)
 =
 C_1\cap\operatorname{Vert}(Y_B).
\tag{6.6}
\]
Then:

1. \(\mathcal V_1(Y_B)\) is nonempty and finite.
2. For every \(v\in\mathcal V_1(Y_B)\),
   \[
   C_1=S_{Y_B}^v,
   \qquad
   K_1\subset S_{Y_B}^v.
   \tag{6.7}
   \]
3. The terminal data therefore determine a canonical finite nonempty
   candidate set of puzzle-vertex labels on the one exterior continuum
   \(C_1\) containing \(K_1\).  This theorem alone has not yet proved
   that the candidate is unique.  It does not distinguish the side
   \(I_{1\to0}\) or construct a protected collar.

#### Proof

KL's modified principal nest consists of critical puzzle pieces
\(E^j\), and its terminal primitive map is
\[
 E^\chi\longrightarrow E^{\chi-1}.
\]
In the project's open-domain notation,
\[
 A_0=\operatorname{int}E^\chi,\qquad
 B=\operatorname{int}E^{\chi-1},
\]
so (6.4) is an authorized closed geometric puzzle piece.  The marked
puzzle construction gives a finite vertex set and
\[
 K(f)\cap\partial Y_B=\operatorname{Vert}(Y_B).
\tag{6.8}
\]

The already proved critical-base cycle exclusion uses the first-return
property to show
\[
 f^i(A_0)\cap B=\varnothing
 \qquad(1\le i<P).
\tag{6.9}
\]
Since \(K_1=f(K_0)\subset f(A_0)\), (6.9) gives
\[
 K_1\subset K(f)\setminus B.
\tag{6.10}
\]
The set \(K_1\) is connected as the continuous image of the connected
filled Julia continuum \(K_0\).  It therefore lies in a unique component
\(C_1\) of the compact set (6.5).

The ambient filled Julia set \(K(f)\) is a continuum in the connected
KL pseudo-puzzle setting.  The closed subset
\[
 K(f)\setminus B
\]
is nonempty by (6.10) and is proper because
\[
 K_0\subset A_0\subset B.
\]
We use the following elementary boundary-bumping fact: every component
of a nonempty proper closed subset \(A\) of a compact connected Hausdorff
space \(X\) meets \(\partial_XA\).  Indeed, if a component \(C\) missed
the boundary, then \(C\subset\operatorname{int}_X A\).  Components and
quasi-components agree in compact Hausdorff spaces.  Clopen separation
of \(C\) from each point of the compact set \(\partial_XA\), followed by
a finite intersection, gives a nonempty set \(D\) clopen in \(A\) with
\[
 C\subset D\subset\operatorname{int}_X A.
\]
Because \(A\) is closed in \(X\), \(D\) is closed in \(X\); because it is
open in \(A\) and contained in \(\operatorname{int}_X A\), it is open in
\(X\).  It is proper since \(A\ne X\), contradicting connectedness of
\(X\).

Applying this fact to \(A=K(f)\setminus B\) shows
\[
 C_1\cap\partial_{K(f)}(K(f)\setminus B)\ne\varnothing.
\tag{6.11}
\]
Because \(B=\operatorname{int}Y_B\),
\[
 \partial_{K(f)}(K(f)\setminus B)
 \subset K(f)\cap\partial Y_B
 =\operatorname{Vert}(Y_B).
\tag{6.12}
\]
For completeness, the inclusion follows directly from the definition
of relative boundary.  A point of \(K(f)\) not on \(\partial B\) lies
either in the relatively open set \(K(f)\cap B\), or in the relatively
open set \(K(f)\cap(\mathbb C\setminus\overline B)\).  It therefore
cannot belong to
\(\partial_{K(f)}(K(f)\setminus B)\).
Equations (6.11)--(6.12) prove that
\(\mathcal V_1(Y_B)\ne\varnothing\); it is finite by finiteness of the
puzzle-vertex set.

For \(v\in\mathcal V_1(Y_B)\), KL define \(S_{Y_B}^v\) to be the
component of \(K(f)\setminus\operatorname{int}Y_B\) containing \(v\).
That closed set is (6.5), and \(v\in C_1\).  Consequently
\[
 S_{Y_B}^v=C_1.
\]
Together with \(K_1\subset C_1\), this proves (6.7).
\(\square\)

The source locks used in this proof are KL Decorations `kingdom.tex`
45--62 and 198--225, the connected-pseudo-puzzle hypothesis in
`psiql.tex` 76--83, and the project theorem
`CRITICAL_BASE_CYCLE_EXCLUSION`.

The KL source attaches
\(\partial^v\Psi(Y_B)=\eta_i\cup\xi_{i+1}\) to each candidate puzzle
vertex \(v\).  Theorem 6.1 supplies set-level component incidence, but
does not say which candidates represent the particular side
\(I_{1\to0}\).  It also supplies no crosscut/collar transport.
Therefore Lemma 5.1 still cannot be invoked at that side.

### Corollary 6.2 -- canonical finite set-level anchor relation

The assignment
\[
 \Theta^{\rm set}_{1\to0}:
 I_{1\to0}\longmapsto\mathcal V_1(Y_B)
\tag{6.13}
\]
is a canonical, finite, nonempty relation in the fixed marked puzzle.
It retains every competing puzzle-vertex attachment label on the common
exterior continuum \(C_1\) containing \(K_1\), and is
presentation-invariant.

#### Proof

The side \(I_{1\to0}\) is canonically determined by the terminal Hubbard
anchor.  The puzzle piece \(Y_B\), component \(C_1\), finite vertex set,
and intersection (6.6) are determined by the actual terminal
first-return branch and marked puzzle.  Theorem 6.1 proves that the
fiber is finite and nonempty. \(\square\)

Corollary 6.2 does not permit an arbitrary choice of vertex.  Each
candidate may be discarded only by a proved access-separation or
collision certificate.

### Corollary 6.3: path-refined finite candidate relation

Let
\[
 H_{10}
 =
 H_{\mathcal T}(\{\kappa_1,\kappa_0\})
 =
 q_{\mathcal T}^{-1}([\kappa_1,\kappa_0]_{\mathcal G})
\tag{6.14}
\]
be the geometric realization of the unique terminal Hubbard-tree path.
Let \(D_{10}\) be the component of \(H_{10}\setminus B\) containing
\(K_1\), and put
\[
 \mathcal V^{\rm path}_{1\to0}
 =
 D_{10}\cap\operatorname{Vert}(Y_B).
\tag{6.15}
\]
Then
\[
 \varnothing\ne
 \mathcal V^{\rm path}_{1\to0}
 \subseteq
 \mathcal V_1(Y_B),
\tag{6.16}
\]
and every \(v\) in this path-refined candidate set lies on the initial
outside-\(B\) component of the actual \(K_1\)-to-\(K_0\) carrier path and
satisfies
\[
 K_1\subset S_{Y_B}^v.
\tag{6.17}
\]

#### Proof

The terminal-anchor theorem makes \(H_{10}\) compact and connected and
places \(K_1,K_0\) in it.  Critical-base cycle exclusion gives
\[
 K_1\subset H_{10}\setminus B,
\qquad
 K_0\subset A_0\subset B.
\]
Thus \(H_{10}\setminus B\) is a nonempty proper closed subset of the
continuum \(H_{10}\).  Boundary bumping inside \(H_{10}\) shows that the
connected set \(K_1\subset H_{10}\setminus B\) lies in a unique
component \(D_{10}\).  Boundary bumping shows that this component meets
\[
 \partial_{H_{10}}(H_{10}\setminus B)
 \subset H_{10}\cap\partial B.
\]
Since \(H_{10}\subset\mathcal T\subset K(f)\), equation (6.8) puts every
such intersection point in the finite set
\(\operatorname{Vert}(Y_B)\).  Hence
\(\mathcal V^{\rm path}_{1\to0}\) is nonempty and finite.

For \(v\in\mathcal V^{\rm path}_{1\to0}\), the connected set \(D_{10}\)
lies in \(K(f)\setminus B\) and contains both \(K_1\) and \(v\).
Therefore \(v\) belongs to the ambient component \(C_1\), so
\[
 v\in\mathcal V_1(Y_B),
 \qquad
 S_{Y_B}^v=C_1.
\]
This proves (6.16)--(6.17). \(\square\)

### Lemma 6.4: puzzle-vertex exterior-component injectivity
(`PUZZLE_VERTEX_EXTERIOR_COMPONENT_INJECTIVITY`)

Let \(Y\) be a closed geometric Yoccoz puzzle piece in the
source-locked KL decoration puzzle.  Then, for every
\(v\in\operatorname{Vert}(Y)\),
\[
 S_Y^v\cap\operatorname{Vert}(Y)=\{v\}.
\tag{6.18}
\]
Consequently the map
\[
 \operatorname{Vert}(Y)\longrightarrow
 \pi_0\!\left(K(f)\setminus\operatorname{int}Y\right),
 \qquad
 v\longmapsto S_Y^v
\tag{6.19}
\]
is injective.

#### Proof

Let \(R_v^-\) and \(R_v^+\) be the two distinct KL ray segments forming
the two ray sides of \(Y\) at \(v\).  Choose the smooth outer
equipotential disk \(D\) at their common truncation level.  The union
\[
 \mathcal J_v
 =
 R_v^-\cup\{v\}\cup R_v^+
\tag{6.20}
\]
is a crosscut of \(D\): the two segments are simple, have disjoint
interiors, land together at \(v\), and have distinct endpoints on
\(\partial D\).  The crosscut theorem gives two components of
\(D\setminus\mathcal J_v\).  Let
\(\Omega_v^{\rm in}\) be the component of
\(D\setminus\mathcal J_v\) containing
\(\operatorname{int}Y\), and let \(\Omega_v^{\rm out}\) be the other
component.

Put
\[
 L_v
 =
 K(f)\cap
 \bigl(\Omega_v^{\rm out}\cup\{v\}\bigr).
\]
We first derive, rather than merely read into the phrase “chop off,”
that
\[
 S_Y^v
 =
 L_v.
\tag{6.21}
\]

The filled Julia continuum lies in \(\operatorname{int}D\).  The set
\(L_v\) is connected.  Otherwise write
\(L_v=A\sqcup B\) as a separation with \(v\in A\).  The compact set
\(B\) misses \(\mathcal J_v\), hence is compactly contained in
\(\Omega_v^{\rm out}\).  It is closed in \(K(f)\), and its positive
separation from \(\mathcal J_v\) and from \(A\) makes it relatively open
in \(K(f)\).  This disconnects the continuum \(K(f)\), a contradiction.
Thus \(L_v\) is a continuum in
\(K(f)\setminus\operatorname{int}Y\) containing \(v\), and therefore
\[
 L_v\subset S_Y^v.
\]

For the reverse inclusion, the finite Jordan boundary of \(Y\) has, in
a sufficiently small neighborhood \(N_v\) of \(v\), exactly the two
selected ray sides.  Hence
\[
 N_v\cap\Omega_v^{\rm in}\subset\operatorname{int}Y.
\tag{6.21a}
\]
If \(S_Y^v\) met \(\Omega_v^{\rm in}\), then
\[
 S_Y^v\cap\Omega_v^{\rm in}
 \quad\text{and}\quad
 S_Y^v\cap(\Omega_v^{\rm out}\cup\{v\})
\]
would be nonempty, disjoint, relatively open subsets covering
\(S_Y^v\).  Relative openness of the second set at \(v\) follows from
(6.21a), and elsewhere from openness of \(\Omega_v^{\rm out}\).
That contradicts connectedness of the component \(S_Y^v\).  Therefore
\(S_Y^v\subset L_v\), proving (6.21).

Now let \(w\in\operatorname{Vert}(Y)\) with \(w\ne v\).  Because \(Y\)
is a closed Jordan disk,
\[
 w\in\overline{\operatorname{int}Y}.
\tag{6.22}
\]
The external rays lie in
\(\mathbb C\setminus K(f)\) except at their landing point.  Hence
\[
 w\notin\mathcal J_v.
\tag{6.23}
\]
Equations (6.22)--(6.23), together with
\(\operatorname{int}Y\subset\Omega_v^{\rm in}\), imply
\[
 w\in\Omega_v^{\rm in}.
\tag{6.24}
\]
By (6.21), \(w\notin S_Y^v\).  Since \(v\in S_Y^v\), equation (6.18)
follows.

If \(S_Y^v=S_Y^w\) for two vertices, then
\(w\in S_Y^v\cap\operatorname{Vert}(Y)\), and (6.18) gives \(w=v\).
Thus (6.19) is injective. \(\square\)

No local connectivity of \(K(f)\) is used.  The proof uses only the
finite ray segments and equipotential disk that are part of the KL
puzzle and the crosscut separation theorem.  For ordinary pieces the
source lock is `kingdom.tex`, the paragraph defining vertices and
\(S_Y^v\).  For geometric unions, lines 273--301 supply the closed
Jordan union and its cyclic boundary-ray model; the crosscut argument
above proves, rather than imports, the extension of (6.21).

### Corollary 6.5: unique terminal puzzle-vertex anchor
(`TERMINAL_K1_UNIQUE_PUZZLE_VERTEX_ANCHOR`)

There is a unique vertex \(v_*\in\operatorname{Vert}(Y_B)\) such that
\[
 C_1=S_{Y_B}^{v_*}
 \quad\text{and}\quad
 K_1\subset S_{Y_B}^{v_*}.
\tag{6.25}
\]
Moreover,
\[
 \mathcal V_1(Y_B)
 =
 \mathcal V^{\rm path}_{1\to0}
 =
 \{v_*\}.
\tag{6.26}
\]

#### Proof

Theorem 6.1 proves that \(\mathcal V_1(Y_B)\) is nonempty and that
\(C_1=S_{Y_B}^v\) for every \(v\) in that set.  Lemma 6.4 makes the
vertex-to-component map injective, so \(\mathcal V_1(Y_B)\) contains at
most one vertex.  It therefore equals \(\{v_*\}\), and (6.25) follows.

Corollary 6.3 gives a nonempty inclusion
\[
 \mathcal V^{\rm path}_{1\to0}
 \subseteq
 \mathcal V_1(Y_B).
\]
Both sets must therefore equal \(\{v_*\}\). \(\square\)

### Lemma 6.6: the anchor is not a small-Julia continuum vertex

Let \(\{K_i\}_{i\in\mathbb Z/P\mathbb Z}\) be the terminal primitive
cycle.  Then
\[
 v_*\notin\bigcup_{i=0}^{P-1}K_i.
\tag{6.27}
\]
Consequently, in KKL's locally connected native Hubbard-tree category,
the quotient fiber of \(v_*\) is a singleton.

#### Proof

Every vertex of the KL puzzle is a finite preimage of the repelling
fixed point \(\alpha\).  Choose \(N\ge0\) with
\[
 f^N(v_*)=\alpha.
\]
If \(v_*\in K_i\), then forward transport of the primitive cycle gives
\[
 \alpha\in K_{i+N}.
\]
But \(f(\alpha)=\alpha\) and \(f(K_j)=K_{j+1}\).  It follows
inductively that \(\alpha\) belongs to every \(K_j\) in the cycle,
contradicting the pairwise disjointness of the \(K_j\) when \(P>1\).
This proves (6.27).

In KKL's locally connected construction, the only nonpoint continuum
vertices are the components \(K_i\) of the small-Julia cycle.  The
remaining vertices are point branch vertices or the point \(\alpha\),
and the quotient is a homeomorphism on every open edge.  Since
\(v_*\in H_{10}\subset\mathcal T\) but is in no \(K_i\), its quotient
fiber is a singleton. \(\square\)

In the non-locally-connected rational-lamination lift, KKL state that
the corresponding tree objects lift but do not identify every lifted
vertex fiber.  Thus (6.27) remains valid in the physical dynamical
plane, while singleton quotient-fiber status outside the locally
connected category remains a separate check.

The refined assignment
\[
 \Theta^{\rm path}_{1\to0}:
 I_{1\to0}\longmapsto\{v_*\}
\tag{6.28}
\]
is therefore a canonical single-valued vertex anchor tied to the very
carrier path that defines \(I_{1\to0}\).  Component incidence now selects
the KL vertex, but still does not identify either lateral carrier prime
end with one of the two arcs of
\(\partial^{v_*}\Psi(Y_B)\).

The first missing one-sided datum is the protected connector

\[
\mathfrak c_{1\to0}(v_*)
 =
(v_*,[\delta_*],C_*,\operatorname{or}_*,\operatorname{obs}_*),
\tag{6.29}
\]

where:

1. \([\delta_*]\) is the actual based KL path class and deck sheet
   obtained from the protected parallel access;
2. \(C_*\) is a fundamental crosscut/collar chain in the common ambient
   surface proving that the native side \(I_{1\to0}\) and the KL vertex
   access \(S_{Y_B}^{v_*}/\partial^{v_*}\Psi(Y_B)\) represent the same
   carrier-relative prime-end access; and
3. \(\operatorname{or}_*\) and \(\operatorname{obs}_*\) record,
   respectively, injective cyclic-order transport and complete obstacle
   avoidance/separation.

This is not a counterexample.  It is the first unfilled coordinate in
the attempted analytic construction.  After (6.29), a second
side/vertex and an actual bridge curve are still required before
Lemma 5.1 gives a horizontal multicurve.

### Lemma 6.7: the two compact half-collars
(`TERMINAL_ANCHOR_COMPACT_HALF_COLLARS`)

1. Every proper compact subinterval
   \(J\Subset I_{1\to0}\) has an embedded conformal quadrilateral
   collar in the native surface
   \(\mathbb U\setminus\mathcal T\).  The collar can avoid any finite
   family of closed obstacles whose ideal closures miss \(J\).
2. Every proper compact subarc in the relative interior of either KL
   tile arc \(\eta_i\) or \(\xi_{i+1}\) forming
   \(\partial^{v_*}\Psi(Y_B)\) has an intrinsic embedded analytic
   quadrilateral collar in that KL tile.

These are independent half-collars.  The lemma supplies no map between
them, no equality of physical accesses, and no uniform modulus.

#### Proof

For Item 1, use KKL's uniformization
\[
 \pi:\mathbb D\longrightarrow\mathbb U\setminus\mathcal T,
 \qquad
 \partial_{\rm id}
 (\mathbb U\setminus\mathcal T)
 =
 (\partial\mathbb D\setminus\Lambda)/\Delta.
\]
A compact proper \(J\Subset I_{1\to0}\) has a compact lift
\(\widetilde J\Subset\partial\mathbb D\setminus\Lambda\) on which the
boundary quotient is injective.  Proper discontinuity on the domain of
discontinuity permits a sufficiently small one-sided Jordan
quadrilateral \(Q\) based on \(\widetilde J\) whose nontrivial deck
translates are disjoint from \(Q\).  The projection of \(Q\cap\mathbb D\)
is therefore an embedded conformal quadrilateral collar of \(J\).
If finitely many closed obstacles have ideal closures disjoint from
\(J\), their lifted closures miss \(\widetilde J\); shrink \(Q\) once
more to avoid them.

Item 2 is the tile-interior collar construction proved in
`KL_TILE_INTERIOR_HOMOGENEOUS_TRACE`: a KL tile is a universal-cover
disk, and a compact subarc away from its ideal vertices admits a
coordinate-Lipschitz quadrilateral collar.  Forgetting the trace norm
from that theorem leaves exactly the analytic collar asserted here.
\(\square\)

### Definition 6.8 -- aligned full restriction record

A **terminal local alignment certificate**
\(\mathfrak a_*\) consists of:

1. one common declared localization \(\Omega_*\) carrying the actual
   terminal tree, the KL geometric piece, and the relevant maps;
2. the actual inclusion
   \[
   j_*:A_*=\Omega_*\setminus K(f)
   \hookrightarrow
   M_*=\Omega_*\setminus\mathcal T;
   \tag{6.30}
   \]
3. one actual oriented proper Wave path
   \(\gamma_*^{\mathcal T}\) selected by the frozen proof-use binder,
   together with its carrier-side/fiber endpoint data;
4. the actual KL central component, tile, paired pulled/tile
   basepoints, oriented outer-seam cut-and-stack normalization, deck
   subgroup, and central/tile seam through which a positive restriction
   would pass, together with every
   binder-authorized oriented seam occurrence or based connector; and
5. a complete closed, or locally finite closed, forbidden/obstacle set
   \(\mathscr F_*\), with its absorption/separation ledger.  Here
   "locally finite closed" means the union of a locally finite family
   of closed subsets; in particular, the union is closed.

All five fields are input to the following definition.  Merely knowing
that some alignment exists is insufficient; two alignments may not be
identified until their invariance is proved.

After the point-sector test at \(v_*\) has passed, define first the
**physical** KKL proper-restriction universe
\[
\begin{aligned}
 \mathscr D_*^{\rm pr}
 =
 \bigl\{
  \delta:\;&
  \delta\text{ is a proper path in }A_*,
  \quad
  |\delta|\subset
  j_*^{-1}(|\gamma_*^{\mathcal T}|),\\
 &\delta\text{ passes every declared KKL path/refinement filter and
   has the declared ordered endpoint subordination}
 \bigr\}\big/\text{compatible orientation-preserving reparametrization}.
\end{aligned}
\tag{6.31}
\]
No maximal-component reduction is made: distinct proper physical paths
in one connected inverse trace remain distinct.

For \([\delta]\in\mathscr D_*^{\rm pr}\), let
\(\operatorname{Auth}_{\mathfrak a_*}([\delta])\) be the set of raw
authorization tuples
\[
 \ell=(i,t,x,[\kappa],\widehat\delta,\widetilde\delta)
\tag{6.32}
\]
authorized by the frozen binder, with the following exact meaning.
Here \(x=\delta(t)\).  In the direct-seam case the tuple has
\([\kappa]=\bot\), one requires \(x\in Y_i\), and one sets
\(\widehat x=e_i(x)\).  In the connector case, \(\kappa\) is a declared
path in \(A_*\), taken up to homotopy rel endpoints, from a retained
physical seam point \(y_i\in Y_i\) to \(x\).  Starting at
\(e_i(y_i)\in\widehat A_i\), lift this connector under the KL covering
\(p_i:\widehat A_i\to A_*\), and call its endpoint \(\widehat x\).
Then \(\widehat\delta\) is the unique lift of \(\delta\) satisfying
\[
 \widehat\delta(t)=\widehat x,
 \qquad
 \widetilde\delta=\Phi_i^{-1}\circ\widehat\delta ,
\tag{6.33}
\]
where \(\Phi_i:\widetilde A\to\widehat A_i\) is the paired based
covering isomorphism.  Occurrences, parameters, and connectors are
transported under compatible oriented reparametrization.

Raw tuples are quotiented by simultaneous compatible
orientation-preserving reparametrization of \(\delta\), \(t\), and the
oriented connector.  If \(\mathscr I_{\rm tile,*}\) is the retained
set of proof-used tile indices, define the actual lift-phase space
\[
 \mathscr L_*([\delta])
 =
 \bigsqcup_{i\in\mathscr I_{\rm tile,*}}
 \left\{
  (i,[\widehat\zeta],[\widetilde\zeta])_{\rm or}:
  p_i\circ\widehat\zeta=\delta,\ 
  \Phi_i\circ\widetilde\zeta=\widehat\zeta
 \right\}.
\]
The disjoint-union tag retains the KL tile copy.  Define the evaluation
map
\[
 E_\delta:
 \operatorname{Auth}_{\mathfrak a_*}([\delta])
 \longrightarrow
 \mathscr L_*([\delta])
\]
by forgetting the occurrence/connector provenance, and put
\[
 \operatorname{Lift}_{\mathfrak a_*}([\delta])
 =
 \operatorname{im}E_\delta,
 \qquad
 \operatorname{Prov}_\delta(L)=E_\delta^{-1}(L).
\]
Thus two different authorized occurrences that produce the same lifted
path pair define one lift phase with two provenance records.

Authorization is a relation, not a choice.  A path that misses every retained
seam, reenters a seam without a binder-selected occurrence, or needs an
unrecorded connector has no authorized tuple.  Different connector
classes with different winding, or different authorized occurrences,
remain different tuples in the fixed marked record.  There is no deck
quotient: the retained seam, paired basepoints, endpoint marking,
obstacles, and deck phase force a fixed presentation.

For every physical restriction retain
\[
 \left(
 X_\delta,[\delta],
 \left\{
   \bigl(L,\operatorname{Prov}_\delta(L),
          \operatorname{tile}(L),
          \operatorname{deck}(L),\operatorname{chan}(L)\bigr):
   L\in\operatorname{Lift}_{\mathfrak a_*}([\delta])
 \right\},
 \operatorname{acc}(\delta),\tau(\delta),
 \operatorname{obs}(\delta)
 \right),
\tag{6.34}
\]
where \(X_\delta\) is the connected component of the geometric inverse
trace containing \(|\delta|\).  Distinct restrictions in one
\(X_\delta\) are not merged.  Define the physical multiplicity
\[
 \mu_*^{\rm phys}=\#\mathscr D_*^{\rm pr}.
\tag{6.35}
\]
The cardinal may be zero, finite, countably infinite, or uncountable.

### Lemma 6.9: seam-normalized path lift
(`TERMINAL_SEAM_NORMALIZED_PATH_LIFT`)

For a fixed marked alignment and
\([\delta]\in\mathscr D_*^{\rm pr}\), the binder supplies exactly one
based KL lift phase of \([\delta]\) if and only if
\[
 \#\operatorname{Lift}_{\mathfrak a_*}([\delta])=1.
\tag{6.36}
\]
If \(L\) denotes that unique phase, it has exactly one canonical
seam-authorization record if and only if, in addition,
\[
 \#\operatorname{Prov}_\delta(L)=1.
\tag{6.36a}
\]
Both statements are independent of the representative of
\([\delta]\) under compatible orientation-preserving reparametrization.
No unrecorded deck translate is another authorized lift.

#### Proof

An authorization tuple fixes either the lifted seam point directly or the
endpoint \(\widehat x\) of the uniquely lifted based connector.  The
path-lifting theorem then gives exactly one lift
\(\widehat\delta\) through \(\widehat x\), and the based covering
isomorphism gives exactly one
\(\widetilde\delta=\Phi_i^{-1}\widehat\delta\).  This is precisely the
evaluation map \(E_\delta\).  Its image is, by definition, the set of
authorized based lift phases, proving (6.36).  Its fiber over a phase is
exactly the set of authorization records producing that phase, proving
(6.36a).  No injectivity of \(E_\delta\) is assumed.

If two connector classes differ by winding number \(m\ne0\), their
lifted endpoints differ by the \(m\)-th power of the oriented deck
generator and are distinct in the fixed marked cover.  Likewise,
distinct binder-authorized occurrences remain distinct in
\(\operatorname{Auth}\), even when evaluation gives the same lift
phase.  An orientation-preserving reparametrization transports \(t\)
and the oriented germ simultaneously; the defining quotient and
uniqueness of path lifting make both \(\operatorname{Auth}\) and
\(\operatorname{Lift}\) independent of the representative.  Finally,
an arbitrary deck translate
changes the retained lifted seam point and is therefore not authorized
by the fixed record. \(\square\)

### Proposition 6.10: filtered collar-or-obstruction theorem
(`TERMINAL_ANCHOR_COLLAR_OR_RESTRICTION_OBSTRUCTION`)

Fix a complete alignment certificate \(\mathfrak a_*\).  Exactly one of
the following ordered first-failure alternatives occurs:

1. \(O_{\rm fib}\): the lifted carrier fiber at \(v_*\) is not proved
   singleton and the aligned route does not select an actual
   point-sector there;
2. \(O_0\): \(\mu_*^{\rm phys}=0\);
3. \(O_{\rm mult}\):
   \(2\le\mu_*^{\rm phys}<\infty\);
4. \(O_\infty\): \(\mu_*^{\rm phys}\) is infinite;
5. \(O_{\rm seam}\):
   \(\mathscr D_*^{\rm pr}=\{[\delta_*]\}\), but
   \[
   \#\operatorname{Lift}_{\mathfrak a_*}([\delta_*])\ne1,
   \]
   or, for its unique lift phase \(L_*\),
   \[
   \#\operatorname{Prov}_{\delta_*}(L_*)\ne1;
   \]
6. \(O_{\rm emb}\): the unique physical member \(\delta_*\) is not a
   proper locally flat embedding;
7. \(O_{\rm obs}\): \(\delta_*\) meets \(\mathscr F_*\);
8. \(O_{\rm acc}\): one of the finite endpoint prime ends of the unique
   seam-normalized lift \(\widetilde\delta_*\) (equivalently
   \(\widehat\delta_*\)) does not belong to the declared KL vertex
   access under the finite predicate (11.22) of
   `TERMINAL_KL_FINITE_ENDPOINT_FIVE_WAY_CLASSIFICATION`, or fails the
   declared endpoint-subordination label;
9. \(O_{\rm PE}\): no nested ambient prime-end neighborhood chain keeps
   both flanks of a collar of the based lift distinct, in cyclic order,
   and subordinate to the declared part of
   \(\partial^{v_*}\Psi(Y_B)\); or
10. \(P_{\rm col}\): all preceding tests pass.

In case \(P_{\rm col}\), the record
uses the tile tag \(i(L_*)\) of the unique lift phase and the endpoint
record \(\operatorname{EndRec}_{\rm KL}(i,\widehat a)\) defined by
(11.23).  Namely,
\[
 \mathbf a_{\partial,*}
 =
 \left(
  \operatorname{EndRec}_{\rm KL}
   \bigl(i(L_*),\overline{\widehat\delta_*}(0)\bigr),
  \operatorname{EndRec}_{\rm KL}
   \bigl(i(L_*),\overline{\widehat\delta_*}(1)\bigr)
 \right)
\]
is an ordered pair of actual five-way tile endpoint records (including
tile tags and finite incidence data), and
\[
 \mathfrak c_{1\to0}(v_*)
 =
 (v_*,[\delta_*],L_*,\ell_*,\mathbf a_{\partial,*},C_*,
   \operatorname{or}_*,\operatorname{obs}_*)
\tag{6.37}
\]
exists.  Here \(C_*\subset A_*\setminus\mathscr F_*\) is an embedded
Jordan strip, \(L_*\) is the unique evaluated lift phase and
\(\ell_*\) its unique provenance tuple from (6.32); the selected
lift to the actual KL tile is injective, and
the two lifted flanks extend distinctly and cyclic-order preservingly
into the declared KL vertex access.  No assertion is made for another
Wave path, the whole horizon, width, or final-root enlargement.

#### Proof

The singleton-fiber test precedes point-sector subordination.  Once it
passes, (6.31) is KKL's full physical geometric proper-restriction
universe, not merely the set of connected inverse-trace components or
parameter-compatible lifts.  Its cardinal is exactly one of \(0,1\),
finite at least two, or infinite.  In the singleton physical-path case,
Lemma 6.9 makes the seam-phase test exact: its failure records either a
missing lift phase, competing lift phases, or competing
occurrence/connector provenance for one phase; its success supplies one
and only one fixed marked lift with one reconstruction record.  The
physical path is KKL proper by (6.31), and the complete alignment
contains the outer-seam normalization.  Therefore
`TERMINAL_SEAM_LIFT_END_PROPERNESS` gives two finite point-valued
prime-end limits for the unique lift and rules out both deck-limit
corners.  No separate path-properness alternative remains; \(O_{\rm
acc}\) is the exact outer/J-side/central/incidence classifier and
tile-tagged access predicate supplied by
`TERMINAL_KL_FINITE_ENDPOINT_FIVE_WAY_CLASSIFICATION`, together with the
declared endpoint subordination.  The
remaining four predicates test embedded realization, avoidance of the fixed
closed forbidden set, finite endpoint access/subordination, and two-flank ambient
prime-end survival.  Taking the first failure makes the ten alternatives
disjoint and exhaustive.

Assume \(P_{\rm col}\).  Since \(\delta_*\) is a proper locally flat
embedding in the orientable surface \(A_*\setminus\mathscr F_*\), the
proper tubular-neighborhood theorem supplies an embedded open strip.
Choose its width on an exhaustion by compact centerline intervals and
let the widths tend to zero at both ends.  Because
\(\mathscr F_*\) is closed or locally finite closed, the widths can be
chosen so that
\[
 C_*\cap\mathscr F_*=\varnothing.
\tag{6.38}
\]

Let
\[
 p_i:\widehat A_i\longrightarrow A_*
\tag{6.39}
\]
be the aligned KL universal-cover tile and use the point
\(\widehat x_*\) from the unique provenance tuple \(\ell_*\).
Every component of \(p_i^{-1}(C_*)\) maps homeomorphically to \(C_*\),
because \(C_*\) is simply connected.  The point
\(\widehat x_*\) chooses one
component and hence an injective lift
\[
 \widetilde C_*\hookrightarrow\widehat A_i.
\tag{6.40}
\]

The intrinsic prime-end closure of this strip is a disk with four
marked sides.  The failure of \(O_{\rm PE}\) supplies a nested basis of
ambient tile prime-end neighborhoods containing the two lifted tails.
Shrink the variable collar inside that basis.  Then the inclusion of
the lifted strip into the ambient tile extends on both marked flanks,
the two flank images remain distinct, and both are subordinate to the
declared part of \(\partial^{v_*}\Psi(Y_B)\).  Holomorphic covering
charts preserve orientation, so their order is the declared cyclic
order.  These data fill (6.37). \(\square\)

### Corollary 6.11 -- exact remaining terminal coordinate

The terminal component, carrier path, and ray marking determine the
single vertex \(v_*\).  They do not construct a terminal local alignment
certificate or compute the full restriction universe (6.31).  The next
actual datum is
\[
 \mathfrak r_*
 =
  \left(
  \mathfrak a_*,
  \mu_*^{\rm phys},
  \left\{
   X_\delta,[\delta],
   \left\{
    \bigl(L,\operatorname{Prov}_\delta(L),
           \operatorname{tile}(L),
           \operatorname{deck}(L),\operatorname{chan}(L)\bigr):
    L\in\operatorname{Lift}_{\mathfrak a_*}([\delta])
   \right\},
   \operatorname{acc}(\delta),\tau(\delta),
   \operatorname{obs}(\delta)
  \right\}_{[\delta]\in\mathscr D_*^{\rm pr}}
 \right).
\tag{6.41}
\]
Finite puzzle-vertex, component, or tile count does not bound
\(\mu_*^{\rm phys}\).  One connected trace component can support an extra KKL
restriction, and one immersion can support infinitely many, as proved
by `PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO`.

In the chosen W1--W14 display order, W1 is only the target Wave
definition.  The first **named universally quantified access
coordinate** is therefore

\[
 \theta^{\rm rel}_{h,\mathrm{W2}}(I_{1\to0}),
\tag{6.42}
\]

because W2 queries every ideal interval and endpoint.  This is a display
order statement, not a claim about the unique order of the atomic SCC
graph.

## 7. Adversarial consequences

1. A component address does not select a Wave trace.
2. A chronological phase is not a universal-cover deck phase.
3. Nested cells do not imply nested finite Julia components.
4. A KL \(J\)-boundary arc is not automatically a side of an internal
   Hubbard-tree carrier.
5. A chart on a central segment does not chart the tile portions of the
   same path.
6. KL's lifting lemma gives a submulticurve, not equality, width
   preservation, or lift exhaustion.
7. The terminal native side is typed, but its protected analytic
   connector is not constructed.
8. Infinite fibers retain addresses and planar supports, but no open
   \(\Psi(E_\omega)\) is introduced.

## 8. Immediate constructive target

The next proof obligation is no longer "choose a KL boundary label."
It is:

> construct the aligned restriction record \(\mathfrak r_*\) at the
> unique vertex \(v_*\); prove that its first-failure branch is
> \(P_{\rm col}\), or record the first actual component, access,
> itinerary, tile, deck phase, and obstruction from Proposition 6.10.
> Then repeat at a second certified side and use KL's lifting lemma to
> build the first genuine carrier-relative Wave-to-KL multicurve chart.

Until that connector exists, the access selector, PE-2 through PE-5,
the virtual Wave correspondence, VAAPC-I, UPTCR, and MLC remain open.

## 9. Dense-obstacle correction and dual crest route

The subsequent theorem
`TERMINAL_FORWARD_INVARIANT_CARRIER_DENSE_OBSTACLE_NO_GO` proves that
\(P_{\rm col}\) cannot be the universal success branch for a proper
forward-invariant carrier.  In the locally connected native primitive
case, the prime-end closure of \(K\setminus\mathcal T\) meets every
inner ideal point.  Thus the aligned record \(\mathfrak r_*\) remains a
valid diagnostic and exact-naturalness target, but an obstacle-free
nondegenerate native strip may not be required by the width branch.

The valid width reroute is relation-valued.  A literal physical curve
joining two KL exterior continua contains an ordered submulticurve lifting
to the horizontal KL family, and
\[
 \mathcal W(\mathcal H_Y(v,w))
 \le
 \operatorname{Bd}_Y(v,w)^{-1}.
\]
The missing datum is therefore a binder-complete physical restriction
family, not a welded collar.

There is also an essential crest/end correction.  A Wave over
\(I_{1\to0}\) has the terminal side in its crest.  At \(v_*\), the two
KL half-access occurrences lie in adjacent tiles; they are not the two
sides of a single KL tile crossing.  The conditional skipping-over route
requires distinct physical endpoints, a fixed separating piece \(Z\),
and a componentwise skip witness for every occurrence.  Its exact open
certificate is
`TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER`.

For the native stationary branch, the corrected KKL indexing gives only
the two source-language pass-through predicates through
\(K_0^b,K_0^{b+1}\).  Filled-set graph naturality now realizes their
distinct final components, but not common-occurrence incidence or order.
It also shows that both proposed final graph restrictions have degree
two, not the degree one printed in KKL.  Before any fixed-pair
restriction is available, one must prove the weaker native
`KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION`, then the stronger
`KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT` and
`KKL_STATIONARY_NESTED_INCIDENCE_ORDER`.  Only afterward can one seek a
uniform ordered proper restriction and realize its endpoints as
\(S_Y^v,S_Y^w\) in an authorized puzzle chart.

Exact endpoint/prime-end naturality and the width-only binder remain
separate.  Both are open, as are the virtual Wave correspondence, VAAPC-I,
UPTCR, and MLC.
