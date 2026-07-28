# Terminal Hubbard-tree anchor and the recursive vertex-package gate

## 1. Result of this pass

This pass separates two questions that were previously bundled together:

1. whether the complete terminal primitive little-Julia cycle has an actual
   connected dynamical carrier; and
2. whether an intermediate virtual-Molecule scale canonically selects the
   subset of that carrier that it is supposed to use.

The first question has a source-licensed answer in the native KKL category.
The second does not.

The pass proves the following scoped statements.

1. `KKL_NATIVE_TERMINAL_HUBBARD_TREE` is imported in its exact native scope.
   A periodically repelling, primitively renormalizable
   \(\psi\)-quadratic-like map has a compact forward-invariant Hubbard tree
   \(\mathcal T\) carrying the complete cycle \(\mathcal K\) of small filled
   Julia sets.  In the non-locally-connected case KKL pass to the locally
   connected rational-lamination model and lift the corresponding objects.
2. `NATIVE_HUBBARD_SUBTREE_FUNCTORIALITY` is proved.  Every finite marked
   vertex package \(S\) in the finite combinatorial Hubbard tree has a unique
   convex subtree \([S]_{\mathcal T}\).  Tree maps always satisfy
   \[
     [\Phi(S)]_{\mathcal T}
     \subset
     \Phi([S]_{\mathcal T}),
   \]
   with equality whenever \(\Phi\) is injective on the selected subtree.
   Enlarging \(S\) adds a forest, every component of which has exactly one
   gate on the old subtree.
3. `TERMINAL_CYCLE_HUBBARD_ANCHOR` is proved under the KKL native
   hypotheses.  For the terminal primitive cycle
   \(\{K_0,\ldots,K_{P-1}\}\), the native carrier is the Hubbard tree itself.
   The unique tree path from \(K_1\) to \(K_0\) supplies a canonical
   **ideal** attachment side and removes the earlier combinatorial
   indeterminacy of the connector.

These statements do **not** prove that an arbitrary Dudko virtual scale has
selected the correct vertices.  The first missing recursive datum is now
isolated as

\[
  \mu_{\rm vert}:
  (B,s,\text{copy-chain data})
  \longmapsto
  \mathscr S_s,
\tag{1.1}
\]

where \(\mathscr S_s\) was provisionally intended to be a finite typed
package of native tree vertices, partial critical-orbit entries, protected
sides, and obstacle records used at virtual scale \(s\).  The follow-up
audit `virtual_cantor_package_interface.md` corrects the construction
order: first realize the full Cantor component family, then extract a finite
proof-use trace or a future-faithful quotient, and only then compare that
trace with the terminal tree.  The compatibility gate remains the open
`VIRTUAL_VERTEX_PACKAGE_SELECTOR`.

The KKL ideal side is not automatically a protected planar prime-end chain
for a Dudko carrier.  Fullness, authorized localization, relative-cover
compatibility, proof-use completeness, and uniform side bounds remain
separate.  Consequently
`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`, VAAPC-I, UPTCR, and MLC remain open.

## 2. Source lock and scope

### 2.1 KKL native Hubbard tree

The checked source is

```text
source-lock/KKL26-v1/
  waves-with-Misha.tex
SHA-256:
AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The relevant source locations are:

- lines 476--490: native prime primitive \(\psi\)-ql renormalization and the
  full cycle \(\mathcal K\) of small filled Julia sets;
- lines 512--570: the Hubbard tree, its vertex/edge tree, forward dynamics,
  and the rational-lamination construction in the
  non-locally-connected case;
- lines 602--650: ideal markings and Hubbard arc diagrams carried by the
  actual tree;
- lines 1254--1274: the exact pullback action on ideal intervals in KKL's
  native category.

The imported scope is exactly a periodically repelling, primitively
renormalizable \(\psi\)-ql map already carrying its KKL native
renormalization.  No theorem about an intermediate Dudko virtual package is
imported.

### 2.2 Dudko's virtual-scale proposal

The checked source is

```text
source-lock/Dudko25/main.tex
SHA-256:
FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454
```

Lines 875--892 define the chain of satellite copies and propose partially
invariant virtual Julia sets as connected hulls of the corresponding Cantor
small Julia sets containing the critical orbit through an appropriate
number of first returns.  The paragraph does not define:

- which terminal native tree vertices represent the Cantor package at a
  virtual scale;
- the integer number of retained first returns;
- the protected side set;
- the obstacle assignment;
- the localization; or
- the enlargement map between two such packages.

It is therefore motivation for (1.1), not a proof of it.

### 2.3 Direct-decoration source

The checked direct-decoration source is

```text
source-lock/KL08/
  kingdom.tex
SHA-256:
5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
```

It supplies the first escape route and terminal primitive cycle already
used in `virtual_scale_to_puzzle_selector.md`.  It does not identify the
recursive package \(\mathscr S_s\) in (1.1).

### 2.4 Fresh-source check

On 2026-07-24, searches for the announced Dudko--Kahn--Lyubich virtual
renormalization work found no public arXiv proof supplying (1.1).  KKL's
checked source still describes virtual renormalization as future work, and
Dudko's checked source still labels the construction an interpolation
problem.  An absence-of-source check is not a mathematical impossibility
theorem; it only forbids importing the missing result.

## 3. Native tree data

Let

\[
  F=(f,\iota):(\mathbb U',\mathbb K')
  \rightrightarrows
  (\mathbb U,\mathbb K)
\tag{3.1}
\]

be a periodically repelling, primitively renormalizable native KKL
\(\psi\)-ql map.  Let \(P>1\) be its prime primitive period, let \(K_0\)
be its uniquely determined small filled Julia set, and put

\[
  K_i=F^i(K_0),\qquad
  \mathcal K=\bigcup_{i=0}^{P-1}K_i.
\tag{3.2}
\]

The \(K_i\) are pairwise disjoint by primitivity.

KKL define the Hubbard tree \(\mathcal T\) to be the smallest connected
subset of the filled carrier containing \(\mathcal K\), initially in the
locally connected case.  It is compact and forward invariant.  They enlarge
the vertex set by the branch points and the distinguished fixed point and
declare the complementary path components to be edges.  These vertices and
edges form the finite combinatorial Hubbard tree

\[
  G_{\mathcal T}=(V_{\mathcal T},E_{\mathcal T}).
\tag{3.3}
\]

The finiteness here is also forced by the source's finite-dimensional edge
space \(\mathbb R^{E(\mathcal T)}\) and its transition matrix.

If the filled carrier is not locally connected, KKL use a locally connected
rational-lamination quotient

\[
  \pi:\mathbb K\longrightarrow\mathbb K_{\rm com}
\tag{3.4}
\]

and lift the corresponding tree data.  The conclusions imported below are
only those KKL explicitly attach to these corresponding objects.  In
particular, we do not infer that an arbitrary partial virtual package has
the same lift.

For bookkeeping, let

\[
  q:\mathcal T\longrightarrow G_{\mathcal T}
\tag{3.5}
\]

collapse every continuum vertex to the corresponding abstract vertex and
map each open tree edge homeomorphically to its abstract edge.  Its fibers
are connected.  Thus \(q\) is monotone.

## 4. Convex subtrees

### Definition 4.1

For a nonempty finite set \(S\subset V_{\mathcal T}\), define its convex
tree hull by

\[
  [S]_{G}
  =
  \bigcup_{u,v\in S}[u,v]_{G},
\tag{4.1}
\]

where \([u,v]_{G}\) is the unique simple path from \(u\) to \(v\) in the
tree \(G_{\mathcal T}\).  Define its geometric realization by

\[
  H_{\mathcal T}(S)
  =
  q^{-1}([S]_{G}).
\tag{4.2}
\]

This notation does not assert that (4.2) is full or that all of its
complementary accesses are protected.

### Lemma 4.2 (least finite subtree)

The set \([S]_{G}\) is the unique least connected subgraph of
\(G_{\mathcal T}\) containing \(S\).  Every leaf of \([S]_{G}\) belongs to
\(S\).

#### Proof

Every connected subgraph containing \(S\) must contain the unique path
\([u,v]_{G}\) for each \(u,v\in S\); otherwise its two vertices would be
disconnected.  It therefore contains the union (4.1).

The union (4.1) is connected because every path in the union meets a path
starting at any fixed base vertex \(u_0\in S\).  Hence it is itself a
connected subgraph containing \(S\), proving leastness and uniqueness.

If a leaf \(x\) were not in \(S\), deleting its incident open edge and
\(x\) would leave a smaller connected subgraph containing \(S\), contrary
to leastness. \(\square\)

### Lemma 4.3 (geometric connectedness)

The realization \(H_{\mathcal T}(S)\) is compact and connected.

#### Proof

The finite subtree \([S]_{G}\) is compact.  Since \(q\) is continuous and
\(\mathcal T\) is compact, its inverse image is compact.

Suppose \(q^{-1}([S]_{G})=A\cup B\) were a separation into nonempty compact
sets.  The compact images \(q(A)\) and \(q(B)\) cover the connected set
\([S]_{G}\).  They cannot be disjoint.  If
\(y\in q(A)\cap q(B)\), then the connected fiber \(q^{-1}(y)\) meets both
\(A\) and \(B\), contradicting the separation.  Thus the inverse image is
connected. \(\square\)

### Remark 4.4 (what was and was not proved)

Lemma 4.3 supplies a source-relative connected carrier.  It does not prove:

1. that \(H_{\mathcal T}(S)\) is full;
2. that fullification preserves a specified protected access;
3. that it lies in a requested virtual localization;
4. that \(S\) is the correct virtual package; or
5. that \(|[S]_{G}|\) is universally bounded.

Each of these is a separate downstream clause.

## 5. Functoriality under a tree map

Let

\[
  \Phi:G_{\mathcal T}\longrightarrow G_{\mathcal T}
\tag{5.1}
\]

be a continuous tree map induced by a declared dynamical branch, with
vertices subdivided when necessary so that vertices map to vertices.

### Theorem 5.1 (`NATIVE_HUBBARD_SUBTREE_FUNCTORIALITY`)

For every finite nonempty \(S\subset V_{\mathcal T}\),

\[
  [\Phi(S)]_{G}
  \subset
  \Phi([S]_{G}).
\tag{5.2}
\]

If \(\Phi|_{[S]_{G}}\) is injective, then

\[
  [\Phi(S)]_{G}
  =
  \Phi([S]_{G}).
\tag{5.3}
\]

Consequently every degree-one corridor branch that is univalent on the
actual selected carrier transports its native subtree exactly.

#### Proof

The image \(\Phi([S]_{G})\) is connected and contains \(\Phi(S)\).  By the
leastness in Lemma 4.2 it contains the least connected subgraph containing
\(\Phi(S)\).  This gives (5.2).

Assume now that the restriction is injective.  It is then a homeomorphism
from the finite tree \([S]_{G}\) to its image.  The leaves of the image are
images of leaves of \([S]_{G}\), hence belong to \(\Phi(S)\) by Lemma 4.2.
A finite tree is the convex hull of its leaves: deleting an edge separates
the tree into two components, and each component contains a leaf.  Therefore
every edge of \(\Phi([S]_{G})\) lies on a path between two vertices of
\(\Phi(S)\), so

\[
  \Phi([S]_{G})\subset[\Phi(S)]_{G}.
\]

Together with (5.2), this proves (5.3). \(\square\)

### Definition 5.2 (fold excess)

The exact obstruction to equality is the finite forest

\[
  \mathfrak E_\Phi(S)
  =
  \overline{
    \Phi([S]_{G})\setminus[\Phi(S)]_{G}
  }.
\tag{5.4}
\]

Equation (5.4) is zero exactly when the desired tree-hull equality holds.
Noninjectivity may or may not create excess; it is not legitimate to infer
zero excess merely because the endpoint labels agree.

At the geometric level, (5.3) lifts only after the selected analytic branch
is proved to transport the vertex continua and edge traces represented by
the graph map.  The abstract theorem does not create that analytic branch.

## 6. Final-root enlargement

### Theorem 6.1 (one-gate enlargement forest)

Let \(S\subset S^+\subset V_{\mathcal T}\) be finite and nonempty.  Then

\[
  [S]_{G}\subset[S^+]_{G}.
\tag{6.1}
\]

Every connected component \(C\) of

\[
  [S^+]_{G}\setminus[S]_{G}
\tag{6.2}
\]

has closure meeting \([S]_{G}\) in exactly one point \(g(C)\), after
subdivision at an interior attachment point when necessary.  Every such
component contains a vertex of \(S^+\setminus[S]\).

#### Proof

Monotonicity (6.1) follows directly from (4.1).

Connectedness of \([S^+]_{G}\) shows that the closure of each component in
(6.2) meets the old subtree.  If it met the old subtree at two distinct
points \(a,b\), the path inside the closure of \(C\) from \(a\) to \(b\)
and the unique path \([a,b]_{G}\subset[S]_{G}\) would form a cycle,
contradicting that \(G_{\mathcal T}\) is a tree.  Hence the gate is unique.

If \(C\) contained no new selected vertex, deleting \(C\) from the enlarged
subtree would leave a connected subgraph containing \(S^+\), contradicting
the leastness of \([S^+]_{G}\). \(\square\)

### Corollary 6.2 (exact combinatorial attachment trace)

The tuple

\[
  \tau_{\rm tree}(C)
  =
  \bigl(
    C,g(C),[g(C),S^+\cap C]_{G}
  \bigr)
\tag{6.3}
\]

is the complete combinatorial attachment trace of an enlargement component.
Thus late root enlargement cannot merge two old tree vertices or attach one
new component at two old gates.

This conclusion is combinatorial.  A new edge may still enter a protected
prime-end collar based at its unique gate.  Therefore Theorem 6.1 proves
neither protected-access survival nor no-birth of ideal intervals.

## 7. The terminal primitive anchor

Return to the direct-decoration terminal branch

\[
  f^P:A_0\longrightarrow B,
  \qquad
  K_i=f^i(K_0).
\tag{7.1}
\]

Assume its induced native \(\psi\)-ql map satisfies the periodically
repelling KKL hypotheses of Section 3.  Let

\[
  S_{\rm cyc}
  =
  \{\kappa_0,\ldots,\kappa_{P-1}\}
  \subset V_{\mathcal T},
\tag{7.2}
\]

where \(\kappa_i\) is the vertex represented by \(K_i\).

### Proposition 7.1 (`TERMINAL_CYCLE_HUBBARD_ANCHOR`)

The native carrier of the complete terminal primitive cycle is

\[
  H_{\rm term}
  =
  H_{\mathcal T}(S_{\rm cyc})
  =
  \mathcal T.
\tag{7.3}
\]

It is compact, connected, forward invariant, and contains every \(K_i\).
The unique path

\[
  [\kappa_1,\kappa_0]_{G}
\tag{7.4}
\]

has a unique first edge incident to \(\kappa_1\).  The side of \(K_1\)
containing that edge is a canonical member

\[
  I_{1\to0}
\tag{7.5}
\]

of KKL's native ideal marking.  Its component itinerary is

\[
  K_1\longmapsto K_2\longmapsto\cdots
  \longmapsto K_{P-1}\longmapsto K_0,
\tag{7.6}
\]

and the complete cycle degree word, beginning at \(K_0\), is

\[
  (2,1,\ldots,1).
\tag{7.7}
\]

#### Proof

KKL define \(\mathcal T\) as the smallest connected carrier containing the
complete cycle.  Lemma 4.2 gives the same leastness for the convex hull of
the corresponding vertices, proving (7.3).  Compactness, connectedness, and
forward invariance are native KKL properties.

The abstract Hubbard graph is a tree, so (7.4) is unique and has one first
edge at \(\kappa_1\).  KKL's minimal ideal marking records the sides of the
small-Julia vertices in the actual Hubbard tree.  Hence the side containing
that first edge is the unique ideal side (7.5).

Equation (7.6) follows from the definitions \(K_i=f^i(K_0)\).  The unique
critical point lies in \(K_0\); primitivity places it in no other \(K_i\).
This is exactly the degree calculation already proved in
`CRITICAL_BASE_CYCLE_EXCLUSION`, giving (7.7). \(\square\)

### Corollary 7.2 (refined first-attachment record)

The earlier record

\[
  \chi_{\rm access}
  =
  \bot_{\rm missing\ analytic\ connector}
\]

can now be refined, in the KKL native terminal category, to

\[
  \chi_{\rm ideal}=0,
  \qquad
  I_{1\to0}\text{ given by (7.5)},
  \qquad
  \chi_{\rm protected\ analytic}=\bot.
\tag{7.8}
\]

The remaining bottom symbol is essential.  An ideal side of the native full
Hubbard tree is not automatically a protected crosscut chain for a partial
Dudko carrier, and no relative-cover or localization statement follows from
(7.5).

## 8. Attempted \(s=2\) lift

Let

\[
  \mathcal M^{(0)}
  \supsetneq
  \mathcal M^{(1)}
  \supsetneq
  \mathcal M^{(2)}
\tag{8.1}
\]

be the first two levels of the canonical satellite-copy chain surrounding
the terminal primitive copy \(\mathcal M_1\).

After an actual virtual Cantor component family and a frozen finite
proof-use trace have been constructed, the native tree comparison would
use a finite typed selection

\[
  \mathscr S_s
  =
  \bigl(
    S_s,\mathscr O_s,\mathscr I_s,
    \mathscr W_s,\mathscr D_s
  \bigr),
\tag{8.2}
\]

where:

- \(S_s\) is the set of native tree vertices and partial-orbit points to be
  retained;
- \(\mathscr O_s\) gives their exact orbit words and stopping indices;
- \(\mathscr I_s\) is the protected ideal/prime-end side set;
- \(\mathscr W_s\) is the obstacle and localization ledger; and
- \(\mathscr D_s\) is the frozen proof-use demand set.

Once (8.2) is supplied, the **topological** candidate is forced:

\[
  H_s^{\rm tree}
  =
  H_{\mathcal T}(S_s).
\tag{8.3}
\]

Theorems 5.1 and 6.1 then give its exact tree-level transport and
enlargement laws.

The checked sources do not supply (8.2) for \(s=2\).  The copy chain (8.1)
is parameter combinatorics.  It does not state which components of the
terminal native tree are the “corresponding Cantor small Julia sets,” nor
the number of critical returns retained at that scale.  The
direct-decoration escape route determines the first visible escape event,
but does not define the recursive vertex package through the disconnected
intermediate satellite object.

**Follow-up type correction.**  The paragraph above is not a license to
identify the full Cantor package with finitely many terminal vertices.
`virtual_cantor_package_interface.md` proves that an infinite component
family cannot be exactly enumerated by a finite vertex set, and that a
finite quotient is valid only after joint observable constancy is proved on
every quotient fiber.  The checked sources do not first construct the
Cantor address space, embedded components, or analytic branch action.
Consequently (8.2) can only be a later finite proof-use trace, not an
unproved finite enumeration of the full virtual family.

### Proposition 8.1 (ambient-tree underdetermination)

An ambient native Hubbard tree, a distinguished critical vertex, and a
virtual-scale label do not determine a virtual subtree.

#### Proof

Consider the path tree

\[
  \kappa_0-\kappa_1-\kappa_2.
\tag{8.4}
\]

The same ambient tree and root \(\kappa_0\) admit the two distinct packages

\[
  S=\{\kappa_0,\kappa_1\},
  \qquad
  S^+=\{\kappa_0,\kappa_1,\kappa_2\}.
\tag{8.5}
\]

Their forced hulls are respectively the first edge and the full two-edge
path.  Their attachment, ideal-side, and future branch inventories differ.
Thus the ambient tree and root do not choose the package.  A dynamical
definition of which vertex represents the next Cantor component, together
with its stopping rule, is indispensable. \(\square\)

Proposition 8.1 is an underdetermination theorem for the presently declared
input fields.  It is not a counterexample to the existence of a richer
dynamical rule.

## 9. Exact new open interface

### Open Problem 9.1 (`VIRTUAL_VERTEX_PACKAGE_SELECTOR`, refined)

For every actual virtual-Molecule block \(B\) and every intermediate scale
\(s\), first solve `VIRTUAL_CANTOR_PACKAGE_REALIZATION`; after the complete
proof-use horizon is frozen, solve
`VIRTUAL_PROOF_USE_TRACE_SELECTOR` and construct (8.2) as a finite trace or
future-faithful quotient.  Before any width bound, compactness theorem, or
rigidity conclusion is used, prove:

1. **Actual components.** Every selected record is an actual component or
   orbit point in the native terminal dynamical plane, with its exact return
   word and sheet.
2. **Cantor correspondence.** The full component family is realized
   independently; the finite trace is exactly the proof-used subfamily or a
   quotient whose fibers are jointly indistinguishable by every claimed
   observable.
3. **Stopping rule.** The retained critical-orbit length is an explicit
   least-event integer.
4. **Demand completeness.** Every Wave, Wanderers, covering,
   quasi-additivity, and width use is present in \(\mathscr D_s\).
5. **Protected sides.** Every proof-used side has an actual prime-end
   representative and survives the connector and all demanded branches.
6. **Obstacle completeness.** Every ambient or filled component is absorbed
   or separated in \(\mathscr W_s\).
7. **Dynamical functoriality.** On a degree-one corridor, the analytic branch
   realizes equality (5.3), not merely label transport.
8. **Enlargement naturality.** Every component of the forest in Theorem 6.1
   has its unique gate, full itinerary, and protected-collar audit.
9. **Presentation invariance.** Equivalent copy-chain descriptions produce
   isomorphic typed packages.
10. **Uniformity.** The package admits either a period-independent
    proof-complete bound or a proved future-faithful compression.

A failed construction must record

\[
  \mathfrak F_{\rm vert}
  =
  \bigl(
    B,s,\mathcal M^{(s)},\mathcal T,
    X,\tau(X),\operatorname{sheet}(X),
    g(X),I(X),\chi(X),\mathcal L
  \bigr),
\tag{9.1}
\]

where \(X\) is the first component whose scale assignment, gate, protected
side, or localization cannot be certified.

## 10. Dependency consequence

The corrected source-facing order is

\[
\begin{aligned}
 &\texttt{KKL\_NATIVE\_TERMINAL\_HUBBARD\_TREE}\\
 &\qquad\downarrow\\
 &\texttt{NATIVE\_HUBBARD\_SUBTREE\_FUNCTORIALITY}
 \quad+\quad
 \texttt{TERMINAL\_CYCLE\_HUBBARD\_ANCHOR}\\
 &\qquad\downarrow\\
 &\texttt{VIRTUAL\_CANTOR\_PACKAGE\_REALIZATION}\\
 &\qquad\downarrow\\
 &\texttt{VIRTUAL\_PROOF\_USE\_TRACE\_SELECTOR}\\
 &\qquad\downarrow\\
 &\texttt{VIRTUAL\_VERTEX\_PACKAGE\_SELECTOR}\\
 &\qquad\downarrow\\
 &\texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}\\
 &\qquad\downarrow\\
 &\texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}.
\end{aligned}
\tag{10.1}
\]

The terminal anchor removes one connector ambiguity.  It does not promote
the virtual selector because the universal scale-to-package arrow remains
open.

## 11. Adversarial audit

1. **Native terminal tree called a virtual theorem.** Rejected.  The import
   is confined to KKL's native prime primitive category.
2. **Non-local connectivity ignored.** Rejected.  The construction uses
   KKL's rational-lamination model and corresponding lift; no Euclidean
   boundary extension is asserted.
3. **Connected called full.** Rejected.  Lemma 4.3 proves compactness and
   connectedness only.
4. **Tree labels called analytic branches.** Rejected.  Theorem 5.1 requires
   a separately declared analytic realization before it can be used on
   carriers.
5. **Endpoint agreement used to prove hull equality.** Rejected.  Equality
   is proved from injectivity on the entire selected subtree.
6. **Noninjective map silently simplified.** Rejected.  The fold excess
   (5.4) is retained.
7. **Late enlargement said to have no attachments.** Rejected.  Theorem 6.1
   records the added forest and its gates.
8. **One-gate attachment said to preserve every access.** Rejected.  The new
   branch may enter a protected collar at its gate.
9. **Ideal side called a protected prime end.** Rejected by (7.8).
10. **Full terminal cycle placed in one critical base.** Rejected by
    `CRITICAL_BASE_CYCLE_EXCLUSION`; the analytic multi-base chain remains
    necessary.
11. **Parameter-copy nesting called a dynamical vertex selection.**
    Rejected by Proposition 8.1.
12. **The phrase “appropriate number” treated as an integer.** Rejected.
    The stopping integer is a field of Open Problem 9.1.
13. **The first escape atlas recursively straightened.** Rejected.  The
    disconnected intermediate object still blocks that operation.
14. **Finite tree called uniformly bounded.** Rejected.  Neither the number
    of selected vertices nor the ideal marking has a universal bound here.
15. **A missing public source called a counterexample.** Rejected.  The
    source audit prevents import but does not prove nonexistence.

## 12. Promotion decision

Promote:

```text
KKL_NATIVE_TERMINAL_HUBBARD_TREE          imported
NATIVE_HUBBARD_SUBTREE_FUNCTORIALITY      proved
TERMINAL_CYCLE_HUBBARD_ANCHOR             proved
```

Add and keep open:

```text
VIRTUAL_CANTOR_PACKAGE_REALIZATION        open
VIRTUAL_PROOF_USE_TRACE_SELECTOR          open
VIRTUAL_VERTEX_PACKAGE_SELECTOR           open
```

Keep open:

```text
VIRTUAL_SCALE_TO_PUZZLE_SELECTOR          open
VIRTUAL_RETURN_BASE_ATLAS                 open
VIRTUAL_WAVE_DEMAND_SCHEMA                open
VIRTUAL_WAVE_MARKED_CORRESPONDENCE        open
VIRTUAL_WAVE_HORIZON_CERTIFICATE          open
VAAPC-I                                   open
UNIVERSAL_PROTECTED_TOWER_CLOSURE         open
MLC                                       open
```

The follow-up type audit makes the immediate task more exact: first
construct the scale-\(2\) address-to-component map and analytic branch
action required by `VIRTUAL_CANTOR_PACKAGE_REALIZATION`.  Only after that
may (8.2) be constructed as a finite proof-use trace or future-faithful
quotient.  The ambient terminal connector no longer needs to be guessed.
