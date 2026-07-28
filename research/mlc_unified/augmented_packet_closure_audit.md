# Augmented-packet closure and port audit

## 1. Purpose and exact status

This pass resolves the source-independent part of
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE` (`VAAPC`).  Once a finite typed
assignment of actual geometric pieces has been fixed, there is no remaining
choice in the fullification procedure:

1. the final filled packet is independent of the order in which assigned
   pieces are processed;
2. every post-fullification merger and localization escape has an actual
   seed-or-bounded-chamber witness;
3. such a merger or escape persists under every monotone enlargement that
   keeps the same packet labels;
4. individual unprotected access to the original atom is enough to choose
   all port arcs pairwise disjoint; and
5. the closure, its collision witnesses, and its ports are natural under a
   sphere-extending univalent change of localization.

The result removes two apparent choices from `VAAPC`: completion order and
global port-arc untangling.  It does **not** construct the finite typed
assignment for an actual virtual-Molecule block, prove that its completed
packets are disjoint, or find an unprotected exposed point on every original
root-shadow atom.

Verdict:

- `AUGMENTED_PACKET_CLOSURE_AUDIT`: **proved**;
- `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`: **open**;
- `VIRTUAL_COMMON_FREE_COMPONENT`: **open**;
- UPTCR-1 and MLC: **open**.

## 2. Source lock and proof boundary

The checked source files are:

| source | locked file | SHA-256 |
|---|---|---|
| Dudko 2025 | `source-lock/Dudko25/main.tex` | `FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454` |
| Kahn--Kapiamba--Lyubich 2026 | `source-lock/KKL26-v1/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |

Dudko's Section 4.5 proposes partially invariant virtual Julia sets as
connected hulls of Cantor small Julia sets carrying a finite part of the
critical orbit:

<https://arxiv.org/html/2512.24171#S4.SS5>.

It does not specify the assigned collar pieces, separated obstacles,
fullification chambers, or surviving unprotected accesses needed below.

KKL construct a stronger native Hubbard tree from the complete primitive
small-Julia cycle, using the rational-lamination model when the filled Julia
set is not locally connected:

<https://arxiv.org/html/2606.27272#S2.SS5>.

This is a positive control for the native KKL category, not a construction
of the missing partial virtual packets.  KKL's bibliography still lists the
Dudko--Kahn--Lyubich virtual-renormalization manuscript as in preparation:

<https://arxiv.org/html/2606.27272#bib.bib22>.

An exact-title and author search on 2026-07-24 found no public arXiv version.
Accordingly, every theorem below is proved directly from elementary plane
topology.  No unpublished virtual-renormalization assertion is imported.

## 3. Algebra of the filled hull

For a compact set \(K\subset\mathbb C\), let \(V_\infty(K)\) be the
unbounded component of \(\mathbb C\setminus K\), and define

\[
  \operatorname{Fill}(K)
  :=
  \mathbb C\setminus V_\infty(K).
\tag{3.1}
\]

This agrees with \(K\) together with all bounded complementary components.
It is defined here for an arbitrary compact set; connectedness is imposed
later when one completed packet is required to be a continuum.

### Lemma 3.1 (closure-operator laws)

For compact plane sets \(K,L\):

\[
\begin{aligned}
  &K\subset\operatorname{Fill}(K), &&\text{extensivity},\\
  &K\subset L
    \Longrightarrow
    \operatorname{Fill}(K)\subset\operatorname{Fill}(L),
    &&\text{monotonicity},\\
  &\operatorname{Fill}(\operatorname{Fill}(K))
    =\operatorname{Fill}(K),
    &&\text{idempotence},\\
  &\operatorname{Fill}\bigl(\operatorname{Fill}(K)\cup L\bigr)
    =\operatorname{Fill}(K\cup L).
    &&\text{absorption}
\end{aligned}
\tag{3.2}
\]

Moreover, \(\operatorname{Fill}(K)\) is compact.  If \(K\) is connected,
then \(\operatorname{Fill}(K)\) is a full continuum.

#### Proof

Extensivity follows from
\(V_\infty(K)\subset\mathbb C\setminus K\).

Suppose \(K\subset L\).  Then
\(\mathbb C\setminus L\subset\mathbb C\setminus K\).  The unbounded
component \(V_\infty(L)\) is an unbounded connected subset of
\(\mathbb C\setminus K\), hence lies in \(V_\infty(K)\).  Taking complements
gives monotonicity.

Choose \(R\) with \(K\subset\overline{D(0,R)}\).  The exterior of that disk
is contained in \(V_\infty(K)\), so \(\operatorname{Fill}(K)\) is bounded.
Components of the plane domain \(\mathbb C\setminus K\) are open; therefore
\(V_\infty(K)\) is open and its complement is closed.  Thus
\(\operatorname{Fill}(K)\) is compact.

The complement of \(\operatorname{Fill}(K)\) is exactly the connected
unbounded domain \(V_\infty(K)\).  Filling a second time adds nothing, which
proves idempotence.  When \(K\) is connected, adding complementary
components preserves connectedness, so the result is a full continuum.

For absorption, monotonicity applied to
\(K\cup L\subset\operatorname{Fill}(K)\cup L\) gives

\[
  \operatorname{Fill}(K\cup L)
  \subset
  \operatorname{Fill}\bigl(\operatorname{Fill}(K)\cup L\bigr).
\tag{3.3}
\]

Conversely, monotonicity gives
\(\operatorname{Fill}(K)\subset\operatorname{Fill}(K\cup L)\), and of
course \(L\subset\operatorname{Fill}(K\cup L)\).  The right side is already
full by idempotence, so

\[
  \operatorname{Fill}\bigl(\operatorname{Fill}(K)\cup L\bigr)
  \subset
  \operatorname{Fill}(K\cup L).
\tag{3.4}
\]

Equations (3.3)--(3.4) prove absorption.
\(\square\)

### Corollary 3.2 (finite processing-order independence)

Let \(Y_0,\ldots,Y_m\) be compact sets and let \(\pi\) be any permutation of
\(\{0,\ldots,m\}\).  Define

\[
\begin{aligned}
  C^\pi_0&=\operatorname{Fill}(Y_{\pi(0)}),\\
  C^\pi_r&=
    \operatorname{Fill}\bigl(C^\pi_{r-1}\cup Y_{\pi(r)}\bigr),
    \qquad 1\le r\le m.
\end{aligned}
\tag{3.5}
\]

Then

\[
  C^\pi_m
  =
  \operatorname{Fill}\left(\bigcup_{r=0}^mY_r\right),
\tag{3.6}
\]

independently of \(\pi\).

#### Proof

Repeatedly apply the absorption identity in Lemma 3.1.  The last expression
depends only on the union of the pieces, not on their enumeration.
\(\square\)

This order-independence is deliberately limited to a **fixed assignment**.
Moving a piece from one packet label to another changes the unions in
(3.6), and no invariance under that operation is asserted.

## 4. The fixed-assignment packet closure

Fix a Jordan disk \(U\).  Let

\[
  \Lambda=\Lambda_{\rm at}\sqcup\Lambda_{\rm obs}
\tag{4.1}
\]

be a finite set of atom and obstacle labels.  For \(i\in\Lambda_{\rm at}\),
let \(A_i\Subset U\) be the original full root-shadow atom.  A fixed typed
assignment gives finitely many compact geometric pieces
\(Y_{\ell,r}\) to each label \(\ell\in\Lambda\).  Put

\[
\begin{aligned}
  S_i
    &=A_i\cup\bigcup_rY_{i,r},
    &&i\in\Lambda_{\rm at},\\
  S_\ell
    &=\bigcup_rY_{\ell,r},
    &&\ell\in\Lambda_{\rm obs},\\
  K_\ell
    &=\operatorname{Fill}(S_\ell),
    &&\ell\in\Lambda.
\end{aligned}
\tag{4.2}
\]

The \(S_\ell\) are the **raw seeds** and the \(K_\ell\) are their unique
**completed packets**.

For \(x\in K_\ell\), define its chamber descriptor by

\[
  \operatorname{ch}_\ell(x)
  =
  \begin{cases}
    \mathtt{seed},&x\in S_\ell,\\
    W,&x\in K_\ell\setminus S_\ell,
  \end{cases}
\tag{4.3}
\]

where in the second case \(W\) is the unique bounded component of
\(\mathbb C\setminus S_\ell\) containing \(x\).  Thus a filled collision is
never recorded only as a Boolean flag: it retains the actual seed or
bounded complementary chamber on both sides.

### Definition 4.1 (geometric closure collision)

The fixed assignment has:

1. a **coverage collision** if a frozen forbidden piece is not contained in
   any completed packet;
2. a **connectivity collision** if some \(S_\ell\) is not connected;
3. a **packet collision** if
   \(K_\ell\cap K_{\ell'}\ne\varnothing\) for distinct labels;
4. a **localization collision** if
   \(K_\ell\cap(\mathbb C\setminus U)\ne\varnothing\).

A packet-collision witness is

\[
  (\ell,\ell',x,
    \operatorname{ch}_\ell(x),
    \operatorname{ch}_{\ell'}(x)),
  \qquad
  x\in K_\ell\cap K_{\ell'}.
\tag{4.4}
\]

A localization witness is

\[
  (\ell,x,\operatorname{ch}_\ell(x)),
  \qquad
  x\in K_\ell\cap(\mathbb C\setminus U).
\tag{4.5}
\]

The source order on packet labels and assigned pieces selects the first
failed label or pair.  No canonical choice of the witness point \(x\) is
needed for the theorem; an actual point and its two actual chambers must be
exhibited in an application.

### Proposition 4.2 (exact closure audit)

For a fixed finite typed assignment, the coverage, connected-seed,
fullification, pairwise-disjointness, and localization clauses of an
augmented-atom packet hold if and only if:

1. every frozen forbidden piece is covered;
2. every raw seed \(S_\ell\) is compact and connected;
3. no witness (4.4) exists; and
4. no witness (4.5) exists.

When these conditions hold, every \(K_\ell\) is a full continuum compactly
contained in \(U\), and the completed family is independent of processing
order.

#### Proof

The forward implication merely unpacks the five geometric packet clauses.

Conversely, compactness of the finite raw unions is immediate.  By
connectedness and Lemma 3.1, every \(K_\ell\) is a full continuum.  Absence
of (4.4) says exactly that the completed packets are pairwise disjoint.
Absence of (4.5), together with compactness of \(K_\ell\), gives
\(K_\ell\Subset U\): the compact set \(K_\ell\) is contained in the open
set \(U\), hence has positive distance from \(\mathbb C\setminus U\).
Coverage is item 1.  Corollary 3.2 gives order independence.
\(\square\)

### Proposition 4.3 (monotone persistence)

Suppose \(S_\ell\subset S'_\ell\) for every fixed label \(\ell\), and put
\(K'_\ell=\operatorname{Fill}(S'_\ell)\).

1. Every packet collision for \(\{K_\ell\}\) remains a packet collision for
   \(\{K'_\ell\}\).
2. Every localization collision for \(\{K_\ell\}\) remains a localization
   collision for \(\{K'_\ell\}\).

Thus neither defect can be repaired by adding pieces while retaining the
same labels.  A repair must delete or reassign data, change the root/sheet
partition, retime the block, or revise the localization.

#### Proof

Lemma 3.1 gives \(K_\ell\subset K'_\ell\) for every label.  Hence any point
in \(K_\ell\cap K_{\ell'}\), or in
\(K_\ell\cap(\mathbb C\setminus U)\), remains in the corresponding enlarged
intersection.
\(\square\)

Connectivity collisions are not declared persistent: adding a justified
connector can connect a raw seed.  Coverage collisions are also not
persistent: adding the omitted required piece repairs coverage.  The
proposition isolates precisely the monotone-irreversible coordinates.

## 5. Port exposure is a local condition

Let \(K_i\) be the completed packet containing the original atom
\(A_i\).  Let \(P_i\subset A_i\) be the union of the impressions prohibited
by the protected marking at the last proof use.  No local connectivity of
\(A_i\), \(K_i\), or their boundaries is assumed.

### Definition 5.1 (unprotected exposure locus)

The unprotected exposure locus of \(A_i\) in \(K_i\) is

\[
\begin{split}
  \operatorname{Exp}(A_i,K_i;P_i)
  :=
  \{x\in A_i\setminus P_i:\;&
  \text{there is a Jordan arc }
  \gamma:[0,1]\to U,\\
  &\gamma(0)=x,\quad
  \gamma\cap K_i=\{x\}\}.
\end{split}
\tag{5.1}
\]

The arc in (5.1) is actual geometric data.  Membership is not inferred from
the fact that \(x\in\partial K_i\).

### Lemma 5.2 (local ports can be made simultaneous)

Let \(K_1,\ldots,K_s\Subset U\) be the atom packets and let
\(L_1,\ldots,L_t\Subset U\) be the obstacle packets.  Assume the whole
family is pairwise disjoint and \(A_i\subset K_i\).  If

\[
  \operatorname{Exp}(A_i,K_i;P_i)\ne\varnothing
  \quad\text{for every }i,
\tag{5.2}
\]

then one can choose Jordan arcs \(\alpha_i\) and
\(x_i\in A_i\setminus P_i\) such that

\[
\begin{aligned}
  &\alpha_i(0)=x_i,\\
  &\alpha_i\cap K_i=\{x_i\},\\
  &\alpha_i((0,1])
    \subset
    U\setminus
    \left(
      \bigcup_{r=1}^sK_r
      \cup
      \bigcup_{\ell=1}^tL_\ell
    \right),
\end{aligned}
\tag{5.3}
\]

and the arcs \(\alpha_i\) are pairwise disjoint.

#### Proof

Because the complete atom/obstacle family is finite, pairwise disjoint, and
compactly contained in \(U\), there is \(\varepsilon>0\) such that the
neighborhoods

\[
  N_i=\{z:\operatorname{dist}(z,K_i)<\varepsilon\}
\tag{5.4}
\]

are pairwise disjoint, compactly contained in \(U\), and miss every
obstacle packet \(L_\ell\).

For each \(i\), choose \(x_i\) and an arc \(\gamma_i\) from (5.1).
Continuity at \(0\) gives \(t_i>0\) such that
\(\gamma_i([0,t_i])\subset N_i\).  Restrict to this initial subarc and
reparameterize it as \(\alpha_i:[0,1]\to U\).  Its positive part still
misses \(K_i\).  Since \(N_i\) misses every \(K_r\) with \(r\ne i\), (5.3)
holds.  Finally, \(\alpha_i\subset N_i\) and the \(N_i\) are pairwise
disjoint, so the arcs are pairwise disjoint.
\(\square\)

Consequently, the global “pairwise disjoint port arcs” clause is not an
additional planar entanglement problem after completed-packet disjointness
has been proved.  The remaining issue is the individual nonemptiness in
(5.2), including the unprotected condition.

### Lemma 5.3 (a metric exposure witness)

Let \(K_1,\ldots,K_s,L_1,\ldots,L_t\Subset U\) be the complete
pairwise-disjoint atom/obstacle packet family from Lemma 5.2.  Suppose
\(y\in U\setminus K_i\), let

\[
  r=\operatorname{dist}(y,K_i)>0,
\tag{5.5}
\]

and suppose there is \(x\in A_i\setminus P_i\) with
\(|x-y|=r\).  If

\[
  \overline{D(y,r)}
  \cap
  \left(
    (\mathbb C\setminus U)
    \cup
    \bigcup_{k\ne i}K_k
    \cup
    \bigcup_{\ell=1}^tL_\ell
  \right)
  =
  \varnothing,
\tag{5.6}
\]

then the segment \([x,y]\) is a valid port after parametrization from
\(x\) to \(y\).

#### Proof

Every interior point \(z\) of \([x,y]\) satisfies
\(|z-y|<r\), so \(z\notin K_i\) by the definition of \(r\).  Condition
(5.6) makes the whole segment miss the other packets and the exterior of
\(U\).  The endpoint \(x\) lies in the original atom and outside the
protected set.  Thus the segment satisfies (5.3).
\(\square\)

This metric condition is sufficient, not necessary.  It is useful because
an actual puzzle or lamination construction can certify it with a local
collar without invoking local connectivity.

### Corollary 5.4 (no-added-piece positive control)

If \(K_i=A_i\), the protected set \(P_i\) is empty, there are no obstacle
packets, and the \(A_i\Subset U\) are finitely many pairwise disjoint
compacta, then every
\(\operatorname{Exp}(A_i,A_i;\varnothing)\) is nonempty and simultaneous
ports exist.

#### Proof

Choose a point \(y_i\notin A_i\) sufficiently close to \(A_i\) that a
closed distance disk as in (5.6) misses all other atoms and
\(\mathbb C\setminus U\).  Compactness supplies a nearest
\(x_i\in A_i\).  Lemma 5.3 gives the individual port and Lemma 5.2 makes
the family simultaneous.
\(\square\)

The corollary is only a no-added-piece positive control.  It does not apply
when a filled collar makes the entire original atom interior to its
augmented packet or when every exposed point is protected.

### Proposition 5.4A (cellwise packet-and-port certificate)

Let \(U\) be a Jordan domain and let
\[
  \overline{D_1},\ldots,\overline{D_N}\Subset U
\tag{5.7a}
\]
be closed Jordan disks with pairwise disjoint closures.  For every packet
label \(\ell\), let \(S_\ell\Subset D_\ell\) be compact and connected, and
assume that the raw seeds collectively cover the complete frozen forbidden
inventory.  Each original atom \(A_i\) is assigned to its own atom-packet
label \(i\), with \(A_i\subset S_i\), and \(P_i\subset A_i\) is its
protected-impression set.

Suppose that for every original atom there are
\[
  x_i\in A_i\setminus P_i
\tag{5.7b}
\]
and a Jordan arc
\(\gamma_i:[0,1]\to\overline{D_i}\) such that
\[
  \gamma_i(0)=x_i,\qquad
  \gamma_i((0,1))\subset D_i\setminus S_i,\qquad
  \gamma_i(1)\in\partial D_i.
\tag{5.7c}
\]
Put \(K_\ell=\operatorname{Fill}(S_\ell)\).  Then:

1. \(K_\ell\Subset D_\ell\) for every \(\ell\);
2. the completed packets are pairwise disjoint;
3. \(x_i\in\operatorname{Exp}(A_i,K_i;P_i)\) for every original atom;
4. the individual ports can be shortened to a pairwise disjoint
   simultaneous family; and
5. the Fixed-Packet Closure and Port Audit and the Augmented-Atom
   Common-Domain Theorem supply the corresponding common free component
   and protected regulated connector.

#### Proof

The exterior of \(\overline{D_\ell}\) is connected, contains infinity, and
misses \(S_\ell\).  It therefore lies in the unbounded component of
\(\mathbb C\setminus S_\ell\).  Every bounded complementary component of
\(S_\ell\) lies in \(D_\ell\), so
\[
  K_\ell=\operatorname{Fill}(S_\ell)\Subset D_\ell.
\]
The pairwise-disjoint closed cells then make the completed packets
pairwise disjoint.

Concatenate the terminal point \(\gamma_i(1)\) with an arc to infinity in
\(\mathbb C\setminus D_i\).  The resulting curve misses \(S_i\) except at
\(x_i\).  Hence every point of \(\gamma_i((0,1])\) lies in the unbounded
component of \(\mathbb C\setminus S_i\), so
\[
  \gamma_i\cap K_i=\{x_i\}.
\]
Together with (5.7b), this proves
\(x_i\in\operatorname{Exp}(A_i,K_i;P_i)\).  Lemma 5.2 makes the ports
simultaneous.  Theorem 7.1 below verifies the fixed-packet clauses, and the
Augmented-Atom Common-Domain Theorem supplies the common component and
connector. \(\square\)

This proposition is a **sufficient local certificate**.  It does not prove
that an actual virtual-Molecule block supplies the disjoint cells, the
complete frozen inventory, the unprotected arcs, or their equivariant
transport through the Wave horizon.  Those are still the source-facing
parts of `VAAPC-C`, `VAAPC-P`, and `VAAPC-H`.

### Proposition 5.5 (port-loss persistence)

Let \(A_i\subset K_i\subset K'_i\) and keep the protected set \(P_i\)
fixed.  Then

\[
  \operatorname{Exp}(A_i,K'_i;P_i)
  \subset
  \operatorname{Exp}(A_i,K_i;P_i).
\tag{5.7}
\]

In particular, an empty exposure locus cannot be repaired by monotone
enlargement of that packet.

#### Proof

Every arc whose positive part misses \(K'_i\) also misses the subset
\(K_i\).  The endpoint and protected-set requirements are unchanged.
\(\square\)

Adding a **new** source-justified candidate access or retiming the protected
marking is not a monotone enlargement of fixed data and is outside the
proposition.

## 6. Naturality

### Lemma 6.1 (filled hull commutes with sphere homeomorphisms)

Let \(h:S^2\to S^2\) be a homeomorphism fixing \(\infty\).  For every compact
\(K\subset\mathbb C\),

\[
  h(\operatorname{Fill}(K))
  =
  \operatorname{Fill}(h(K)).
\tag{6.1}
\]

#### Proof

The map \(h\) bijects the components of \(S^2\setminus K\) with those of
\(S^2\setminus h(K)\).  Because \(h(\infty)=\infty\), it maps the component
containing \(\infty\) to the component containing \(\infty\).  Taking their
complements proves (6.1).
\(\square\)

### Proposition 6.2 (naturality of the complete audit)

Suppose \(h:U\to\widetilde U\) is a conformal homeomorphism of Jordan disks.
Transport every raw piece, original atom, protected set, and port arc by
\(h\).  Then:

1. \(h(K_\ell)=\operatorname{Fill}(h(S_\ell))\);
2. packet and localization collisions are transported bijectively, with
   their seed/chamber descriptors;
3. \(h\) bijects the unprotected exposure loci; and
4. zero collision plus simultaneous ports holds before transport if and
   only if it holds afterward.

#### Proof

Carathéodory boundary extension and the Schoenflies theorem extend \(h\) to
a sphere homeomorphism fixing \(\infty\), after conjugating by an
orientation-preserving sphere homeomorphism if needed.  Lemma 6.1 gives
item 1.  A homeomorphism preserves intersections, complementary components,
and containment in the localization, proving item 2.  It maps Jordan arcs
to Jordan arcs and the protected set to its declared transported protected
set, proving item 3.  Item 4 follows.
\(\square\)

The extension hypothesis is essential.  A bare abstract correspondence of
packet labels, without an actual homeomorphism on neighborhoods of the full
packets, does not imply (6.1) or transport access arcs.

## 7. Main theorem

### Theorem 7.1 (Fixed-Packet Closure and Port Audit)

For every fixed finite typed assignment in a Jordan localization, the
following statements are equivalent:

1. the assignment satisfies the geometric augmented-packet clauses:
   connected seeds, complete coverage, pairwise disjoint fullifications
   compactly contained in the localization, and one explicit pairwise
   disjoint unprotected singleton port to every original atom;
2. the unique completed packets \(K_\ell=\operatorname{Fill}(S_\ell)\)
   have no coverage, connectivity, packet, or localization collision, and
   every atom has nonempty unprotected exposure locus (5.1).

The completed packets are independent of the processing order.  Packet
collisions, localization collisions, and empty exposure loci persist under
monotone enlargement with fixed labels.  The entire zero-collision
certificate is natural under a sphere-extending univalent transport.

#### Proof

Proposition 4.2 proves the equivalence of all non-port clauses and order
independence.  Lemma 5.2 proves that nonempty individual exposure loci are
equivalent to the simultaneous port requirement.  Propositions 4.3 and 5.5
give persistence.  Proposition 6.2 gives naturality.
\(\square\)

This theorem is recorded in the machine ledger as
`AUGMENTED_PACKET_CLOSURE_AUDIT`.

## 8. Reduction of the live dynamical gate

Theorem 7.1 decomposes `VAAPC` into five source-facing clauses.

### `VAAPC-I` Frozen actual input

After the last future root enlargement, enumerate:

1. every actual root-shadow atom;
2. every proof-used collar and critical exclusion through its last use;
3. every absorbed or separated ambient component;
4. every localization-forbidden component;
5. every protected impression; and
6. every selected univalent transport through the complete Wave horizon.

Every item must have its actual component, attachment trace, return word,
parent route, sheet, and proof-use interval.

### `VAAPC-C` Zero completed-packet collision

Give a source-faithful packet label to every item from `VAAPC-I`, prove each
raw seed connected, and show that no witness (4.4) or (4.5) exists.  By
Theorem 7.1, no procedural “completion-order” argument remains.

### `VAAPC-P` Unprotected exposure

For every original atom, exhibit either:

- an actual arc proving membership in (5.1); or
- a metric collar witness satisfying Lemma 5.3.

Theorem 7.1 then supplies pairwise disjoint simultaneous ports.  A boundary
point with no access arc is insufficient, and an access landing only on a
newly attached piece is not a port to the original atom.

This clause is an independent geometric input, recorded as
`VIRTUAL_UNPROTECTED_ATOM_EXPOSURE`.  It does not follow from
`VIRTUAL_COMMON_FREE_COMPONENT`.  The implication runs in the opposite
direction: `VAAPC-P`, together with collision-free completed packets,
produces simultaneous ports by Theorem 7.1, and the Augmented-Atom
Common-Domain Theorem then implies the common free component.

### `VAAPC-H` Complete-horizon transport

Prove that every stage map is defined and univalent on neighborhoods of the
**full completed packets**, not only on the named small Julia components.
Transport the protected sets and attachment traces as well.  Proposition
6.2 then gives the closure and port naturality for free.

### `VAAPC-U` Uniform incidence or faithful compression

Bound the retained atoms, obstacle packets, protected impressions, and
transported ports independently of satellite period, rotation number, and
corridor length, or construct a future-faithful compressed state and prove
that every later proof-use query factors through it.

The subsequent
[horizon-first inventory audit](vaapc_inventory_source_audit.md) proves the
unique dependency closure and exact extension-stability criterion once a
finite horizon graph is supplied.  The checked sources do not supply that
graph: the first missing datum is the virtual Wave stopping horizon, recorded
as `VIRTUAL_WAVE_HORIZON_CERTIFICATE`.  Consequently `VAAPC-I` and the tests
for `VAAPC-C`, `VAAPC-P`, `VAAPC-H`, or `VAAPC-U` remain open.  This is a
missing analytic construction, not a proved dynamical counterexample.  No
failure tuple for an actual block is emitted.

## 9. First-failure certificate

For a source-defined block, the first failure must refine equation (5.2) of
`virtual_common_free_component.md` by adding the closure witness:

\[
\begin{split}
  \mathfrak F_{\rm close}
  =(&B,j,Y,\operatorname{type}(Y),\tau(Y),w(Y),\varsigma(Y),\\
    &\ell,\ell',x,
      \operatorname{ch}_\ell(x),
      \operatorname{ch}_{\ell'}(x),
      \Gamma_\ell,\Gamma_{\ell'},U).
\end{split}
\tag{9.1}
\]

For localization failure, \(\ell'\) is replaced by the exterior label.
For port failure, record

\[
  \mathfrak F_{\rm port}
  =
  (B,j,i,A_i,K_i,P_i,
    \operatorname{Exp}(A_i,K_i;P_i),
    \tau_i,w_i,\varsigma_i,U).
\tag{9.2}
\]

An actual proof of emptiness in (9.2) is required; failure to find an arc is
not such a proof.

If a packet certificate fails, `VIRTUAL_COMMON_FREE_COMPONENT` may still
hold through a different decomposition.  It is refuted only by the separate
free-domain separator tuple from `virtual_protected_routing_domain.md`.

## 10. Adversarial cross-examination

| attack | result |
|---|---|
| Process the same assigned pieces in a different order | No effect. Corollary 3.2 proves equality of the final filled sets. |
| Move one piece to a different packet | Outside order independence. The raw union attached to each label has changed and must be re-audited. |
| A separated annulus surrounds an atom | Its filled chamber meets the atom packet, producing (4.4). The collision persists under enlargement. |
| Assign that annulus to the surrounded atom | The original atom can become interior to its packet, making its exposure locus empty. |
| Two seeds are disjoint before filling | Insufficient. The audit uses intersections of the actual completed packets and retains the bounded chambers causing the collision. |
| Each original atom has an individual access, but the long arcs cross | Not an obstruction. Lemma 5.2 truncates them in pairwise disjoint packet neighborhoods. |
| The augmented atom has a boundary point in the original atom | Insufficient without an actual access arc; non-local connectivity is allowed. |
| The only exposed original points are protected impressions | `VAAPC-P` fails. Protected points cannot be relabeled free. |
| Adding more collar pieces might repair a merger | Impossible with fixed labels by Proposition 4.3. |
| Adding more pieces might expose an interior atom | Impossible by Proposition 5.5. |
| A conformal branch transports only the named atoms | Insufficient. Naturality requires a neighborhood map for every full completed packet and its marking. |
| Infinitely many accumulating ambient components | Outside the finite theorem unless replaced by one proved compact finite summary preserving all later access queries. |
| Zero topological collision but vanishing analytic width | Not addressed. The theorem is topological and does not prove a uniform collar modulus. |
| The finite-cell regression passes | Diagnostic only. It cannot prove any analytic virtual-Molecule clause. |

## 11. Promotion decision and immediate next move

Promote:

- `AUGMENTED_PACKET_CLOSURE_AUDIT`.

Keep open:

- `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`;
- `VIRTUAL_COMMON_FREE_COMPONENT`;
- `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`;
- `VIRTUAL_CANONICAL_INTERFACE_CARRIER`;
- UPTCR-1; and
- MLC.

The next analytic move is no longer “choose a completion order.”  It is:

> prove `VIRTUAL_WAVE_HORIZON_CERTIFICATE` for the first actual
> virtual-Molecule block, then construct the typed part of `VAAPC-I`, compute
> the unique filled packets, and prove `VAAPC-C` and `VAAPC-P`; otherwise
> emit (9.1) or prove the empty-exposure assertion in (9.2).

The public connected-hull paragraph is not detailed enough to carry out
that enumeration.  A complete proof therefore still requires new
virtual-renormalization geometry, not further formal manipulation of the
published statement.
