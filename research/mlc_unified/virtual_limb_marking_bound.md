# Access-complete virtual limb marking

## 1. Status and purpose

KKL Proposition 3.7 uses a uniform bound on the complete ideal
multi-interval associated to each limb. In the KKL Hubbard tree, occupancy by
at most \(B\) small filled Julia sets yields the estimate
\[
  |\mathcal L_j|\le 6B.
\]
For a virtual hull, counting only the selected small Julia sets is
insufficient because dynamically used prime ends, fjord mouths, dam endpoints,
and critical-orbit accesses can introduce additional terminal atoms.

This note proves the exact finite-tree part of the transfer. It does **not**
construct the virtual tree, prove access completeness, or identify the
resulting intervals with KKL's canonical marking. Those remain analytic and
dynamical obligations in the Virtual Section-4 Interface.

## 2. Reduced anchored carriers

Fix one limb. Let \(S=\{a\}\sqcup S^\circ\) be a finite set of prescribed
marked atoms, where \(a\) is the limb anchor and
\[
  m=|S^\circ|.
\]
An atom can be a clustered small filled Julia set or any additional endpoint
or access that must remain distinguishable in a proof-used curve family.

### Definition 2.1 (reduced anchored limb carrier)

A reduced anchored limb carrier for \(S\) is a finite tree \(T\) such that:

1. \(S\subset V(T)\);
2. \(T\) is the minimal connected subtree containing \(S\);
3. every vertex in \(V(T)\setminus S\) has valence at least three.

Condition 3 loses no combinatorial information: unmarked valence-two
subdivision vertices can be suppressed. Minimality implies that every leaf of
\(T\) lies in \(S\).

Each edge of an embedded tree has two oriented tree sides. Let
\(\mathcal S(T)\) denote this multiset. In addition, permit a multiset
\(\mathcal D(s)\) of local ideal decorations at every prescribed atom
\(s\in S\), including the anchor. These record, for example, the at most two
ideal sides that KKL charges to a distinguished tree vertex. Define the
complete combinatorial limb marking by
\[
  \mathcal L(T,S)
  =
  \mathcal S(T)
  \sqcup
  \bigsqcup_{s\in S}\mathcal D(s).
\tag{2.1}
\]

The word *complete* here is conditional: every proof-used access must already
have been included in \(S\) or in one of the declared local decorations.

## 3. Exact tree count

### Lemma 3.1 (unmarked branch count)

Assume \(m\ge1\). If \(U=V(T)\setminus S\), then
\[
  |U|\le m-1.
\tag{3.1}
\]

**Proof.**
Let \(L\) be the number of leaves. Every leaf lies in \(S\), hence
\(L\le |S|=m+1\). For a finite tree,
\[
  \sum_{v\in V(T)}(\deg v-2)=-2.
\]
Every \(u\in U\) contributes at least \(1\). Every nonleaf marked vertex
contributes at least \(0\), while each leaf contributes \(-1\). Therefore
\[
  |U|-L\le -2,
\]
so
\[
  |U|\le L-2\le m-1.
\]
\(\square\)

### Theorem 3.2 (access-complete limb bound)

For a reduced anchored carrier with \(m\ge1\),
\[
  |E(T)|\le 2m-1
\tag{3.2}
\]
and
\[
  |\mathcal S(T)|=2|E(T)|\le4m-2.
\tag{3.3}
\]
If every prescribed atom, including the anchor, has at most \(\sigma\)
local decorations, then
\[
  |\mathcal L(T,S)|
  \le (4+\sigma)m+\sigma-2.
\tag{3.4}
\]
In particular, if \(\sigma\le2\), then
\[
  |\mathcal L(T,S)|\le6m.
\tag{3.5}
\]

For \(m=0\), the limb is empty and its limb marking is declared empty; the
anchor is not charged to an empty limb.

**Proof.**
By Lemma 3.1,
\[
  |V(T)|=|S|+|U|
  \le(m+1)+(m-1)=2m.
\]
Since \(T\) is a tree,
\[
  |E(T)|=|V(T)|-1\le2m-1.
\]
Every edge has exactly two oriented sides, proving (3.3). The local
decorations contribute at most \(\sigma(m+1)\), which gives (3.4) and
(3.5).
\(\square\)

### Corollary 3.3 (uniform per-limb and total bounds)

Suppose every limb \(j\) has an access-complete reduced carrier with at most
\(B_*\) non-anchor atoms and at most two local decorations at every
prescribed atom, including the anchor. Then
\[
  |\mathcal L_j|\le6B_*.
\tag{3.6}
\]
For \(q\) limbs,
\[
  |\mathcal I|
  =
  \sum_{j=1}^{q}|\mathcal L_j|
  \le6B_*q.
\tag{3.7}
\]
The constant is independent of \(q\), rotation number, and virtual depth
provided \(B_*\) is.

This is the precise combinatorial form needed by the pigeonhole denominators
in KKL Section 4.

### Corollary 3.4 (bounded-fiber conversion)

Suppose a limb contains at most \(B\) selected small Julia components and
there is an explicit assignment of every non-anchor marked atom to one of
those components with fibers of size at most \(c_{\rm acc}\). Then
\[
  m\le c_{\rm acc}B
\quad\text{and}\quad
  |\mathcal L_j|\le6c_{\rm acc}B.
\tag{3.8}
\]

Thus the virtual replacement for KKL occupancy can be discharged by a
uniform bounded-fiber access theorem. The existence of that assignment is
not a consequence of connectedness or partial invariance.

## 4. Necessity of access completeness

### Proposition 4.1 (selected-component occupancy no-go)

No function of the selected-component count alone bounds the complete ideal
marking of a virtual limb.

**Proof.**
For each \(N\), take an embedded star tree with one anchor, one terminal
representing the sole selected small Julia component, and \(N\) further
terminals representing pairwise distinguished proof-used accesses. The
selected-component count is always one. The carrier has \(N+1\) edges and
therefore \(2N+2\) oriented tree sides, before any local decorations are
added. This tends to infinity with \(N\). \(\square\)

The example remains valid if all access terminals are attached through
fjords to a single connected continuum. Connectivity does not identify
distinct prime-end accesses.

### Proposition 4.2 (unmarked subdivision is harmless)

Arbitrarily many unmarked valence-two subdivisions do not change the
complete marking count after reduction.

**Proof.**
Suppressing an unmarked valence-two vertex replaces its two incident edge
segments by one edge. It preserves the embedded path, prescribed atoms,
complementary access order, and the two oriented sides of the underlying
unsubdivided edge. Hence only marked atoms and genuine branch vertices enter
Theorem 3.2. \(\square\)

This prevents a false negative: raw triangulation or puzzle-mesh size is not
the relevant occupancy.

## 5. Interface consequence

The finite-tree portion of the Virtual Section-4 Interface is now reduced to
the following analytic statement.

### Open realization statement

For every virtual-Molecule block routed to the KKL occupancy split, construct
in each limb a reduced carrier satisfying:

1. **access completeness:** every prime end, fjord side, dam endpoint,
   critical-orbit access, and tree side used by the flux/alignment
   restrictions is represented;
2. **bounded atom load:** the number \(m_j\) of non-anchor atoms is bounded by
   a universal \(B_*\), or admits the bounded-fiber estimate
   \(m_j\le c_{\rm acc}B\);
3. **bounded local decoration:** every prescribed atom, including the
   anchor, produces at most two canonical ideal intervals, or a separately
   stated universal number;
4. **faithful realization:** the combinatorial sides correspond injectively
   to the ideal intervals used by the virtual WAD and wave definitions.

Once these four items hold, Corollary 3.3 supplies the period-independent
ideal-marking bound. It does not supply the remaining Section-4 inputs:

- virtual canonical-WAD versus renormalization-width comparison;
- comparability across every selected cycle component;
- faithful restriction of flux and alignment laminations;
- the large-width threshold needed to invoke the trichotomy.

## 6. Adversarial checklist

Before using (3.6), verify:

1. the anchor is included but not charged repeatedly;
2. touching small Julia sets have been clustered consistently;
3. every proof-used prime-end access appears in \(S\);
4. fjord and dam sides are either atoms or bounded local decorations;
5. no omitted Cantor component creates a used access outside the carrier;
6. marked valence-two vertices are retained, while only unmarked ones are
   suppressed;
7. the bound is on atoms per limb, not merely on components per limb;
8. the same carrier is used by the WAD restriction and wave definitions;
9. \(B_*\) and the decoration bound are independent of period, rotation
   number, and transition depth.

Failure of Item 3 or Item 7 is detected by Proposition 4.1. Failure of Item 8
is a category mismatch, not a counting error.
