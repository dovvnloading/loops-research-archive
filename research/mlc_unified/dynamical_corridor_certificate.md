# Finite-state certificate for virtual corridor cloning

## 1. Status and purpose

`corridor_clone_criterion.md` recognizes a clone after its full transition graph has
already been constructed. This note gives finite, adversarially checkable certificates
for the two global graph properties that are easiest to hide:

1. the corridor gate is a KKL cross section;
2. every delayed clone is primitive.

It then states a finite-state dynamical certificate which, if realized by the
finite-horizon core transition of a virtual block and made compatible with its WAD
correspondence, activates the entropy theorem in `virtual_clone_entropy.md`.

The certificates are proved here. Their realization for Dudko's virtual Julia sets
remains open.

## 2. Cross sections are exactly feedback vertex sets

Let \(G\) be a finite directed multigraph and let \(E\subset V(G)\). Write
\[
  A=V(G)\setminus E
\]
and \(G[A]\) for the induced directed subgraph on \(A\).

In this note, a directed path may repeat vertices; it is a walk in the
matrix-power sense. A simple path is named explicitly.

### Lemma 2.1 (cross-section/acyclicity equivalence)

The following are equivalent:

1. every sufficiently long directed path in \(G\) meets \(E\);
2. \(G[A]\) is a directed acyclic graph.

When these conditions hold, every directed path avoiding \(E\) has at most
\[
  |A|-1
\tag{2.1}
\]
edges.

**Proof.** If \(G[A]\) contains a directed cycle, iterating that cycle gives
arbitrarily long paths avoiding \(E\), so Item 1 fails.

Conversely, a directed path in \(G[A]\) with at least \(|A|\) edges visits at least
\(|A|+1\) vertices. Some vertex repeats, and the segment between two consecutive
occurrences contains a directed cycle. Thus acyclicity forces (2.1), proving
Item 1. \(\square\)

KKL additionally requires that no edge has both endpoints in \(E\). This local
condition is independent of Lemma 2.1.

### Corollary 2.2 (uniform crossing bound)

If a reduced quotient has at most \(a\) active vertices and its active subgraph is
acyclic, then it has a cross-section bound depending only on \(a\). In KKL's reduced
clone construction, every path-start label can consequently be chosen from a
universal set of depth at most \(a+1\), independently of clone length.

The harmless \(+1\) avoids dependence on whether path length is counted by vertices
or edges.

## 3. Primitivity under arbitrary clone delay

Let \(G_0\) be a finite directed graph with a nonempty cross section \(E\), with no
edge from \(E\) to \(E\). Let \(G_n\) be its length-\(n\) clone.

For a closed directed walk \(C\) in \(G_0\), let:

- \(\ell(C)\) be its number of edges;
- \(r_E(C)\) be the number of passages through \(E\), counted cyclically with
  multiplicity.

Each passage through \(E\) acquires exactly \(n\) additional chain edges in \(G_n\).
Thus the lifted closed walk \(C^{(n)}\) has
\[
  \ell(C^{(n)})=\ell(C)+n\,r_E(C).
\tag{3.1}
\]

### Lemma 3.1 (strong connectivity survives cloning)

If \(G_0\) is strongly connected and every \(e\in E\) lies on a
positive-length closed walk, then every \(G_n\) is strongly connected. The added
hypothesis is automatic when \(G_0\) is strongly connected and has more than one
vertex.

**Proof.** Project a clone path by identifying the copies of each \(e\in E\). A base
path can be lifted by replacing every passage through \(e\) with the full directed
chain \(e_0\to\cdots\to e_n\). From a point already inside a chain, first travel to
its exit; to reach a point inside a target chain, enter its first cell and stop at the
required copy. Strong connectivity of the base supplies the portions between these
operations. \(\square\)

### Theorem 3.2 (delay-robust primitivity witness)

Assume \(G_0\) is strongly connected. Suppose it has two closed directed walks
\(C_1,C_2\) such that
\[
  r_E(C_1)=r_E(C_2)
  \quad\text{and}\quad
  |\ell(C_1)-\ell(C_2)|=1.
\tag{3.2}
\]
Then \(G_n\) is primitive for every \(n\ge0\).

**Proof.** By (3.1), the two lifted closed walks have lengths differing by one for
every \(n\). The period of a strongly connected directed graph is the greatest common
divisor of the lengths of all its closed walks. That period divides both lifted
lengths, hence divides their difference \(1\). Lemma 3.1 supplies strong
connectivity.

For completeness, period one implies primitivity as follows. At any fixed vertex
\(v\), the gcd of return-walk lengths equals the global period: paths from \(v\) to
the base point of any closed walk and back show, by subtracting the connecting return
length, that the return gcd at \(v\) divides every closed-walk length. A finite
collection of return lengths with gcd one generates every sufficiently large integer
as a nonnegative sum. After fixing paths \(x\to v\) and \(v\to y\) for every ordered
pair of vertices, sufficiently long common lengths are obtained by inserting such
return walks at \(v\). Hence, for one common \(M\), there is a length-\(M\) path
between every ordered pair, so the \(M\)-th adjacency power is strictly positive.
Thus \(G_n\) is primitive. \(\square\)

The two walks in (3.2) make the base nontrivial, so Lemma 3.1 applies. Condition
(3.2) is sufficient, not necessary. It is useful because it is a bounded
local witness whose validity is independent of corridor length.

### Proposition 3.3 (primitive base does not suffice)

There is a primitive base graph with a cross section whose length-one clone is
periodic.

**Proof.** Let \(G_0\) be the union of a directed \(3\)-cycle and a directed
\(5\)-cycle sharing exactly one vertex \(e\), and set \(E=\{e\}\). The graph is
strongly connected. Every closed walk is a concatenation of the two simple cycles, so
the base period is
\[
  \gcd(3,5)=1.
\]
Thus \(G_0\) is primitive. The set \(E\) is a cross section and has no
\(E\)-to-\(E\) edge.

In the length-one clone, the two generating cycle lengths become \(4\) and \(6\).
Every closed walk is a concatenation of these delayed cycles, so the cloned period is
\[
  \gcd(4,6)=2.
\]
The clone is strongly connected but not primitive. \(\square\)

Therefore KKL's separate primitivity hypothesis on the cloned graphs cannot be
dropped merely because the reduced base is primitive.

## 4. The finite-state corridor certificate

Fix universal integers
\[
  a_0,d_0,L_0,R_0,q_0,N_0<\infty.
\]
A finite-horizon marked dynamical block has a **finite-state corridor certificate** if
its complete core/Hubbard transition multigraph, together with the WAD itinerary
incidence used by Value, has the following data.

### `FC1` Complete states

Its vertices are finite Hubbard-tree/core transition states, partitioned into an
active set and at most \(q_0\) corridor families. Edge multiplicity is the actual
core-pushforward occurrence count. Every WAD coordinate, Wave itinerary, critical
branch, and access used by the block has a declared compatible incidence with these
states and edges. No proof-used core or WAD coordinate is eliminated before its last
use.

### `FC2` Pure translated interiors

After absorbing at most \(L_0\) entry cells and \(R_0\) exit cells into the active
set, each remaining corridor has exactly one label-preserving transition to the next
cell and no other edge incident to an interior cell. All non-chain edges enter at the
first surviving cell or exit at the last. All surviving parallel corridors have a
common clone length; corridors of other lengths are placed in separate complete
blocks rather than padded with fictitious states. The surviving length exceeds the
crossing/label bound in `FC6`; shorter corridors are absorbed into the universally
bounded active block.

### `FC3` Bounded reduced gate

Deleting the distinguished chain edges and identifying equal corridor labels produces
a reduced graph
\[
  G_0=A\sqcup E
\]
with
\[
  |A|\le a_0,
  \qquad
  |E|\le d_0,
\tag{4.1}
\]
and no edge from \(E\) to \(E\). For several corridors, \(E\) is their total disjoint
union; (4.1) bounds the sum, not each summand separately.

### `FC4` Feedback and recurrence

The induced active graph \(G_0[A]\) is acyclic.

### `FC5` Robust mixing

The reduced base is strongly connected and has a pair of closed walks satisfying
(3.2). The source-licensed reduced KKL graph is nontrivial.

### `FC6` Horizon and source identity

Every edge and both walks in `FC5` are realized within the declared finite horizon,
with actual maximum first-return exponent \(K\le N_0\). The transition is the
Hubbard/core incidence used
to define KKL's core eigenweights—not a graph fitted afterward to its spectral
radius. If \(N_{\beta\gamma}\) is the raw source-to-target occurrence incidence,
the project source-column count map must satisfy \(B=N^{\mathsf T}\), with
chronological products and left/right Value weights translated as in
`transfer_convention_and_frame.md`. The WAD pullbacks entering Value carry a proved,
typed itinerary-incidence map compatible with that bridge. For the Value corollary,
the outgoing retained WAD must satisfy the coefficientwise domination
\[
  Y\le (f^r)^*X+E
\]
for an actual pullback exponent \(r\ge n\), where \(n\) is the literal clone delay.
Every surviving clone has length \(n>N_0\ge K\).

### Theorem 4.1 (certificate implies a uniform graph clone block)

A finite-state corridor certificate produces an exact cross-section clone in KKL's
graph-theoretic sense after endpoint absorption. Its reduced cross-section dimension
and label depth are universally bounded, and every clone graph is primitive.

**Proof.** `FC1`--`FC3` and endpoint absorption give the exact edge-multiplicity
hypotheses of `corridor_clone_criterion.md`, Theorem 3.2 and Lemma 4.2. For several
corridors, `FC3` bounds the total cross section and `FC4`, by Lemma 2.1, proves it is
a cross section of the combined reduced quotient. Corollary 2.2 bounds reduced label
depth, and `FC6` puts the common delay strictly above that actual return bound.
`FC5` and Theorem 3.2 prove primitivity for every delay; the same two-walk witness
excludes a cycle-permutation return matrix. Thus the abstract clone datum satisfies
the graph hypotheses of `virtual_clone_entropy.md`, Theorem 4.1. \(\square\)

### Corollary 4.2 (conditional KKL Value contraction)

Assume in addition the full periodically repelling prime-primitive \(\psi\)-ql
hypotheses of the imported KKL Value theorem, identify the certificate's
source-column core map with \(N^{\mathsf T}\), identify its WAD incidence with the
KKL pullback valuation, use KKL \(v\) as the project left eigenweight and KKL \(w\)
as the project right eigenweight. Assume explicitly that
\(Y\le(f^r)^*X+E\) coefficientwise for an actual pullback exponent \(r\ge n\),
where \(n\) is the literal clone delay. If the return graph is non-permutation and
\(K\le N_0<n\), then the corrected literal-clone theorem supplies the
negative-weight equation and the complete positive-entropy corridor has
\[
  V_{\rm out}
  \le
  2^{-1/(2d_0)}V_{\rm in}
  +V_{\rm out}(\text{error}).
\tag{4.2}
\]

**Proof.** Theorem 4.1 supplies the exact primitive clone graph. Apply KKL
monotonicity to the displayed coefficientwise domination, then apply KKL pullback
contraction with exponent \(r\). Since \(r\ge n\) and \(\lambda>1\),
\(\lambda^{-r}\le\lambda^{-n}=q^{-1}\le2^{-1/(2d_0)}\); linearity puts \(E\) in
the separate outgoing error term. \(\square\)

The error in (4.2) has not been bounded here. It must be measured in outgoing Value
and pass the discounted charge theorem.

## 5. Exact source comparison

KKL26 proves the needed certificate only in its parabolically bounded finite Hubbard
tree setting:

1. `not-all-good2.tex`, Lemma `lem:get-around`, lines 74--105, bounds the time needed
   to return from the critical limb to finitely many controlled limbs;
2. Corollary `cor:cross-section`, lines 107--120, turns that bound into a Hubbard-tree
   edge cross section;
3. Proposition `prop:eigenweights`, lines 131--157, asserts that increasing the
   parabolic length clones that cross section and applies the clone appendix.

Those arguments use the parabolic bound on the number of small Julia sets in each
limb and the finite Hubbard tree.

Dudko25 `main.tex`, lines 875--892, defines the virtual-Molecule gap and proposes
partially invariant connected hulls of Cantor small Julia sets containing only a
prescribed number of critical first returns. It does not define a finite transition
graph, a gate, a return-time bound, a feedback-vertex property, or a mixing witness.

Consequently neither source proves `FC1`--`FC6` for virtual blocks.

## 6. Refined realization theorem

### Finite-State Virtual Corridor Certificate (`OPEN`)

Every positive-entropy virtual-Molecule block admits `FC1`--`FC6` with universal
constants.

This decomposes into six falsifiable obligations:

1. **Markov extraction:** produce finitely many complete core transition states from
   the Cantor virtual hull and its prescribed critical first returns, together with
   the WAD-to-core incidence used by Value;
2. **corridor purity:** prove every sufficiently interior branch is the declared
   conformal translation and that no critical, immersion, or access branch enters it;
3. **feedback:** prove every directed active cycle meets the corridor gate, or move
   the cycle into a separate entropy block;
4. **mixing:** construct a bounded delay-robust witness such as (3.2);
5. **uniform complexity:** bound total gate size, active size, endpoint windows,
   parallel corridor number, and label depth;
6. **source identity:** identify this exact transition with the KKL
   Hubbard/core pushforward and its WAD/Value pullback incidence inside the
   finite-horizon correspondence.

The cross-section recurrence and clone primitivity are no longer opaque once these
data exist: Lemma 2.1 and Theorem 3.2 discharge them.

## 7. Adversarial audit

The certificate fails under any of:

1. an active directed cycle disjoint from \(E\);
2. a hidden critical pullback entering an interior corridor cell;
3. a corridor transition with multiplicity greater than one;
4. a WAD class that splits into two future itineraries after state compression;
5. a clone whose period changes with the delay, as in Proposition 3.3;
6. a mixing witness whose length or number of gate passages grows with the satellite
   period;
7. individually bounded corridor gates whose total cardinality is unbounded;
8. an edge or primitivity witness that lies beyond the selected finite horizon;
9. a graph transition that is not the source-licensed KKL Value transition.

Each item invalidates a specific `FC` clause. None is an additive surface-width error.
