# Exact corridor-to-clone criterion

## 1. Status

`virtual_clone_entropy.md` gives uniform contraction once a virtual corridor has a
bounded-dimensional reduced clone model. This note proves the finite directed-graph
criterion for being such a clone.

It proves:

1. an exact translation corridor with a bounded cross section is precisely a
   cross-section clone;
2. defects confined to bounded entry and exit windows can be absorbed into the active
   graph without increasing reduced cross-section dimension;
3. finitely many disjoint exact corridors combine by taking the disjoint union of
   their cross sections.

It does not prove that the dynamical/WAD transition graph of a Dudko virtual hull
satisfies the criterion.

## 2. Cross-section clones

Let \(G_0\) be a finite directed multigraph with vertex partition
\[
  V(G_0)=A\sqcup E.
\]
Assume:

1. no edge has both endpoints in \(E\);
2. \(E\) is a cross section: every sufficiently long directed path meets \(E\).

The length-\(n\) **clone of \(E\)** replaces \(E\) by copies
\[
  E_0,E_1,\ldots,E_n
\]
and:

1. redirects every edge \(a\to e\), \(a\in A,e\in E\), to \(a\to e_0\);
2. redirects every edge \(e\to a\) to \(e_n\to a\);
3. keeps every edge inside \(A\);
4. adds one chain edge
   \[
     e_k\longrightarrow e_{k+1}
   \tag{2.1}
   \]
   for every \(e\in E\) and \(0\le k<n\);
5. has no other edges.

This is the graph operation used by KKL's cloning appendix.

## 3. Exact translation corridor

### Definition 3.1

A directed multigraph \(G\) has an **exact translation corridor of length \(n\)** with
cross-section type \(E\) if its vertices have a partition
\[
  V(G)=A\sqcup E_0\sqcup\cdots\sqcup E_n
\tag{3.1}
\]
and fixed label-preserving bijections
\[
  \tau_k:E\longrightarrow E_k
\]
such that:

1. for every \(e\in E\) and \(0\le k<n\), there is exactly one distinguished chain
   edge
   \[
     \tau_k(e)\to\tau_{k+1}(e);
   \]
   these are the only edges whose two endpoints lie in corridor cells;
2. every non-chain edge meeting the corridor enters through \(E_0\) or exits through
   \(E_n\);
3. after identifying all \(E_k\) with \(E\), the entry and exit edge
   multiplicities are independent of \(n\);
4. all remaining edges lie inside \(A\);
5. the **reduced quotient** \(G_0\), obtained by first deleting the distinguished chain
   edges and then identifying \(\tau_k(e)\) with \(e\), has no \(E\)-to-\(E\) edge
   and \(E\) is a cross section.

The condition is on the full directed multigraph, including edge multiplicities.
A homeomorphism between geometric cells is not enough.

### Theorem 3.2 (corridor-to-clone equivalence)

A graph has an exact translation corridor in the sense of Definition 3.1 if and only
if it is the length-\(n\) clone of its quotient cross section \(E\subset G_0\).

**Proof.** If \(G\) is a clone, the defining construction gives Items 1--5.

Conversely, delete the distinguished chain edges and identify the labels
\[
  \tau_0(e),\ldots,\tau_n(e)
\]
to one vertex \(e\). Items 2--4 recover exactly the entry, exit, and active edges of
the quotient \(G_0\). Item 1 says that expanding \(e\) back into \(n+1\) copies adds
exactly the clone chain (2.1), and it forbids every extra interior edge. Thus the
expansion reconstructs \(G\) edge for edge, including multiplicity. \(\square\)

### Corollary 3.3

If the quotient graph and its clone satisfy KKL's primitivity hypotheses, the common
clone delay \(n\) exceeds the actual maximum first-return length \(K\), the resulting
return matrix is irreducible and non-permutation, and
\[
  |E|\le d,
\]
then the corrected negative-weight clone theorem applies and the complete corridor
has the graph-theoretic Value factor
\[
  \lambda_n^{-n}<2^{-1/(2d)}
\]
from `virtual_clone_entropy.md`, Theorem 4.1.

This corollary is conditional on the corridor graph being the source-licensed KKL core
transition graph. It does not promote an arbitrary directed graph to a
\(\psi\)-ql dynamical system.

## 4. Endpoint-defect absorption

Virtual corridors may have exceptional entry and exit windows. Bounded endpoint
defects do not obstruct cloning.

### Definition 4.1

A corridor
\[
  E_0,\ldots,E_n
\]
is **exact outside endpoint windows \((L,R)\)** if all edges incident to
\[
  E_L,E_{L+1},\ldots,E_{n-R}
\]
obey the exact chain rule, except for entry edges into \(E_L\) and exit edges from
\(E_{n-R}\). Every other exceptional edge and vertex is confined to the active graph
together with
\[
  E_0,\ldots,E_{L-1},
  \qquad
  E_{n-R+1},\ldots,E_n.
\]
In addition, after the distinguished edges of the central chains
\[
  E_L,\ldots,E_{n-R}
\]
are deleted and their vertices are identified label by label, the surviving copy of
\(E\) is required to be a cross section of the resulting reduced quotient. This is a
separate recurrence hypothesis; it does not follow merely from the local chain rule.

### Lemma 4.2 (absorb bounded endpoint defects)

Assume \(n\ge L+R\). A corridor exact outside endpoint windows \((L,R)\) is an exact
clone of length
\[
  n'=n-L-R
\tag{4.1}
\]
after the two exceptional windows are absorbed into an enlarged active graph. The
reduced cross-section cardinality remains \(|E|\).

**Proof.** Put all vertices in the exceptional windows into the new active set
\(A'\). Relabel
\[
  E'_j=E_{L+j},
  \qquad
  0\le j\le n'.
\]
By Definition 4.1, every edge incident to an interior \(E'_j\) is its unique chain
edge, all non-chain entries land in \(E'_0\), and all non-chain exits leave
\(E'_{n'}\). Every other edge lies in \(A'\). The quotient cross section is still a
copy of \(E\). Apply Theorem 3.2. \(\square\)

If \(L+R\) is universal, this absorption changes active topology and label depth only
by a universal amount. If the exceptional windows grow with the corridor, the lemma
gives no uniform statement.

## 5. Several parallel corridors

### Proposition 5.1 (finite corridor union)

Suppose the active graph \(A\) is attached to \(q\) pairwise vertex-disjoint exact
translation corridors of a common length \(n\), with cross sections
\[
  E^{(1)},\ldots,E^{(q)},
\]
there are no edges between interior cells of different corridors, and the union
\[
  E=\bigsqcup_{\nu=1}^qE^{(\nu)}
\]
is a cross section of the combined reduced quotient graph. Then their
union is the clone of the cross section
in the quotient graph. In particular,
\[
  |E|=\sum_{\nu=1}^q|E^{(\nu)}|.
\tag{5.1}
\]

**Proof.** The disjoint union of the chain identifications gives the cells
\[
  E_k=\bigsqcup_\nu E_k^{(\nu)}.
\]
The absence of cross-corridor interior edges verifies the chain rule for \(E_k\).
All other edges enter at \(E_0\), exit at \(E_n\), or lie in \(A\). Apply
Theorem 3.2. \(\square\)

Thus a universal number of bounded cross-section corridor types gives bounded reduced
dimension. An unbounded number of parallel corridors does not.

Corridors of unequal lengths must first be aligned by absorbing bounded length
differences into their endpoint windows or treated as separate complete blocks.
Padding them by fictitious identity cells is not an allowed graph operation unless
those cells are dynamically realized.

## 6. WAD/dynamical realization gate

For a virtual block, the graph in Theorem 3.2 must be constructed from actual
dynamics, not chosen after the fact. A valid realization must provide:

1. vertices corresponding to the finite Hubbard-tree/core transition used to define
   the KKL eigenweights, or to a proved virtual substitute for that core;
2. edge multiplicities equal to actual core pushforward occurrences;
3. a finite-horizon selected branch for every edge;
4. label-preserving conformal translation on every interior chain edge;
5. no omitted critical branch, Wave itinerary, or self-access entering an interior
   cell;
6. future-closed port incidences compatible with the graph quotient;
7. a complete WAD-to-core itinerary-incidence map, so the cloned transition is the
   same core matrix used by the KKL Value theorem;
8. bounded endpoint windows and a universal number of parallel corridor types.

Only after these are proved can Corollary 3.3 invoke the entropy gap.

### Virtual Corridor Graph Realization (`OPEN`)

Every positive-entropy virtual block admits the WAD/dynamical realization above with
universal bounds on:

\[
  |E|,
  \qquad
  L+R,
  \qquad
  q,
\]
and on every edge label used by the reduced matrix.

This is the combinatorial/dynamical core of
`H2_VIRTUAL_CLONE_REALIZATION`.

## 7. Adversarial audit

The exact clone criterion or its spectral/Value application fails under any of:

1. a critical branch from an interior \(E_k\) to the active graph;
2. two different chain successors for one labeled type;
3. an interior edge joining two parallel corridors;
4. a WAD restriction that breaks into an unrecorded itinerary;
5. entry or exit multiplicities that depend on corridor length;
6. endpoint windows with \(L+R\to\infty\);
7. an unbounded number of corridor components;
8. a reducible or trivial return graph, which blocks the irreducible spectral
   application, or failure of a separately required KKL aperiodicity hypothesis;
   periodicity alone does not invalidate literal cloning;
9. fictitious padding used to equalize unequal corridor lengths.

Each failure changes the transition graph. It cannot be charged as a geometric
additive constant before its effect on the Perron multiplier and Value is quantified.

## 8. Source boundary

KKL26 `waves-with-Misha.tex`, lines 2240--2268, defines a cross section and its clone.
The graph equivalence, endpoint-defect absorption, and finite-corridor-union results
here are internal. The checked source's printed weighted \(+\lambda^k\) clone
equation remains quarantined. This note proves graph structure only; the independent
spectral repair is `corrected_clone_theorem_derivation.md`.

No cited source constructs this exact graph from Dudko's partially invariant virtual
Julia-set hull. The terms “translation,” “corridor,” and “clone” remain distinct until
the realization gate in Section 6 is proved.
