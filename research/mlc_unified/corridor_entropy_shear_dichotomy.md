# Corridor entropy, translation, and shear

## 1. Status

The exact clone certificate covers corridors whose interior core transition is
bijective after label transport. A virtual bounded-type corridor need not be known to
have that form. This note proves the finite-state alternatives for a homogeneous
**framed endomorphism**. An open layer-to-layer transfer has no intrinsic spectral
radius until its endpoint frame is fixed.

1. an irreducible zero-entropy layer is a permutation cycle and therefore a
   translation after relabeling;
2. an irreducible non-permutation layer has a dimension-controlled entropy gap;
3. every remaining nonexpanding non-translation endomorphism is reducible and has a
   transient-extinction or feed-forward polynomial-shear structure.

The third branch is the precise obstruction to a naive
"exact clone or positive entropy" dichotomy. Its dynamical realization and
pseudo-Siegel calibration remain open.

## 2. Layered core transfers

Let \(E_0,\ldots,E_n\) be equally sized finite state sets, with
\[
  |E_k|=d.
\]
Assume every interior core edge goes from \(E_k\) to \(E_{k+1}\). After choosing
labels, its edge multiplicities are a nonnegative integer matrix
\[
  B_k\in M_d(\mathbb Z_{\ge0}).
\]
We use the source-column convention throughout:
\[
  (B_k)_{ij}
  =
  \#\{\text{edges from source }j\in E_k
        \text{ to target }i\in E_{k+1}\}.
\tag{2.1}
\]
Thus column vectors evolve by \(x_{k+1}=B_kx_k\), and the chronological product of
\(B_0,\ldots,B_{m-1}\) is \(B_{m-1}\cdots B_0\).
This is a core/Hubbard transition model. It is not a WAD response matrix. To enter a
Value proof it needs a separate source-faithful WAD-to-core itinerary incidence.

An individual \(B_k:\mathbb R^{E_k}\to\mathbb R^{E_{k+1}}\) is an open transfer.
Its spectral radius depends on an identification of \(E_{k+1}\) with \(E_k\).
Spectral language below therefore applies only to an endomorphism with a declared
source-licensed endpoint identification, most safely a closed return to the same
framed state.

### Lemma 2.1 (permutation cocycles have an identity interior gauge)

If every \(B_k\) is a permutation matrix, then there are labelings of the layers in
which every \(B_k\) is the identity. Hence the layered **interior cocycle** is
deterministic label-preserving transport.

**Proof.** Set \(Q_0=I\) and define permutation matrices recursively by
\[
  Q_{k+1}=B_kQ_k.
\]
Changing the labels of \(E_k\) by \(Q_k\) changes the \(k\)-th transfer to
\[
  Q_{k+1}^{-1}B_kQ_k=I.
\]
Thus every label has exactly one label-preserving successor at every layer.
\(\square\)

This does not imply an exact clone corridor. Side edges, entry/exit multiplicities,
the cross-section property, critical/access data, and WAD incidence still require
the hypotheses of `corridor_clone_criterion.md`. Geometry may also vary between the
cells.

## 3. Irreducible layers: translation or uniform entropy

We use (2.1): the \(j\)-th column lists outgoing edge multiplicities from state
\(j\).

### Theorem 3.1 (irreducible integer entropy dichotomy)

Let \(B\) be a **nonzero** irreducible nonnegative integer \(d\times d\) matrix.
Exactly one of the following holds:

1. \(B\) is the permutation matrix of one directed cycle and
   \(\rho(B)=1\);
2. \(B\) is not a permutation matrix and
   \[
     \rho(B)\ge 2^{1/d}>1.
   \tag{3.1}
   \]

**Proof.** Irreducibility means the directed multigraph is strongly connected.
If every vertex has exactly one outgoing edge, finiteness and strong connectivity
force the graph to be one directed cycle, proving Item 1.

Otherwise some source column \(v\) has two distinct outgoing edges, counting
multiplicity.
Follow each edge by a shortest return path to \(v\). This produces two
first-return closed walks \(C_1,C_2\), each of length at most \(d\). Their first
edge occurrences differ, so binary concatenations are uniquely parsed at visits to
\(v\). The \(2^r\) concatenations of \(r\) loops have at most \(r+1\) possible
lengths, all at most \(rd\). Hence some \(L_r\le rd\) satisfies
\[
  (B^{L_r})_{vv}\ge\frac{2^r}{r+1}.
\]
Repeating those walks and using the spectral-radius formula gives
\[
  \rho(B)
  \ge
  \left(\frac{2^r}{r+1}\right)^{1/L_r}
  \ge
  \left(\frac{2^r}{r+1}\right)^{1/(rd)}.
\]
Letting \(r\to\infty\) proves \(\rho(B)\ge2^{1/d}\).
\(\square\)

Unlike `virtual_clone_entropy.md`, Theorem 3.1 does not require aperiodicity. It is a
local transfer-entropy statement, not yet a KKL Value contraction theorem.

### Corollary 3.2

A homogeneous irreducible **framed return endomorphism** of bounded dimension has
either:

- deterministic zero-entropy transport, removable by the label gauge of Lemma 2.1;
  or
- a universal positive core-entropy gap.

If a grouped branching window is the source-licensed primitive core transition of a
KKL Value block, (3.1) gives the homogeneous contraction
\[
  V_{\rm out}
  \le
  2^{-1/d}V_{\rm in}
  +V_{\rm out}(\text{error}).
\tag{3.2}
\]

The source-licensed and primitive qualifications are essential. Spectral growth of an
abstract transfer does not by itself construct the \(\psi\)-ql pullback or its Value.

## 4. Reducible nonexpansion is extinction or polynomial shear

### Theorem 4.1 (Frobenius shear normal form)

Let \(B\) be a nonnegative integer matrix with
\[
  \rho(B)\le1.
\]
After a simultaneous permutation of rows and columns, \(B\) is block upper triangular
and every diagonal strongly connected block is either:

1. a directed-cycle permutation matrix; or
2. a \(1\times1\) zero block.

Consequently, after raising \(B\) to a common multiple of the cycle lengths, its
recurrent diagonal action is the identity and every non-permutation contribution is
feed-forward through the acyclic condensation graph. Powers of \(B\) grow at most
polynomially, of degree at most the number of strongly connected components minus
one. If there is no recurrent diagonal block, \(B\) is nilpotent.

**Proof.** Put the directed graph of \(B\) in Frobenius normal form, ordered by its
acyclic condensation graph. A cyclic irreducible diagonal block is nonzero and has
spectral radius at most \(\rho(B)\le1\). By Theorem 3.1 it is a directed-cycle
permutation block. An acyclic singleton component contributes a \(1\times1\) zero
block.

It remains to include the transient blocks in the growth estimate. An entry of
\(B^m\) is the weighted count of length-\(m\) directed walks. A walk follows a path
in the condensation DAG, so it makes at most \(c-1\) strict component transitions
when there are \(c\) components. Inside a cycle component, motion is deterministic
and periodic; inside a zero component, no positive residence is possible. For each
of the finitely many component paths, entry/exit vertices, and intercomponent edge
choices, the walk is determined by distributing at most \(m\) residence steps among
at most \(c\) cycle components. The number of such distributions is
\(O(m^{c-1})\). Summing the finitely many weighted choices gives
\[
  (B^m)_{ij}=O_B(m^{c-1})
\]
for every \(i,j\). If there is no cycle component, every walk has fewer than \(c\)
edges, so \(B^c=0\). \(\square\)

The coefficient in the polynomial bound is not universal without a bound on
off-diagonal edge multiplicities.

### Example 4.2 (the shear obstruction)

For
\[
  S=
  \begin{pmatrix}
    1&1\\
    0&1
  \end{pmatrix},
\qquad
  S^m=
  \begin{pmatrix}
    1&m\\
    0&1
  \end{pmatrix}.
\tag{4.1}
\]
There is one local transfer type and \(\rho(S)=1\), but the transport is not a
permutation and cannot be made into the identity by relabeling. Its complexity grows
linearly rather than exponentially.

Thus bounded local type count does not imply exact cloning, and zero exponential
entropy does not imply bounded transport error.

## 5. Defect decomposition

For a nonstationary layered corridor \(B_0,\ldots,B_{n-1}\), call \(k\) a **defect**
when \(B_k\) is not a permutation matrix.

### Lemma 5.1 (maximal pure runs)

If there are \(q\) defects, the complement of the defect layers is the union of at
most \(q+1\) maximal permutation runs. Each run has an identity interior cocycle
after label transport.

**Proof.** Removing \(q\) indices from a line leaves at most \(q+1\) intervals.
Apply Lemma 2.1 on each interval. \(\square\)

If \(q\) is universally bounded, the defects and their bounded windows can be treated
as a bounded number of active transition blocks. If \(q\to\infty\), bounded local
type count alone gives no bounded clone decomposition.

The constant shear sequence
\[
  B_k=S
\]
has one local type and \(q=n\), yet has neither a positive entropy gap nor a pure
translation run. This is an exact finite-state counterexample to the proposed
dichotomy unless a third, regularized shear branch is present.

## 6. Refined virtual transfer trichotomy

### Virtual Corridor Transfer Trichotomy (`OPEN`)

Assume the exact memory-safe compilation and source-faithful follower required by
`H2_VIRTUAL_SUPPORT_AUTOMATON`: counter/stack effects are represented by the
restricted augmented machine, every eligible pumped repetition acts identically on
the relevant reachable memory fiber, and every numerical or proof-used loop emission
is retained. Then every virtual-Molecule corridor admits a universally
bounded-dimensional, finite-horizon, source-faithful layered core model such that
every complete entropy-clock subblock carries a source-licensed endpoint frame and
belongs to one of:

1. **translation:** all interior transfers are permutations, Lemma 2.1 gives an
   identity interior gauge, and the independent purity, gate, source, and WAD clauses
   of the finite-state clone certificate all hold;
2. **positive entropy:** a uniformly bounded closed or canonically framed grouped
   return has a source-licensed primitive core transition satisfying (3.1), with its
   WAD Value and response errors controlled in outgoing units;
3. **nonexpanding transfer:** the framed complete transition has \(\rho\le1\) and
   the Frobenius form of Theorem 4.1. A purely transient block is routed to
   extinction; feed-forward shear coordinates are absorbed by a
   pseudo-Siegel/sectorial regularization or retained in a calibrated finite shear
   state.

For a nonstationary product, the theorem must additionally control changes of the
Frobenius flag. A sequence of individually reducible zero-entropy matrices can have
positive product entropy. For example,
\[
  U=
  \begin{pmatrix}1&1\\0&1\end{pmatrix},
  \qquad
  L=
  \begin{pmatrix}1&0\\1&1\end{pmatrix}
\]
both have spectral radius \(1\), while
\[
  LU=
  \begin{pmatrix}1&1\\1&2\end{pmatrix}
\]
has Perron root \((3+\sqrt5)/2>1\). A sequence of changing flags need not share one
triangular gauge. Therefore classifying each \(B_k\) separately is insufficient.
Moreover, a target relabeling of an open transfer can change its spectral radius.
Only the framed complete return, not an unframed layer, is eligible for this
classification.

This trichotomy is a candidate replacement if `FC2` corridor purity fails. It does
not weaken the target theorem: it names the additional invariant required by the
exact shear counterexample.

## 7. Adversarial audit

Any realization must survive:

1. a constant unipotent shear such as (4.1);
2. an unbounded number of isolated non-permutation defects;
3. permutation transfers with changing labels, which are not genuine defects;
4. reducible matrices whose invariant flags change from cell to cell;
5. a branching abstract transfer that is not the KKL source core;
6. a positive spectral gap whose outgoing Value error consumes the entire margin;
7. a shear coefficient growing with satellite period despite fixed matrix dimension;
8. fake layer compression that changes edge time and therefore changes the entropy
   normalization;
9. a transient nilpotent transfer incorrectly called branching;
10. an open transfer whose apparent entropy disappears after an endpoint relabeling.

The shear branch must be regularized or represented. It cannot be discarded as an
additive \(O(1)\) topological error because (4.1) accumulates without exponential
entropy.
