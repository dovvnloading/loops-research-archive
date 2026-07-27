# Uniform entropy from corrected bounded-complexity clones

## 1. Status

KKL states a complete-block asymptotic for one fixed cross-section cloning datum.
The checked preprint snapshot has a false \(+\lambda^k\) finite-\(n\) recurrence;
see `kkl_transfer_orientation_audit.md`, Section 6. The source recurrence is not
imported. `corrected_clone_theorem_derivation.md` instead derives, directly from the
literal clone, the exact negative-weight equation
\[
  \rho(H(\lambda_n))=\lambda_n^n,
  \qquad
  H(t)=\sum_k t^{-k}R_k.
\tag{1.1}
\]
That repair and its two independent adversarial audits are the foundation used here.

It proves:

1. every irreducible non-permutation integer transition graph of dimension at most
   \(d\) has the gap \(\rho\ge2^{1/d}\);
2. every corrected literal clone with gate dimension and first-return depth bounded
   by \(d,N\), and common delay \(n>N\), has the period-independent total multiplier
   \(\lambda_n^n>2^{1/(2d)}\);
3. in the bounded-total-entropy branch, bounded dimension and bounded edge-label
   depth give uniform Perron eigencone compactness;
4. without bounded reduced dimension, primitive graphs can have entropy tending to
   zero.

It does not prove which Dudko virtual corridors belong to the translation-clone
branch, or that those corridors admit such reduced clone data. That is the scoped
Virtual Clone Realization theorem in Section 7. Non-clone transfer and shear branches
are separated in `corridor_entropy_shear_dichotomy.md`.

## 2. Corrected reduced clone data

A **corrected reduced clone datum**
\[
  \mathfrak C=((R_k)_{k=2}^{K},n)
\]
consists of:

1. nonnegative integer matrices \(R_k\in M_m(\mathbb Z_{\ge0})\), where
   \(R_k(i,j)\) counts first-return edge-occurrence walks of length \(k\);
2. the unweighted return matrix
   \[
     R=\sum_{k=2}^{K}R_k,
   \tag{2.1}
   \]
   which is irreducible and not a permutation matrix;
3. universal bounds \(m\le d\) and \(K\le N\);
4. a common literal clone delay \(n>N\);
5. the negative-weight return family
   \[
     H(t)=\sum_{k=2}^{K}t^{-k}R_k;
   \tag{2.2}
   \]
6. a number \(\lambda_{\mathfrak C}>1\) satisfying its own exact equation
   \[
     \rho(H(\lambda_{\mathfrak C}))
     =
     \lambda_{\mathfrak C}^{\,n}.
   \tag{2.3}
   \]

For a strongly connected literal cross-section clone with no gate-to-gate edge,
Items 1, 5, and 6 are proved in `corrected_clone_theorem_derivation.md`. They remain
hypotheses for an abstract virtual corridor until its entire typed
edge-occurrence graph has been realized. Side edges, unequal delays, omitted
multiplicities, or relabeled return lengths change (2.3).

For \(t\ge1\),
\[
  t^{-K}R\le H(t)\le t^{-2}R\le R.
\tag{2.4}
\]

## 3. Explicit bounded-dimension entropy gap

### Theorem 3.1 (irreducible integer entropy gap)

Let \(R\) be an irreducible nonnegative integer matrix of dimension
\(1\le m\le d\), and suppose \(R\) is not a permutation matrix. Then
\[
  \rho(R)\ge
  g_d:=2^{1/d}>1.
\tag{3.1}
\]

**Proof.** Regard \(R\) as the adjacency matrix of a directed multigraph, counting
edge occurrences. It is strongly connected.

If \(m=1\), then \(R=[q]\) with integer \(q\ge2\), so
\(\rho(R)=q\ge2=g_1\).

Assume \(m>1\). If every vertex had exactly one outgoing edge occurrence, strong
connectivity would make \(R\) the permutation matrix of one directed cycle. Hence
some vertex \(v\) has two distinct outgoing edge occurrences \(e_1,e_2\).

For \(i=1,2\), choose a simple directed path from the endpoint of \(e_i\) back to
\(v\). Strong connectivity gives one of length at most \(m-1\). Adjoining \(e_i\)
produces two distinct closed walks \(\gamma_i\) based at \(v\), of lengths
\[
  1\le\ell_i\le m.
\]
Choose each return path shortest. The resulting loops first return to \(v\), and
their first edge occurrences differ, so concatenations are uniquely parsed at visits
to \(v\). The \(2^r\) binary concatenations of \(r\) loops have at most \(r+1\)
possible lengths, all at most \(rm\). Hence some \(L_r\le rm\) satisfies
\[
  (R^{L_r})_{vv}\ge\frac{2^r}{r+1}.
\]
Repeating those \(L_r\)-walks and applying the spectral-radius formula gives
\[
  \rho(R)
  \ge
  \left(\frac{2^r}{r+1}\right)^{1/L_r}
  \ge
  \left(\frac{2^r}{r+1}\right)^{1/(rm)}.
\]
Letting \(r\to\infty\) yields
\(\rho(R)\ge2^{1/m}\ge2^{1/d}\).
\(\square\)

The exponent \(1/d\) is sharp: a directed \(d\)-cycle with one doubled edge has
\(R^d=2I\). Its importance here is independence from the graph, edge
multiplicities, clone length, and satellite period.

## 4. Uniform total contraction for corrected clone templates

### Theorem 4.1 (corrected bounded-complexity clone contraction)

Let \(\mathfrak C=((R_k),n)\) be a corrected reduced clone datum. Put
\[
  q_{\mathfrak C}:=\lambda_{\mathfrak C}^{\,n}.
\]
Then
\[
  q_{\mathfrak C}
  \ge
  \rho(R)^{\,n/(n+K)}
  \ge
  2^{\,n/[d(n+K)]}
  >
  2^{1/(2d)}.
\tag{4.1}
\]
Consequently, suppose the datum is the core transition of a source-licensed KKL
primitive block and the actual outgoing WAD satisfies
\[
  Y\le (f^r)^*X+E
\tag{4.2}
\]
coefficientwise for some pullback exponent \(r\ge n\), where \(n\) is the literal
clone delay. Then
\[
  V_{\mathfrak C}(Y)
  \le
  2^{-1/(2d)}V_{\mathfrak C}(X)
  +V_{\mathfrak C}(E).
\tag{4.3}
\]

**Proof.** Equations (2.3)--(2.4) and Perron monotonicity give
\[
  q_{\mathfrak C}
  \ge
  \lambda_{\mathfrak C}^{-K}\rho(R)
  =
  q_{\mathfrak C}^{-K/n}\rho(R).
\]
Thus \(q_{\mathfrak C}\ge\rho(R)^{n/(n+K)}\). By monotonicity, linearity, the KKL
Value theorem, \(r\ge n\), and \(\lambda_{\mathfrak C}>1\),
\[
  V_{\mathfrak C}(Y)
  \le
  \lambda_{\mathfrak C}^{-r}V_{\mathfrak C}(X)
  +V_{\mathfrak C}(E)
  \le
  q_{\mathfrak C}^{-1}V_{\mathfrak C}(X)
  +V_{\mathfrak C}(E)
  \le
  2^{-1/(2d)}V_{\mathfrak C}(X)
  +V_{\mathfrak C}(E).
\]
\(\square\)

Thus exact clone realization, bounded gate dimension, bounded first-return depth,
delay \(n>N\), and an actual WAD pullback exponent \(r\ge n\) are sufficient.
Bounded dimension alone is not: negative return weights make the depth bound
indispensable. A graph delay may not be substituted for a shorter pullback exponent.
Endpoint travel making \(r>n\) only strengthens the contraction.

### Theorem 4.2 (entrywise perturbation margin)

Let \(H(t)\) be the corrected reference family and let \(\widetilde H(t)\) be an
actual nonnegative reduced transition. Suppose, at its own root
\(\widetilde\lambda>1\),
\[
  \widetilde H(\widetilde\lambda)
  \ge
  (1-\epsilon)H(\widetilde\lambda)
  \quad\text{entrywise},
  \qquad
  0\le\epsilon<1.
\tag{4.3}
\]
Suppose the actual family satisfies its own corrected equation
\[
  \rho(\widetilde H(\widetilde\lambda))
  =
  \widetilde\lambda^{\,n}.
\tag{4.4}
\]
Writing \(\widetilde q=\widetilde\lambda^n\), one has
\[
  \widetilde q
  \ge
  \bigl((1-\epsilon)g_d\bigr)^{n/(n+K)}.
\tag{4.5}
\]
In particular, the perturbed complete block still contracts Value strictly whenever
\[
  \epsilon<1-g_d^{-1}
  =
  1-2^{-1/d}.
\tag{4.6}
\]
For \(n>N\), its homogeneous factor is strictly smaller than
\[
  \bigl((1-\epsilon)g_d\bigr)^{-1/2}.
\tag{4.7}
\]
Here the Value conclusion is asserted only when
\(\widetilde\lambda\) is the core eigenvalue of a source-licensed KKL block.

**Proof.** Perron monotonicity and homogeneity give
\[
  \widetilde q
  \ge
  (1-\epsilon)\rho(H(\widetilde\lambda))
  \ge
  (1-\epsilon)\widetilde\lambda^{-K}\rho(R).
\]
Rearranging proves (4.5); Theorem 3.1 and \(n>N\) give (4.7). Under
(4.6), the base of the power is greater than one. \(\square\)

The tolerance in (4.6) deteriorates like \(d^{-1}\). Thus “small perturbation” must
be measured after reduced dimension is fixed; no dimension-free loss can be hidden
in this argument.

An unweighted comparison only at \(t=1\) is insufficient because changed return
lengths are penalized at \(\widetilde\lambda\). One-sided lower domination also does
not give eigencone compactness: arbitrarily large extra multiplicities can make
Perron-coordinate ratios diverge. The bounded-entropy theorem below applies to exact
data; a perturbed use additionally needs an upper actual multiplier or transition
bound.

## 5. Bounded-entropy eigencone compactness

The contraction factor alone does not compare Value with response or corridor error.
That comparison also needs control of the Perron eigenweights.

### Lemma 5.1 (integer entry bound)

Let \(R\) be irreducible, integral, and \(m\times m\), with \(m\le d\). If
\[
  \rho(R)\le H,
\]
then every entry satisfies
\[
  R_{ij}\le H^d.
\tag{5.1}
\]

**Proof.** If \(R_{ij}>0\), choose a simple directed path from \(j\) back to \(i\) of
length \(r\le m-1\). Fixing that return path and choosing any of the \(R_{ij}\) edge
occurrences from \(i\) to \(j\) gives \(R_{ij}\) closed walks of length
\(q=r+1\le m\). Concatenating them gives at least \(R_{ij}^s\) closed walks of length
\(sq\), hence
\[
  \rho(R)\ge R_{ij}^{1/q}.
\]
Therefore
\[
  R_{ij}\le\rho(R)^q\le H^m\le H^d.
\]
Zero entries already satisfy (5.1). \(\square\)

### Theorem 5.2 (bounded-entropy reduced eigencone)

Fix \(d,N<\infty\) and \(H>1\). Consider all corrected reduced clone data satisfying
\[
  \dim R\le d,
  \qquad
  \rho(R)\le H,
  \qquad
  n\ge N.
\tag{5.2}
\]
Then:

1. the total multiplier obeys
   \[
     \rho(R)^{n/(n+K)}
     \le
     \lambda_{\mathfrak C}^{\,n}
     \le
     H;
   \tag{5.3}
   \]
2. every nonzero entry of \(H(\lambda_{\mathfrak C})\) lies in
   \([H^{-1},H^d]\);
3. the normalized left and right Perron eigenvectors of
   \(H(\lambda_{\mathfrak C})\) have coordinate ratios bounded explicitly by
   \[
     H^{2(d-1)}.
   \tag{5.4}
   \]

**Proof.** The lower bound in (5.3) is the first inequality in Theorem 4.1.
Negative weights give
\[
  H(\lambda_{\mathfrak C})\le R,
\]
so \(q:=\lambda_{\mathfrak C}^n\le\rho(R)\le H\). Since \(n\ge N\),
\[
  \lambda_{\mathfrak C}^{\,N}\le H
\tag{5.5}
\]
and every retained path weight is at least
\(\lambda_{\mathfrak C}^{-N}\ge H^{-1}\). Lemma 5.1 gives
\(R_{ij}\le H^d\), proving Item 2.

Let \(x>0\) satisfy \(H(\lambda_{\mathfrak C})x=qx\). On every support edge
\(i\to j\),
\[
  H(\lambda_{\mathfrak C})_{ij}x_j\le qx_i,
\]
so \(x_j/x_i\le H^2\). Any two vertices are connected by a simple support path
of length at most \(d-1\), which proves (5.4). Apply the same argument to the
transpose for the left ray. \(\square\)

If the full cloned eigenvectors along the corridor are obtained from the reduced
cross-section eigenvectors by powers of \(\lambda_{\mathfrak C}\), as in the exact
clone recurrence, (5.3) bounds the layer factor by \(H\). Combined with (5.4), all
coordinate ratios on the union of the clone layers are bounded by
\(H^{2(d-1)+1}\). Thus the bounded branch has uniform left/right eigenweight
distortion on the literal clone layers. Additional active vertices require their own
realization bound.

For WAD supports with uniformly bounded Hubbard-tree intersection complexity, KKL's
Value formula then compares Value and total WAD weight with constants depending only
on the declared bounds. This last comparison still requires the exact source support
hypotheses; eigencone compactness alone does not bound arbitrary intersection length.

## 6. Entropy/eigencone dichotomy

Fix \(H>1\). Every corrected reduced clone datum lies in exactly one of:

1. **bounded reduced entropy**
   \[
     \rho(R)\le H,
   \]
   where Theorem 5.2 gives eigencone compactness after bounded label depth;
2. **large reduced entropy**
   \[
     \rho(R)>H,
   \]
   where
   \[
     \lambda_{\mathfrak C}^{-n}
     <
     H^{-1/2}.
\tag{6.1}
   \]

The second branch has arbitrarily strong homogeneous contraction as \(H\) grows, but
this does not automatically pay an error measured in a different coordinate. A proof
must still bound the outgoing Value of the error before using (6.1).

## 7. Virtual Clone Realization theorem

### Virtual Clone Realization (`OPEN`)

For every virtual corridor assigned to the translation-clone branch, construct a
corrected reduced clone datum and a source-licensed WAD model such that:

1. the reduced cross-section dimension is at most a universal \(d\);
2. the actual maximum first-return length \(K\le N\) is universal after
   complete-block grouping, and the common delay satisfies \(n>N\);
3. the return matrix is irreducible and non-permutation, while any separate KKL
   aperiodicity hypothesis for the full core is also proved;
4. the full core transition satisfies the exact negative-weight clone equation
   (2.3), or the actual weighted retained transition satisfies (4.3)--(4.6) at
   its own root;
5. the finite-horizon correspondence realizes every cloned edge and every WAD
   restriction itinerary used by the Value proof;
6. the future-closed port and Value-feature states identify the same support
   transition;
7. bounded intersection complexity holds in the bounded-entropy branch;
8. all surface, localization, and peripheral errors have outgoing Value bounded below
   the contraction margin, with the exact future discount.

`corridor_clone_criterion.md`, Theorem 3.2, proves the abstract finite-graph doorway:
an exact translation corridor is a clone if and only if its distinguished interior
edges and reduced quotient satisfy the stated edge-multiplicity and cross-section
conditions. Its endpoint-defect lemma also absorbs universally bounded entry and exit
windows. It does **not** derive those hypotheses from a virtual hull.

Thus Items 1--4 still require the Virtual Corridor Graph Realization theorem in that
note: construct the actual finite-horizon Hubbard/core transition multigraph, prove
the complete WAD-to-core itinerary incidence and that no critical or immersion branch
is omitted, and establish universal cross-section, label, endpoint-window, and
parallel-corridor bounds. Items 5--8 are the analytic access and error realization.
Calling a long corridor “translation-like” does not establish any of them.

This is no longer asserted as the only virtual branch.
`corridor_entropy_shear_dichotomy.md` proves that nonzero irreducible
non-permutation **closed or canonically framed return endomorphisms** of bounded
dimension have their own uniform entropy gap. Its nonexpanding branch includes
transient/nilpotent extinction as well as recurrent common-flag shear. The open
Virtual Corridor Transfer Trichotomy must prove return closure and route all of
those branches before this clone theorem is invoked.

## 8. Necessity of reduced-complexity control

### Proposition 8.1 (unbounded dimension destroys the entropy gap)

There is a sequence of primitive \(d\times d\) integer matrices \(A_d\) with
\[
  \rho(A_d)\downarrow1.
\tag{8.1}
\]

**Proof.** Let \(A_d\) be the adjacency matrix of a directed \(d\)-cycle with one
additional self-loop at one vertex. The graph is strongly connected and aperiodic,
so \(A_d\) is primitive. Its Perron root \(\rho_d>1\) satisfies
\[
  \rho_d^d=\rho_d^{d-1}+1,
\qquad
  \rho_d-1=\rho_d^{-(d-1)}.
\tag{8.2}
\]
If a subsequence had \(\rho_d\ge1+\epsilon\), the right side of (8.2) would tend to
zero while the left side remained at least \(\epsilon\), a contradiction. Hence
\(\rho_d\to1\). \(\square\)

Thus a universal entropy factor requires bounded reduced dimension, a direct entropy
lower bound, or a different acceleration. Raw corridor length may be unbounded; the
point is to bound the **reduced cross section**, not the full cloned graph.

## 9. Adversarial audit

The reduction fails if:

1. the virtual quotient has reduced dimension \(d_B\to\infty\);
2. its return graph is reducible or a cycle permutation, or the full KKL core lacks
   its separately required aperiodicity certificate;
3. the declared negative-weight clone equation ignores a critical branch, an
   immersion itinerary, or an edge occurrence;
4. the actual return depth \(K_B\) is unbounded or the grouped delay does not satisfy
   \(n>K_B\);
5. a terminal Schur response is substituted for the lifted WAD transition without
   the fiber-observability audit;
6. the right Perron vector is controlled but the left eigenweight used by KKL Value is
   not;
7. bounded eigenweights are claimed to control arcs of unbounded Hubbard-tree
   intersection length;
8. the large-entropy contraction is used to absorb an error before that error is
   converted to outgoing Value units;
9. an unweighted or wrong-root perturbation comparison is substituted for (4.3);
10. one-sided lower perturbation domination is used as if it implied eigencone
    compactness.

## 10. Source boundary

KKL26 `waves-with-Misha.tex`, lines 2236--2318, states a fixed-cross-section clone
construction and the limits
\(\lambda_n\to1\) and \(\lambda_n^n\to h(1)>1\). The same passage's displayed
finite-\(n\) equation is false under its literal graph definitions; the explicit
counterexample is in `kkl_transfer_orientation_audit.md`, Section 6.1. The project
does not repair that attribution. It independently proves the corrected
\(t^{-k}\) equation, fixed-template limits, both typed gate-eigenvector limits, and
the quantitative family bound in `corrected_clone_theorem_derivation.md`.
KKL `value1.tex`, lines 6--20 and 103--111, supplies Value monotonicity and pullback
contraction in the primitive periodically repelling \(\psi\)-ql setting.

The gap \(2^{1/d}\), corrected variable-template Theorem 4.1, bounded-entropy
eigencone theorem, entropy/eigencone dichotomy, and unbounded-dimension
counterexample are internal results. They repair the finite graph theorem, not the
printed KKL proof and not KKL's dynamical hypotheses for virtual corridors.
