# Corrected fixed-cross-section clone spectral theorem

## 1. Status and result

This note derives the spectral equation directly from the literal directed-graph
clone
\[
  E_0\longrightarrow E_1\longrightarrow\cdots\longrightarrow E_n.
\]
It does not use the inconsistent finite-\(n\) equation in the checked KKL
appendix.

For a fixed finite cross section, the correct reduced row-source return matrix is
\[
  H(t)
  =
  t^{-1}D(tI-Q)^{-1}C
  =
  \sum_{j\ge 0}t^{-(j+2)}DQ^jC.
\tag{1.1}
\]
Thus a first-return directed walk of length \(k\) has weight \(t^{-k}\), not
\(t^k\).
If \(\lambda_n\) is the Perron root of the length-\(n\) clone, then
\[
  \boxed{\rho(H(\lambda_n))=\lambda_n^n.}
\tag{1.2}
\]
Under the hypotheses below,
\[
  \lambda_n\longrightarrow 1,
  \qquad
  \lambda_n^n\longrightarrow \rho(H(1))>1.
\tag{1.3}
\]
If the base is primitive, \(m=|E|\le d\), and \(K\) is the actual maximum
first-return length, then the integer return graph satisfies
\(\rho(H(1))\ge2^{1/m}\) and, for every \(n>K\),
\[
  \lambda_n^n>2^{1/(2d)}.
\tag{1.4}
\]
The Perron vectors restricted to the fixed copy \(E_0\), when normalized on
\(E_0\), converge to the corresponding Perron vectors of \(H(1)\).

The proof needs irreducibility of the cloned graph and
\(\rho(H(1))>1\), but not aperiodicity of every clone. A primitive base graph is
a convenient sufficient condition for the strict inequality. It does **not**
imply that every delayed clone is primitive.

## 2. Typed graph data

Let \(G\) be a finite directed multigraph with a nonempty vertex partition
\[
  V(G)=A\sqcup E.
\tag{2.1}
\]
Assume:

1. no edge has both endpoints in \(E\);
2. \(G\) is strongly connected;
3. \(E\) is a cross section: there is an \(L<\infty\) such that every directed
   walk of length at least \(L\) meets \(E\).

Parallel edge occurrences are counted with multiplicity.

Use the **row-source** incidence convention
\[
  N_{uv}
  =
  \#\{\text{edge occurrences }u\to v\}.
\tag{2.2}
\]
With rows and columns ordered as \(A,E\), write the base incidence as
\[
  N_0=
  \begin{pmatrix}
    Q&C\\
    D&0
  \end{pmatrix},
\tag{2.3}
\]
where
\[
  Q:A\to A,\qquad
  C:A\to E,\qquad
  D:E\to A
\]
in the row-source directed-walk-counting sense. Concretely,
\[
  Q\in\mathbb Z_{\ge0}^{A\times A},\quad
  C\in\mathbb Z_{\ge0}^{A\times E},\quad
  D\in\mathbb Z_{\ge0}^{E\times A}.
\]

The cross-section hypothesis is equivalent to nilpotence of \(Q\): a directed
cycle in \(A\) can be repeated to avoid \(E\) for arbitrarily long times, while
in a finite acyclic directed graph the length of an \(A\)-only walk is bounded. If
\[
  Q^s=0,
\tag{2.4}
\]
then every first-return directed walk from \(E\) to \(E\), with no internal
vertex in
\(E\), has length at most \(s+1\). Equation (1.1) is therefore the finite
Laurent polynomial
\[
  H(t)
  =
  \sum_{j=0}^{s-1}t^{-(j+2)}DQ^jC.
\tag{2.5}
\]
The entry \(H(t)_{ef}\) is the sum of \(t^{-|\gamma|}\) over all first-return
directed walks \(\gamma:e\to f\).

The unweighted first-return incidence is
\[
  R:=H(1)=\sum_{j=0}^{s-1}DQ^jC.
\tag{2.6}
\]

### Lemma 2.1 (return irreducibility)

Under the assumptions above, \(R\) is irreducible.

**Proof.** Take \(e,f\in E\). Strong connectivity gives a directed walk from
\(e\) to \(f\). Cutting that walk at its successive visits to \(E\) expresses it
as a concatenation of first-return directed walks. These return walks give a walk
from \(e\) to \(f\) in the directed multigraph of \(R\). Thus that graph is strongly
connected. \(\square\)

## 3. Literal clone and exact reduction

For \(n\ge0\), the length-\(n\) clone \(G_n\) has vertex set
\[
  A\sqcup E_0\sqcup E_1\sqcup\cdots\sqcup E_n.
\tag{3.1}
\]
It retains the \(A\to A\) edges \(Q\), redirects the \(A\to E\) edges \(C\)
to \(A\to E_0\), redirects the \(E\to A\) edges \(D\) to \(E_n\to A\), and
adds exactly one edge
\[
  e_k\to e_{k+1}
\tag{3.2}
\]
for every \(e\in E\) and \(0\le k<n\). There are no other edges.

In row-source blocks its incidence \(N_n\) is
\[
\begin{array}{c|ccccc}
 &A&E_0&E_1&\cdots&E_n\\ \hline
A   &Q&C&0&\cdots&0\\
E_0 &0&0&I&\cdots&0\\
E_1 &0&0&0&\ddots&0\\
\vdots&\vdots&\vdots&\ddots&\ddots&I\\
E_n&D&0&0&\cdots&0 .
\end{array}
\tag{3.3}
\]
For \(n=0\), this means (2.3).

Collapsing every \(E_k\) back to \(E\) sends directed walks in \(G_n\) to
directed walks in
\(G\), while a visit to \(E\) is replaced by traversal of its chain. Conversely,
a base walk lifts by replacing each visit to \(e\in E\) with the appropriate
traversal \(e_0\to\cdots\to e_n\). If a lifted walk starts at \(e_k\), first
traverse \(e_k\to\cdots\to e_n\); if it ends at \(e_k\), stop after entering
\(e_0\) and traverse to \(e_k\). Strong connectivity of \(G\) therefore implies
strong connectivity of every \(G_n\). The clones may nevertheless be periodic.

Let \(\lambda_n>0\) be the Perron root of \(N_n\), and let
\[
  p^{(n)}
  =
  (p_A,p_0,p_1,\ldots,p_n)^{\mathsf T}>0
\]
be a right Perron vector:
\[
  N_np^{(n)}=\lambda_np^{(n)}.
\tag{3.4}
\]
Because \(N_n\) is row-source, this is a future-weight equation: the component
at a source is the sum of its target weights divided by \(\lambda_n\).

The chain rows give
\[
  p_{k+1}=\lambda_np_k,
  \qquad
  p_k=\lambda_n^kp_0.
\tag{3.5}
\]
The \(A\)-row and \(E_n\)-row equations give
\[
  (\lambda_nI-Q)p_A=Cp_0,
\tag{3.6}
\]
\[
  \lambda_np_n=Dp_A.
\tag{3.7}
\]
Since \(Q\) is nilpotent,
\[
  (\lambda_nI-Q)^{-1}
  =
  \sum_{j=0}^{s-1}\lambda_n^{-(j+1)}Q^j.
\tag{3.8}
\]
Substituting (3.5)--(3.6) into (3.7) yields
\[
  D(\lambda_nI-Q)^{-1}Cp_0
  =
  \lambda_n^{n+1}p_0.
\]
After division by \(\lambda_n\),
\[
  H(\lambda_n)p_0=\lambda_n^np_0.
\tag{3.9}
\]
Because \(p_0>0\) and \(H(\lambda_n)\) is irreducible, the eigenvalue on the
right is its Perron root. This proves (1.2).

The converse is equally important. If \(t>0\), \(u>0\), and
\[
  H(t)u=t^nu,
\tag{3.10}
\]
define
\[
  p_0=u,\qquad
  p_k=t^ku,\qquad
  p_A=(tI-Q)^{-1}Cu.
\tag{3.11}
\]
Then (3.10) verifies every block equation in (3.3), so \(N_np=tp\).
Strong connectivity makes \(p_A>0\); hence \(t\) is the Perron root of \(N_n\).
Thus (3.9) is not merely a necessary scalar identity: it is an exact typed
equivalence of positive eigenproblems.

### Theorem 3.1 (corrected fixed-cross-section clone theorem)

Assume the hypotheses of Section 2 and suppose
\[
  \rho(R)>1.
\tag{3.12}
\]
Then for every \(n\ge0\):

1. \(G_n\) is strongly connected and has a simple positive Perron root
   \(\lambda_n>1\);
2. \(\lambda_n\) is the unique \(t>1\) satisfying
   \[
     \rho(H(t))=t^n;
   \tag{3.13}
   \]
3. the exact limits are
   \[
     \lambda_n\to1,
     \qquad
     \lambda_n^n\to\rho(R)>1;
   \tag{3.14}
   \]
4. more precisely,
   \[
     n\log\lambda_n\to\log\rho(R),
     \qquad
     n(\lambda_n-1)\to\log\rho(R).
   \tag{3.15}
   \]

**Proof.** For \(t>0\), \(H(t)\) has the fixed irreducible support of \(R\).
Let
\[
  h(t):=\rho(H(t)).
\]
It is continuous. If \(t_2>t_1>0\), every return length is at least \(2\), so
\[
  H(t_2)
  \le
  \left(\frac{t_1}{t_2}\right)^2H(t_1).
\tag{3.16}
\]
Perron monotonicity gives
\[
  h(t_2)
  \le
  \left(\frac{t_1}{t_2}\right)^2h(t_1)<h(t_1).
\tag{3.17}
\]
Thus \(h\) is strictly decreasing, \(h(1)=\rho(R)>1\), and
\(h(t)\to0\) as \(t\to\infty\). Since \(t^n\) is nondecreasing, (3.13) has a
unique root \(t>1\). The equivalence (3.10)--(3.11) identifies this root with
\(\lambda_n\).

For \(n\ge1\), at the root,
\[
  1<\lambda_n^n=h(\lambda_n)\le h(1)=\rho(R).
\tag{3.18}
\]
For \(n=0\), the exact equation is instead
\(h(\lambda_0)=\lambda_0^0=1\); in particular, no strict inequality involving
\(\lambda_0^0\) is asserted. Consequently, still for \(n\ge1\),
\[
  1<\lambda_n\le\rho(R)^{1/n},
\tag{3.19}
\]
so \(\lambda_n\to1\). Continuity of \(h\) and (3.13) now give
\[
  \lambda_n^n=h(\lambda_n)\to h(1)=\rho(R).
\]
Taking logarithms proves the first limit in (3.15). Equation (3.19) gives
\(\lambda_n-1=O(n^{-1})\); hence
\[
  n\bigl((\lambda_n-1)-\log\lambda_n\bigr)
  =
  O\bigl(n(\lambda_n-1)^2\bigr)\to0,
\]
which proves the second. \(\square\)

## 4. Quantitative return entropy and finite-length gap

The condition \(\rho(R)>1\) is the exact nontrivial-return condition. The integer
structure gives a useful quantitative gap in terms of the gate dimension
\[
  m:=|E|.
\]

### Lemma 4.1 (gate-dimension entropy gap)

Let \(R\ne[0]\) be an irreducible nonnegative integer matrix of dimension \(m\).
If \(R\) is not a permutation matrix, then
\[
  \rho(R)\ge2^{1/m}.
\tag{4.1}
\]

**Proof.** The strongly connected directed multigraph of \(R\) has a vertex
\(v\) with two distinct outgoing edge occurrences
\(\epsilon_1,\epsilon_2\); otherwise every outdegree would be one and the graph
would be one directed cycle. For each \(i\), append to \(\epsilon_i\) a shortest
directed walk from its endpoint back to \(v\). The resulting closed walk
\(\gamma_i\) first returns to \(v\) at its end and has length
\[
  1\le\ell_i\le m.
\]
The two closed walks are distinct because their first edge occurrences differ.

Let \(a_L\) be the number of words in \(\gamma_1,\gamma_2\) whose concatenated
length is \(L\). First-return parsing at \(v\) makes the map from such words to
edge-occurrence walks injective, so
\[
  (R^L)_{vv}\ge a_L.
\tag{4.2}
\]
As a formal power series,
\[
  \sum_{L\ge0}a_Lz^L
  =
  \frac{1}{1-z^{\ell_1}-z^{\ell_2}}.
\tag{4.3}
\]
Let \(z_0\in(0,1)\) be the unique positive solution of
\(z_0^{\ell_1}+z_0^{\ell_2}=1\). For \(|z|<z_0\), the triangle inequality
shows
\[
  |z^{\ell_1}+z^{\ell_2}|<1,
\]
while the denominator vanishes at \(z_0\). Hence \(z_0\) is the radius of
convergence in (4.3). The Cauchy--Hadamard formula gives exponential growth
rate \(r=z_0^{-1}\), which is the unique \(r>1\) satisfying
\[
  r^{-\ell_1}+r^{-\ell_2}=1.
\tag{4.4}
\]
At \(r_0=2^{1/m}\),
\[
  r_0^{-\ell_1}+r_0^{-\ell_2}
  \ge
  2r_0^{-m}
  =
  1.
\]
The left side of (4.4) is strictly decreasing in \(r\), hence \(r\ge r_0\).
Equation (4.2) and the spectral-radius formula give
\(\rho(R)\ge r\ge2^{1/m}\). \(\square\)

### Lemma 4.2 (primitive base makes the return graph nonpermutational)

If the base incidence \(N_0\) is primitive, then \(R\) is not a permutation
matrix. Consequently,
\[
  \rho(R)\ge2^{1/m}>1.
\tag{4.5}
\]

**Proof.** Lemma 2.1 makes \(R\) irreducible. Suppose it is a permutation
matrix. Then every \(e\in E\) has exactly one first-return-walk occurrence
leaving it.

Every \(a\in A\) lies on a first-return directed walk: choose a directed walk
from some \(e\in E\) to \(a\), retain the suffix after its last visit to \(E\),
then extend from \(a\) only until the next visit to \(E\). If \(a\), or any
\(e\), had two outgoing edge occurrences, extending each occurrence to the next
visit to \(E\) would produce two distinct first-return directed walks from the
same starting element of \(E\). Hence every vertex of \(G\) has outdegree exactly
one, counting multiplicity.

A finite strongly connected graph with outdegree one at every vertex is a single
directed cycle. Because \(E\ne\varnothing\) and there are no \(E\)-to-\(E\)
edges, that cycle has length at least two. Its incidence is periodic, contradicting
primitivity of \(N_0\). Thus \(R\) is not a permutation matrix, and Lemma 4.1
proves (4.5). \(\square\)

Primitivity of the base is sufficient, not logically necessary. Theorem 3.1
continues to hold for an imprimitive strongly connected base whenever
\(\rho(R)>1\), and Lemma 4.1 then gives the same quantitative gap.

Define the actual maximum first-return length
\[
  K
  :=
  \max\{j+2:DQ^jC\ne0\}.
\tag{4.6}
\]
It is finite, satisfies \(2\le K\le s+1\), and may be smaller than a chosen
crossing bound.

### Theorem 4.3 (uniform complete-clone multiplier)

Assume \(N_0\) is primitive, \(m=|E|\le d\), and let \(K\) be (4.6). Then for
every \(n\ge1\),
\[
  \lambda_n^n
  \ge
  \rho(R)^{\,n/(n+K)}
  \ge
  2^{\,n/(m(n+K))}.
\tag{4.7}
\]
In particular, whenever \(n>K\),
\[
  \boxed{\lambda_n^n>2^{1/(2d)}.}
\tag{4.8}
\]

**Proof.** Write
\[
  H(t)=\sum_{k=2}^{K}t^{-k}R_k,
  \qquad
  R_k:=DQ^{k-2}C,
  \qquad
  R=\sum_{k=2}^{K}R_k.
\tag{4.9}
\]
For \(t\ge1\),
\[
  H(t)\ge t^{-K}R
\tag{4.10}
\]
entrywise. At \(t=\lambda_n\), Perron monotonicity and the exact clone equation
give
\[
  \lambda_n^n
  =
  \rho(H(\lambda_n))
  \ge
  \lambda_n^{-K}\rho(R).
\]
Therefore
\[
  \lambda_n^{n+K}\ge\rho(R),
\]
which yields the first inequality in (4.7). Lemmas 4.1--4.2 yield the second.
If \(n>K\), then \(n/(n+K)>1/2\), and
\[
  2^{\,n/(m(n+K))}
  >
  2^{1/(2m)}
  \ge
  2^{1/(2d)}.
\]
\(\square\)

## 5. Convergence of both typed Perron vectors

The phrase “normalize the eigenvector” is ambiguous for a graph whose number of
vertices grows with \(n\). Here the normalization must be imposed on the fixed
cross section \(E_0\). A unit norm on the whole cloned graph generally drives the
\(E_0\)-restriction to zero merely because there are \(n+1\) corridor layers.

### Theorem 5.1 (row-source right/project-left convergence)

Let \(p^{(n)}\) be the right Perron vector of the row-source matrix \(N_n\), and
normalize it by
\[
  \sum_{e\in E}(p_0^{(n)})_e=1.
\tag{5.1}
\]
Let \(u>0\) be the similarly normalized right Perron vector of \(R=H(1)\).
Then
\[
  p_0^{(n)}\longrightarrow u.
\tag{5.2}
\]
Moreover,
\[
  p_k^{(n)}=\lambda_n^kp_0^{(n)},
  \qquad
  p_A^{(n)}=(\lambda_nI-Q)^{-1}Cp_0^{(n)}.
\tag{5.3}
\]

**Proof.** Equation (3.9) makes \(p_0^{(n)}\) the normalized positive Perron
vector of \(H(\lambda_n)\). The simplex in (5.1) is compact. Any subsequential
limit \(u_*\) satisfies, by (3.14) and continuity,
\[
  Ru_*=\rho(R)u_*.
\]
Irreducibility of \(R\) makes its normalized nonnegative Perron vector unique, so
\(u_*=u\). Every subsequence has the same limit. Equations (5.3) are
(3.5)--(3.6). \(\square\)

Now transpose the incidence. The project's convention is the
**target-row/source-column** matrix
\[
  B_n:=N_n^{\mathsf T},
  \qquad
  (B_n)_{\text{target},\text{source}}
  =
  \#\{\text{source}\to\text{target}\}.
\tag{5.4}
\]
The chronological column-source action is forward on source masses. A right
Perron vector \(q^{(n)}\) of \(B_n\) is a left Perron weight for \(N_n\).

### Theorem 5.2 (project-right/row-source left convergence)

Normalize \(q^{(n)}>0\), \(B_nq^{(n)}=\lambda_nq^{(n)}\), by
\[
  \sum_{e\in E}(q_0^{(n)})_e=1.
\tag{5.5}
\]
Let \(z>0\) be the normalized right Perron vector of \(R^{\mathsf T}\).
Then
\[
  q_0^{(n)}\longrightarrow z,
\tag{5.6}
\]
and the exact clone formulas are
\[
  q_k^{(n)}=\lambda_n^{-k}q_0^{(n)},
\tag{5.7}
\]
\[
  q_A^{(n)}
  =
  \lambda_n^{-n}
  (\lambda_nI-Q^{\mathsf T})^{-1}D^{\mathsf T}q_0^{(n)}.
\tag{5.8}
\]
In particular,
\[
  H(\lambda_n)^{\mathsf T}q_0^{(n)}
  =
  \lambda_n^nq_0^{(n)}.
\tag{5.9}
\]

**Proof.** The chain columns of \(N_n\), equivalently the chain rows of \(B_n\),
give (5.7). The \(A\)-components give (5.8), and the \(E_0\)-components reduce
to (5.9). The compactness-and-uniqueness argument of Theorem 5.1, applied to
\(H(\lambda_n)^{\mathsf T}\), proves (5.6). \(\square\)

Thus transposition swaps the two limiting Perron vectors, but it does not change
the scalar equation or turn \(t^{-k}\) into \(t^k\). In the project's Value
notation, the row-source right vector in Theorem 5.1 is the project **left**
eigenweight, while Theorem 5.2 supplies the project **right** eigenweight.

## 6. Exact three-vertex regression test

Take
\[
  E=\{e\},
  \qquad
  A=\{a,b\},
\]
with edges
\[
  e\to a,\qquad
  a\to e,\qquad
  a\to b,\qquad
  b\to e.
\tag{6.1}
\]
In the ordered active basis \((a,b)\),
\[
  Q=
  \begin{pmatrix}
    0&1\\
    0&0
  \end{pmatrix},
  \qquad
  C=
  \begin{pmatrix}
    1\\
    1
  \end{pmatrix},
  \qquad
  D=
  \begin{pmatrix}
    1&0
  \end{pmatrix}.
\tag{6.2}
\]
Since \(Q^2=0\),
\[
\begin{aligned}
  H(t)
  &=
  t^{-1}D(tI-Q)^{-1}C\\
  &=
  t^{-2}+t^{-3}.
\end{aligned}
\tag{6.3}
\]
The exact clone equation is therefore
\[
  \lambda_n^n
  =
  \lambda_n^{-2}+\lambda_n^{-3},
\]
or equivalently
\[
  \boxed{\lambda_n^{n+3}=\lambda_n+1.}
\tag{6.4}
\]
This is also the characteristic equation of the literal clone at its positive
root: direct determinants for \(n=0,1,2,3,4\) give respectively
\[
  t^3-t-1,\quad
  t^4-t-1,\quad
  t^5-t-1,\quad
  t^6-t-1,\quad
  t^7-t-1.
\]
The determinant check is diagnostic; (6.4) already follows exactly from the
typed block equations.

Here
\[
  H(1)=2,
\]
so
\[
  \lambda_n\to1,
  \qquad
  \lambda_n^n\to2.
\tag{6.5}
\]

For the row-source right vector, normalize \(p_0=1\). Then
\[
  p_k=\lambda_n^k,
  \qquad
  p_A=
  \begin{pmatrix}
    \lambda_n^{-1}+\lambda_n^{-2}\\
    \lambda_n^{-1}
  \end{pmatrix}.
\tag{6.6}
\]
For the project matrix \(B_n=N_n^{\mathsf T}\), normalize its right vector by
\(q_0=1\). Then
\[
  q_k=\lambda_n^{-k},
  \qquad
  q_A=
  \begin{pmatrix}
    \lambda_n^{-(n+1)}\\
    \lambda_n^{-(n+2)}
  \end{pmatrix}.
\tag{6.7}
\]
The \(E_0\) equation for (6.7) is exactly (6.4).

The erroneous positive-weight reduction would instead use
\(t^2+t^3\) and assert
\[
  \lambda_n^n=\lambda_n^2+\lambda_n^3.
\]
Together with (6.4), this would force
\(\lambda_n^n=\lambda_n^{n+5}\), impossible for \(\lambda_n>1\).
The example therefore detects both the exponent sign and any silent confusion of
the row-source and source-column eigenvectors.

## 7. Which assumptions are actually needed?

### 7.1 Clone primitivity is not needed for this theorem

Strong connectivity is enough for a simple positive Perron root and a unique
positive Perron vector up to scale. Literal cloning preserves strong connectivity.
Aperiodicity is unnecessary for (1.2)--(1.3) and Theorems 5.1--5.2.

Moreover, a primitive base does not imply primitive clones. Let \(E=\{e\}\) be
the common gate of two otherwise disjoint directed cycles of lengths \(3\) and
\(5\). The base has period \(\gcd(3,5)=1\). The length-one clone increases both
cycle lengths to \(4\) and \(6\), so that clone has period \(2\). Any downstream
theorem requiring primitive clones must therefore add a separate delay-robust
period certificate. This issue is independent of the corrected spectral equation.

### 7.2 The strict return multiplier is needed

If \(G\) is only strongly connected, \(\rho(H(1))\) can equal \(1\). The simplest
case is the two-cycle
\[
  e\to a\to e.
\]
Every clone is one directed cycle, its Perron root is \(1\), and
\(\lambda_n^n\to1\), not a number greater than \(1\). The exact minimal
hypothesis for strict total expansion is \(\rho(H(1))>1\); primitivity of the
base is one sufficient certificate by Lemma 4.2.

### 7.3 The cross-section condition is essential

The cross-section condition makes \(Q\) nilpotent and bounds all first-return
lengths. Without it, an active directed cycle can avoid \(E\) forever. For
example, if \(Q\) has spectral radius greater than \(1\), every clone retains
that active subsystem and
\[
  \lambda_n\ge\rho(Q)>1;
\]
the conclusion \(\lambda_n\to1\) is false. A formal resolvent
\((tI-Q)^{-1}\) does not repair this at \(t=1\).

For one fixed finite graph, no numerical crossing constant is otherwise needed:
nilpotence alone makes (2.5) finite, and the reduction is exact for every
\(n\), including \(n\) below the crossing bound. A **uniform** theorem over
varying base graphs would need uniform control of at least:

1. \(|E|\) and the active dimension;
2. the nilpotence/crossing bound \(s\);
3. edge multiplicities or an equivalent compact family;
4. a certificate that the return matrix is nonpermutational (Lemma 4.1 then
   quantifies the gap when \(|E|\) is bounded);
5. a normalization and compactness condition for uniform eigenvector estimates.

The fixed-cross-section theorem alone does not supply these family-uniform
constants.

### 7.4 Fixed-template convergence is not family-uniform eigencone control

Theorems 5.1--5.2 fix \(Q,C,D\) first and then let \(n\to\infty\). Their
convergence must not be made uniform over templates with unbounded edge
multiplicities. Already at the reduced level, consider
\[
  R_M=
  \begin{pmatrix}
    1&M\\
    1&1
  \end{pmatrix},
  \qquad M\ge1.
\tag{7.1}
\]
These are positive two-dimensional integer matrices, but their normalized right
and left Perron vectors are proportional to
\[
  (\sqrt M,1)^{\mathsf T},
  \qquad
  (1,\sqrt M)^{\mathsf T},
\tag{7.2}
\]
respectively. As \(M\to\infty\), the two normalized vectors approach opposite
faces of the simplex. Thus bounded gate dimension and a uniform spectral lower
bound do not by themselves give uniform positive coordinate ratios.

The same example blocks a second invalid inference. If
\[
  J=
  \begin{pmatrix}
    1&1\\
    1&1
  \end{pmatrix},
\]
then \(R_M\ge J\) entrywise for every \(M\). This one-sided domination gives a
spectral-radius lower bound, but it gives no eigencone compactness: the ratios in
(7.2) still diverge. More generally, a retained-mass inequality of the form
\(\widetilde H\ge cH\) cannot by itself control left/right Perron distortion.
Such a conclusion needs additional upper comparability or bounded-multiplicity
and connectivity data. It does not follow from Perron monotonicity.

### 7.5 Scope of the construction

The derivation assumes:

- one common delay \(n\) on every element of \(E\);
- no \(E\)-to-\(E\) base edge;
- no side edge incident to an interior clone layer;
- exact retention of every edge occurrence and its multiplicity.

Unequal delays, direct \(E\)-to-\(E\) edges, endpoint defects, or interior side
branches change the block equations and require a different return operator.
They cannot be absorbed by changing the exponent sign.

## 8. Source-convention boundary

Let \(N_n\) denote the literal row-source incidence throughout this note. The
project matrix is
\[
  B_n=N_n^{\mathsf T}.
\]
Consequently:

| object | row-source \(N_n\) | project source-column \(B_n\) |
|---|---|---|
| entry | row = source, column = target | row = target, column = source |
| chain right-vector ratio | \(p_k=\lambda_n^kp_0\) | \(q_k=\lambda_n^{-k}q_0\) |
| reduced operator on \(E_0\) | \(H(\lambda_n)\) | \(H(\lambda_n)^{\mathsf T}\) |
| limiting \(E_0\) vector | right PF vector of \(H(1)\) | right PF vector of \(H(1)^{\mathsf T}\) |

Both conventions give the same Perron root and the same negative return-walk
weights \(t^{-k}\). Transposition reverses matrix orientation; it does not reverse
the sign of a delay exponent.

This theorem repairs the fixed finite graph calculation only. A dynamical use
still has to prove that the proposed graph is the complete core incidence, that
its corridor is a literal clone with no omitted branch, and that its left/right
weights enter the Value functional in the source-licensed roles.
