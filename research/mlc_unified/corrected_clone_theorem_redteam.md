# Red-team audit of the corrected fixed-cross-section clone theorem

## 1. Verdict

The negative-exponent first-return operator is the correct one for the literal
clone
\[
  E_0\longrightarrow E_1\longrightarrow\cdots\longrightarrow E_n.
\]
With row-source incidence \(N_n\), the exact reduced equation is
\[
  H(\lambda_n)p_0=\lambda_n^n p_0,
  \qquad
  H(t)=\sum_{\gamma:E\rightsquigarrow E}
  t^{-|\gamma|}[\gamma],
\tag{1.1}
\]
where the sum is over first-return edge-occurrence paths in the un-cloned graph.
For the project source-column incidence \(B_n=N_n^{\mathsf T}\), the reduced
equation is the transpose
\[
  H(\lambda_n)^{\mathsf T}q_0=\lambda_n^n q_0.
\tag{1.2}
\]
Transposition does not change the exponent sign.

For one **fixed** finite graph, the following conclusions survive the audit:
\[
  \lambda_n\to1,
  \qquad
  \lambda_n^n\to\rho(H(1))>1,
\tag{1.3}
\]
provided the literal clone is irreducible, the gate is a genuine cross section,
and \(\rho(H(1))>1\). Normalized Perron vectors restricted to \(E_0\) converge to
the corresponding Perron vectors of \(H(1)\) and \(H(1)^{\mathsf T}\).

There is also a family-uniform lower bound stronger than the previously used
\(d^{-2}\)-exponent estimate. Let \(m=|E|\le d\), let every first-return length
be at most \(K\le N\), and assume \(\rho(H(1))>1\). For \(n\ge1\), put
\(\mu_n=\lambda_n^n\). Then
\[
  \boxed{
  \mu_n
  \ge
  \rho(H(1))^{\,n/(n+K)}
  \ge
  2^{\,n/[d(n+K)]}.
  }
\tag{1.4}
\]
Consequently, if \(n>N\),
\[
  \boxed{
  \lambda_n^n
  >
  2^{1/(2d)}.
  }
\tag{1.5}
\]
The non-strict uniform form
\(\lambda_n^n\ge2^{1/(2d)}\) is therefore valid. The integer-multigraph
hypothesis and the strict-return condition are essential.

The audit found, and the canonical derivation repaired, one boundary defect:
\(1<\lambda_n^n\) is false at \(n=0\), since \(\lambda_0^0=1\). The theorem may
include \(n=0\) in the spectral equation and \(\lambda_0>1\), but every strict
total-multiplier inequality starts at \(n\ge1\).

## 2. Exact typed setup

To avoid using \(A\) both for a graph and for its active vertices, let \(G\) be a
finite directed multigraph and write
\[
  V(G)=F\sqcup E,
\]
where \(E\ne\varnothing\) is the gate. Count parallel edge occurrences
separately. Assume:

1. there is no \(E\)-to-\(E\) edge;
2. \(G\) is strongly connected;
3. \(E\) is a cross section in the **walk** sense: some \(N\) has the property
   that every directed walk of \(N-1\) edges contains a vertex of \(E\).

The word “walk” is important. If “path” means “simple path,” the condition does
not exclude an active directed cycle and does not imply the needed nilpotence.

In row-source convention, ordered as \(F,E\), write
\[
  N_0=
  \begin{pmatrix}
    Q&C\\
    D&0
  \end{pmatrix}.
\tag{2.1}
\]
The cross-section hypothesis gives
\[
  Q^{N-1}=0.
\tag{2.2}
\]
A first return from \(E\) to \(E\) has the form
\[
  E\xrightarrow{D}F
  \xrightarrow{Q^j}F
  \xrightarrow{C}E,
\]
so its edge length is \(k=j+2\). Equations (2.2) and the absence of
\(E\)-to-\(E\) edges give
\[
  2\le k\le N.
\tag{2.3}
\]
Thus
\[
  H(t)
  =
  t^{-1}D(tI-Q)^{-1}C
  =
  \sum_{j=0}^{N-2}t^{-(j+2)}DQ^jC,
\tag{2.4}
\]
and
\[
  R:=H(1)=\sum_{j=0}^{N-2}DQ^jC.
\tag{2.5}
\]
If a different source counts vertices rather than edges when it assigns the
label \(N\), one must replace \(N\) below by the actual largest exponent
\[
  K:=\max\{|\gamma|:\gamma\text{ is a first return}\}.
\tag{2.6}
\]
The inequality \(n>N\) has no invariant meaning until this convention is locked.

## 3. Exact equation: derivation and minimal hypotheses

In the literal length-\(n\) clone, the \(E\)-to-\(F\) edges leave \(E_n\), the
\(F\)-to-\(E\) edges enter \(E_0\), and the only interior clone edges are
\[
  e_k\to e_{k+1}
  \quad(0\le k<n).
\tag{3.1}
\]
Let \(p=(p_F,p_0,\ldots,p_n)^{\mathsf T}>0\) be a row-source right Perron
vector:
\[
  N_np=\lambda_np.
\]
The typed block equations are
\[
  p_k=\lambda_n^k p_0,
\tag{3.2}
\]
\[
  (\lambda_nI-Q)p_F=Cp_0,
\tag{3.3}
\]
\[
  Dp_F=\lambda_np_n.
\tag{3.4}
\]
Substitution gives
\[
  H(\lambda_n)p_0=\lambda_n^np_0.
\tag{3.5}
\]
For \(B_n=N_n^{\mathsf T}\) and \(B_nq=\lambda_nq\), the chain equation is
\[
  q_k=\lambda_n^{-k}q_0,
\tag{3.6}
\]
and elimination gives
\[
  H(\lambda_n)^{\mathsf T}q_0=\lambda_n^nq_0.
\tag{3.7}
\]

The algebraic reduction (3.5) needs only the literal block structure,
invertibility of \(\lambda_nI-Q\), and a nonzero \(E_0\)-restriction. To identify
the eigenvalue in (3.5) with
\(\rho(H(\lambda_n))\), positivity of \(p_0\) and irreducibility of
\(H(\lambda_n)\) are needed. Strong connectivity of \(G\) is a convenient
sufficient hypothesis: it makes every clone strongly connected and makes
\(R=H(1)\) irreducible. Since the support of \(H(t)\) is independent of
\(t>0\), every \(H(t)\) is then irreducible.

The following changes invalidate the scalar equation as written:

- unequal delays on different gate vertices replace \(t^nI\) by a diagonal
  delay operator;
- an \(E\)-to-\(E\) edge adds a \(t^{-1}\) return term;
- an interior clone side edge adds an \(n\)-dependent return term;
- an omitted edge occurrence changes \(H(t)\), even if its Boolean support does
  not change;
- changing \(E_0\to\cdots\to E_n\) from \(n\) edges to a chain with a different
  delay convention changes the exponent on the right.

These are graph-purity obligations, not harmless choices of notation.

## 4. Fixed-template asymptotics

Let
\[
  h(t):=\rho(H(t)).
\]
For \(t>0\), \(h\) is continuous. Every return has positive length, so \(h\) is
strictly decreasing when \(R\ne0\), and \(h(t)\to0\) as \(t\to\infty\).
If
\[
  \rho(R)=h(1)>1,
\tag{4.1}
\]
then, for every \(n\ge0\), the equation
\[
  h(t)=t^n
\tag{4.2}
\]
has a unique solution \(t>1\), and the exact positive-eigenvector equivalence
identifies it with \(\lambda_n=\rho(N_n)\).

For \(n\ge1\),
\[
  1<\lambda_n^n=h(\lambda_n)\le h(1)=\rho(R),
\]
so
\[
  1<\lambda_n\le\rho(R)^{1/n}.
\]
Therefore \(\lambda_n\to1\), and continuity gives
\[
  \lambda_n^n=h(\lambda_n)\to h(1)=\rho(R).
\]
This proof is valid only with the graph fixed while \(n\to\infty\).

### Attack 4.1: a bounded-complexity family is not a fixed template

Bounded gate dimension and bounded return length do not make
\(\lambda_n\to1\) uniform over templates whose edge multiplicities vary with
\(n\). Let \(E=\{e\}\), use \(M_n\) first-return paths of length \(2\) and one
first-return path of length \(3\), and choose \(M_n\) of order \(e^n\). Then
\[
  H_n(t)=M_nt^{-2}+t^{-3}.
\]
The root of \(H_n(\lambda_n)=\lambda_n^n\) has
\(\lambda_n\to e\), not \(1\). The underlying graph can be made primitive by
using the length-\(2\) and length-\(3\) return cycles. Thus “fixed
cross-section” must mean a fixed return datum, not merely fixed values of
\(|E|\) and \(N\).

### Attack 4.2: the strict return multiplier cannot be omitted

For the two-cycle
\[
  e\to a\to e,
\]
one has \(H(t)=t^{-2}\), \(\rho(H(1))=1\), and every clone is a directed cycle
with Perron root \(1\). Hence neither
\(\lambda_n>1\) nor a strict total multiplier follows from strong connectivity
alone.

An irreducible nonnegative integer matrix has spectral radius \(1\) exactly
when its graph is one directed cycle with unit multiplicities. Thus the minimal
strict-return hypothesis is
\[
  \rho(H(1))>1.
\]
Primitivity of the base graph is a sufficient but stronger certificate.

### Attack 4.3: the walk cross section cannot be omitted

Take \(E=\{e\}\), \(F=\{a\}\), edges \(e\to a\), \(a\to e\), and two
self-loop occurrences \(a\to a\). Then \(Q=[2]\), so \(E\) is not a cross
section and every clone retains an active subsystem of spectral radius \(2\).
In fact \(\lambda_n>2\) and \(\lambda_n\to2\), not \(1\). The formal resolvent
\((tI-Q)^{-1}\) is not continuous through \(t=1\) and does not provide an
\(H(1)\) first-return matrix.

## 5. Uniform lower bound

The lower bound uses two independent facts:

1. negative return weights lose at most a factor \(\lambda^{-K}\);
2. a nontrivial irreducible integer return graph of dimension at most \(d\)
   has a uniform entropy gap.

### Lemma 5.1 (irreducible integer entropy gap)

Let \(R\) be an irreducible \(m\times m\) nonnegative integer matrix. If
\(\rho(R)>1\), then
\[
  \rho(R)\ge2^{1/m}.
\tag{5.1}
\]

**Proof.** If \(m=1\), then \(R=[r]\) with integer \(r\ge2\).
Suppose \(m>1\). If every vertex had exactly one outgoing edge occurrence,
irreducibility would make \(R\) the permutation matrix of one directed cycle,
contrary to \(\rho(R)>1\). Hence some vertex \(v\) has two distinct outgoing
edge occurrences.

Complete each occurrence by a shortest path back to \(v\). This produces two
distinct first-return closed walks at \(v\), of lengths
\(\ell_1,\ell_2\le m\). Every binary word of \(r\) such loops is a distinct
closed edge-occurrence walk. Their total lengths take at most \(r+1\) values,
all at most \(rm\). For some \(L_r\le rm\),
\[
  (R^{L_r})_{vv}\ge\frac{2^r}{r+1}.
\]
Since \(L_r\to\infty\), the spectral-radius formula gives
\[
  \rho(R)
  \ge
  \limsup_{r\to\infty}
  \left(\frac{2^r}{r+1}\right)^{1/L_r}
  \ge2^{1/m}.
\]
\(\square\)

This avoids the unnecessary least-common-multiple loss and improves the cruder
\(2^{1/m^2}\) bound.

### Theorem 5.2 (uniform total clone multiplier)

Let \(m=|E|\le d\), assume \(\rho(R)>1\), and suppose every first-return
length lies in
\[
  k_{\min}\le k\le K.
\]
For the present no-\(E\)-to-\(E\) setup, \(k_{\min}=2\), and the stated
cross-section convention gives \(K\le N\). For \(t\ge1\),
\[
  t^{-K}R\le H(t)\le t^{-k_{\min}}R
\tag{5.2}
\]
entrywise. Perron monotonicity therefore gives
\[
  t^{-K}\rho(R)
  \le h(t)\le
  t^{-k_{\min}}\rho(R).
\tag{5.3}
\]

At \(t=\lambda_n\), put \(\mu_n=\lambda_n^n\). For \(n\ge1\), (5.3) becomes
\[
  \mu_n
  \ge
  \mu_n^{-K/n}\rho(R),
\qquad
  \mu_n
  \le
  \mu_n^{-k_{\min}/n}\rho(R).
\]
Hence the two-sided quantitative estimate is
\[
  \boxed{
  \rho(R)^{\,n/(n+K)}
  \le
  \lambda_n^n
  \le
  \rho(R)^{\,n/(n+k_{\min})}.
  }
\tag{5.4}
\]
Combining the lower estimate with Lemma 5.1 yields
\[
  \lambda_n^n
  \ge
  2^{\,n/[m(n+K)]}
  \ge
  2^{\,n/[d(n+K)]}.
\tag{5.5}
\]
If \(K\le N<n\), then
\[
  \frac{n}{n+K}
  \ge
  \frac{n}{n+N}
  >
  \frac12,
\]
and therefore
\[
  \lambda_n^n>2^{1/(2d)}.
\tag{5.6}
\]

The return-length exponent in (5.4) is sharp under the minimal hypotheses. With
one gate vertex and two internally disjoint first-return paths, both of length
\(K\),
\[
  R=[2],
  \qquad
  H(t)=2t^{-K},
\]
and
\[
  \lambda_n^n=2^{n/(n+K)}.
\tag{5.7}
\]
At \(n=K\), this is exactly \(\sqrt2\).

### What the bound does not say

- Without \(\rho(R)>1\), the multiplier can equal \(1\).
- Without an actual maximum return exponent \(K\), even \(d=1\) and \(R=[2]\)
  allow \(2^{n/(n+K)}\) to approach \(1\).
- Integer edge-occurrence counts are essential. For arbitrary positive real
  weights, a one-dimensional return weight \(1+\varepsilon\) has no uniform
  gap above \(1\).
- The estimate controls the complete multiplier \(\lambda_n^n\), not
  \(\lambda_n\) itself; the latter necessarily approaches \(1\) for a fixed
  template.

## 6. Perron-vector convergence and its limits

Let \(u\) and \(z\) be the normalized right Perron vectors of
\(R\) and \(R^{\mathsf T}\), respectively.

For the row-source right vector, normalize
\[
  \sum_{e\in E}(p_0^{(n)})_e=1.
\]
Since \(p_0^{(n)}\) is the Perron vector of \(H(\lambda_n)\), the fixed support is
irreducible, and \(H(\lambda_n)\to R\),
\[
  p_0^{(n)}\to u.
\tag{6.1}
\]
For the project source-column right vector, normalize
\[
  \sum_{e\in E}(q_0^{(n)})_e=1.
\]
Then \(q_0^{(n)}\) is the Perron vector of
\(H(\lambda_n)^{\mathsf T}\), and
\[
  q_0^{(n)}\to z.
\tag{6.2}
\]
Thus the current cross-section convergence statements are correct.

Three qualifications are necessary.

### 6.1 Whole-graph normalization is the wrong statement

There are \(n+1\) clone layers with mutually comparable weights. Normalizing a
Perron vector to have unit mass on the whole growing graph generally makes its
\(E_0\)-mass tend to zero. Convergence must be stated after normalization on the
fixed section \(E_0\).

Nor does the full corridor become asymptotically constant. If
\(k_n/n\to\theta\in[0,1]\), then the exact chain formulas and (1.3) give
\[
  p_{k_n}^{(n)}
  \longrightarrow
  \rho(R)^\theta u,
\qquad
  q_{k_n}^{(n)}
  \longrightarrow
  \rho(R)^{-\theta}z.
\tag{6.3}
\]
The limiting corridor has a nontrivial multiplicative profile.

### 6.2 Irreducibility is needed for a canonical limit

If \(R\) is reducible or has more than one top Perron component, \(R\) has no
unique normalized positive Perron vector. For example,
\[
  H(t)=
  \begin{pmatrix}
    2t^{-2}&0\\
    0&2t^{-3}
  \end{pmatrix}
\]
selects the first component for every \(t>1\), while
\(H(1)=2I\) has a two-dimensional Perron eigenspace. A statement about “the”
limiting Perron vector is then undefined without an additional selection rule.
Strong connectivity excludes this defect.

### 6.3 Gate size and return depth do not give uniform eigencones

Even with \(|E|=2\), maximum return length \(3\), and a primitive base graph,
normalized gate eigenvectors can degenerate when multiplicities grow. Take the
return matrix
\[
  R_M=
  \begin{pmatrix}
    0&M\\
    1&1
  \end{pmatrix}.
\tag{6.4}
\]
It is realized by:

- \(M\) length-\(2\) return occurrences \(e_1\rightsquigarrow e_2\);
- one length-\(2\) return \(e_2\rightsquigarrow e_1\);
- one length-\(3\) return \(e_2\rightsquigarrow e_2\).

The resulting base graph is strongly connected and has closed walks of lengths
\(3\) and \(4\), hence is primitive. But
\[
  \rho(R_M)=\frac{1+\sqrt{1+4M}}2,
\]
and both left and right Perron coordinate ratios grow like \(\sqrt M\).
Therefore no family-uniform eigenvector ratio follows from \(d,N\) alone.
One also needs an upper entropy/multiplicity bound, or an equivalent compact
family condition.

For reduced \(E_0\)-vectors, a bound
\(\rho(R)\le H\), together with \(d,N\) and \(n>N\), is enough in principle:
irreducibility and integrality bound the entries of \(R\), while the weights
\(\lambda^{-k}\) remain in a compact positive interval. Control of the active
components \(p_F,q_F\) can require further bounds on the active realization.

## 7. Counterexample matrix

The three-vertex graph
\[
  e\to a,\qquad
  a\to e,\qquad
  a\to b,\qquad
  b\to e
\]
has first-return lengths \(2\) and \(3\). Hence
\[
  H(t)=t^{-2}+t^{-3}.
\]
The literal clone equation is
\[
  \lambda_n^n=\lambda_n^{-2}+\lambda_n^{-3},
\]
equivalently
\[
  \lambda_n^{n+3}=\lambda_n+1.
\tag{7.1}
\]
This exactly matches the characteristic equation of the clone. The positive
weight replacement \(t^2+t^3\) fails. Transposing the incidence leaves (7.1)
unchanged and only swaps the reduced left/right eigenvectors.

This example also verifies the quantitative bound. Here \(d=1\), \(K=N=3\),
and \(\rho(R)=2\), so
\[
  2^{n/(n+3)}
  \le
  \lambda_n^n
  \le
  2^{n/(n+2)}.
\]

## 8. Recommended theorem statement

A source-independent corrected theorem can safely be stated as follows.

> **Corrected fixed-cross-section clone theorem.** Let \(G\) be a finite
> strongly connected directed multigraph, let \(E\ne\varnothing\) be a gate with
> no \(E\)-to-\(E\) edge, and assume every directed walk of \(N-1\) edges meets
> \(E\). Form the literal uniform length-\(n\) clone
> \(E_0\to\cdots\to E_n\). Let \(H(t)\) be the row-source first-return matrix
> with weight \(t^{-|\gamma|}\), and put \(R=H(1)\). If
> \(\rho(R)>1\), then for every \(n\ge0\) the clone is strongly connected,
> its Perron root \(\lambda_n>1\) is the unique \(t>1\) satisfying
> \(\rho(H(t))=t^n\), and, as \(n\to\infty\),
> \[
>   \lambda_n\to1,
>   \qquad
>   \lambda_n^n\to\rho(R).
> \]
> Perron vectors normalized on \(E_0\) converge to those of \(R\) in
> row-source orientation and \(R^{\mathsf T}\) in project source-column
> orientation. If \(n\ge1\), \(m=|E|\le d\), and \(K\le N\) is the maximum
> first-return length, then
> \[
>   \rho(R)^{n/(n+K)}
>   \le\lambda_n^n
>   \le\rho(R)^{n/(n+2)}.
> \]
> In particular, \(n>N\) implies
> \(\lambda_n^n>2^{1/(2d)}\).

The base graph may be assumed primitive as a convenient sufficient condition
for \(\rho(R)>1\), but clone primitivity is not needed for this spectral theorem
and does not follow from base primitivity. Any later use that needs
aperiodicity must retain a separate delay-robust period certificate.

## 9. Dependency boundary

This audit establishes only a finite directed-graph theorem. It does not prove
that a dynamical corridor:

1. has no omitted critical or immersion branch;
2. realizes the literal clone at every interior layer;
3. has uniformly bounded gate dimension or return depth;
4. transports WAD data through the same typed incidence;
5. enters the KKL Value functional with the required left/right roles.

Those remain separate realization and source-bridge obligations. In particular,
the scalar correction \(t^{-k}\) cannot by itself certify the virtual corridor
branch of the MLC program.
