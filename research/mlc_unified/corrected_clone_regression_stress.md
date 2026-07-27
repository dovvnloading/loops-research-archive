# Regression stress test for the corrected clone multiplier

## 1. Scope and verdict

This note independently stress-tests the corrected finite-graph statement
\[
  q_n:=\lambda_n^n=\rho(H(\lambda_n)),
  \qquad
  H(t)=\sum_{k=2}^{K}t^{-k}R_k,
  \qquad
  R=\sum_{k=2}^{K}R_k.
\tag{1.1}
\]
The test targets:

- the sharp entropy gap for irreducible integer multigraph matrices;
- the delayed lower estimate
  \[
    q_n\ge \rho(R)^{\,n/(n+K)};
  \tag{1.2}
  \]
- periodic return matrices;
- parallel edge occurrences;
- mixtures of unequal return lengths;
- the boundary \(n=K\).

No counterexample was found. The tests also isolate a useful boundary
refinement:

> Under the minimal assumptions that \(R\) is irreducible and
> \(\rho(R)>1\), equality in (1.2) can occur at \(n=K\). If the underlying
> base graph is primitive, however, then the estimate at \(n=K\) is strict.
> Thus the strict square-root conclusion may be stated for \(n\ge K\) under
> the primitive-base hypothesis, although \(n>K\) remains the safe statement
> without that extra hypothesis.

This is a finite combinatorial regression report only. It does not certify
that a dynamical corridor realizes the literal clone, has bounded gate
dimension or return depth, or satisfies the hypotheses needed by the Value
functional.

## 2. Exact checks

### 2.1 Sharp irreducible-integer gap

Let \(R\) be an irreducible, non-permutation, nonnegative integer matrix of
dimension \(m\). Some vertex has two distinct outgoing edge occurrences.
Complete each occurrence by a shortest path back to that vertex. The two
resulting first-return loops have lengths \(\ell_1,\ell_2\le m\), and their
edge-occurrence words are uniquely decodable. If \(r>1\) is defined by
\[
  r^{-\ell_1}+r^{-\ell_2}=1,
\]
then the concatenated loop language gives \(\rho(R)\ge r\). Since
\[
  2(2^{1/m})^{-m}=1
\]
and \(\ell_i\le m\),
\[
  \rho(R)\ge 2^{1/m}.
\tag{2.1}
\]
Parallel edges cause no ambiguity because edge occurrences, rather than only
their endpoints, label the walks.

The bound is sharp in every dimension: take a directed \(m\)-cycle and double
one edge. Its characteristic polynomial is
\[
  x^m-2,
\]
so its Perron root is exactly \(2^{1/m}\). For \(m=1\), the example is
\([2]\).

### 2.2 Delayed inequality and its equality criterion

For \(t\ge1\),
\[
  H(t)-t^{-K}R
  =
  \sum_{k=2}^{K-1}(t^{-k}-t^{-K})R_k
  \ge0.
\tag{2.2}
\]
At \(t=\lambda_n\), Perron monotonicity and (1.1) give
\[
  q_n\ge\lambda_n^{-K}\rho(R)
       =q_n^{-K/n}\rho(R),
\]
which is exactly (1.2). If at least one \(R_k\ne0\) for \(k<K\), then the
inequality in (2.2) is nonzero. Because \(R\), \(H(t)\), and
\(t^{-K}R\) have the same irreducible support, strict Perron monotonicity gives
\[
  q_n>\rho(R)^{\,n/(n+K)}.
\tag{2.3}
\]
If all returns have length \(K\), then
\[
  H(t)=t^{-K}R
\]
and equality holds in (1.2) for every \(n\).

### 2.3 The exact \(n=K\) boundary

Under only irreducibility and \(\rho(R)>1\), the boundary need not be strict.
Let
\[
  R=
  \begin{pmatrix}
    0&2&0\\
    0&0&1\\
    1&0&0
  \end{pmatrix},
  \qquad
  \rho(R)=2^{1/3},
\]
and assign every return occurrence length \(K=5\). Then
\[
  H(t)=t^{-5}R,
  \qquad
  q_n=2^{\,n/[3(n+5)]}.
\]
At \(n=K=5\),
\[
  q_5=2^{1/6},
\]
exactly the square-root gate bound. The expanded base graph is periodic: all
closed walks have length divisible by \(5\).

The primitive-base hypothesis rules out this equality case. If all
first-return paths had the common length \(K\ge2\), then every closed walk in
the base graph would have length divisible by \(K\), because the cross-section
hypothesis excludes an active closed walk avoiding the gate. The base period
would therefore be divisible by \(K\), contradicting primitivity. Hence a
primitive base has at least one return length below its actual maximum \(K\).
Equation (2.3) then gives, already at \(n=K\),
\[
  q_K>\sqrt{\rho(R)}
      \ge 2^{1/(2m)}
      \ge 2^{1/(2d)}
  \quad(m\le d).
\tag{2.4}
\]
For \(n>K\), the same strict square-root conclusion follows even when all
returns have length \(K\), because \(n/(n+K)>1/2\).

### 2.4 Periodic \(R\) with a primitive expanded base

Periodicity of the reduced return matrix is not an obstruction. Use the same
three-cycle return matrix as above, but assign:

- the two occurrences \(e_0\to e_1\) lengths \(2\) and \(3\);
- \(e_1\to e_2\) length \(2\);
- \(e_2\to e_0\) length \(2\).

Then
\[
  H(t)=
  \begin{pmatrix}
    0&t^{-2}+t^{-3}&0\\
    0&0&t^{-2}\\
    t^{-2}&0&0
  \end{pmatrix}.
\]
The two expanded closed cycles have lengths \(6\) and \(7\), so the expanded
base is primitive, while \(R=H(1)\) still has period \(3\). The clone equation
reduces exactly to
\[
  \lambda_n^{3n+7}=\lambda_n+1.
\tag{2.5}
\]
At \(n=K=3\), (2.5) implies
\[
  q_3=\lambda_3^3>2^{1/6}.
\]
This checks that clone primitivity is unnecessary and that a periodic
reduced return graph is compatible with strict complete-block expansion.

### 2.5 Parallel and unequal returns

For one gate vertex, take one return of length \(2\) and four parallel return
occurrences of length \(7\). Then
\[
  R=[5],
  \qquad
  H(t)=t^{-2}+4t^{-7},
\]
and the exact clone equation is
\[
  \lambda_n^{n+7}=\lambda_n^5+4.
\tag{2.6}
\]
The expanded base is primitive because its closed-cycle lengths include
\(2\) and \(7\). At \(n=7\), the lower estimate is strict:
\[
  q_7>\sqrt5.
\]
This example simultaneously exercises multiplicity, unequal return lengths,
and the \(n=K\) boundary.

## 3. Exhaustive small-matrix diagnostics

The following finite catalogs were enumerated. Irreducibility and the
permutation exception were checked from the directed multigraph support. The
reported minimizing matrices were then checked symbolically by their
characteristic polynomials.

| dimension \(m\) | exhaustive catalog | irreducible non-permutation matrices | observed minimum | exact minimizing polynomial |
|---:|---|---:|---:|---|
| 1 | entries \(0,\ldots,4\), excluding \([0]\) and \([1]\) | 3 | \(2\) | \(x-2\) |
| 2 | every entry in \(0,\ldots,3\) | 143 | \(2^{1/2}\) | \(x^2-2\) |
| 3 | every entry in \(0,\ldots,2\) | 11,230 | \(2^{1/3}\) | \(x^3-2\) |
| 4 | total edge multiplicity at most \(7\) | 9,572 | \(2^{1/4}\) | \(x^4-2\) |

Every catalog minimum is the doubled-edge directed cycle. These enumerations
are diagnostic corroboration; the proof of (2.1) is the exact walk-language
argument in Section 2.1, not the finite search.

## 4. Seeded delayed-return diagnostics

Two reproducible diagnostic batches were run.

1. **Exhaustive scalar returns.** For \(2\le K\le7\), every coefficient vector
   \((R_2,\ldots,R_K)\in\{0,1,2\}^{K-1}\) with \(R_K>0\) and
   \(\sum R_k\ge2\) was tested at
   \(n\in\{1,K-1,K,K+1,2K+1\}\), with duplicate \(n\)-values retained by the
   simple harness. There were 3,610 root comparisons, no violation of
   (1.2), and 30 single-length equality checks. The smallest computed ratio
   \(q_n/\rho(R)^{n/(n+K)}\) differed from \(1\) by less than
   \(2\times10^{-15}\), in a predicted equality case.

2. **Seeded matrix returns.** With seed `20260723`, 750 accepted irreducible
   return families of dimensions \(2,3,4\), maximum length \(2\le K\le7\),
   and bounded random integer multiplicities produced 3,750 comparisons.
   The batch included 14 periodic return matrices, 720 families with parallel
   occurrences, and 625 families with at least one submaximal return length.
   There were no lower-bound violations and no failure of strictness in a
   mixed-length family.

As a separate block-structure regression, 100 seeded small return families
were expanded into literal graphs with disjoint active paths, cloned directly,
and compared with the root of (1.1). The largest absolute discrepancy between
the two independently computed Perron roots was
\(4.5\times10^{-15}\).

All root comparisons in this section used floating-point eigensolvers and
bisection. They are deliberately classified as diagnostics, not proof.

## 5. Adversarial conclusions

1. The sharp integer gap is \(2^{1/m}\), including for periodic matrices and
   matrices whose branching is supplied only by parallel edge occurrences.
2. The delayed estimate (1.2) follows directly from entrywise order and has
   the correct exponent sign.
3. Equality in (1.2) occurs exactly for a single return length \(K\); mixed
   return lengths make it strict.
4. The condition \(n>K\) is sharp under the minimal irreducible-return
   hypotheses for a strict square-root estimate.
5. Under a primitive-base hypothesis, the boundary improves to \(n\ge K\),
   because primitivity forces a submaximal return length.
6. Periodicity of \(R\) and of a clone does not invalidate the Perron-root
   argument; irreducibility is the relevant spectral hypothesis.
7. None of these finite-graph checks supplies the still-missing dynamical
   realization, memory-safety, WAD-transport, or source-licensed Value
   hypotheses.

