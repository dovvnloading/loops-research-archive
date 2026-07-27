# Quantitative audit of the corrected clone theorem

## 1. Verdict

The proposed exact-clone estimate is correct under the stated typed hypotheses.
Let
\[
  H(t)=\sum_{k=1}^{N}t^{-k}R_k,
  \qquad
  R=H(1)=\sum_{k=1}^{N}R_k,
\tag{1.1}
\]
where the \(R_k\) are nonnegative integer matrices, \(R\) is irreducible and
not a permutation matrix, and \(m=\dim R\le d\). (For the literal construction
without \(E\)-to-\(E\) edges, the nonzero \(R_k\) in fact have \(k\ge2\).)
Suppose a common-delay literal clone has Perron root \(\lambda_n>1\) and satisfies
the corrected equation
\[
  q_n:=\lambda_n^n=\rho(H(\lambda_n)).
\tag{1.2}
\]
Then
\[
  \rho(R)^{\,n/(n+N)}
  \le q_n\le \rho(R),
\tag{1.3}
\]
and hence
\[
  q_n
  \ge 2^{\,n/(d^2(n+N))}.
\tag{1.4}
\]
In particular, if \(n>N\), then
\[
  q_n>2^{1/(2d^2)}
  \quad\text{and}\quad
  q_n^{-1}<2^{-1/(2d^2)}.
\tag{1.5}
\]

The strict sign in (1.5) is justified precisely by \(n>N\). If \(n=N\), the
same argument gives only
\[
  q_n\ge2^{1/(2d^2)}.
\tag{1.6}
\]

The perturbed multiplier estimate is also valid, but only when the perturbed
object satisfies its **own** corrected clone equation and the entrywise
comparison holds at its own Perron root. Lower domination by itself does not
give perturbed eigencone compactness.

## 2. Orientation and support audit

The proof is insensitive to transposition at the scalar level. In the row-source
convention of `corrected_clone_theorem_derivation.md`, \(H(t)\) acts on the
restriction of the row-source right Perron vector to \(E_0\). In the project's
source-column convention, \(H(t)^{\mathsf T}\) acts on the corresponding
project-right vector. Since
\[
  \rho(H(t)^{\mathsf T})=\rho(H(t)),
\]
all scalar inequalities below survive this change of convention.

The sign of the return weights is not convention-dependent. A return path of
length \(k\) contributes \(t^{-k}\) in either convention. Transposition must not
be used to replace \(t^{-k}\) by \(t^k\).

Because \(R=\sum_kR_k\), \(H(t)\) and \(R\) have the same zero pattern for every
\(t>0\). Thus irreducibility of \(R\) implies irreducibility of every \(H(t)\).
Primitivity is not required for any estimate in Sections 3--6.

## 3. Exact multiplier estimate

For \(t\ge1\) and \(1\le k\le N\),
\[
  t^{-N}\le t^{-k}\le1.
\]
Therefore
\[
  t^{-N}R\le H(t)\le R
\tag{3.1}
\]
entrywise. Perron monotonicity and homogeneity give
\[
  t^{-N}\rho(R)\le\rho(H(t))\le\rho(R).
\tag{3.2}
\]
Evaluate this at \(t=\lambda_n\) and use (1.2):
\[
  \lambda_n^{-N}\rho(R)\le q_n\le\rho(R).
\tag{3.3}
\]
Since \(\lambda_n=q_n^{1/n}\), the lower inequality is
\[
  q_n\ge q_n^{-N/n}\rho(R).
\]
All quantities are positive, so
\[
  q_n^{\,1+N/n}\ge\rho(R),
\]
which is equivalent to
\[
  q_n\ge\rho(R)^{\,n/(n+N)}.
\tag{3.4}
\]
This proves (1.3). No limiting argument and no clone aperiodicity are used.

## 4. Entropy gap for irreducible non-permutation returns

The existing \(2^{1/d^2}\) gap does not actually require primitivity once the
return matrix is explicitly assumed not to be a permutation.

### Lemma 4.1

If \(R\) is an irreducible nonnegative integer \(m\times m\) matrix and is not a
permutation matrix, then
\[
  \rho(R)\ge2^{1/m^2}\ge2^{1/d^2}.
\tag{4.1}
\]

### Proof

Irreducibility implies that every vertex of the directed multigraph of \(R\)
has at least one outgoing edge occurrence. If every vertex had exactly one,
strong connectivity would make the graph one directed cycle and \(R\) its
permutation matrix. Hence some vertex \(v\) has two distinct outgoing edge
occurrences.

Extend each occurrence to a closed walk based at \(v\), using a simple return
path of length at most \(m-1\). This gives two distinct closed walks of lengths
\(\ell_1,\ell_2\le m\). Repeating them to their common length
\[
  L=\operatorname{lcm}(\ell_1,\ell_2)\le m^2
\]
gives two distinct closed walks of length \(L\). Concatenation according to
binary words gives at least \(2^r\) distinct closed walks of length \(rL\).
Consequently
\[
  \rho(R)\ge2^{1/L}\ge2^{1/m^2}\ge2^{1/d^2}.
\]
\(\square\)

Combining Lemma 4.1 with (3.4) gives
\[
  q_n
  \ge
  2^{\,n/(d^2(n+N))}.
\tag{4.2}
\]
When \(n>N\),
\[
  \frac{n}{n+N}>\frac12,
\]
so (1.5) follows. Notice that the graph entropy gap remains
\(2^{1/d^2}\); it is the complete delayed-block multiplier that is reduced to
the square-root gap in the uniform \(n>N\) estimate.

## 5. Perturbed multiplier

Let \(\widetilde H(t)\) be a nonnegative matrix family of the same reduced
dimension, and let \(0\le\epsilon<1\). The sufficient hypotheses are:

1. there is an actual root \(\widetilde\lambda>1\);
2. the perturbed object satisfies its own corrected equation
   \[
     \widetilde q
     :=
     \widetilde\lambda^n
     =
     \rho(\widetilde H(\widetilde\lambda));
   \tag{5.1}
   \]
3. at least at \(t=\widetilde\lambda\),
   \[
     \widetilde H(\widetilde\lambda)
     \ge
     (1-\epsilon)H(\widetilde\lambda)
   \tag{5.2}
   \]
   entrywise.

Requiring (5.2) for every \(t\ge1\) is a convenient stronger hypothesis, but is
not needed for this numerical conclusion. Perron monotonicity, (3.2), and
(5.1)--(5.2) give
\[
\begin{aligned}
  \widetilde q
  &\ge
  (1-\epsilon)\rho(H(\widetilde\lambda))\\
  &\ge
  (1-\epsilon)\widetilde\lambda^{-N}\rho(R)\\
  &=
  (1-\epsilon)\widetilde q^{-N/n}\rho(R).
\end{aligned}
\]
Thus
\[
  \boxed{
  \widetilde q
  \ge
  \bigl((1-\epsilon)\rho(R)\bigr)^{n/(n+N)}
  \ge
  \bigl((1-\epsilon)g_d\bigr)^{n/(n+N)}
  },
\qquad
  g_d:=2^{1/d^2}.
\tag{5.3}
\]

If
\[
  \epsilon<1-g_d^{-1},
\tag{5.4}
\]
then \((1-\epsilon)g_d>1\), so (5.3) supplies a uniform strict multiplier.
For \(n>N\),
\[
  \widetilde q
  >
  \sqrt{(1-\epsilon)g_d},
\qquad
  \widetilde q^{-1}
  <
  \bigl((1-\epsilon)g_d\bigr)^{-1/2}.
\tag{5.5}
\]
At equality in (5.4), this argument gives no uniform separation from \(1\).

### What is not sufficient

An unweighted comparison
\[
  \widetilde H(1)\ge(1-\epsilon)H(1)
\]
does not imply (5.2): retained paths could have been assigned different or
longer return lengths, and negative weights penalize those changes at
\(\widetilde\lambda>1\). A dynamical perturbation theorem must either preserve
the path labels or prove the weighted comparison directly.

Likewise, (5.1) cannot be replaced by the assertion that
\(\widetilde\lambda\) is an eigenvalue of some unreduced transition unless the
Schur/first-return reduction is proved for that actual transition. Side edges,
unequal corridor delays, or omitted return branches change the reduced
equation.

## 6. Exact reduced eigencone bounds

Assume now
\[
  \rho(R)\le H_0,
  \qquad
  H_0>1,
  \qquad
  n\ge N.
\tag{6.1}
\]
For brevity put \(M=H(\lambda_n)\) and \(q=q_n\). From (1.3),
\[
  q\le\rho(R)\le H_0.
\tag{6.2}
\]
Moreover,
\[
  \lambda_n^N=q^{N/n}\le H_0,
\tag{6.3}
\]
so every retained return-path weight satisfies
\[
  \lambda_n^{-k}\ge\lambda_n^{-N}\ge H_0^{-1}.
\tag{6.4}
\]
Every nonzero entry of \(M\) therefore obeys
\[
  H_0^{-1}\le M_{ij}\le R_{ij}.
\tag{6.5}
\]

For completeness, irreducibility alone gives the integer entry bound used here.
If \(R_{ij}>0\), choose a simple path from \(j\) back to \(i\) of length at most
\(m-1\). Choosing one of the \(R_{ij}\) parallel occurrences on the first edge
and fixing the return path produces \(R_{ij}\) closed walks of some length at
most \(m\). Concatenation yields
\[
  R_{ij}\le\rho(R)^m\le H_0^d.
\tag{6.6}
\]
Hence all nonzero reduced entries lie in the compact interval
\[
  H_0^{-1}\le M_{ij}\le H_0^d.
\tag{6.7}
\]

There is also a direct, explicit cone estimate. Let \(x>0\) satisfy
\[
  Mx=qx.
\]
For every support edge \(i\to j\),
\[
  M_{ij}x_j\le qx_i,
\]
and (6.2), (6.5) imply
\[
  \frac{x_j}{x_i}\le H_0^2.
\tag{6.8}
\]
Any two vertices are joined by a simple directed path of length at most
\(m-1\), so
\[
  \frac{\max_i x_i}{\min_i x_i}
  \le H_0^{2(m-1)}
  \le H_0^{2(d-1)}.
\tag{6.9}
\]
Applying the same argument to \(M^{\mathsf T}\) gives the identical bound for
the left Perron vector. Periodicity causes no problem: irreducibility suffices
for the strictly positive left and right Perron rays.

Thus, after any fixed normalization on the reduced gate, both Perron rays lie
in a compact subset of the positive cone, uniformly in the clone length and in
the admissible reduced template.

### Corridor layers

The literal chain equations are
\[
  p_k=\lambda_n^kp_0
\]
for the row-source right/project-left vector and
\[
  z_k=\lambda_n^{-k}z_0
\]
for the project-right/row-source left vector. For \(0\le k\le n\),
\[
  \lambda_n^k\le\lambda_n^n=q\le H_0.
\tag{6.10}
\]
Combining (6.9) and (6.10) bounds all coordinate ratios on the union of the
clone layers by
\[
  H_0^{\,2(d-1)+1}.
\tag{6.11}
\]
This statement concerns the gate and the literal clone chain. A bound for
additional active vertices, geometric WAD weights, or Hubbard-tree
intersection lengths requires the corresponding realization and complexity
hypotheses; it does not follow merely from the reduced matrix.

## 7. Perturbed eigencones: necessary extra hypothesis

The lower comparison (5.2) alone does **not** imply a compact family of
perturbed Perron rays. Even with \(\epsilon=0\), fixed reduced dimension, and
fixed maximum return length, one may add arbitrarily large retained
multiplicity in one entry. For example, scalar negative weighting of
\[
  \widetilde R_M=
  \begin{pmatrix}
    M+1&1\\
    1&0
  \end{pmatrix}
  \ge
  R_0=
  \begin{pmatrix}
    1&1\\
    1&0
  \end{pmatrix}
\tag{7.1}
\]
gives exact common-delay clone equations, while the right and left Perron
coordinate ratios of the symmetric matrix \(\widetilde R_M\) diverge with
\(M\). Its total multiplier also diverges. Thus a lower retained-transition
estimate is a contraction certificate, not an eigencone compactness
certificate.

A useful sufficient perturbed version is the following. Suppose, in addition
to (5.1)--(5.2), that
\[
  \widetilde q\le\widetilde H_0,
  \qquad
  n\ge N,
  \qquad
  \epsilon\le\epsilon_0<1.
\tag{7.2}
\]
On every edge of the irreducible reference support,
\[
  \widetilde H(\widetilde\lambda)_{ij}
  \ge
  (1-\epsilon_0)\widetilde H_0^{-1}.
\tag{7.3}
\]
Following reference-support paths in the perturbed Perron equations yields,
for both left and right rays,
\[
  \frac{\max x_i}{\min x_i}
  \le
  \left(
    \frac{\widetilde H_0^2}{1-\epsilon_0}
  \right)^{d-1}.
\tag{7.4}
\]
Thus compact perturbed eigencones require an upper actual multiplier/entropy
bound (or another upper control of the actual transition), as well as a loss
bounded away from \(1\).

## 8. Large-entropy branch

If
\[
  \rho(R)>H_0>1
  \quad\text{and}\quad
  n\ge N,
\]
then (3.4) gives
\[
  q_n
  \ge
  \rho(R)^{n/(n+N)}
  >
  H_0^{1/2}.
\tag{8.1}
\]
The strict inequality remains valid when \(n=N\), because
\(\rho(R)>H_0\). Hence the homogeneous complete-block Value factor, wherever
the KKL Value theorem is separately source-licensed, satisfies
\[
  q_n^{-1}<H_0^{-1/2}.
\tag{8.2}
\]
It is not \(H_0^{-1}\). The square-root loss is the unavoidable consequence of
allowing the return-word depth \(N\) to be as large as the common delay \(n\).

## 9. Dependency and failure checklist

The quantitative conclusion is valid only after all of the following have been
proved for the actual corridor:

1. the reduced return operator uses the negative weights \(t^{-k}\);
2. every return length is at most the declared universal \(N\);
3. the common delay is exactly \(n\), with no unequal-delay or interior-side-edge
   correction hidden in (1.2);
4. \(R\) is irreducible and is not a permutation matrix;
5. the reduced gate dimension is at most \(d\);
6. the actual or perturbed transition satisfies its own exact reduced
   eigen-equation;
7. any perturbed comparison is weighted and holds at the actual root;
8. eigencone compactness is invoked only in a bounded-total-entropy branch;
9. KKL Value contraction is invoked only after its dynamical surface, support,
   and left/right weight hypotheses are independently verified.

Under these hypotheses, the proposed corrected multiplier estimate is
proof-certified. The universally valid complete-block factor produced by the
simple condition \(n>N\) is
\[
  2^{-1/(2d)},
\]
by the strengthened integer entropy gap proved in the reconciliation below.
The earlier \(2^{-1/(2d^2)}\) estimate remains valid but is not sharp.

## 10. Reconciliation: sharp irreducible integer entropy gap

### 10.1 Verdict on the strengthened argument

The strengthened estimate
\[
  \rho(R)\ge2^{1/m}
\tag{10.1}
\]
for an irreducible \(m\times m\) nonnegative integer matrix with
\(\rho(R)>1\) is valid. It improves Lemma 4.1. The \(m^{-2}\) exponent there
came from forcing two loops to a common length by a least common multiple.
A pigeonhole argument over the possible lengths of binary concatenations
removes that loss.

The proof requires walks to be sequences of **edge occurrences**. This makes
parallel edges distinguishable. It also requires the two chosen closed walks
to be first-return walks to their base vertex; shortest completions provide
exactly that property and make binary concatenations uniquely decodable.

### 10.2 Adversarial proof

If \(m=1\), irreducibility and \(\rho(R)>1\) give
\[
  R=[r]
  \quad\text{with integer }r\ge2,
\]
so \(\rho(R)=r\ge2=2^{1/m}\).

Now let \(m>1\). Every vertex has at least one outgoing edge occurrence. If
every vertex had exactly one, irreducibility would make the graph one directed
cycle with unit edge multiplicities, and its spectral radius would be \(1\).
Thus some vertex \(v\) has two distinct outgoing edge occurrences
\[
  e_0,\ e_1.
\]

For \(i=0,1\), choose a shortest directed path from the head of \(e_i\) back to
\(v\). It has at most \(m-1\) edges and does not visit \(v\) before its final
vertex; otherwise truncation at the first visit would be shorter. Prepending
\(e_i\) gives a closed walk \(\gamma_i\) based at \(v\), of length
\[
  1\le\ell_i\le m,
\]
with no internal visit to \(v\). This includes all edge cases:

- if \(e_i\) is a self-loop, its completion has length \(0\) and
  \(\ell_i=1\);
- if \(e_0,e_1\) are parallel, they remain distinct edge occurrences even
  though they have the same endpoints;
- if both are distinct self-loop occurrences, the two length-one loops are
  still distinct.

For every binary word
\[
  \sigma=(\sigma_1,\ldots,\sigma_r)\in\{0,1\}^r,
\]
concatenate
\[
  \Gamma_\sigma
  =
  \gamma_{\sigma_1}\gamma_{\sigma_2}\cdots\gamma_{\sigma_r}.
\]
The map \(\sigma\mapsto\Gamma_\sigma\) is injective. Indeed, the visits to
\(v\) uniquely mark the loop boundaries because neither \(\gamma_i\) has an
internal visit to \(v\), and the first edge occurrence after each boundary is
either \(e_0\) or \(e_1\), recovering the corresponding symbol. This rules out
the possible ambiguity that can occur when arbitrary, non-first-return closed
walks are used as code words.

The length of \(\Gamma_\sigma\) is
\[
  |\Gamma_\sigma|
  =
  a\ell_1+(r-a)\ell_0
\]
for some \(a\in\{0,\ldots,r\}\). Hence the \(2^r\) distinct walks occupy at
most \(r+1\) total lengths. By pigeonhole, for some integer
\[
  r\le L_r\le rm
\]
there are at least \(2^r/(r+1)\) distinct closed edge-occurrence walks of
length \(L_r\) at \(v\):
\[
  (R^{L_r})_{vv}\ge\frac{2^r}{r+1}.
\tag{10.2}
\]

The spectral-radius step does not require an unproved convergence along the
varying subsequence \(L_r\). For each fixed \(r\), concatenating any one of the
walks counted in (10.2) independently \(s\) times gives
\[
  (R^{sL_r})_{vv}
  \ge
  \bigl((R^{L_r})_{vv}\bigr)^s.
\]
The Gelfand formula, or equivalently
\(\rho(R^{L_r})\ge(R^{L_r})_{vv}\), therefore yields
\[
\begin{aligned}
  \rho(R)
  &\ge
  \bigl((R^{L_r})_{vv}\bigr)^{1/L_r}\\
  &\ge
  \left(\frac{2^r}{r+1}\right)^{1/L_r}\\
  &\ge
  \left(\frac{2^r}{r+1}\right)^{1/(rm)}.
\end{aligned}
\tag{10.3}
\]
Letting \(r\to\infty\) proves (10.1).

The estimate is sharp. A directed \(m\)-cycle with one of its edges doubled is
irreducible and has
\[
  \rho(R)^m=2,
\]
so \(\rho(R)=2^{1/m}\). For \(m=1\), the sharp example is \(R=[2]\).

### 10.3 Corrected quantitative constants

Since \(m\le d\), the sharp dimension-only gap is
\[
  g_d^\sharp:=2^{1/d}.
\tag{10.4}
\]
Consequently, (3.4) strengthens to
\[
  q_n
  \ge
  \rho(R)^{n/(n+N)}
  \ge
  2^{\,n/[d(n+N)]}.
\tag{10.5}
\]
If \(n>N\), then
\[
  q_n>2^{1/(2d)},
  \qquad
  q_n^{-1}<2^{-1/(2d)}.
\tag{10.6}
\]
Thus (10.6), rather than the valid but weaker (1.5), is the recommended
uniform complete-block estimate.

For the perturbed theorem, (5.3) strengthens to
\[
  \widetilde q
  \ge
  \bigl((1-\epsilon)\rho(R)\bigr)^{n/(n+N)}
  \ge
  \bigl((1-\epsilon)2^{1/d}\bigr)^{n/(n+N)}.
\tag{10.7}
\]
The sharp dimension-only threshold supplied by this argument is therefore
\[
  \boxed{\epsilon<1-2^{-1/d}.}
\tag{10.8}
\]
Under (10.8) and \(n>N\),
\[
  \widetilde q
  >
  \sqrt{(1-\epsilon)2^{1/d}},
\qquad
  \widetilde q^{-1}
  <
  \bigl((1-\epsilon)2^{1/d}\bigr)^{-1/2}.
\tag{10.9}
\]

All formulas in Sections 1, 4, and 5 using \(2^{1/d^2}\) remain logically
correct as conservative estimates, but (10.4)--(10.9) supersede them for
downstream theorem statements and constant ledgers. The eigencone estimates in
Sections 6--7 and the large-entropy estimate in Section 8 are unchanged.
