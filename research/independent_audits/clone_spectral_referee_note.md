# Delayed cross-section cloning: source-convention check and quantitative bounds

**Research verification note — November 4, 2026.** Independent finite-matrix calculation; not a referee report on an entire dynamics paper, not a claim of mathematical priority, and not a proof of MLC.

## Source and precise question

Kahn, Kapiamba and Lyubich, *MLC for parabolically bounded primitive renormalization*, [arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272), Appendix C (pp. 67–68), construct a clone graph by replacing a cross section with a directed chain. Their printed reduced operator weights an edge labeled \(k\) by \(\lambda^k\) and asserts in (C.2) that its Perron root equals \(\lambda_n^n\).

The question checked here is **only** whether that finite-\(n\) equation is compatible with the explicit graph and pushforward definitions on those pages. A typographical sign change, an implicit different convention, or subsequent author correction may explain the printed mismatch. No conclusion about the paper's main dynamical theorem follows from the calculation below.

## 1. Typed construction

Let a finite directed multigraph have vertices \(V=A\sqcup E\), with \(E\ne\varnothing\), no \(E\)-to-\(E\) edges, and a cross-section condition: all sufficiently long directed walks meet \(E\). Use *row-source* adjacency, ordered \(A,E\):

\[
N_0=\begin{pmatrix}Q&C\\D&0\end{pmatrix}.
\]

The cross-section condition makes \(Q\) nilpotent. Assume the full graph is strongly connected and the first-return matrix \(R\) below has spectral radius \(\rho>1\). Replace \(E\) by \(E_0\to\cdots\to E_n\); edges from \(A\) enter \(E_0\), and edges leaving \(E\) now leave \(E_n\). Denote the Perron root of this whole clone matrix by \(\lambda_n\).

Define the nonnegative return-length matrices, all but finitely many zero,

\[
R_k=DQ^{k-2}C\quad(k\ge2),\qquad
H(t)=\sum_{k\ge2}t^{-k}R_k=t^{-1}D(tI-Q)^{-1}C,
\quad R=H(1),\quad\rho=\rho(R)>1.
\]

The return graph on \(E\) is irreducible: every path between two gates in the strongly connected original graph decomposes at successive visits to \(E\). Thus \(R\) has a simple positive Perron eigenvalue, even when the return graph or some clones are periodic.

## 2. Exact reduction: negative powers of return length

Let \((p_A,p_0,\ldots,p_n)>0\) be a **right** Perron vector for row-source adjacency. Its block equations read

\[
p_{k+1}=\lambda_np_k,\quad
(\lambda_nI-Q)p_A=Cp_0,\quad
\lambda_np_n=Dp_A.
\]

Eliminating \(p_A\) and using \(p_n=\lambda_n^np_0\) gives

\[
D(\lambda_nI-Q)^{-1}Cp_0=\lambda_n^{n+1}p_0,
\quad
\boxed{H(\lambda_n)p_0=\lambda_n^np_0}.
\]

Since \(p_0>0\), the exact scalar equation is

\[
\boxed{\rho(H(\lambda_n))=\lambda_n^n.}\tag{1}
\]

Equivalently, with *pushforward* (target-row/source-column) adjacency, take the transpose matrix and its right Perron vector. The cloned corridor then has weights \(v(E_k)=\lambda_n^{-k}v(E_0)\). A first return of length \(k\) contributes \(\lambda_n^{-k}\), not \(\lambda_n^k\), to the \(n\)-step reduced eigenvalue equation. Matrix transposition does not change the Perron root.

This directly tests the **literal** positive-power edge-label definition printed alongside (C.2), rather than merely correcting a notation choice in an abstract renewal theorem.

## 3. Exact small-graph countercheck

Take \(E=\{e\}\), \(A=\{a,b\}\) and edges

\[
e\to a,\qquad a\to e,\qquad a\to b,\qquad b\to e.
\]

The base graph is primitive (cycles of lengths 2 and 3); every clone is primitive (cycles of lengths \(n+2\) and \(n+3\), which are coprime). The two first-return walks have lengths 2 and 3.

The full cloned adjacency matrix has exact Perron equation

\[
\lambda_n^{n+3}=\lambda_n+1.\tag{2}
\]

Since \(H(t)=t^{-2}+t^{-3}\), the corrected (1) is exactly (2). Using the **printed positive-power weighting** instead would give

\[
\lambda_n^n=\lambda_n^2+\lambda_n^3
=\lambda_n^{n+5},
\]

where (2) supplies the last equality. This forces \(\lambda_n=1\), contrary to (2), which has a unique root greater than one. Taking \(n=4\) (beyond the base cross-section horizon), direct matrix diagonalization gives \(\lambda_4\approx1.112775684279\); the two sides of the positive-power equation are approximately \(1.533311908191\) and \(2.616186162436\).

**Narrow inference:** The positive-power reduced matrix and (C.2) cannot both describe the cloned graph with its printed definition for this example. This does not show the intended asymptotic theorem is false: the negative-power repair recovers the limit used in downstream arguments.

## 4. Two-sided finite-clone bounds

Set \(k_{\min}=\min\{k:R_k\ne0\}\), \(K=\max\{k:R_k\ne0\}\), and \(\rho=\rho(R)>1\).

**Proposition 1.** For every integer \(n\ge0\),

\[
\boxed{\rho^{1/(n+K)}
\le\lambda_n\le\rho^{1/(n+k_{\min})}.}\tag{3}
\]

For \(n\ge1\), writing \(L=\log\rho\),

\[
\rho^{n/(n+K)}\le\lambda_n^n\le\rho^{n/(n+k_{\min})},
\qquad
0\le L-n\log\lambda_n\le \frac{KL}{n+K}.\tag{4}
\]

**Proof.** The positive irreducible return operator \(H(t)\) has decreasing spectral radius for \(t>0\), with \(\rho(H(1))=\rho>1\); hence (1) has a unique solution \(\lambda_n>1\). For \(t\ge1\), entrywise
\(t^{-K}R\le H(t)\le t^{-k_{\min}}R\).
Perron monotonicity at \(t=\lambda_n\) yields
\(\rho\lambda_n^{-K}\le\lambda_n^n\le\rho\lambda_n^{-k_{\min}}\).
Rearranging proves (3), and taking logarithms gives (4). \(\square\)

These graph-dependent bounds are not uniform analytic estimates for unbounded families of quadratic renormalizations.

## 5. Fixed-template second-order expansion

Normalize positive Perron vectors \(r,\ell\) of \(R\) by \(\ell^Tr=1\). Define

\[
L=\log\rho,\qquad
\mu=\frac{\ell^T\bigl(\sum_k kR_k\bigr)r}{\rho}.
\]

Then \(k_{\min}\le\mu\le K\).

**Proposition 2.** For a **fixed** return graph as \(n\to\infty\),

\[
\boxed{\log\lambda_n=\frac Ln-\frac{\mu L}{n^2}+O(n^{-3})},\tag{5}
\]

\[
\boxed{\lambda_n=1+\frac Ln+\frac{L^2/2-\mu L}{n^2}+O(n^{-3})},\tag{6}
\]

\[
\boxed{\lambda_n^n=\rho\left(1-\frac{\mu L}{n}+O(n^{-2})\right)}.\tag{7}
\]

**Proof.** Write \(s_n=\log\lambda_n=O(1/n)\) by (3). Simplicity of the Perron root makes
\(\Phi(s)=\log\rho(H(e^s))\) real analytic near zero, with
\(\Phi(0)=L\) and \(\Phi'(0)=-\mu\), by ordinary eigenvalue differentiation. The exact equation gives \(ns_n=\Phi(s_n)=L-\mu s_n+O(s_n^2)\). Thus \((n+\mu)s_n=L+O(n^{-2})\), yielding (5); exponentiation yields (6) and (7). \(\square\)

The three-vertex example has \(\rho=2,\mu=5/2\). This is standard finite-dimensional perturbation theory and is **not** asserted as an original general spectral theorem.

## Addendum: a primitive graph whose reduced return matrix is imprimitive

A second source-convention check concerns Appendix C's numbered assertion (3): "\(\hat T_\lambda\) is primitive for \(\lambda>0\)." This need not hold even assuming, as the preprint explicitly does, that **both the original graph and every delayed clone are primitive**. Irreducibility, not primitivity, is the property that follows and suffices for the Perron-vector and spectral-radius parts of the argument.

**Five-vertex counterexample.** Take \(E=\{e,f\}\), \(A=\{a,b,c\}\), with directed edges

\[
e\to a,\ e\to b,\ b\to a,\ a\to f,\ f\to c,\ c\to e.
\]

Every sufficiently long path visits \(E\), and there are no edges within \(E\). The base is strongly connected and has cycles of lengths \(4\) and \(5\): respectively \(e\,a\,f\,c\,e\) and \(e\,b\,a\,f\,c\,e\). Therefore its adjacency matrix is primitive. When \(E\) is cloned into \(E_0\to\cdots\to E_n\), the resulting graph is still strongly connected and has corresponding cycles of lengths \(2n+4\) and \(2n+5\). Their gcd is 1, proving **every** cloned adjacency matrix primitive, including all lengths allowed by the source assumptions.

However the two first-return walks \(e\to f\) have lengths 2 and 3, while the sole first-return walk \(f\to e\) has length 2. Hence

\[
R_2=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
R_3=\begin{pmatrix}0&1\\0&0\end{pmatrix},\qquad
H(t)=\begin{pmatrix}0&t^{-2}+t^{-3}\\t^{-2}&0\end{pmatrix}.
\]

At \(t=1\),

\[
R=H(1)=\begin{pmatrix}0&2\\1&0\end{pmatrix},
\quad R^2=2I,\quad
\operatorname{spec}(R)=\{\sqrt2,-\sqrt2\}.
\]

Thus \(R\) (and the positively weighted return matrix \(\hat T_\lambda\), which has the **same bipartite support** for every \(\lambda>0\)) is irreducible of period two, not primitive. Nonetheless \(\rho(R)=\sqrt2>1\), and the corrected clone equation (1) gives

\[
\lambda_n^n=\lambda_n^{-2}\sqrt{1+\lambda_n^{-1}}
\quad\Longleftrightarrow\quad
\lambda_n^{2n+5}=\lambda_n+1.
\]

The explicit graph also shows why replacing a primitivity claim with irreducibility is sufficient: the Perron root and **normalized positive Perron vectors** remain unique; only the strict dominance of its modulus over all other eigenvalues is lost. The original \(\hat T_\lambda\) construction is still irreducible, and the corrected asymptotic argument does not require every return graph to be aperiodic.

**Review boundary.** This refutes the stated primitivity conclusion under the printed graph hypotheses, not the claim that all \(T_n\) are primitive (they are, in this example). It does not establish a counterexample to Theorem A, B or C of the complex-dynamics paper. The two errors—positive rather than negative return-length weights, and unjustified primitivity of the reduced return graph—should be reported as separate finite-graph issues to the authors.

## 6. Reproducibility and publication boundary

Run the accompanying \`verify_clone_spectral.py\` (NumPy required). It independently assembles full cloned adjacency matrices, independently assembles the return polynomial, compares the Perron roots for \(n=0,1,2,4,8,16\), and checks (3), (5) numerically on both a one-gate and a two-gate graph.

Before making a published correction claim: (i) obtain an independent specialist reading of the exact Appendix C conventions, (ii) check for newer versions or author errata, and (iii) ask the authors whether the power sign was intentional. No currently open MLC gate is affected by this document.