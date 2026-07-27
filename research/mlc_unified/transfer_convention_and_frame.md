# Source-column transfers and endpoint frames

## 1. Status

This note locks the matrix convention used by every corridor, clone, WAD-incidence,
and support-automaton calculation in this project. It also proves why spectral radius
is meaningful only for a framed return, not an unframed open transfer.

The algebraic statements are proved here. The exact typed-incidence bridge to the
KKL Value coordinate sums is source-audited below. Identifying a virtual
return with that incidence and transporting its WAD/access frame remain open
analytic tasks.

## 2. Global convention

For a transfer from a finite source set \(E\) to a finite target set \(F\), write
\[
  B:\mathbb R^E\longrightarrow\mathbb R^F,
  \qquad
  B_{ij}
  =
  \#\{\text{occurrences from source }j\in E\text{ to target }i\in F\}.
\tag{2.1}
\]
Thus columns are sources, rows are targets, and column state vectors evolve by
\[
  x_{\rm target}=Bx_{\rm source}.
\]
For chronological transfers
\[
  E_0\xrightarrow{B_1}E_1\xrightarrow{B_2}\cdots
  \xrightarrow{B_m}E_m,
\]
the composite is
\[
  B_{[1,m]}=B_m\cdots B_1.
\tag{2.2}
\]

If \(Q_k\) is the permutation identifying a new basis of \(E_k\) with the old basis,
then
\[
  B_k^{\rm new}=Q_k^{-1}B_kQ_{k-1}.
\tag{2.3}
\]
Consequently, a permutation cocycle can be gauged to the identity by taking
\(Q_k=B_kQ_{k-1}\). This proves only identity transport in the layered interior; it
does not prove corridor purity or the cross-section property.

All block incidence matrices in `virtual_support_automaton_construction.md` use the
same convention. Left/right Perron vectors and WAD coefficients must be checked
against (2.1), not inferred from an unlabeled graph picture.

### 2.1 Exact typed bridge to KKL Value

Let
\[
  N_{\beta\gamma}
  =
  \#\{\alpha\in\iota^*\beta:f_*\alpha=\gamma\},
\]
where \(\beta\) is the source Hubbard edge and \(\gamma\) the target edge. The
coordinate sums in KKL `value1.tex`, lines 57--70, unambiguously give
\[
  Nv=\lambda v,
  \qquad
  N^{\mathsf T}w=\lambda w.
\]
The project matrix in (2.1) is
\[
  \boxed{B=N^{\mathsf T}}.
\tag{2.4}
\]
For a chronological sequence,
\[
  B_m\cdots B_1=(N_1\cdots N_m)^{\mathsf T}.
\tag{2.5}
\]
Thus the project product order is correct. The KKL symbol \(T_F\) itself has
incompatible orientation cues in the checked TeX: the ordinary right-eigenvector
reading gives \(T_F=N\) and hence \(B=T_F^{\mathsf T}\), while the basis-image
reading of the pushforward arrow gives \(T_F=B\). We therefore source-lock \(N\)
and (2.4), not either unconditional equation involving the ambiguous symbol
\(T_F\).

Since the source coordinate sums give \(Nv=\lambda v\) and
\(N^{\mathsf T}w=\lambda w\), in the project convention \(v\) is the left
eigenweight and \(w\) is the right eigenvector:
\[
  v^{\mathsf T}B=\lambda v^{\mathsf T},
  \qquad
  Bw=\lambda w.
\]
KKL's Hubbard-edge Value coefficient translates as
\[
  c_\beta=v_\beta^2w_\beta
  =(\ell_{\rm left})_\beta^2(r_{\rm right})_\beta.
\tag{2.6}
\]
Swapping the exponents is not a normalization. The complete source audit and a
nonsymmetric numerical check are in
`kkl_transfer_orientation_audit.md`, Sections 3--5.

### 2.2 Clone-source quarantine

The same audit, Section 6, finds that the displayed finite-\(n\) clone recurrence
in the checked KKL snapshot is internally inconsistent in orientation/exponent
sign. A literal primitive three-vertex example contradicts the displayed exact
equation while still exhibiting the advertised limiting behavior. Accordingly:

1. the typed incidence bridge (2.4) and the left/right equations are
   proof-licensed for the KKL Value calculation;
2. for a literal fixed cross-section clone satisfying the stated graph hypotheses,
   the independently proved row-source reduction is
   \[
     H(t)=t^{-1}D(tI-Q)^{-1}C=\sum_k t^{-k}R_k,
   \]
   while the project source-column reduction is \(H(t)^{\mathsf T}\);
3. the KKL \(+\lambda^k\) finite-\(n\) clone equation and its proof may not be
   imported verbatim.

Transposition preserves spectral radius; it does not change \(+\!k\) to \(-\!k\).

## 3. Why product order is substantive

Let
\[
 A=\begin{pmatrix}0&0\\1&1\end{pmatrix},
 \quad
 B=\begin{pmatrix}0&0\\0&1\end{pmatrix},
 \quad
 C=\begin{pmatrix}0&1\\0&1\end{pmatrix}.
\]
Then
\[
  ABC=\begin{pmatrix}0&0\\0&1\end{pmatrix},
  \qquad
  CBA=\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]
Their spectral radii are \(1\) and \(2\), respectively. Therefore reversing (2.2)
can manufacture an entropy witness. Every future calculation must state whether its
word is chronological and use (2.2).

## 4. Framed returns

An open transfer \(B:\mathbb R^E\to\mathbb R^F\) is not an endomorphism unless an
identification \(h:F\to E\) is part of the data. Its matrix spectral radius is not
invariant under independent changes of the target frame.

For example, set
\[
  S=\begin{pmatrix}1&1\\0&1\end{pmatrix},
  \qquad
  J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]
Merely swapping the target labels replaces \(S\) by \(JS\) in the source-column
convention, but
\[
  \rho(S)=1,
  \qquad
  \rho(JS)=\frac{1+\sqrt5}{2}.
\tag{4.1}
\]

A **framed return** is either:

1. a closed word returning to the same source-faithful automaton state and the same
   declared core frame; or
2. an open word equipped with a canonical source-licensed endpoint identification
   that is retained as part of the state.

### Lemma 4.1 (return spectral invariance)

Under a relabeling \(Q\) of the common base frame, a framed return matrix \(P\)
changes to \(Q^{-1}PQ\). Hence its characteristic polynomial, spectral radius,
Frobenius type, and primitivity are frame invariant.

**Proof.** Apply (2.3) at the common initial and terminal frame. The intermediate
permutations telescope in the chronological product, leaving \(Q^{-1}PQ\).
Similarity preserves the stated quantities. \(\square\)

No analogous conclusion holds for independent initial and terminal relabelings of an
open transfer, as (4.1) shows.

## 5. Entropy certification rule

A support product is eligible for dynamical Perron/Value use only after all of the
following are proved:

1. it is a framed return in the sense of Section 4;
2. the word is dynamically repeatable in the exact decorated language;
3. its matrix is the source-defined forward count incidence in convention (2.1),
   with the proved typed identification \(B=N^{\mathsf T}\) and the KKL Value
   left/right equations;
4. its cyclic recurrent component is nontrivial and the required primitive grouping
   has been established;
5. the corresponding WAD pullback incidence uses the same frame and product order,
   and its actual pullback exponent is at least any delay exponent used in the graph
   multiplier;
6. all counter guards are fiber-safe and every retained stack word returns to the
   required state.

A branch-recurrent support of a one-way word proves only a statement about the
displayed matrix. It is not a gauge-invariant dynamical entropy witness.

## 6. Regression tests

Every transfer edit must preserve these tests:

1. chronological \(A,B,C\) evaluates as \(CBA\), never \(ABC\);
2. a permutation cocycle becomes identity under (2.3);
3. \(S\) and \(JS\) are recognized as the same open bipartite transfer under a
   target relabeling but are forbidden from sharing a spectral classification;
4. a closed return changes only by similarity under a base-frame relabeling;
5. the zero singleton SCC is transient, not entropy producing;
6. WAD/core incidence composes in the same chronological order as the core matrix;
7. for one occurrence \(1\to2\), the raw row-source incidence \(N\) and the project
   source-column matrix \(B\) are transposes;
8. on a nonsymmetric primitive example, KKL Value uses
   \(\ell_{\rm left}^2r_{\rm right}\), not
   \(r_{\rm right}^2\ell_{\rm left}\);
9. no transpose is accepted as a repair of the quarantined clone exponent sign.
