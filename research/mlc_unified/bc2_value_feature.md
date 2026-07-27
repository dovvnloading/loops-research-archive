# BC2: minimal Value features and the source-licensed primitive block

## 1. Status

This note solves the **linear lifted-state** form of the finite-support observability
problem created by `bc1_finite_port_response.md`, Theorem 7.1.

It proves:

1. an exact row-space criterion for whether a collection of WAD valuations is
   determined by a compressed linear state;
2. the exact minimal number of additional Value moments;
3. one extra scalar is sufficient for one fixed KKL valuation, independently of WAD
   support size;
4. on one source-licensed KKL primitive block, that scalar satisfies the imported
   strict pullback contraction with an exact additive Value-error term.

It does not prove that the same finite feature family works across arbitrary
primitive/neutral/virtual chart changes. That is
`H2_VALUE_FEATURE_REALIZATION`.

## 2. Linear support model

Fix a finite set \(A\) of global WAD support coordinates and write its weight vector
as
\[
  w=(w_a)_{a\in A}\in\mathbb R_{\ge0}^A.
\]
Any lifted homogeneous state made of total weights, entries of the uneliminated port
Laplacian, standard-width aggregates, and already retained linear moments has the form
\[
  z=Tw
\tag{2.1}
\]
for a real matrix \(T\).

A terminal response obtained after Schur elimination is generally a rational,
nonlinear function of \(w\). The row-space theorems below apply to it only after all
relevant intermediate ports are retained in the lifted Laplacian. For a genuinely
eliminated terminal response, observability must instead be checked directly on the
fibers of its nonlinear state map. Adjoining the Value moment itself remains a valid
repair in either model.

A finite family of WAD valuations has coefficient matrix \(C\):
\[
  V(w)=Cw,
  \qquad
  C=
  \begin{pmatrix}
    c_1^{\mathsf T}\\
    \vdots\\
    c_k^{\mathsf T}
  \end{pmatrix}.
\tag{2.2}
\]
For KKL Value,
\[
  c_j(a)=\ell_j(a)^2\ge0.
\]

### Definition 2.1

The valuation family \(C\) is **observable from \(T\)** if
\[
  Tw=Tw'
  \quad\Longrightarrow\quad
  Cw=Cw'
\tag{2.3}
\]
for all \(w,w'\in\mathbb R_{\ge0}^A\).

This definition permits an arbitrary recovery function from \(Tw\); linear recovery is
not assumed.

## 3. Exact observability theorem

### Theorem 3.1 (row-space criterion)

The following are equivalent:

1. \(C\) is observable from \(T\);
2. \(\ker T\subseteq\ker C\);
3. \(\operatorname{row}(C)\subseteq\operatorname{row}(T)\);
4. there is a matrix \(R\) such that
   \[
     C=RT,
     \qquad
     V(w)=Rz.
   \tag{3.1}
   \]

**Proof.** Items 2--4 are equivalent finite-dimensional linear algebra.
Item 4 immediately implies Item 1.

Assume Item 1 and take \(h\in\ker T\). Choose a strictly positive vector \(w_0\) and
\(\epsilon>0\) small enough that
\[
  w_0+\epsilon h\ge0,
  \qquad
  w_0-\epsilon h\ge0.
\]
Their \(T\)-states agree. Observability gives
\[
  C(w_0+\epsilon h)=C(w_0-\epsilon h),
\]
so \(Ch=0\). Thus \(\ker T\subseteq\ker C\), proving Item 2. \(\square\)

The positive cone does not weaken the criterion: a kernel direction can always be
tested around a sufficiently positive base weight.

### Corollary 3.2 (minimal augmentation rank)

Let
\[
  d_{\rm miss}
  =
  \operatorname{rank}
  \begin{pmatrix}
    T\\ C
  \end{pmatrix}
  -
  \operatorname{rank}T.
\tag{3.2}
\]
Then \(d_{\rm miss}\) is exactly the minimum number of additional linear moments
needed to make \(C\) observable.

**Proof.** The number in (3.2) is the dimension of the image of
\(\operatorname{row}(C)\) in the quotient
\[
  \mathbb R^A/\operatorname{row}(T).
\]
Adding representatives of a basis of that image makes every row of \(C\) lie in the
augmented row space, so Theorem 3.1 gives observability. Fewer rows cannot span an
image of dimension \(d_{\rm miss}\). \(\square\)

### Corollary 3.3 (one valuation needs at most one new scalar)

For one valuation \(c^{\mathsf T}w\), either it is already observable from \(T\), or
adjoining the single coordinate
\[
  V_c(w)=c^{\mathsf T}w
\tag{3.3}
\]
makes it observable. This statement is independent of \(|A|\).

## 4. Application to the lifted response

For an incidence-faithful port graph, let
\[
  b(a)=e_{s(a)}-e_{t(a)}.
\]
The response and total weight are linear functions of \(w\):
\[
  Q(w)=\sum_aw_a,
  \qquad
  L(w)=\sum_aw_a\,b(a)b(a)^{\mathsf T}.
\tag{4.1}
\]
After vectorizing the symmetric response matrix, the corresponding state matrix has
columns
\[
  T_{\rm resp}(:,a)
  =
  \left(
    1,\,
    \operatorname{vec}_{\rm sym}(b(a)b(a)^{\mathsf T}),\,
    s_1(a),\ldots,s_m(a)
  \right),
\tag{4.2}
\]
where the \(s_j\) are any other retained linear aggregates.

### Corollary 4.1 (exact lifted Value-faithfulness test)

A KKL valuation with coefficient \(c(a)=\ell(a)^2\) is determined by the recorded
response/aggregate state exactly when
\[
  c\in\operatorname{row}(T_{\rm resp}).
\tag{4.3}
\]

Thus “Value-faithful ports” is not a label. For each proposed **lifted linear**
compression, (4.3) is the exact finite test. Theorem 7.1 of
`bc1_finite_port_response.md` is the case where two columns of \(T_{\rm resp}\) agree
while their \(c\)-entries differ.

If intermediate ports have already been Schur-eliminated, the exact replacement test
is
\[
  Z(w)=Z(w')
  \Longrightarrow
  c^{\mathsf T}w=c^{\mathsf T}w',
\tag{4.4}
\]
where \(Z\) is the nonlinear terminal-state map. The row-space rank formula must not
be applied directly to \(Z\).

## 5. Source-licensed primitive Value block

Let \(F\) be a primitively renormalizable, periodically repelling \(\psi\)-ql map in
the setting of KKL's Value Theorem, with core eigenvalue \(\lambda_F>1\). Let
\[
  V_F(X)
  =
  \sum_aX(a)\ell_F(a)^2.
\tag{5.1}
\]
On a base Hubbard edge \(\beta\), the typed incidence audit gives
\[
  \ell_F(\beta)^2=v_\beta^2w_\beta
  =(\ell_{\rm project,left})_\beta^2(r_{\rm project,right})_\beta,
\]
where \(B=N^{\mathsf T}\). This exponent assignment is part of the source identity,
not a freely swappable normalization.

KKL proves
\[
  V_F(X)\ge V_F(Y)
  \quad\text{when }X\dominates Y,
\tag{5.2}
\]
and
\[
  V_F((f^n)^*X)
  \le
  \lambda_F^{-n}V_F(X).
\tag{5.3}
\]

### Theorem 5.1 (exact affine Value contraction)

Suppose the output WAD \(Y\), pulled back and expressed in the same global support
coordinates, satisfies
\[
  Y\le (f^n)^*X+E
\tag{5.4}
\]
coefficientwise for a nonnegative WAD error \(E\). Then
\[
  V_F(Y)
  \le
  \lambda_F^{-n}V_F(X)+V_F(E).
\tag{5.5}
\]
If
\[
  n\log\lambda_F\ge E_*,
\]
the homogeneous part contracts by at most \(e^{-E_*}<1\).

**Proof.** Positivity and linearity of \(V_F\) applied to (5.4) give
\[
  V_F(Y)
  \le
  V_F((f^n)^*X)+V_F(E).
\]
Apply (5.3). The entropy form follows from
\(\lambda_F^{-n}=e^{-n\log\lambda_F}\). \(\square\)

For this one block, the augmented coordinate \(V_F(X)/r_B\) is therefore a complete
observable for the KKL Value contraction, regardless of the number of WAD support
coordinates. No reconstruction from \(\Lambda_B\) is needed.

This is not yet the complete KKL tame argument: one must still prove the output
comparison (5.4), control \(V_F(E)\), and handle the Wave alternative under the exact
source hypotheses.

## 6. Corrected fixed cross-section cloning special case

KKL's clone appendix fixes a primitive directed graph \(A\), a cross section \(E\),
and a crossing bound \(N\), replaces \(E\) by a chain of \(n+1\) clones, and
separately assumes the cloned graphs \(A_n\) are primitive. Base primitivity alone
does not imply this extra hypothesis. For the Perron--Frobenius eigenvalue
\(\lambda_n\), the appendix states
\[
  \lambda_n\longrightarrow1,
  \qquad
  \lambda_n^n\longrightarrow h(1)>1,
\tag{6.1}
\]
with convergence of a normalized eigenvector on the fixed cross section. The checked
finite-\(n\) recurrence used in that passage is false, as isolated in
`kkl_transfer_orientation_audit.md`, Section 6. Therefore its proof is not imported.
The source-independent theorem in `corrected_clone_theorem_derivation.md` derives
instead
\[
  H(t)=\sum_k t^{-k}R_k,
  \qquad
  \rho(H(\lambda_n))=\lambda_n^n,
\]
and proves (6.1), with \(h(1)=\rho(H(1))\), for every fixed literal clone satisfying
its stated hypotheses.

### Corollary 6.1 (uniform contraction of a fixed complete cloned block)

Assume a fixed source-licensed literal cloning sequence satisfying the corrected
fixed-cross-section theorem. Then there are \(\mu_{\rm cl}>1\) and \(n_0<\infty\)
such that
\[
  \lambda_n^n\ge\mu_{\rm cl}
\tag{6.2}
\]
for every \(n\ge n_0\). If a source-licensed KKL primitive block has this cloned core
graph and its complete dynamical step is the \(n\)-fold pullback, then
\[
  V_n((f^n)^*X)
  \le
  \mu_{\rm cl}^{-1}V_n(X).
\tag{6.3}
\]

**Proof.** Choose any
\[
  1<\mu_{\rm cl}<h(1).
\]
Equation (6.1) gives (6.2) for all sufficiently large \(n\). Apply KKL Value
contraction with core eigenvalue \(\lambda_n\):
\[
  V_n((f^n)^*X)
  \le
  \lambda_n^{-n}V_n(X)
  \le
  \mu_{\rm cl}^{-1}V_n(X).
\]
\(\square\)

This is a genuine complete-block contraction even though the elementary factor
\(\lambda_n^{-1}\) tends to one. It uses the independent corrected theorem and does
not validate or silently import the printed finite-\(n\) source recurrence.

It does not prove that a virtual corridor is such a clone, that the transpose
eigenweights needed for uniform Value/size comparison have uniformly controlled
cross-section ratios, or that surface/WAD errors satisfy the required discounted
budget.

## 7. Transition between different valuations

Let a nonnegative linear WAD transition be
\[
  w_{\rm out}\le A_Bw_{\rm in}+e_B,
\tag{7.1}
\]
and let \(C_{\rm out}\) contain the valuations required after the transition. Assume
the input uses a lifted linear state. Then
\[
  C_{\rm out}w_{\rm out}
  \le
  C_{\rm out}A_Bw_{\rm in}+C_{\rm out}e_B.
\tag{7.2}
\]

### Proposition 7.1 (exact transition-observability criterion)

The homogeneous term in (7.2) is determined by an input state
\(z_{\rm in}=T_{\rm in}w_{\rm in}\) for all nonnegative weights if and only if
\[
  \operatorname{row}(C_{\rm out}A_B)
  \subseteq
  \operatorname{row}(T_{\rm in}).
\tag{7.3}
\]
When (7.3) holds there is a matrix \(R_B\) with
\[
  C_{\rm out}A_B=R_BT_{\rm in}.
\tag{7.4}
\]

**Proof.** Apply Theorem 3.1 to the coefficient matrix
\(C_{\rm out}A_B\). \(\square\)

For a monotone cone transition one additionally needs \(R_B\) to preserve the
declared state cone, normally by having nonnegative coefficients in the chosen chart.
Row-space observability alone does not imply positivity or contraction.

## 8. Remaining mixed-block theorem

### Uniform Value-Feature Realization (`OPEN`)

For every complete positive-entropy block:

1. specify every outgoing valuation and its exact source hypotheses;
2. construct the WAD transition \(A_B\) or a nonlinear domination certificate;
3. retain a lifted feature matrix \(T_B\) satisfying (7.3), or prove the direct fiber
   condition (4.4) for a nonlinear terminal response;
4. prove the missing rank
   \[
     \operatorname{rank}
     \begin{pmatrix}
       T_B\\ C_{\rm out}A_B
     \end{pmatrix}
     -
     \operatorname{rank}T_B
   \]
   is universally bounded after translation/neutral compression;
5. prove a positive chart representation with strict contraction after the complete
   entropy-clock grouping;
6. convert all local errors to the same outgoing Value coordinates with the exact
   future discount.

Theorem 5.1 closes the same-valuation primitive algebra. Items 2--6 are the
primitive/neutral/virtual interpolation problem.

## 9. Adversarial audit

The finite-feature proposal fails if:

1. the number of linearly independent outgoing valuation rows grows without bound;
2. a chart change has (7.3) but every recovery matrix has a negative coefficient in a
   coordinate where monotonicity is required;
3. the support transition is nonlinear in a way not represented by a declared
   domination certificate;
4. the valuation changes after a later pullback not included in the current feature
   family;
5. a small core eigenvalue is counted as uniform contraction without entropy-clock
   grouping;
6. \(V_F(E)\) has no relative, discounted, or telescoping bound.

## 10. Source lock

KKL26 `value1.tex`, lines 6--20, defines expanding valuations; lines 45--53 give the
harmonic/geometric inequality used for domination; lines 56--111 construct
\(\ell_F\), prove domination monotonicity, and prove pullback contraction. These are
imported only for a primitively renormalizable periodically repelling \(\psi\)-ql map.

KKL26 `waves-with-Misha.tex`, lines 2236--2318, states fixed-cross-section cloning,
\(\lambda_n^n\to h(1)>1\), \(\lambda_n\to1\), and eigenvector convergence. The
displayed exact recurrence in the same proof is contradicted by the literal
three-vertex test in `kkl_transfer_orientation_audit.md`, Section 6.1. Corollary 6.1
invokes the internally proved corrected fixed-cross-section theorem and combines it
with imported KKL Value contraction.

The row-space results, minimal-rank formula for lifted states, lifted-response test,
and affine-error reduction in this note are internal finite-dimensional proofs.
