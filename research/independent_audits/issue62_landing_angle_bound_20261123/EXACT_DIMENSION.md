# Issue 62: exact one-third dimension from the actual fine return

Date: 2026-11-23 (America/New_York). Repository at initial base
ed64c7ad839dcc8b799d53379434f892fdc92a2c.

**Continuation.** The [physical octal reconstruction](../issue62_octal_reconstruction_20261123/README.md) now determines the sets themselves by an inverse-fiber argument and entropy saturation. Its [measure and trace proof](../issue62_octal_reconstruction_20261123/MEASURE_AND_TRACE.md) supplies quantitative consequences on those actual sets. The independent dimension proof below remains valid with its original hypotheses and source attribution.

## Conclusion and dependence

The established upper bound can be sharpened to

\[
\boxed{\dim_H E_0=\dim_H E_1=\dim_H E_2=\dim_H E=\frac13.}
\tag{1}
\]

Here these are the **actual landing-angle sets**, in the normalized external-angle coordinate of the actual quadratic-like return \(G=f_{c_*}^3\). They are not defined to be the survivor sets of a finite graph.

The new lower bound uses the already written conjugacy of \(G^3|K9\) to the Chebyshev interval map and the classical entropy–dimension theorem for multiplication maps on the circle. It requires neither equality of the physical set with the graph survivor nor a finite-to-one bound for the landing map. A compact invariant-core argument below removes any possible ambiguity between forward invariance and surjectivity in the dimension theorem.

The [elementary upper bound](NOTE.md) remains a separate argument using the actual source-sector inclusion and exact rational path counts. The Chebyshev entropy and the entropy–dimension theorem are classical inputs, not claims of new general theorems here.

## 1. Exact actual dynamical hypotheses, with archive locators

Use

\[
G=f_{c_*}^{3},\qquad H=G^3=f_{c_*}^{9},\qquad
C_0=K9,\quad C_1=G(C_0),\quad C_2=G^2(C_0),\quad
B=C_0\cup C_1\cup C_2.
\]

The following are the previously written physical inputs.

1. The three \(C_j\) are pairwise disjoint compact real intervals, cyclically mapped **onto** one another by \(G\). Their physical order is \(C_2<C_0<C_1\); \(0\) belongs to \(C_0\), while \(C_1\) is strictly positive and \(C_2\) strictly negative.
2. \(K3\) is the connected, locally connected dendrite filled set of the actual degree-two return \(G\). Its normalized continuous Carathéodory landing map
   \[
   L:\mathbb T\longrightarrow K3
   \]
   is onto and obeys \(L\circ d=G\circ L\), where \(d(\theta)=2\theta\bmod1\).
3. There is a homeomorphism
   \[
   h_9:C_0\longrightarrow[-2,2],\qquad
   h_9\circ H=Q_{-2}\circ h_9,\qquad Q_{-2}(x)=x^2-2.
   \tag{2}
   \]

The exact locator for (2) is
[the actual interval-root proof](../tip_interval_root_and_marked_morphism_obstruction_20261106.md),
§3, “The inner quadratic straightening is exactly Chebyshev.” Its proof applies the Douady–Hubbard straightening theorem to the actual connected filled set and uses
\(0\mapsto x_9\mapsto x_{18}\mapsto x_{18}\), with all three initial points distinct. If \(Q_a\) is the straightening, the relation gives \(a^3(a+2)=0\), and nonperiodicity excludes \(a=0\). Thus \(a=-2\), and the straightening conjugates the complete actual \(K9\) to \([-2,2]\). This is much stronger than a similarity of a finite orbit table.

The same note, §§3–4, proves \(K9=[x_9,x_{18}]=[-p,p]\) and gives the exact real interval images. The actual sole critical point and branch monotonicity are established in
[the terminal-first-child proof](../tip_kl_terminal_first_child_20261106.md),
§3. The landing map and the disjoint three-phase setup are stated in
[the native side trichotomy](../tip_native_finite_J_side_target_trichotomy_20261109.md),
§1, and in the C4 source-sector note, §5.

Define

\[
E_j=L^{-1}(C_j),\qquad E=L^{-1}(B)=E_0\cup E_1\cup E_2.
\]

Each \(E_j\) is nonempty and compact, \(d^3(E_j)\subset E_j\), and \(L|_{E_j}\) is onto \(C_j\). Surjectivity follows from surjectivity of \(L\): by its definition, every preimage of a point of \(C_j\) belongs to \(E_j\). No inverse-ray branch selection is needed.

## 2. Entropy of the actual return is \(\log 2\)

For completeness, the Chebyshev entropy can be obtained without an unproved entropy computation.

The homeomorphism

\[
\phi:[0,1]\longrightarrow[-2,2],\qquad
\phi(t)=2\cos(\pi t)
\]

conjugates the full tent map

\[
\tau(t)=
\begin{cases}
2t,&0\le t\le1/2,\\
2-2t,&1/2\le t\le1
\end{cases}
\]

to \(Q_{-2}\), since \(\phi(\tau(t))=2\cos(2\pi t)=Q_{-2}(\phi(t))\).

The upper entropy bound is immediate from the Lipschitz constant \(2\). A mesh of spacing at most \(\epsilon 2^{-N}\) in \([0,1]\) is an \((N,\epsilon)\)-spanning set, of size at most \(2+2^N/\epsilon\). Hence \(h_{\rm top}(\tau)\le\log2\).

For the lower bound fix \(n\ge2\). The map \(\tau^n\) has \(2^n\) full affine branches on the dyadic intervals of length \(2^{-n}\). Remove the first and last branches, leaving \(m=2^n-2\) branches. Choose \(0<\epsilon_n<2^{-n}\) and \(J=[\epsilon_n,1-\epsilon_n]\). The full domains of those \(m\) interior branches lie in \(J\). On each such branch take its inverse image \(J_i\) of \(J\). These are pairwise disjoint compact intervals in \(J\), with a strictly positive minimum separation \(\delta_n\), and \(\tau^n:J_i\to J\) is a homeomorphism.

Every word of length \(k\) over those \(m\) branches has a nonempty inverse cylinder. Select one point in each. Two distinct words first disagree at some time \(r<k\), so their selected points under \(\tau^{nr}\) lie in two different \(J_i\)'s and are separated by at least \(\delta_n\). Thus there are \(m^k\) points separated for \(\tau\) over \(nk\) iterates. It follows that

\[
h_{\rm top}(\tau)\ge\frac1n\log(2^n-2).
\]

Let \(n\to\infty\). Together with the upper bound this proves

\[
h_{\rm top}(Q_{-2}|[-2,2])
=h_{\rm top}(\tau)=\log2.
\tag{3}
\]

Conjugacy (2) now gives \(h_{\rm top}(H|C_0)=\log2\).

## 3. The other two physical return maps have the same entropy

There are two independent justifications.

**Actual homeomorphisms.** The only critical point of the central return \(G\) is \(0\). On \(C_1,C_2\) it is therefore real, continuous and strictly monotone. Since these phase maps are onto, \(G:C_1\to C_2\) and \(G:C_2\to C_0\) are homeomorphisms. For \(j=1,2\),

\[
\psi_j=G^{3-j}|C_j:C_j\longrightarrow C_0
\]

is a homeomorphism and commutes with \(H=G^3\). Hence it conjugates \(H|C_j\) to \(H|C_0\).

**An argument needing even less.** Even if the homeomorphism facts are not imported, the onto maps \(G^j:C_0\to C_j\) and \(G^{3-j}:C_j\to C_0\) commute with \(H\). They are continuous surjective semiconjugacies in both directions. The entropy factor inequality in each direction therefore gives equality.

For clarity, the factor inequality needs no finite-fiber hypothesis. If \(\pi:X\to Y\) is a continuous onto semiconjugacy between compact metric systems, uniform continuity gives a \(\delta>0\) such that \(\delta\)-close source points have \(\epsilon\)-close images. Choosing one preimage of each point of an \((N,\epsilon)\)-separated set in \(Y\) yields an \((N,\delta)\)-separated set in \(X\). Taking exponential growth rates proves \(h_{\rm top}(Y)\le h_{\rm top}(X)\).

Consequently

\[
h_{\rm top}(H|C_j)=\log2,\qquad j=0,1,2.
\tag{4}
\]

Also \(H=G^3\) preserves each of the three disjoint compact components of \(B\). Entropy of a finite invariant union is the maximum of the entropies of its components: the separated or spanning cardinalities differ from the largest component count by at most a factor of three. The standard iterate identity \(h_{\rm top}(G^3|B)=3h_{\rm top}(G|B)\) therefore yields

\[
h_{\rm top}(G|B)=\frac{\log2}{3}.
\tag{5}
\]

The lower dimension proof below only needs (4); it does not rely on the iterate identity.

## 4. The classical dimension theorem and the forward-invariance issue

For \(q\ge2\), a compact forward-invariant set \(X\subset\mathbb T\) for \(M_q(\theta)=q\theta\bmod1\) satisfies

\[
\dim_H X=\frac{h_{\rm top}(M_q|X)}{\log q}.
\tag{6}
\]

The original source is Harry Furstenberg, *Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine Approximation*, Mathematical Systems Theory **1** (1967), 1–49, Proposition III.1, printed pp. 36–37:

- DOI: <https://doi.org/10.1007/BF01692494>
- Original-paper scan: <https://mathweb.ucsd.edu/~asalehig/F_Disjointness.pdf>

That proposition proves equality of Hausdorff dimension, the grid-counting dimension and symbolic entropy divided by \(\log q\).

An explicit modern circle statement is Giulio Tiozzo, *Topological entropy of quadratic polynomials and dimension of sections of the Mandelbrot set*, Advances in Mathematics **273** (2015), 651–715, DOI <https://doi.org/10.1016/j.aim.2014.12.033>. The inspected author PDF is
<https://www.math.utoronto.ca/tiozzo/docs/Hdim.pdf>.
Its Proposition 5.5, printed p. 18, gives (6). The application on printed p. 26 explicitly applies it to a **forward-invariant** set and to an iterate \(D^p\), so \(M_q\) need not map \(X\) onto itself. Proposition 5.3, printed pp. 17–18, separately states the entropy factor inequality. Theorem 7.2, printed p. 20, provides an independent check for compact forward-invariant subsets of a topologically finite quadratic Julia set.

The author PDF has 50 pages. The separately available arXiv version is **1305.3542v1, 15 May 2013**, 56 pages; do not silently transfer the author-PDF page locators to that version:
<https://arxiv.org/abs/1305.3542v1>.

The inspected source snapshots were downloaded on 2026-11-24. The SHA-256 of the author PDF is 8e7b97b5057384b3c7164343aae8450e4f10c3eca93e564c0870fef0f3dfa933; the SHA-256 of the original Furstenberg scan is cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358.

Here is also a direct way to avoid any convention about the word “invariant” in (6). It is sufficient to use the theorem only on compact sets mapped onto themselves, as follows.

### Invariant-core lemma

Let \(F:X\to X\) and \(R:Y\to Y\) be continuous maps of nonempty compact metric spaces, with \(R\) onto. Suppose \(\pi:X\to Y\) is continuous and onto, and \(\pi F=R\pi\). Put

\[
X_\infty=\bigcap_{n\ge0} F^n(X).
\]

Then \(X_\infty\) is nonempty and compact, \(F(X_\infty)=X_\infty\), and \(\pi(X_\infty)=Y\).

**Proof.** The nonempty compact sets \(F^n(X)\) are nested. For \(y\in Y\), every compact set \(F^n(X)\cap\pi^{-1}(y)\) is nonempty because \(\pi(F^n(X))=R^n(Y)=Y\). Their nested intersection is nonempty, proving \(\pi(X_\infty)=Y\). The inclusion \(F(X_\infty)\subset X_\infty\) is immediate. Conversely, for \(x\in X_\infty\), the compact sets
\[
F^{-1}(\{x\})\cap F^n(X)
\]
are nested and nonempty, because \(x\in F^{n+1}(X)\). Their intersection supplies \(x'\in X_\infty\) with \(F(x')=x\). This proves equality. \(\square\)

## 5. Lower bound for every actual phase set

Fix \(j\in\{0,1,2\}\) and apply the core lemma with

\[
X=E_j,\quad F=d^3=M_8,\quad
Y=C_j,\quad R=H|C_j,\quad\pi=L|E_j.
\]

All hypotheses were checked in §1; \(R\) is onto because the three phase maps form an onto cycle. We obtain a nonempty compact set

\[
E_{j,\infty}=\bigcap_{n\ge0}d^{3n}(E_j)\subset E_j
\]

on which \(d^3\) is onto, and an onto factor \(L:E_{j,\infty}\to C_j\). By (4) and the elementary factor inequality,

\[
h_{\rm top}(d^3|E_{j,\infty})
\ge h_{\rm top}(H|C_j)=\log2.
\]

Apply Furstenberg's theorem with \(q=8\):

\[
\dim_H E_j\ge\dim_H E_{j,\infty}
=\frac{h_{\rm top}(d^3|E_{j,\infty})}{\log8}
\ge\frac{\log2}{3\log2}=\frac13.
\tag{7}
\]

The separately proved elementary upper bound gives \(\dim_H E\le1/3\). Since \(E_j\subset E\), (7) proves (1).

This argument does not require \(d(E_j)=E_{j+1}\), nor a surjectivity assertion for a particular angular phase map, nor a bounded number of landing rays at any point. Those would be stronger facts than needed.

## 6. Grid boundaries are absent, giving box dimension as well

The exact graph proof defines \(Q=\{i/768:0\le i<768\}\) and \(Z=\bigcup_{r\ge0}d^{-r}(Q)\). Since \(768=3\cdot2^8\),

\[
d^8(Q)=\{0,1/3,2/3\}.
\]

Each of these three angles lies outside the actual open survivor region
\(S=I\cup d^{-1}(I)\cup d^{-2}(I)\), as direct rational comparison with the 28 intervals shows. Every point of \(E\) has every forward iterate in \(S\). Therefore

\[
E\cap Z=\varnothing.
\tag{8}
\]

Thus the graph proof's depth-\(3k\) cylinders cover **all** of \(E\), with at most \(96\cdot2^k\) intervals of diameter \(1/(768\cdot8^k)\). Interpolation between the successive scales, whose ratio is the fixed number \(8\), gives \(\overline{\dim}_B E\le1/3\). Since Hausdorff dimension is no larger than lower box dimension for compact subsets of the circle, (1) implies

\[
\boxed{\dim_H E_j=\underline{\dim}_B E_j
=\overline{\dim}_B E_j
=\dim_H E=\underline{\dim}_B E=\overline{\dim}_B E=\frac13.}
\tag{9}
\]

The same covers also give finite \(1/3\)-dimensional Hausdorff content in the limit:
\(\mathcal H^{1/3}(E)\le96\cdot768^{-1/3}\) under the convention using sums of diameter powers. This does **not** establish positivity of that Hausdorff measure, so no positive-measure claim is made.

The quantitative statement is in the normalized G external-angle coordinate. A topological side parametrization preserves nowhere density, but an arbitrary homeomorphism need not preserve Hausdorff or box dimension. In particular (9) is not a physical conformal width or logarithmic capacity statement.

## 7. Every individual original seam root set also has dimension one third

The actual source symmetries allow one more precise conclusion. Number the four seams as

\[
\begin{aligned}
I_0&=(41/192,43/192),&
I_1&=(53/192,55/192),\\
I_2&=(137/192,139/192),&
I_3&=(149/192,151/192),
\end{aligned}
\]

and put \(A_i=E_0\cap I_i\). The complete source-sector theorem gives \(E_0=\bigcup_{i=0}^3A_i\), and each \(A_i\) is compact inside its open seam.

The required physical symmetry is explicitly present in
[the terminal-first-child proof](../tip_kl_terminal_first_child_20261106.md),
§7: it constructs a real-symmetric normalized straightening \(h_G\) with \(h_G(0)=0\) to a real quadratic \(Q\). The source's physical landing map is \(L=h_G^{-1}\circ\ell_Q\), where \(\ell_Q\) is the normalized quadratic landing map.

First \(K3\) is invariant under \(z\mapsto-z\). The central domain of the even map \(G\) is symmetric, and \(G(-z)=G(z)\), so the filled-set membership condition is the same for \(z\) and \(-z\). For \(z\in K3\), conjugacy gives

\[
Q(h_G(-z))=h_G(G(-z))=h_G(G(z))=Q(h_G(z)).
\]

Hence \(h_G(-z)=\pm h_G(z)\). For \(z\ne0\), injectivity excludes the plus sign; at \(z=0\), both values vanish. Thus

\[
h_G(-z)=-h_G(z)\quad(z\in K3).
\tag{10}
\]

The normalized external map of a real quadratic obeys reflection symmetry and odd symmetry: \(\Phi(\bar w)=\overline{\Phi(w)}\) and \(\Phi(-w)=-\Phi(w)\). The first follows from real coefficients and uniqueness of the normalization at infinity. For the second, the functional equation gives
\(Q(\Phi(-w))=\Phi(w^2)=Q(\Phi(w))\); the negative alternative is selected by the normalization near infinity and then throughout the connected exterior. Passing to the continuous boundary landing map yields

\[
\ell_Q(-\theta)=\overline{\ell_Q(\theta)},\qquad
\ell_Q(\theta+1/2)=-\ell_Q(\theta).
\]

Real symmetry of \(h_G\) and (10) therefore give

\[
L(-\theta)=\overline{L(\theta)},\qquad
L(\theta+1/2)=-L(\theta).
\tag{11}
\]

Since \(C_0=[-p,p]\), the set \(E_0\) is invariant under the two angular isometries
\(\theta\mapsto-\theta\) and \(\theta\mapsto\theta+1/2\). Exact rational endpoint calculation gives their seam permutations

\[
(0\ 3)(1\ 2),\qquad (0\ 2)(1\ 3),
\]

respectively. They generate a transitive action on the four seams and carry \(A_i\) exactly onto the corresponding \(A_{i'}\). All four \(A_i\) are therefore isometric. The finite-union formula for Hausdorff dimension, together with \(\dim_H E_0=1/3\), proves

\[
\boxed{\dim_H A_i=\underline{\dim}_B A_i
=\overline{\dim}_B A_i=\frac13\qquad(0\le i<4).}
\tag{12}
\]

For the box dimensions, the upper bound is inherited from \(E_0\), while Hausdorff dimension supplies the lower bound.

The archive's [actual finite-side classification, C4 note Theorem 5.2](../tip_native_C4_wake_root_sheet_naturality_20261109.md), identifies the original rooted finite J-side subset in tile \(j\) as the zero-translate copy of \(A_{m(j)}\), where \(m=(0\ 1)(2\ 3)\) is the mate involution. Consequently that specific rooted finite-side subset has exact Hausdorff and box dimension \(1/3\) in its unwrapped source-angle coordinate. This does not say it contains an interval; it is compact and nowhere dense.

## 8. Referee scope

It neither identifies the whole rational survivor set with physical fine landings nor fills any missing free-group connector word. The native KKL geometric-trace restriction and full marking pullback remain separate. No MLC conclusion follows from this specialized dimension calculation.

## Attribution and review

Furstenberg's entropy–dimension theorem and the classical Chebyshev entropy
are credited above. This contribution applies those theorems to the actual
archive landing sets using the separately established physical return and
sector facts. Prepared with OpenAI GPT-6 Astra Pro for proof development and
independent adversarial review. No human specialist review or new Lean
formalization has occurred.
