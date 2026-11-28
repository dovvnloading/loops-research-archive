# Candidate retained before formalization: continuous two-polynomial semiconjugacy

## Exact candidate

For \(c,d\in\mathbb C\), let \(h:\mathbb C\to\mathbb C\) be continuous and suppose, for every \(z\in\mathbb C\),
\[
 h(z^2+c)=h(z)^2+d,\qquad
 h(z^2+c+1)=h(z)^2+d+1.
\tag{S}
\]
Then either \(h(z)=z\) for every \(z\) and \(d=c\), or \(h(z)=\overline z\) for every \(z\) and \(d=\overline c\).

No injectivity, surjectivity, properness, orientation, value at zero, differentiability, or normalization at infinity is assumed. The object is a continuous simultaneous semiconjugacy of two specified members of the actual quadratic family.

### MLC-relevant conclusion to be proved in Lean

Let
\[
M=\{c\in\mathbb C:\exists B\in\mathbb R\ \forall n,\ |f_c^n(0)|\le B\}.
\]
Let \(q:M\to Y\) be a continuous surjection with connected fibers, with \(Y\) Hausdorff and locally connected. Fix \(c\in M\). Assume that for every \(d\) in the fiber of \(c\), a continuous \(h\) satisfying (S) exists. Then the fiber is \(\{c\}\), and every relative neighborhood of \(c\) in the actual \(M\) contains a relatively open connected neighborhood.

The quotient is an explicit hypothesis. Construction or identification of a canonical pinched-disk quotient is not being claimed. Existence of these simultaneous semiconjugacies on any unresolved combinatorial fiber also remains open. The additional equation is the criterion, not an assumption of parameter equality or singletonness.

## New step to attempt

Subtracting the two equations and using surjectivity of the complex square gives
\[
h(w+1)=h(w)+1.
\]
The equations at zero and one then force \(h(0)=0\); consequently \(h(c)=d\).

The substantive step is automatic preservation of the entire real translation flow from this single discrete translation, without assuming \(h\) is invertible.

Fix \(z\in\mathbb C\), \(t\in\mathbb R\). Choose integers \(m_n\) with \(m_n/(2n)\to t\), and select the square root near \(n+z+t\), defining \(z_n\) by
\[
(z_n+n)^2=(z+n)^2+m_n,\qquad z_n\to z+t.
\]
The integer translation identity and (S) give
\[
(h(z_n)+n)^2=(h(z)+n)^2+m_n.
\]
Hence
\[
h(z_n)-h(z)=\frac{m_n}{2n}-
 \frac{h(z_n)^2-h(z)^2}{2n}\longrightarrow t.
\]
Continuity now gives \(h(z+t)=h(z)+t\). This proves a flow-preservation fact, not just uniqueness of a homeomorphic conjugacy.

The remainder is an exact quadratic calculation. With \(H(y)=h(iy)\), real covariance gives \(h(x+iy)=x+H(y)\). Evaluate (S) at \(iy\):
\[
H(y)^2=-y^2.
\]
Evaluate it at \(x+i\), and use \(H(1)^2=-1\):
\[
H(2x+\operatorname{Im}c)=2xH(1)+H(\operatorname{Im}c).
\]
Putting \(x=-\operatorname{Im}c/2\) and then varying \(x\) gives \(H(y)=yH(1)\) for all \(y\). Since \(H(1)=i\) or \(-i\), the claimed classification follows. In particular, injectivity and surjectivity are conclusions.

Every parameter in the specified fiber therefore belongs to \(\{c,\overline c\}\). Connectedness makes this finite fiber a singleton. Classical compact-monotone-quotient topology then gives the stated neighborhood basis in \(M\).

## Classical screen and discarded statements

1. **Discarded: parameter separation by angled internal addresses.** Schleicher, *Internal Addresses of the Mandelbrot Set and Galois Groups of Polynomials*, Theorem 3.9, already characterizes combinatorial classes by these addresses. Separating all points inside a nonhyperbolic class would simply assume the unresolved rigidity. [Primary text](https://armj.math.stonybrook.edu/html-articles/Files-2015-2024/16-42/).

2. **Discarded: finite Thurston contraction and spectral degeneration.** These do not by themselves compare increasing postcritical marking spaces or identify actual parameter fibers. Buff–Epstein–Koch, *Eigenvalues of the Thurston Operator*, Theorems 1.4–1.5 and section 9.4, already provide unicritical eigenvalue bounds, accumulation, and critical-orbit characteristic formulas. [Primary author text](https://public.websites.umich.edu/kochsc/eigenvalues.pdf).

3. **Discarded: recurrence instability as a new reduction.** Rivera-Letelier, *Rational Maps with Decay of Geometry: Rigidity, Thurston's Algorithm and Local Connectivity*, Theorem D and Appendix 9, already relate this to MLC. [Primary text](https://www.math.stonybrook.edu/preprints/ims00-09.pdf).

4. **Discarded: the homeomorphism version of (S) as new.** It reduces to classical Shcherbakov–Nakai rigidity. The unit translation and the inverse-branch map \(A(z)=\sqrt{z^2+1}\), in the coordinate \(w=1/z\), give tangent-to-identity germs of different orders:
\[
T(w)=w/(1+w),\qquad A(w)=w/\sqrt{1+w^2}.
\]
Their germ group is non-solvable by Nakai's Proposition 1.7, and Theorem 4 / Theorem 5.1 gives conformal or anticonformal rigidity for a linking homeomorphism. [Nakai, 1994 primary text](https://www.numdam.org/article/AIF_1994__44_2_569_0.pdf).

5. **Why the retained statement is stronger than that citation.** Nakai's linking map is a homeomorphism of neighborhoods and induces a germ-group isomorphism. In (S), \(h\) is merely continuous and could a priori identify points or fail to have open image; an inverse and an infinity germ are unavailable. The square-root flow argument proves automatic noncollapse directly. No theorem in the checked sources supplies this missing conclusion for the two specified polynomials. The simple real-valued square-and-unit-translation functional equation is classical; the claim of new content is the unrestricted complex-parameter, possibly noninjective semiconjugacy theorem and its proved fiber consequence, not the general theme of functional-equation rigidity.

6. **Full polynomial-semigroup rigidity is not assumed.** Cabrera–Makienko–Plaumann, *Semigroup representations in holomorphic dynamics*, Proposition 7 and Theorem 13, treat full polynomial/rational semigroup automorphisms or sandwich-semigroup isomorphisms. The two equations (S) do not give such an isomorphism. [Primary text](https://arxiv.org/pdf/1009.3000).

7. **Existing archive work.** Main's mixed-susceptibility modules are excluded and will not be imported. Open PR #276 proves a different theorem for an injective map commuting with a quarter-turn. The retained statement assumes neither injectivity nor quarter-turn covariance; it permits complex conjugation. Its root-flow proof uses one translation direction and is not a use of PR #276. [PR #276](https://github.com/dovvnloading/loops-research-archive/pull/276).

8. **Classical endpoint, credited.** Singleton-fiber implications to local connectivity are classical, e.g. Schleicher, *On Fibers and Local Connectivity of Mandelbrot and Multibrot Sets*, Proposition 3.5 and Corollary 3.6. The archive's independent \`QuadraticMonotoneFiberTopology\` gives the explicit compact-monotone formulation for Lean. [Primary text](https://arxiv.org/pdf/math/9902155).

## Retention decision and limits

Retain the continuous-semiconjugacy statement for formalization, and reject the homeomorphism-only statement as the requested new result. The missing automatic-noncollapse step is explicit and has a proposed proof. This is a source-based originality assessment, not a certificate of worldwide priority; specialist review remains necessary.

This record precedes all new Lean code. No successful compilation is claimed here. If the automatic-noncollapse argument fails or a classical theorem is found that supplies it directly, the candidate must be rejected rather than relabeled.
