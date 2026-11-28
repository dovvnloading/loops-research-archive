# Source comparison for the critical-orbit projective jet

Audit date: 2026-11-28. This file records the candidate selected before
formalization, the closest primary results checked, and the limits of the
novelty claim. The compiled theorem inventory and validation status belong in
[NOTE.md](NOTE.md). Statements below are not certificates of compilation.

## The precise candidate retained

Write

\[
f_c(z)=z^2+c,\qquad P_j(c)=f_c^j(0),
\]

and, wherever its denominator is nonzero, define

\[
\mathcal R_n(c)=
\frac{P_{3n}(c)\bigl(P_n(c)-P_{2n}(c)\bigr)}
     {P_n(c)\bigl(P_{3n}(c)-P_{2n}(c)\bigr)}.
\]

This is a cross-ratio of the ordered quadruple
\((0,P_n(c),P_{2n}(c),P_{3n}(c))\), with the convention fixed by the displayed
formula. All four entries are actual points in one quadratic critical orbit.

The strengthened candidate is the following pair of finite Laurent jets, for
each integer \(k\geq3\):

\[
\begin{aligned}
c_1(\lambda)&=\lambda/2-\lambda^2/4,\\
\mathcal R_k(c_1(\lambda))
  &=-\lambda^{-k}-\frac34-\frac{\lambda}{16}+O(\lambda^3),
\end{aligned}
\tag{1}
\]

and

\[
\begin{aligned}
c_2(t)&=-1-t-t^2,\qquad \mu(t)=-4t(1+t),\\
\mathcal R_{2k}(c_2(t))
  &=-\mu(t)^{-k}-\frac34-\frac{\mu(t)}{16}
      +\frac{\mu(t)^2}{128}+O(\mu(t)^3).
\end{aligned}
\tag{2}
\]

The first fixed point is \(\lambda/2\) and its multiplier is exactly
\(\lambda\). The second chart has the two-cycle
\(t\mapsto-1-t\mapsto t\); its return multiplier is exactly \(\mu(t)\).
Thus the subtraction in (1) and (2) uses the dynamical multiplier, rather
than an arbitrary parameter that merely vanishes at the center.

Here the analytic reading of \(O(q^3)\) is a remainder \(q^3 H\) with \(H\)
holomorphic at the center. The intended algebraic theorem replaces this
notation with an exact finite polynomial identity and a denominator with
nonzero constant term. An algebraic theorem alone must not be advertised as
a separately formalized complex-analytic limit theorem. The range \(k\geq3\)
is part of this strengthened candidate; it is not silently extended to
\(k=1\) or \(k=2\).

The distinguishing coefficient is the quadratic finite coefficient: zero
in (1), and \(1/128\) in (2). The common finite residue \(-3/4\) is an earlier,
weaker candidate preserved in the PR history.

## A discarded candidate: the center multiplicity census

Mihalache and Vigneron, *Factorization of the Misiurewicz–Thurston
polynomials*, **Theorem 2, equation (14), p. 1014**, gives the exact
multiplicity of an exact-period-\(p\) center in
\(P_{\ell+n}-P_\ell\), when \(p\mid n\). In the quadratic case it is

\[
\left\lfloor\frac{\ell-1}{p}\right\rfloor+2.
\]

Their Theorem 1 recalls that the roots of \(P_n\) are simple.
([Primary paper](https://nyjm.albany.edu/j/2026/32-39p.pdf#page=5).)

These results already determine the proposed pole-order census for
\(\mathcal R_n\). They also give the seemingly less obvious mixed-period
contact: if \(n=(2r+1)p/2\), then

\[
\mathcal R_n-1=
\frac{P_{2n}(P_n-P_{3n})}
     {P_n(P_{3n}-P_{2n})}
\]

has order \(r+3\) at an exact-period-\(p\) center. The numerator factors have
orders \(1\) and \(r+2\); the denominator is nonzero there. Consequently
the multiplicity census, including that mixed case, was rejected as a
novelty claim. A Lean proof of it would not change this assessment.

That source does not specify the finite Laurent coefficients in the true
multiplier coordinate. Root orders do not determine those coefficients.

## Koenigs linearization: a necessary comparison

Koenigs, *Nouvelles recherches sur les équations fonctionnelles*,
**§I.1, pp. 385–386**, recalls the normalized iterate construction and
Schröder equation for an attracting fixed point with nonzero multiplier:

\[
B\circ F=F'(a)B,\qquad B(a)=0,\qquad B'(a)=1.
\]

The construction was established in his 1884 paper.
([1885 primary paper](https://www.numdam.org/item/10.24033/asens.268.pdf#page=2);
[1884 primary paper](https://www.numdam.org/article/ASENS_1884_3_1__S3_0.pdf).)

This supplies the geometric scale of iterates for a fixed nonzero
multiplier. It does not identify the finite coefficients of the raw
critical-orbit cross-ratio as the multiplier tends to zero. A holomorphic
linearizing coordinate is not generally a Möbius map, so replacing the
actual orbit by its linearized orbit does not preserve this observable.

The extra work in (1) and (2) is precisely to calculate that discrepancy,
including the critical starting point and its singular normalization at
multiplier zero. The claim is not a new linearization theorem. Classical
power-series techniques remain available; the proposed addition is the
specific identity and its stabilization for every \(k\geq3\).

## Cross-ratio distortion and the Schwarzian

Teplinsky, *On cross-ratio distortion and Schwarz derivative*,
**Theorem 1, equation (4), pp. 2–3 of the arXiv version**, gives a
Schwarzian expansion of cross-ratio distortion for a holomorphic map whose
derivative is nowhere zero on a quasiconvex domain. Its remainder constants
depend on the map and on the chosen compact subset.
([Primary paper](https://arxiv.org/pdf/0710.2629#page=3).)

This is the closest general comparison for interpreting a cross-ratio
coefficient as a nonlinear defect. That interpretation is classical and
is not claimed here as an invention. Direct application to the normalized
return quadruple fails at its critical anchor: the return map has derivative
zero at \(y_0=-1/2\). Moreover, the multiplier-zero limit varies the map, so a
fixed-map remainder estimate is not by itself the required parameter jet.

The proposed proof therefore computes the critical first step and the
return secants explicitly. It must establish the asserted cancellation
and remainder divisibility for every clock \(k\geq3\); citing Schwarzian
distortion does not supply those coefficients. This distinction is a
comparison of the displayed hypotheses and conclusions, not a claim that
the calculation is inaccessible by classical methods.

## Thurston-operator spectra

Buff, Epstein and Koch, *Eigenvalues of the Thurston operator*,
**§8.4, Proposition 12, p. 26 of the author PDF**, computes the relevant
characteristic polynomial for a unicritical polynomial with periodic
critical point using products of derivatives along that orbit. Their
**Theorems 3 and 4** give spectral bounds and substantial accumulation of
the spectra toward the unit circle.
([Primary paper](https://www.math.univ-toulouse.fr/~buff/Preprints/Eigenvalues/eigenvalues.pdf#page=26);
[published version](https://doi.org/10.1112/topo.12145).)

These statements prevent presenting an explicit critical-orbit spectral
formula, or the bare possibility of degenerating contraction, as new.
Their operator eigenvalue variable must also be distinguished from the
attracting-cycle multiplier in (1) and (2). Their stated results do not
calculate the anchored four-point Laurent jet under a deformation away
from a center. This packet does not infer a Teichmüller contraction theorem
from the local jet.

## The additional calculation and its scope

The normalized recurrence behind the retained candidate is

\[
Y(y)=y+y^2,\qquad
y_0=-\frac12,\qquad
y_{j+1}=qY(y_j)+e q^3Y(y_j)^2.
\tag{3}
\]

For (1), \(q=\lambda\), \(e=0\), and
\(P_j=\lambda(1/2+y_j)\). For (2), \(q=\mu(t)\),
\(e=-1/(8(1+t)^3)\), and \(P_{2j}=t(1+2y_j)\).
These are explicit substitutions in the actual quadratic maps. They do
not postulate a realization of an abstract recurrence.

In (3), the candidate finite jet is

\[
R_k=-q^{-k}-\frac34-\frac{q}{16}-\frac{e q^2}{16}+O(q^3),
\qquad k\geq3.
\tag{4}
\]

If \(e\) varies analytically with the parameter, its value at the center
determines the quadratic finite coefficient. At the two centers the actual
return polynomials are

\[
f_0(z)=z^2,\qquad f_{-1}^2(z)=-2z^2+z^4.
\]

Writing these as \(bz^2+dz^4+\cdots\), the quantity \(d/b^3\) is respectively
\(0\) and \(-1/8\). Formula (4) is intended to recover these values from the
quadratic finite coefficient via multiplication by \(-16\). This is the
specific curvature information singled out by the candidate. An
all-period version for arbitrary quadratic centers is not asserted here.

For comparison, a nondegenerate orbit of an affine map of multiplier \(q\)
has, at indices \(0,k,2k,3k\), exactly

\[
R_k^{\mathrm{aff}}=-q^{-k}-1-q^k.
\]

The same formula holds after a simultaneous Möbius change of its four
points. Subtracting it from (4) gives constant finite term \(1/4\).
Thus the intended consequence is an explicit obstruction to matching these
ordered critical-orbit quadruples with a multiplier-preserving Möbius
orbit near the stated centers. It does not obstruct holomorphic
linearization. Nor does it separate two arbitrary quadratic parameters
in one Mandelbrot fiber.

The coefficient computation requires an argument beyond the cited
statements: keep the critical first-step contribution, factor the return
secants, and show which factors survive after the pole is removed. The
all-clock cancellation of the other contributions is the mathematical
content being submitted to Lean. The general ideas of linearization,
cross-ratio invariance, polynomial iteration, and Schwarzian distortion
are not new claims.

## What this audit establishes, and what it does not

No exact instance of (1)–(4), with this critical anchor, true multiplier
normalization, all-clock range, and quadratic finite coefficient, was
located in the primary sources checked. The multiplicity candidate was
discarded because a precise existing theorem does imply it. The retained
candidate is not obtained by direct substitution into the other cited
theorem statements; its additional finite coefficient calculation must
stand on its own proof.

This bounded search is not a guarantee of priority or of absence from the
literature. Formal verification can establish the submitted identities;
it cannot certify novelty, importance, or a connection to MLC that has not
been proved. In particular, these two local center charts provide no
uniform control at infinitely renormalizable parameters, no injectivity
theorem for the pinched-disk quotient, and no resolution of the archive's
remaining fiber hypothesis.

## Bibliographic details

- G. Koenigs, *Recherches sur les intégrales de certaines équations
  fonctionnelles*, Annales scientifiques de l'École Normale Supérieure,
  série 3, **1** (1884), supplement, 3–41,
  [DOI 10.24033/asens.247](https://doi.org/10.24033/asens.247).
- G. Koenigs, *Nouvelles recherches sur les équations fonctionnelles*,
  Annales scientifiques de l'École Normale Supérieure, série 3, **2**
  (1885), 385–404,
  [DOI 10.24033/asens.268](https://doi.org/10.24033/asens.268).
- A. Teplinsky, *On cross-ratio distortion and Schwartz derivative*,
  Nonlinearity **21** (2008), 2777–2783,
  [DOI 10.1088/0951-7715/21/12/003](https://doi.org/10.1088/0951-7715/21/12/003).
  The author's arXiv version uses “Schwarz” in the title:
  [arXiv:0710.2629](https://arxiv.org/abs/0710.2629).
- X. Buff, A. L. Epstein and S. Koch, *Eigenvalues of the Thurston
  operator*, Journal of Topology **13** (2020), 969–1002,
  [DOI 10.1112/topo.12145](https://doi.org/10.1112/topo.12145).
- N. Mihalache and F. Vigneron, *Factorization of the
  Misiurewicz–Thurston polynomials*, New York Journal of Mathematics
  **32** (2026), 1010–1016,
  [journal PDF](https://nyjm.albany.edu/j/2026/32-39p.pdf).

Prepared with OpenAI ChatGPT GPT-6 Astra Pro assistance. No human specialist
review has occurred.
