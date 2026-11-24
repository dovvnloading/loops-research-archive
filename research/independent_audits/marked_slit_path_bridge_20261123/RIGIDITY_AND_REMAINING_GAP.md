# Rigidity endgame: corrected implication and the reach of the new area theorems

**Source check: 2026-11-23 (America/New_York).** This note repairs the terminal implication in the global H4/UPTCR-6 contract and records relevant recent preprints. It does not construct the required quasiconformal conjugacy, prove the missing no-line-field statement, or construct parameter neighborhoods. Global H4 remains open.

## 1. Minimal valid replacement for the H4 endgame

**Rigidity lemma.** Let `f_c(z)=z^2+c` and `g(z)=z^2+c'` be infinitely quadratic-like renormalizable quadratic polynomials. Assume:

1. There is an orientation-preserving global quasiconformal sphere homeomorphism h with `h(infinity)=infinity` and `h o f_c=g o h`.
2. The physical Julia set `J(f_c)` supports no invariant measurable line field on a set of positive planar area.

Then `c=c'`.

**Proof.** McMullen's *Complex Dynamics and Renormalization*, [Theorem 8.1(2), p. 122](https://abel.math.harvard.edu/~ctm/papers/home/text/papers/real/book.pdf), gives `K(f_c)=J(f_c)` for an infinitely renormalizable quadratic. This connected filled Julia set is the whole nonescaping set, not merely the selected renormalization core.

Differentiating the conjugacy almost everywhere, away from the finite critical set, gives the invariant Beltrami equation

\[
 \mu_h(z)=\mu_h(f_c(z))\,
             \frac{\overline{f_c'(z)}}{f_c'(z)}.
\tag{1}
\]

If `mu_h` were nonzero on a positive-area subset of `J(f_c)`, normalizing it by its absolute value on that invariant nonzero set would give an invariant line field. Hence `mu_h=0` almost everywhere on `J(f_c)=K(f_c)`.

The given h is therefore a **hybrid equivalence** near the connected filled Julia sets. To make the polynomial-like application explicit, choose a large equipotential domain W for `f_c`, with `W_-=f_c^{-1}(W) compactly contained in W`. The map `f_c:W_- -> W` is polynomial-like of degree two with filled set `K(f_c)`. Its image under h is the holomorphic restriction of the target polynomial on `h(W_-) -> h(W)`, and h conjugates these restrictions with vanishing Beltrami coefficient on their filled set. Thus both original polynomials are straightenings of the same connected polynomial-like restriction. The connected-case uniqueness clause of Douady–Hubbard, [*On the dynamics of polynomial-like mappings*, Theorem 1(b)](https://www.numdam.org/item/10.24033/asens.1491.pdf), supplies an affine conjugacy `A(z)=az+b` between them.

Comparing coefficients in `A o f_c=g o A` gives `a=a^2` and `2ab=0`. Since a is nonzero, `a=1,b=0`; the constants give `c=c'`. This proves the lemma without asserting that the particular quasiconformal map h is globally conformal.

**Replacement contract text.** Construct the normalized global quasiconformal conjugacy on the actual physical dynamical planes and justify no invariant line fields on the physical Julia set in the stated regime. Use `K=J`, invariant Beltrami coefficients, and connected hybrid uniqueness as above to obtain equality of parameters. Separately construct nested compact connected **relative neighborhoods** of c in the Mandelbrot set whose intersection is the full marked combinatorial fiber. Parameter equality alone does not construct those neighborhoods.

If global conformality of the particular h is required for another purpose, add and prove that h is conformal on the basin of infinity. Together with `K=J` and the Julia-set argument this gives `mu_h=0` almost everywhere on the plane. The hybrid-uniqueness route does not need this additional exterior condition.

## 2. Why the unrestricted global-conformality sentence is false

For a real number `a>0`, `a!=1`, define

\[
 h_a(z)=
 \begin{cases}
 z|z|^{a-1},&|z|\leq1,\\
 z,&|z|\geq1.
 \end{cases}
\]

This is a global orientation-preserving quasiconformal homeomorphism, fixes 0, 1 and infinity, and is exactly the identity near infinity. It commutes with `f(z)=z^2`. Its Beltrami coefficient is

\[
 \mu_{h_a}(z)=\frac{a-1}{a+1}\frac{z}{\bar z}
 \quad (0<|z|<1),
 \qquad \mu_{h_a}(z)=0\quad(|z|>1).
\]

The Julia set of `z^2` is the area-zero unit circle, so it supports no line field of positive planar area. Nevertheless h is not conformal on its bounded Fatou component. Thus no line fields **on J**, even combined with identity near infinity, does not justify vanishing of a global Beltrami coefficient on an unspecified Fatou set. This example is not infinitely renormalizable and does not refute the lemma in §1; it identifies why its `K=J` and hybrid-uniqueness steps must be explicit.

## 3. Current primary sources and exact scope

The following are **preprint results**, with versions and dates checked against the live arXiv submission histories on 2026-11-23 (America/New_York). No later version was listed on that check.

| Source and version | Exact date | Statements relevant here |
|---|---|---|
| Carsten Lunde Petersen, [*The Intersection of nested filled-in little Julia sets have zero area*, arXiv:2610.33328v1](https://arxiv.org/html/2610.33328v1) | Submitted 2026-10-23, 22:04:09 UTC | **Theorem 1:** for every infinitely renormalizable quadratic, the intersection of the nested little filled Julia sets containing the critical value has area zero. |
| Willie Rush Lim, [*Wandering continua, renormalization, and Lebesgue measure on Julia sets*, arXiv:2611.05949v2](https://arxiv.org/html/2611.05949v2) | v1 submitted 2026-11-04; v2 revised 2026-11-09, 20:01:42 UTC | **Theorem E:** every wandering continuum in the Julia set of a finite-type entire function is null. **Theorem H**, §1.3, proved in §2.3: every component of an infinitely renormalizable unicritical renormalization core is null; almost every core point is recurrent; the core and postcritical set have equal area. |
| Willie Rush Lim, [*Lebesgue measure of the postcritical set of neutral quadratic polynomials*, arXiv:2609.35563v1](https://arxiv.org/html/2609.35563v1) | Submitted 2026-09-28, 16:29:02 UTC | **Theorem A:** every quadratic with a neutral fixed point has a null postcritical set, without an arithmetic condition. **Theorem D:** the corresponding statement for the specifically defined compactified sector-tower class. **§1.4.1, Corollary F:** the neutral-cascade line-field consequence excludes its Mother-Hedgehog grand orbit; excluding line fields elsewhere uses a separate argument. **§1.5, Conjecture G:** nullity of the postcritical set for every quadratic remains conjectural. |

For Lim's Theorem H, write `K_n` for the little filled Julia set about the critical point, and `q_n` for its period. The core is

\[
 \mathcal K_\infty
  =\bigcap_n\bigcup_{j=0}^{q_n-1}f^j(K_n).
\]

This is a different set from the single critical end `intersection_n K_n`, or Petersen's critical-value end. The theorem gives

\[
 \operatorname{Area}(\mathcal K_\infty\setminus P(f))=0,
 \qquad
 \operatorname{Area}(\mathcal K_\infty)=\operatorname{Area}(P(f)).
\tag{2}
\]

It does not prove that either area is zero for an arbitrary infinitely renormalizable parameter. Nor does nullity of each component imply nullity of their possibly uncountable union. For example a positive-measure fat Cantor set times an interval has positive area, while each of its connected components is a null vertical interval.

The mechanism in Lim's **Theorem A** is also scoped: on a measurable forward-invariant subset of the Julia set where f is injective, almost every point is recurrent and belongs to the postcritical set. For infinite-type entire functions an orbital boundedness assumption is additionally required. It is not a general nullity theorem for every recurrent or invariant set.

**Textual audit point.** In the v2 proof of Theorem H, the sentence defining
`E=core\union_(j>=0) f^(-j)(critical end)` calls E null. The intended conclusion is that the removed union is null and E has full measure in the core. The countable-preimage argument in §4 supplies that step; applying Theorem A to E then gives the theorem's stated conclusion. This local wording error should not be repeated or treated as a proof that the entire core is null.

## 4. What the area results actually give to a Beltrami argument

**Countable grand-orbit lemma.** If A is a planar null set and f is a nonconstant polynomial, then every `f^m(A)` and `f^(-n)(A)` is null. For images, restrict to bounded disks where f is Lipschitz. For preimages, outside the finite critical-value set use countably many local holomorphic inverse branches; the remaining critical fibers are finite. Therefore

\[
 \bigcup_{m,n\geq0}f^{-n}(f^m(A))
\]

is null. The same holds for countably many specified null components or ends.

Consequently a Beltrami coefficient whose **essential nonzero set has already been proved to lie** in that countable union vanishes almost everywhere there. No closure of the union is licensed: a closure of a null set can have positive area.

Likewise, if the essential nonzero set has been proved to lie in the whole core, equation (2) reduces its nullity to the independent statement `Area P(f)=0`. The neutral theorem supplies that area input only in its actual declared class; it does not identify arbitrary mixed towers with sector towers. Even an independently known `Area P(f)=0` does not locate an arbitrary invariant Beltrami coefficient inside the core or inside a countable grand orbit. Such support localization is a separate dynamical theorem.

None of these area conclusions makes a null continuum a point or gives a modulus bound, an analytic compactness statement, or a basis of parameter neighborhoods.

## 5. The entry-time interchange: an exact criterion and a real obstruction

The difference between “eventually enters every small set” and “eventually enters their intersection” is substantial. The following elementary lemma isolates the missing uniformity.

Let X be a measurable set of finite area and let `E_n` be decreasing measurable sets with null intersection `E_infinity`. Define

\[
 S_n=X\cap\bigcup_{j\geq0}f^{-j}(E_n),\qquad
 B_{n,J}=X\cap\bigcup_{0\leq j\leq J}f^{-j}(E_n).
\]

Then

\[
 \operatorname{Area}\Bigl(\bigcap_n S_n\Bigr)=0
 \quad\Longleftrightarrow\quad
 \forall\varepsilon>0\ \exists J\ 
 \sup_n\operatorname{Area}(S_n\setminus B_{n,J})<\varepsilon.
\tag{3}
\]

**Proof.** For fixed J, the decreasing sets `B_(n,J)` intersect in the finite union of the first J preimages of `E_infinity`, intersected with X. This set is null by §4, so their areas tend to zero. The right side of (3) consequently bounds the area of `intersection_n S_n` by every epsilon. Conversely, if that intersection is null, the decreasing finite-area sets S_n have areas tending to zero. All sufficiently large n already have small tails. For the finitely many remaining n, `B_(n,J)` increases to S_n as J increases; choose one J controlling those finitely many tails. This proves the equivalence.

The tail has a genuinely analytic expression. If `tau_n(x)` is the first entry time into E_n, the polynomial change-of-variables formula, excluding finitely many critical values, gives

\[
 \operatorname{Area}(S_n\setminus B_{n,J})
 =\sum_{j>J}\int_{E_n}
   \sum_{\substack{x\in X,\ \tau_n(x)=j\\ f^j(x)=y}}
      \frac{dA(y)}{|(f^j)'(x)|^2}.
\tag{4}
\]

A usable estimate must control these actual inverse Jacobians and actual first-entry domains; an incidence count or a separately normalized stochastic model does not establish (4).

**This tightness cannot be imposed universally with X equal to the whole Julia set.** McMullen's [Theorem 8.2](https://abel.math.harvard.edu/~ctm/papers/home/text/papers/real/book.pdf) states that almost every Julia point eventually lands in each little-Julia cycle. Once in a cycle, it eventually visits its selected central component. Thus, for nested central little Julia sets E_n, almost every Julia point belongs to every S_n. Meanwhile infinitely renormalizable quadratic polynomials with positive-area Julia sets exist: Avila–Lyubich, [*Lebesgue measure of Feigenbaum Julia sets*, Theorem 1.1](https://www.math.stonybrook.edu/~mlyubich/posmeas.pdf), published in [*Annals of Mathematics* 195 (2022), pp. 1–88](https://annals.math.princeton.edu/2022/195-1/p01). For these maps `intersection_n S_n` has positive area, despite nullity of the limiting critical end. Hence (3)'s uniform tightness fails on the whole Julia set.

If an H4 argument uses entry-time tightness, X must instead be an independently justified residual support set, or it must use a different argument. The new area theorems sharpen what can be removed after such localization; they do not supply the localization or the remaining no-line-field proof.

## 6. Status retained

The corrected classical endgame is: a global quasiconformal conjugacy plus no invariant line fields on the physical Julia set gives a hybrid equivalence, then connected straightening uniqueness gives parameter equality. The recent preprints give new null sets and a sharper description of possible residual area. They do not establish the general conjugacy, no-line-field, or parameter-neighborhood hypotheses of H4/UPTCR-6. No global gate is promoted by this note.

Prepared with OpenAI GPT-6 Astra Pro for source inspection, proof development
and adversarial review. No human specialist review has occurred.
