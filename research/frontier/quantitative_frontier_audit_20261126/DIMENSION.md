# Physical versus angular scale at the actual 3/9 tip

**Target:** the quantitative direct-decoration end compactification, especially [the preceding exponential shrinking theorem](../../independent_audits/decoration_exponential_shrinking_20261126/NOTE.md), §5 (only crude dimension bounds), and the physical/angular observables in [the analytic history audit](../../independent_audits/decoration_analytic_history_end_blowup_20261126/NOTE.md), §6. The question is whether the actual marked external-angle clock determines the physical spatial scale.

**Claim:** At the source-realized fixed real 3/9 tip of HISTORY.md, let \(E\) be the native physical direct-decoration end Cantor set and \(A_+\) the upper-sector set of its selected external angles. Then
\[
 \boxed{\quad \frac{89}{150}<\dim_H E<\frac{19}{32},
             \qquad \dim_H A_+=\frac12.\quad}                  \tag{1}
\]
The physical dimension bracket is \((0.593333\ldots,0.59375)\), and follows from exact 48-bit outward dyadic arithmetic on a finite positive transfer-operator certificate plus the analytic proof below. The upper-sector landing map from \(A_+\) to \(E\) is a homeomorphism, with every sufficiently close pair expanded by an unbounded factor relative to its angular distance. Its pointwise logarithmic scaling exponents are the physical derivative Birkhoff averages divided by \(\log4\), when those limits exist, and there are actual points where the exponents differ and points where the exponent has no limit. Consequently no single power of the marked angular cylinder length is uniformly comparable to the physical cylinder size. These are results about the chosen end Cantor set, not the whole Julia set or Mandelbrot set.

## 1. Actual real cylinders, distortion, and angles

Write \(a=-c_*\), \(g=f^2\), and use the exact physical branch identifications, real root interval \([\alpha,-\alpha]\subset P\), and the source parameter isolator stated in HISTORY.md. On
\[
 I_0=[-93/100,93/100]
\]
the two inverse branches are \(\phi_L(x)=-\sqrt{a-\sqrt{x+a}}\), \(\phi_R(x)=-\phi_L(x)\). Both map \(I_0\) strictly into itself, with disjoint images, by the rational inequalities in [check.py](check.py); the analytic derivative bound \(3/4\) from HISTORY.md applies. They preserve \([\alpha,-\alpha]\), since the extreme branch value at \(\alpha\) has magnitude \(-\alpha\) and that magnitude is decreasing in the input. The root \(0\) belongs to this interval and the branch identities there are actual puzzle inverse maps.

Put \(I_w=\phi_w(I_0)\), where a finite word has the same composition convention as HISTORY.md. Each \(\phi_w\) is monotone on the real interval, and distinct same-length cylinders are disjoint. The unique coded point \(e_\omega=\lim_m\phi_{\omega|m}(0)\) is the actual physical end, by the earlier native full-cylinder shrinking theorem; hence the compact real IFS attractor is exactly \(E\), not an auxiliary Cantor set. Its coding by \(\Omega_+\) is injective.

The derivatives are bounded away from zero: for any \(y=\phi_j(x)\) on these sheets,
\[
 |g'(y)|=4|y|(a-y^2),\qquad
 |g'(y)|^2\le 64a^3/27 < (15/4)^2.
\]
The maximum over \(0\le |y|\le\sqrt a\) follows by differentiating the cubic \(16u(a-u)^2\) in \(u=y^2\). The rational last inequality is tested. Therefore \(4/15<|\phi_j'|\le3/4\) on \(I_0\).

The logarithms \(\log|\phi'_j|\) are Lipschitz on \(I_0\), with a common finite constant \(K\), by analyticity and nonvanishing. For a word \(w\) of length \(n\), apply the chain rule at \(x,y\in I_0\) and bound the distance between their images under a suffix of length \(l\) by \((3/4)^l|x-y|\). Summing proves
\[
 \left|\log|\phi_w'(x)|-\log|\phi_w'(y)|\right|
 \le 4K|I_0|.
\]
Thus there is one distortion constant \(D\ge1\) for all words and all real inputs, bounding the ratio of the absolute derivatives in either direction. In particular for every \(x\in I_0\)
\[
 D^{-1}|I_0|\,|\phi_w'(x)|\le |I_w|\le D|I_0|\,|\phi_w'(x)|.    \tag{2}
\]
Also there is \(\kappa>0\) such that each child interval has length at least \(\kappa\) times its parent's length, by integrating the derivative of the prefix on the child input interval and using distortion. The same argument gives a sibling gap of at least a fixed positive multiple of the parent length, since \(\phi_L(I_0)\) and \(\phi_R(I_0)\) have strictly positive distance.

For angles, use the **actual** two-sector lifts from the prior analytic-history audit §6: \(J_+=[1/6,1/3]\), \(J_-=[2/3,5/6]\); \(L\) preserves sectors with lift integers 1 and 2, while \(R\) exchanges them with integers 3 and 0. Conjugacy of the two angles gives the following recursion for the upper-sector angle:
\[
 \theta_+(L\omega)=(1+\theta_+(\omega))/4,\qquad
 \theta_+(R\omega)=(1-\theta_+(\omega))/4 .
\]
Indeed the \(R\)-image in \(J_+\) is the lift with integer zero of the lower input angle \(1-\theta_+(\omega)\). The two affine maps on \(J_+\) have ratio of absolute slopes \(1/4\) and strictly separated images. Their coded compact set \(A_+\) has dimension \(\log2/\log4=1/2\): at depth \(n\) there are \(2^n\) intervals of length \(|J_+|4^{-n}\), and the fair Bernoulli measure on these disjoint cylinders satisfies the matching mass bound on balls, by stopping intervals or by the uniform gap. The native ray-cofinality theorem supplies the correspondence of \(\theta_+(\omega)\) to \(e_\omega\). Thus the selected upper-sector landing is a homeomorphism by the two compact injective codings.

## 2. Positive operator criterion, with full analytic justification

For a real exponent \(s>0\), define on continuous functions on \(E\)
\[
 (T_s h)(x)=\sum_{j=L,R}|\phi'_j(x)|^s\,h(\phi_j(x)).
\]
The operator is positive. Its \(n\)th iterate on \(1\) is \(\sum_{|w|=n}|\phi_w'(x)|^s\) by the chain rule (the order in which words are generated is immaterial to the sum).

**Criterion.** If a strictly positive continuous \(h\) on \(E\) satisfies \(T_s h\le r h\) for some \(r<1\), then \(\dim_HE\le s\). If \(T_s h\ge r h\) for some \(r>1\), then \(\dim_HE\ge s\).

For the upper bound, \(h\) has positive minimum and finite maximum. Iterating the inequality and comparing \(1\) to \(h\) bounds \(T_s^n1\) by a constant times \(r^n\). Equation (2) shows that \(\sum_{|w|=n}|I_w|^s\) tends to zero; these intervals cover \(E\) and shrink uniformly, proving the upper claim.

For the lower bound, choose \(x_0\in E\) and define
\[
 Z_n=T_s^n1(x_0),\qquad
 \mu_n=Z_n^{-1}\sum_{|w|=n}|\phi_w'(x_0)|^s\delta_{\phi_w(x_0)}.
\]
These are probabilities supported on \(E\). Since \(T_s^k1\ge c r^k\) on \(E\) for \(c>0\), positivity gives \(Z_n\ge c r^k Z_{n-k}\) for \(n\ge k\). For a fixed prefix \(u\) of length \(k\) and \(n\ge k\), all support points in \(I_u\) are exactly those indexed by \(uv\); the separated real cylinders guarantee this even if a support point is an endpoint. The chain rule and (2) give
\[
 \mu_n(E\cap I_u)
 \le (D/|I_0|)^s |I_u|^s\, Z_{n-k}/Z_n
 \le C |I_u|^s .
\]
Take a weakly convergent subsequence of the probabilities on compact \(E\); each prefix cylinder is clopen in \(E\), so the same estimate holds for its limit \(\mu\). For \(0<\rho<|I_0|\), take the first intervals along every address whose length is at most \(\rho\). These form a disjoint finite partition of \(E\) into cylinders (uniform contraction bounds the stopping depth). Each has length at least \(\kappa\rho\) and at most \(\rho\). Any ball of radius \(\rho\) on the real line meets at most \(4/\kappa+2\) such intervals, since they are disjoint and each meeting interval is contained in the interval of radius \(2\rho\) about the center. Therefore \(\mu(B(x,\rho))\le C'\rho^s\). The mass distribution principle follows directly by applying this bound to any sufficiently fine covering and summing; it gives \(\dim_HE\ge s\). This proves the criterion without assuming a pressure formula or a Gibbs measure theorem.

The inequalities used below have a uniform strict margin, and \(T_t h\) depends continuously on \(t\) uniformly in \(x\in E\), since all \(|\phi_j'|\) lie in a compact positive interval. The same strict inequality with some \(r<1\) or \(r>1\) therefore persists for \(t\) on both sides of \(s\) sufficiently close to it. The resulting dimension bounds are strict.

## 3. Exact finite certificate

For \(m=9\), index the \(2^m=512\) length-\(m\) binary prefixes by their binary integers, L=0 and R=1, most significant bit first. If \(x\) has prefix \(i\), its preimages \(\phi_L(x)\) and \(\phi_R(x)\) have prefixes \(\lfloor i/2\rfloor\) and \(2^{m-1}+\lfloor i/2\rfloor\). Also the absolute derivatives of the two inverse branches are identical at the same input:
\[
 d(x)=\frac{1}{4\sqrt{x+a}\sqrt{a-\sqrt{x+a}}}.
\]
A test function \(h\) taking values \(v_i>0\) on the prefix cylinders is continuous on \(E\). If \(l_i\le d(x)^s\le u_i\) there, then the following finite strict inequalities suffice:
\[
 l_i(v_{\lfloor i/2\rfloor}+v_{2^{m-1}+\lfloor i/2\rfloor})>v_i
 \quad\text{for a lower dimension test},
\]
and the analogous upper test with \(u_i\) and \(<\). The finite number of strict inequalities supplies the uniform factor \(r\ne1\).

[check.py](check.py) implements precisely this test. All values are integers or rational numbers. Here is the error and indexing audit:

1. The inherited exact bracket for \(a\) is enclosed outward in integers scaled by \(B=2^{48}\). Addition and subtraction of such intervals use the endpoint formulas. For a positive interval \([l,h]/B\), its square root is enclosed by \([\lfloor\sqrt{l B}\rfloor,\lceil\sqrt{h B}\rceil]/B\), using integer square root. Thus the enclosure remains valid even though the same parameter appears more than once (dependency may widen but cannot invalidate it).
2. Starting with \(I_0\), at each depth the code prepends L to all old cells and then R to all old cells. Induction gives exactly the stated prefix indexing and an outward enclosure of every **actual** interval \(I_w\). No identification with an approximate real periodic orbit is used.
3. If the two positive square-root quantities have scaled enclosures \([t_l,t_h]/B,[v_l,v_h]/B\), then the scaled derivative is enclosed by \([\lfloor B^3/(4t_hv_h)\rfloor,\lceil B^3/(4t_lv_l)\rceil]\). For \(s=p/q\in(0,1)\), the scaled power of an integer endpoint \(x\) is enclosed by computing the exact integer floor of \(B(x/B)^{p/q}\), comparing \(k^q\) with \(x^pB^{q-p}\). Monotonicity gives lower and upper weight endpoints. The upper uses floor plus one, valid also in the equality case.
4. The 60 positive matrix iterations merely produce a candidate integer vector. No convergence rate or eigensolver correctness is needed. The final test verifies all 512 strict integer inequalities independently, using the lower or upper weight bounds. Each positive margin is divided by the corresponding positive \(Bv_i\); a downward rounded ppm margin is reported. The candidate generation is deterministic and has no randomness or floating-point operation.

Local execution under Python 3.13.5, standard library only, command:
\[
\texttt{python -B research/frontier/quantitative\_frontier\_audit\_20261126/check.py}
\]
The result:

| Test | Exponent | States | Minimum certified relative strict gap (rounded down, ppm) |
|---|---:|---:|---:|
| Lower | 89/150 | 512 | 154 |
| Upper | 19/32 | 512 | 298 |

The real-interval/critical-value inequalities in HISTORY.md also pass. Locally executed source Git blob: c6b387955c2963e7db6ae8bd57f4ea43d9bd4d1d, matched against the remote committed blob. These exact checks plus the proved operator criterion establish (1) for the inherited actual parameter bracket. They are not a formal proof of the bracket's original source realization; no full archive CI or Lean theorem is implied.

## 4. Every-point angular distortion and exact logarithmic exponents

If two addresses first differ after their common prefix \(w\) of length \(k\), their angles differ by a quantity between two fixed positive multiples of \(4^{-k}\), by affine angular separation. Their physical points differ by a quantity between two fixed positive multiples of \(|I_w|\), by real sibling separation and (2). In particular the lower derivative bound yields
\[
 \frac{|e_\omega-e_\eta|}
      {|\theta_+(\omega)-\theta_+(\eta)|}
 \ge C (16/15)^k.                                           \tag{3}
\]
As \(\theta_+(\eta)\to\theta_+(\omega)\) with \(\eta\ne\omega\), the common prefix length tends to infinity, so the ratio tends to infinity at **every** point in the selected upper-sector Cantor set. The inverse has relative difference quotient tending to zero at every point of \(E\). These are derivatives along the Cantor subsets, not a statement about a differentiable extension across gaps or on the full circle. In particular the upper-sector landing map is nowhere locally Lipschitz on its domain.

Put \(\ell(x)=\log|g'(x)|\) on \(E\), a bounded continuous function because the actual branch ranges avoid the critical points. At every \(\omega\), the local ratios obey
\[
 \frac{\log|e_\omega-e_\eta|}
 {\log|\theta_+(\omega)-\theta_+(\eta)|}
 = \frac{1}{k\log4}\sum_{j=0}^{k-1}\ell(g^j(e_\omega))
     + O(1/k)                                               \tag{4}
\]
for \(k\ge1\), with uniform error. Indeed the physical distance is comparable to \(|\phi_w'(g^k(e_\omega))|=1/|(g^k)'(e_\omega)|\) and the angular distance to \(4^{-k}\); the logarithmic errors are bounded independently of \(w\). The Birkhoff average is bounded. Every \(k\) can be realized as the common prefix length of a second address with \(\omega\). Thus the lower and upper limit logarithmic exponents at the corresponding angle are exactly the lower and upper derivative Birkhoff averages divided by \(\log4\).

For the two constant histories in the **forward** coding, the points are the actual branch fixed points \(\alpha<0\) and \(b=(-1+\sqrt{4a-3})/2>0\), with
\[
 |g'(\alpha)|=4\alpha^2,\qquad |g'(b)|=4(a-1).
\]
They are different: the isolator implies \(\alpha^2>a-1\) (indeed \(\alpha^2=\alpha+a\) and \(\alpha>-1\)). Hence the two corresponding scaling exponents are different. No constants \(C_-,C_+>0\) and single exponent \(t\) can satisfy \(C_-4^{-t|w|}\le|I_w|\le C_+4^{-t|w|}\) for all words: apply (2) to the words \(L^k\) and \(R^k\) at their fixed points, take \(k\)th roots, and compare the distinct multipliers.

There are also actual angles where the exponent does not exist. Construct an infinite address by concatenating alternating blocks of L and R of positive lengths \(n_i\) with \(n_i/\sum_{j<i}n_j\to\infty\). For a block of \(n\) copies of \(j\), the sum of \(\ell\) during that block differs from \(n\ell(e_{j^\infty})\) by a uniform constant: by the chain rule it is \(-\log|\phi_j^n'(y)|\) at the actual tail \(y\in E\), and distortion bounds its difference from the value at the branch fixed point by \(\log D\). At successive block endpoints the contribution of the preceding blocks is negligible because \(\ell\) is bounded. The two subsequences of averages tend respectively to the two different fixed-point exponents. Equation (4) proves nonexistence of the local logarithmic exponent at this physical point.

The angular and geometric metrics therefore differ even on this one physical, source-realized family. Uniform calibration of a proof-used conformal width does not follow from these Euclidean length estimates, nor does the discrepancy itself refute a width comparison which retains adequate derivative or conformal data. The result rules out only the specified universal single-exponent length comparison.

## Scope and attribution

The exact parameter, native ray pairing, real inverse formulas and physical cofinality are inherited from the cited archive notes (and their Kahn–Lyubich decoration source), not independently re-proved here. The analytic argument uses elementary bounded distortion of an invariant real IFS, positive operators, weak compactness of probability measures, and the mass distribution principle; the finite-state test is an explicit certificate, not a new general thermodynamic formalism theorem. The prior literature on conformal Cantor-set dimensions and pressure is extensive; no global priority is claimed. The contribution is the rigorous application to the actual archived native tip, including certified dimension separation and precise length-calibration obstructions. No new H1–H4, UPTCR, or MLC gate closure. AI assistance: OpenAI GPT-6.2, mathematical proof search, exact arithmetic implementation, execution and drafting; independent specialist review pending.
