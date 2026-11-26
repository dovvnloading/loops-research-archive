# A single affine-invariant scalar retains the entire analytic past

**Target:** the explicit open observable-quotient question at the end of [the prior analytic-history audit](../../independent_audits/decoration_analytic_history_end_blowup_20261126/NOTE.md), §8. This strengthens [HISTORY.md](HISTORY.md) and [HISTORY_METRIC.md](HISTORY_METRIC.md) at the actual real 3/9 tip. It shows that the full analytic past, although it has continuum cardinality and is not determined by any finite discrete memory, *is* encoded by a single real-valued affine-invariant differential observable. No global gate promotion.

## 1. Exact theorem

Use the physical parameter isolator and actual inverse branches of HISTORY.md; set \(I_0=[-93/100,93/100]\). Let
\[
 b_\eta(x)=\frac{H_\eta''(x)}{H_\eta'(x)},\qquad x\in I_0.
\]
The scalar \(b_\eta(0)=H_\eta''(0)\) determines the normalized analytic chart and the entire backward history. More strongly, evaluation at **any fixed** \(x\in I_0\) is injective on the history space. For distinct histories \(\eta,\zeta\) with longest common suffix \(w\) of length \(k\),
\[
 \boxed{\quad
 \frac1{200}|\phi_w'(x)|
 < |b_\eta(x)-b_\zeta(x)|
 \le 4|\phi_w'(x)|,\qquad x\in I_0 .
 \quad}                                                     \tag{1}
\]
In particular at every such \(x\) the scalar encoding and its inverse are Hölder in the binary suffix metric, with the explicit bounds
\[
 \frac1{200}(4/15)^k
 < |b_\eta(x)-b_\zeta(x)|
 \le4(5/12)^k.
 \tag{2}
\]
At \(k=0\) take \(\phi_w=\mathrm{id}\). The constants are independent of histories and word length. They concern the actual fixed-tip branches, not arbitrary renormalization levels.

This is a finite-dimensional sufficient statistic for the entire affine chart, not a finite-state approximation. One real number has infinitely many possible values; storing finitely many bits cannot encode all histories. Finite precision permits only a finite guaranteed readout depth.

## 2. Exact recurrence and simultaneous interval certificate

For \(t=\sqrt{x+a}>0\), \(v=\sqrt{a-t}>0\), write
\[
 d(x)=1/(4tv),\qquad
 p(x)=\frac{12t-8a}{16t^2(a-t)}.
\]
The first is the common absolute derivative of the two inverse branches; the second is their common pre-Schwarzian, obtained from \(g''(y)=12y^2-4a\) and the inverse-function identity \(\phi''/\phi'=-g''(\phi)/(g'(\phi))^2\). In particular
\[
 \phi_L'(x)=d(x),\quad\phi_R'(x)=-d(x),\qquad
 b_{\xi L}(x)=p(x)+d(x)b_\xi(-v),\quad
 b_{\xi R}(x)=p(x)-d(x)b_\xi(v).                             \tag{3}
\]
These follow from the exact pre-Schwarzian composition rule and the normalized append map, which does not affect the pre-Schwarzian. They are not a fitted recurrence.

The independent standard-library checker [check_scalar.py](check_scalar.py) encloses (3) for every actual \(x\in I_0\), all histories and the entire inherited parameter bracket, using integers scaled by \(2^{48}\).

* Divide the outward dyadic enclosure of \(I_0\) into 4096 closed grid intervals \(X_i\). On each cell enclose \(t,v,d,p\) by interval operations. For positive intervals square-root endpoints are outward rounded by integer square root; products take all four endpoint products, division all four endpoint ratios with positive divisor, and endpoints round outward. The tests verify \(0<d\le5/12\), \(|p|\le1\), and both branch images lie in the grid interval. Thus the estimates hold throughout the continuous real interval, not at just its endpoints or grid centers. The derivative lower bound \(4/15\) on \(I_0\) was proved in DIMENSION.md §1.
* For any finite composition the pre-Schwarzian is a sum of terms from the chain rule bounded in absolute value by \(\sum_{j\ge0}(5/12)^j=12/7<2\). The prior analytic limit and local derivative convergence on the common domain carry this bound to **every** history. The same formula and limit apply on the entire outward interval for the fixed parameter, since it lies inside the common complex stadium, and the certified grid bounds hold there. Initialize every cell with the interval \([-2,2]\), known to enclose all histories, not a guess that they are close to a finite truncation.
* Given such a vector of interval bounds, for \(\phi_j(X_i)\) the code finds a contiguous span of closed grid cells covering the whole outward image. The hull of their prior intervals bounds the predecessor evaluation in (3). Apply the two signed affine formulas with outward interval arithmetic and take their hull for the new interval on \(X_i\). This encloses all histories again, since every infinite history has a predecessor and one last letter. Inductively all 20 iterations enclose the full infinite family. No interval iteration convergence or fixed-point approximation is assumed.
* At the 21st evaluation retain the L and R output intervals separately. Every cell has the **strict** inequality lower(L) minus upper(R) \(>1/200\). Thus for arbitrary distinct last symbols and a common real input,
\[
       b_{\xi L}(x)-b_{\upsilon R}(x)>1/200.                 \tag{4}
\]
The use of a common cell for the two evaluations is conservative: all pairs of histories and all inputs in the cell are allowed.

Local Python 3.13.5 run on the exact committed source (Git blob a2b15423f430efbb64ca531861fdb4ce2fb60a33):

| Item | Certified value |
|---|---:|
| Closed real cells | 4096 |
| Enclosure refinements | 20 |
| Dyadic precision | 48 bits |
| Minimum L-minus-R interval gap, rounded down | 6911 ppm |
| Uniform branch derivative upper bound | 5/12 |
| Absolute branch pre-Schwarzian upper bound | 1 |

The source was rerun after matching the remote blob; an earlier locally executed copy differed by three blank lines only. The matching run passes. There are no sampled-history or floating-point comparisons in this certificate. This finite induction proves a uniform result for all infinite histories because its initial enclosure was independently proved and each refinement preserves enclosure.

## 3. Quantitative decoding

For any two different histories write \(\eta=\xi w,\ \zeta=\upsilon w\), where \(w\) is their longest common suffix. Then \(\xi,\upsilon\) have different last letters. The composition rule gives exactly
\[
 b_{\xi w}(x)-b_{\upsilon w}(x)
 =\phi_w'(x)(b_\xi(\phi_w(x))-b_\upsilon(\phi_w(x))).
\]
The input \(\phi_w(x)\) lies in \(I_0\), so (4) gives the absolute lower bound in (1). The uniform bound \(2\) for each function gives the upper bound. Chain-rule multiplication and the uniform derivative bounds yield (2). This proves injectivity for evaluation at any \(x\); compactness and continuity give a homeomorphism onto the scalar image.

There is also an exact recursive readout. Given the scalar \(b=b_\eta(x)\) with a specified \(x\), choose a grid cell containing \(x\). The separated L/R intervals certify the unique last letter \(j\). Update the pair by
\[
     x_{\rm new}=\phi_j(x),\qquad
     b_{\rm new}=(b-p(x))/\phi_j'(x).
\]
The result is the predecessor history's exact evaluation. Iterating recovers the entire past. This is an exact-real mathematical decoder, not a claim that an arbitrary finite decimal approximates the whole infinite history or that the exact parameter can be queried at no cost. For two histories with different length-\(k\) suffixes, the lower bound in (2) is at least \((1/200)(4/15)^{k-1}\); thus finite-depth classes have explicit uniform positive separation. The formula also gives a bound on the required scalar measurement resolution for a specified finite depth.

## 4. The scalar history set has the same dimension as the physical ends

Let \(B_x=\{b_\eta(x):\eta\in\Omega_-\}\). It is a compact Cantor subset of the real line. In fact for every \(x\in I_0\)
\[
                  \dim_H B_x=\dim_H E.                     \tag{5}
\]
Consequently the strict rational dimension bracket in DIMENSION.md holds also for the scalar set.

We give the proof, keeping the *backward suffix tree* separate from the physical forward prefix tree. Put \(D_w=|\phi_w'(x)|\). The closed interval hull \(J_w\) of the scalar subset with suffix \(w\) has length between \((1/200)D_w\) and \(4D_w\), by (1) and the availability of both preceding symbols. The two child hulls \(J_{Lw},J_{Rw}\) are disjoint with gap at least \((1/200)D_w\): (4) orders the two groups at the common input \(\phi_w(x)\), and the affine pre-Schwarzian relation changes their order at most by the sign of \(\phi'_w(x)\). Thus same-depth hulls are disjoint, and child/parent length ratios have a positive lower bound \((1/200)(4/15)/4\). Uniform derivative contraction bounds all lengths by \(4(5/12)^{|w|}\). These are statements about interval hulls, not convexity of the scalar Cantor sets themselves.

Let \(x_0\in E\) and \(Z_n(s)=\sum_{|w|=n}|\phi_w'(x_0)|^s\), \(s\ge0\). The bounded distortion estimate of DIMENSION.md gives comparability, uniformly for every \(y\in I_0\), of \(\sum_{|w|=n}|\phi_w'(y)|^s\) and \(Z_n(s)\) with factors \(D^{\pm s}\). It also gives
\[
 D^{-s}Z_n(s)Z_k(s)\le Z_{n+k}(s)\le D^s Z_n(s)Z_k(s).
\]
Indeed use the chain rule with either prefix or suffix fixed and sum. The limit \(P(s)=\lim_n n^{-1}\log Z_n(s)\) exists: adding \(s\log D\) to the log sums yields a subadditive sequence, and subtracting it yields a superadditive sequence; their asymptotic slopes coincide since their difference is constant. This is the elementary subadditive lemma (or follows by division into blocks of fixed length and bounded remainders). Since derivative factors lie between \(m_0=4/15\) and \(\lambda_0=5/12\), for \(t>s\)
\[
 (t-s)\log m_0\le P(t)-P(s)\le(t-s)\log\lambda_0.
\]
Thus \(P\) is continuous, strictly decreasing, \(P(0)=\log2\), tends to a negative value and then to \(-\infty\), and has a unique zero \(s_*\).

If \(P(s)<0\), the physical intervals \(I_w\) and scalar hulls \(J_w\) both have sums of \(s\)-powers of their depth-\(n\) lengths tending to zero, by (2) of DIMENSION.md, the diameter bounds above, and distortion. Therefore both dimensions are at most \(s\).

If \(P(s)>0\), choose a block length \(l\) with \(D^{-s} Z_l(s)>1\). Uniformly on \(E\), \(T_s^l1\ge r_0>1\), and positivity gives \(T_s^k1\ge c r^k\) with \(r=r_0^{1/l}>1,\ c>0\), by decomposing \(k\) into multiples of \(l\) and a remainder and taking the minimum over the finitely many remainder functions. Consequently \(Z_n(s)\ge c r^k Z_{n-k}(s)\) for \(n\ge k\). The physical mass-distribution proof of DIMENSION.md §2 now yields \(\dim_HE\ge s\).

For the scalar set place one atom in each suffix-\(w\) cylinder of depth \(n\), with probability proportional to \(|\phi_w'(x_0)|^s\). For a fixed suffix \(u\) of length \(k\), its constituent words are \(vu\), not \(uv\). Their total weight before normalization is exactly
\[
 |\phi_u'(x_0)|^s
       \sum_{|v|=n-k}|\phi_v'(\phi_u(x_0))|^s
 \le D^s|\phi_u'(x_0)|^s Z_{n-k}(s).
\]
Use the preceding growth inequality, distortion between \(x\) and \(x_0\), and the lower bound on \(|J_u|\) to obtain mass \(\le C|J_u|^s\) uniformly in \(n\ge k\). Pass to a weak limit; suffix classes are clopen by their positive sibling gaps. Stopping hulls at scale \(\rho\) gives disjoint intervals of lengths between a fixed positive multiple of \(\rho\) and \(\rho\). A ball of radius \(\rho\) meets only boundedly many, exactly as in DIMENSION.md. Hence the limiting probability satisfies a mass bound \(C'\rho^s\), and \(\dim_H B_x\ge s\). Taking \(s\to s_*\) from both sides proves (5). No identification of the physical prefix order with the backward suffix order was used.

## 5. Full native cylinder length and the observable quotient

The normalized finite charts \(S_w\) and their limits on the original neighborhood of \(P\) form a compact family by the prior analytic-history audit. Every element is normalized univalent, so the continuous functional \(\operatorname{diam}H(P)\) has positive minimum and finite maximum there (it cannot vanish on the nondegenerate \(P\)). It follows that
\[
 \operatorname{diam}Q_w=|\phi_w'(0)|\operatorname{diam} S_w(P)
       \asymp |\phi_w'(0)|\asymp |I_w|.
\]
All comparisons are uniform in words at this fixed puzzle. The nonexistence of a single angular power law in DIMENSION.md §4 therefore holds for the **full actual complex puzzle cylinders** too, not merely the real intervals.

Combining the prior forward/shape/parity graph theorem with the injective scalar gives an exact graph-boundary representation
\[
              \Omega_+\times B_0\times\mathbb Z/2 .
\]
The scalar factor reconstructs the entire analytic chart on the prior domain and hence all chart observables which are continuous functions of that chart. The forward and parity coordinates are still required for the corresponding physical/angular data. This gives a precise answer to the affine-shape observable quotient question at the selected tip. It does not show that the three factors retain all **proof-used** ambient obstacles, relative-cover sheet classes or authorized root enlargements. The pre-Schwarzian is affine invariant, not invariant under arbitrary conformal changes of the source coordinate. No finite-bit encoding, uniform-in-parameter calibration, H1–H4, UPTCR or MLC follows.

## Sources and proof boundary

Physical realization and angular data are inherited from the archive's earlier source-defined audits cited in HISTORY.md and DIMENSION.md; those inputs are not re-certified here. The general scenery and dual Cantor-set framework is classical; see Bedford–Fisher, *Ratio geometry, rigidity and the scenery process for hyperbolic Cantor sets*, ETDS 17 (1997), 531–564, DOI [10.1017/S0143385797079194](https://doi.org/10.1017/S0143385797079194), and Bedford–Fisher–Urbański, *The Scenery Flow for Hyperbolic Julia Sets*, PLMS 85 (2002), 467–492, DOI [10.1112/S002461150201362X](https://doi.org/10.1112/S002461150201362X). Published abstracts and bibliographic records checked; not a full priority or literature audit. No theorem from those papers is invoked in the proofs above. The quantitative scalar separation at the actual archive tip and its exact arithmetic certificate are the proposed contribution. AI assistance: GPT-6.2 proof search, source comparison, exact code and execution, drafting and self-audit. Independent human specialist review pending.
