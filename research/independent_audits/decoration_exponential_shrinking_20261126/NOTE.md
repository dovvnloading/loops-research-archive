# Quantitative shrinking and separation of physical direct-decoration cylinders

**Date:** 2026-11-26. **Base:** main at 8138d7ac61c8756948ba25e0c4047274a996d238 (merged PR #157).

**Status:** proposed written analytic strengthening, pending independent mathematical review. Target: DIRECT_DECORATION_PULLBACK_COMPACTIFICATION (proved, qualitative statement); quantitative continuation of the corrected DIRECT_DECORATION_END_PRIME_END_COFINALITY result in [PR #156](../decoration_end_cofinality_20261126/NOTE.md). No frozen ledger promotion; the single-prime-end clause remains false. In particular the result is not VIRTUAL_END_BLOWUP_REALIZATION.

## 1. Statement and exact scope

Retain the physical hypotheses of PR #156, §§1–3:

* A fixed quadratic polynomial \(f(z)=z^2+c\), with connected \(K(f)=J(f)\), and the actual directly attached noncentral KL decoration with dividing fixed point \(\alpha\) of rotation denominator \(q>1\) and finite escape time \(n\).
* The native closed Jordan ray/equipotential separator \(P=Y^{(n-1)q+1}\), and disjoint closed univalent pullbacks \(Q_L,Q_R\subset P\), each mapped homeomorphically onto \(P\) by \(g=f^q\). Denote these inverse homeomorphisms by \(\phi_L,\phi_R\). These are the shallow \(q\)-time branches, not an independently constructed virtual return. Every cylinder is an actual closed puzzle piece with Julia boundary consisting of preimages of \(\alpha\).
* The actual terminal primitive cycle of period \(r>1\), \(K_i=f^i(K_0)\), \(0\le i<r\), of pairwise disjoint compact connected little filled Julia sets, with \(0\in K_0\), \(f(K_{r-1})=K_0\), and proper degree-two quadratic-like return \(f^r\) with connected filled set \(K_0\). The cycle degree word is \((2,1,\ldots,1)\); in particular the tail from \(K_{r-1}\) to \(K_0\) is one-to-one. These are the physical source conditions used in PR #156, not new assertions about virtual cycles.

For a finite word \(w=a_1\cdots a_m\), let \(\phi_w=\phi_{a_1}\circ\cdots\circ\phi_{a_m}\), \(Q_w=\phi_w(P)\), and \(Q_\varnothing=P\). All diameters and distances between planar sets below are Euclidean. Word depth counts \(g\)-steps, not \(f\)-steps.

**Theorem.** There exist \(A<\infty\), \(0<\lambda<1\), and \(\kappa>0\), depending on this fixed physical puzzle and parameter but not on word length or choice of word, such that
\[
 \operatorname{diam}Q_w\le A\lambda^{|w|},
 \qquad
 \operatorname{dist}(Q_{wL},Q_{wR})
 \ge \kappa\,\operatorname{diam}Q_w.                 \tag{1}
\]
In addition there are \(0<B_-\le B_+<\infty\) and, for each length-\(r\) suffix \(v\), a chosen anchor \(z_v\in Q_v\), such that for every prefix \(u\), including the empty prefix,
\[
 \frac{B_-}{|(g^{|u|})'(\phi_u(z_v))|}
 \le \operatorname{diam}Q_{uv}
 \le \frac{B_+}{|(g^{|u|})'(\phi_u(z_v))|}.            \tag{2}
\]
Thus the actual full closed puzzle geometry has a two-sided derivative calibration. The resulting planar end Cantor set has an expanding \(g\)-action, a bi-Hölder binary coding, and a bi-Lipschitz coding for the physical cylinder-diameter ultrametric (§5).

Only one fixed parameter and one actual direct-decoration scale are considered. No uniformity as parameters, \(q,n,r\), or renormalization levels vary is claimed. The proof below uses classical hyperbolic metric comparison and Koebe distortion, not a new assertion of either classical theorem and not an a priori modulus theorem.

## 2. An omitted critical-cycle predecessor and a finite compact core

Set
\[
 C=\bigcup_{i=0}^{r-1}K_i,\quad \Omega=\mathbb C\setminus C,\quad
 B=\bigcup_{|v|=r}Q_v.
\]
Here \(C\) is compact and forward invariant, and contains all finite critical values of every positive iterate of \(f\): the only critical point of \(f\) is \(0\), and an iterate's critical values are forward images of it.

We recall the depth-\(r\) exclusion argument of PR #156, Lemma 1, to identify the domain of every estimate. No \(K_i\) contains \(\alpha\), since its fixedness would force it into every member of the disjoint cycle. Forward invariance then excludes every iterated preimage of \(\alpha\) from \(C\). Thus \(C\) misses the boundary of every physical puzzle cylinder (outside the Julia set the boundary consists of exterior rays and equipotential arcs). If a connected \(K_i\) meets \(Q_v\), it must be contained in its interior. On every \(K_i\) the return \(f^r\) is onto and noninjective: on \(K_0\) this is the proper quadratic-like degree-two return on its connected filled set; on any other phase conjugate it by the degree-one tail homeomorphism to \(K_0\), as in PR #156. In particular \(f^{qr}\) is noninjective there. But \(f^{qr}=g^r\) is one-to-one on \(Q_v\) for \(|v|=r\). Hence \(B\cap C=\varnothing\). The set \(B\) is compact, so \(B\Subset\Omega\).

Each \(K_i\) is full: any bounded complementary component cannot meet the basin of infinity (which has paths to infinity avoiding \(K_i\subset K(f)\)); being open and contained in \(K(f)=J(f)\) is impossible. The complement of the finite union of disjoint full continua is connected. Indeed any two points outside \(C\) can be kept outside pairwise disjoint Jordan neighborhoods of all \(K_i\), obtained from close exterior equipotentials of the individual full continua (small disks for singletons). The exterior of finitely many disjoint closed Jordan disks is path connected. Thus \(\Omega\) is a connected hyperbolic plane domain, omitting at least two distinct finite points.

There is a specific point missing from the covering domain \(g^{-1}(\Omega)\) but belonging to \(\Omega\). Choose \(y\in K_0\) and its unique predecessor \(x\in K_{r-1}\) under \(f\). Since \(r>1\), \(c=f(0)\in K_1\) and \(y\ne c\), so \(x\ne0\) and the other predecessor is \(a=-x\ne x\). Any predecessor of \(y\) in \(C\) must belong to \(K_{r-1}\), by disjointness of the cyclic phase images; hence \(a\notin C\). Since \(g(a)=f^{q-1}(y)\in C\), this proves
\[
 g^{-1}(\Omega)\subset\Omega\setminus\{a\}.           \tag{3}
\]
The containment follows also from forward invariance of \(C\); the puncture is strict even if the preimage domain has more than one component. It is not necessary to compute or classify these components.

## 3. An explicit quantitative hyperbolic contraction

Use the curvature \(-1\) hyperbolic density \(\rho_U\) (on the unit disk \(\rho_{\mathbb D}(z)=2/(1-|z|^2)\)), and its path distance \(d_U\). Let
\[
 M_\rho=\max_B \rho_\Omega,\quad
 m_\rho=\min_B \rho_\Omega>0,\quad
 D>\max_{z\in B}d_\Omega(z,a),\quad D>0.
\]
These are finite at this fixed parameter, by compactness in the connected domain. Put
\[
 b_*=\tanh(D/2),\qquad
 t_*=-\log b_*,\qquad
 \lambda=\frac{t_*}{\sinh t_*}\in(0,1).              \tag{4}
\]

**Puncture comparison.** For \(z\in B\setminus\{a\}\), take a universal covering \(p:\mathbb D\to\Omega\), \(p(0)=z\). A path from \(z\) to \(a\) of hyperbolic length less than \(D\) lifts from 0 to a point \(b\) of \(p^{-1}(a)\); the lifted path has the same length. The disk distance formula gives \(0<|b|<b_*\). The restriction of \(p\) to \(\mathbb D\setminus p^{-1}(a)\) is a covering of \(\Omega\setminus\{a\}\) (use the component containing 0 if needed). Covering invariance and domain monotonicity, applied first to that component and then to the punctured disk \(\mathbb D\setminus\{b\}\), give
\[
 \frac{\rho_\Omega(z)}{\rho_{\Omega\setminus\{a\}}(z)}
 \le \frac{\rho_{\mathbb D}(0)}{\rho_{\mathbb D\setminus\{b\}}(0)}
 = \frac{2|b|\log(1/|b|)}{1-|b|^2}
 = \frac{t}{\sinh t},\qquad t=-\log|b|.              \tag{5}
\]
For the equality, move \(b\) to zero by the disk automorphism \((\zeta-b)/(1-\bar b\zeta)\) and use \(\rho_{\mathbb D^*}(\zeta)=1/(|\zeta|\log(1/|\zeta|))\). The derivative of the automorphism at 0 has modulus \(1-|b|^2\). The function \(t/\sinh t\) decreases for \(t>0\): the numerator of its derivative is \(\sinh t-t\cosh t<0\), as follows by differentiating that numerator from 0. Hence (5) is at most \(\lambda\). This also handles points arbitrarily close to the puncture; a compact subset of the *smaller* domain need not be assumed.

Every component \(U\) of \(g^{-1}(\Omega)\) covers \(\Omega\) without ramification. Indeed the polynomial is proper, and all its finite critical values lie in \(C\). Thus
\[
 \rho_\Omega(g(z))|g'(z)|=\rho_U(z)
 \ge \rho_{\Omega\setminus\{a\}}(z)
 \ge \lambda^{-1}\rho_\Omega(z)
 \quad(z\in B\cap g^{-1}(\Omega)).                 \tag{6}
\]
This is a one-step physical derivative inequality, not a contraction of a freely chosen inverse of \(g\) on all of \(\Omega\).

For a word \(u\) of length \(k\) and \(|v|=r\), every point of \(Q_{uv}\) and each of its first \(k\) iterates under \(g\) belongs to \(B\): after deleting \(j\le k\) initial letters the word still has length at least \(r\), and its cylinder is inside the depth-\(r\) prefix cylinder. Multiplying (6) telescopes the density ratios, giving
\[
 |(g^k)'(z)|\ge \frac{m_\rho}{M_\rho}\lambda^{-k}
 \quad(z\in Q_{uv}).                                \tag{7}
\]
There is no appeal to the global expansion of \(f\) on \(J(f)\), which can fail.

**Input recipe for the rate.** For a quantitative application it suffices to certify an upper bound \(D\) for the indicated distances in \(\Omega\). For example, polygonal paths from the omitted point to a finite disk cover of \(B\), with positive certified distance from \(C\), yield such a bound by disk comparison \(\rho_\Omega(z)\le 2/\operatorname{dist}(z,C)\), followed by short paths within the disks. If \(b_*\le\beta<1\) is a certified rational bound, one can replace \(\lambda\) by the larger rational \(6/(6+(1-\beta)^2)<1\): use \(-\log b_*\ge1-b_*\) and \(\sinh t\ge t+t^3/6\). This recipe identifies the geometric quantities still to be measured for any numerical instance; no numerical certificate of those quantities is asserted here.

## 4. Transfer to full physical cylinders, including the gaps

A derivative estimate on a Julia trace alone would not control the full exterior parts of a puzzle. We therefore construct actual inverse neighborhoods. Every \(Q_v\), \(|v|=r\), is a compact connected full set (in the source assumptions it is a closed Jordan puzzle piece). Choose a bounded simply connected open \(V_v\) with \(Q_v\Subset V_v\Subset\Omega\) by taking a sufficiently close exterior equipotential neighborhood of \(Q_v\) itself. This is the full-continuum Jordan neighborhood lemma used in the earlier archive; no global inverse on \(\Omega\) is invoked.

For any \(u\), choose \(z_v\in Q_v\). Since all critical values of \(g^{|u|}\) lie in \(C\), its restriction over \(V_v\) is a covering; the component containing \(\phi_u(z_v)\) maps conformally onto \(V_v\). Let \(h_{u,v}:V_v\to\mathbb C\) be this inverse, for empty \(u\) the identity. It agrees with \(\phi_u\) on all of \(Q_v\): agreement at the anchor, local uniqueness of the inverse at every point of agreement (noncritical since the target avoids \(C\)), relative closedness by continuity, and connectedness of \(Q_v\) give agreement everywhere. In particular it takes \(Q_v,Q_{vL},Q_{vR}\) to the exact \(Q_{uv},Q_{uvL},Q_{uvR}\), not to homotopic representatives.

Choose a conformal chart \(\chi_v:\mathbb D\to V_v\), \(\chi_v(0)=z_v\). Fix \(s_v\in(0,1)\) with \(\chi_v^{-1}(Q_v)\subset\{|z|\le s_v\}\), and fix \(z'_v\in Q_v\setminus\{z_v\}\), with \(\tau_v=|\chi_v^{-1}(z'_v)|>0\). Let \(F=h_{u,v}\circ\chi_v\). Koebe growth, with its affine normalization removed, bounds the diameter between
\[
 l_v |F'(0)|\le\operatorname{diam}Q_{uv}\le H_v |F'(0)|,
 \qquad l_v=\frac{\tau_v}{(1+\tau_v)^2},\quad H_v=\frac{2s_v}{(1-s_v)^2}.   \tag{8}
\]
For the lower bound compare the images of \(0\) and \(\chi_v^{-1}(z'_v)\); for the upper bound compare each point to the image of \(0\) and use the triangle inequality. Because
\[
 |F'(0)|=\frac{|\chi_v'(0)|}{|(g^{|u|})'(\phi_u(z_v))|},
\]
taking the minimum of \(l_v|\chi_v'(0)|\) and maximum of \(H_v|\chi_v'(0)|\) over the finitely many suffixes proves (2). Equations (7) and (2) give
\[
 \operatorname{diam}Q_w\le B_+(M_\rho/m_\rho)\lambda^{|w|-r}
 \quad (|w|\ge r).
\]
Take \(A\) at least \(B_+(M_\rho/m_\rho)\lambda^{-r}\) and at least \(\max_{|w|<r}(\operatorname{diam}Q_w)\lambda^{-|w|}\). This proves the first estimate in (1) for **full** physical pieces.

For relative separation, put \(s=s_v\) and
\[
 \delta_v=\operatorname{dist}\big(\chi_v^{-1}(Q_{vL}),\chi_v^{-1}(Q_{vR})\big)>0.
\]
This is strictly positive by the disjoint compact source children and the one-to-one chart. For \(\zeta,\eta\) in these respective sets, the disk automorphism sending 0 to \(\zeta\) has derivative modulus \(1-|\zeta|^2\) at 0, and its inverse sends \(\eta\) to a point of modulus \(t=|\eta-\zeta|/|1-\bar\zeta\eta|\ge\delta_v/(1+s^2)\). Apply the Koebe lower growth bound to \(F\) recentered by this automorphism and the Koebe lower derivative bound to \(F\) at \(\zeta\). Since \((1+t)^2\le4\), this gives
\[
 |F(\eta)-F(\zeta)|
 \ge |F'(0)|\, G_v,\qquad
 G_v=\frac{1-s}{(1+s)^3}\frac{(1-s^2)\delta_v}{4(1+s^2)}>0.              \tag{9}
\]
Taking the infimum over both sets and using (8) proves the second estimate of (1) for \(|w|\ge r\) with \(\kappa\le\min_v G_v/H_v\). For shorter words the positive ratios \(\operatorname{dist}(Q_{wL},Q_{wR})/\operatorname{diam}Q_w\) are a finite list; reduce \(\kappa\) to its minimum with these ratios. All denominators are positive since every finite puzzle piece has nonempty interior. This proves the theorem.

## 5. Consequences for the physical end space

Nested compactness and (1) give \(E_\omega=\bigcap_m Q_{\omega|m}=\{e_\omega\}\). These points belong to \(K(f)\) because their \(g\)-orbits stay in \(P\) (the intermediate \(f\)-iterates then stay in finitely many compact images of \(P\)). Distinct addresses give distinct points by sibling disjointness. The actual inverse homeomorphisms give \(g(e_{a\omega})=e_\omega\) for \(a=L,R\). Thus the end set \(E\subset B\) is compact, conjugate to the one-sided two-symbol shift. For \(z\in E\), (6) iterates at every step, so (7) gives \(|(g^k)'(z)|\ge(m_\rho/M_\rho)\lambda^{-k}\) for all \(k\ge0\). This is expansion on the end set only.

For two distinct addresses with longest common prefix \(w\) of length \(m\), define
\[
 d_*(\omega,\eta)=\operatorname{diam}Q_w,\quad d_*(\omega,\omega)=0.
\]
This is an ultrametric: common-prefix length satisfies the minimum inequality, and cylinder diameters are nonincreasing along extensions. Its topology is the usual binary Cantor topology by the exponential upper bound and the positive finite-depth diameters. The estimate
\[
 \kappa\,d_*(\omega,\eta)\le |e_\omega-e_\eta|\le d_*(\omega,\eta)           \tag{10}
\]
follows immediately from the sibling gap and parent diameter. In particular the Euclidean end set is quantitatively separated in its own scale-adapted metric, not just topologically homeomorphic to an abstract Cantor set.

There is also a two-sided estimate in the usual binary metric \(d_2=2^{-m}\). Let \(\Delta=\operatorname{dist}(Q_L,Q_R)>0\). Fix \(R\) so the closed disk of radius \(R\) contains \(P\), and \(M\ge\max(2,\lambda^{-1},\sup_{|z|\le R}|g'(z)|)\). The polynomial is \(M\)-Lipschitz on this convex disk. Both end orbits lie in \(P\), and their \(m\)-th images lie in distinct first-generation cylinders. Thus
\[
 \Delta M^{-m}\le |e_\omega-e_\eta|\le A\lambda^m,
\]
equivalently \(\Delta d_2^{\log M/\log 2}\le |e_\omega-e_\eta|\le A d_2^{-\log\lambda/\log2}\). The coding and its inverse are Hölder. This gives the (possibly weak) dimension bounds
\[
 \frac{\log 2}{\log M}\le\dim_H E\le
 \min\!\left(2,\frac{\log 2}{-\log\lambda}\right).
\]
Indeed the binary ultrametric space has Hausdorff dimension 1: its depth-\(m\) cylinders cover it by \(2^m\) sets of diameter \(2^{-m}\), and the fair Bernoulli measure gives mass \(2^{-m}\) to each such cylinder, implying the matching lower bound by the mass distribution principle. Apply the elementary Hölder dimension inequality to the coding and its inverse. No dimension formula for the Julia set or for the parameter locus is claimed.

## 6. Dependencies, limits, and review checklist

* Native data: Kahn–Lyubich, [A priori bounds for some infinitely renormalizable quadratics: II. Decorations, arXiv:math/0609046v2](https://arxiv.org/pdf/math/0609046v2), §2.1, printed pp. 5–6 (ray/equipotential puzzle data, the two pullbacks and Lemma 2.1), §2.2 (terminal nest). Use their source-defined puzzle and primitive cycle, not their main a priori bounds result. Read those versioned page images.
* Archive inputs: [FIRST_DECORATION_SCALE_ESCAPE_ATLAS and CRITICAL_BASE_CYCLE_EXCLUSION](../../mlc_unified/virtual_scale_to_puzzle_selector.md), especially Proposition 6.1, and [DIRECT_DECORATION_PULLBACK_COMPACTIFICATION](../../mlc_unified/virtual_cantor_pullback_compactification.md), including the full-continuum Jordan neighborhood Lemma 13.3. [PR #156, §§1–3](../decoration_end_cofinality_20261126/NOTE.md) supplies the precise native hypotheses, the earlier depth-\(r\) exclusion and qualitative theorem. §2 above repeats the exclusion argument and adds the omitted predecessor. No assumption of the singleton prime-end clause is made.
* Classical inputs, with normalization checked against the sources: A. F. Beardon and D. Minda, [The hyperbolic metric and geometric function theory](https://www.math.stonybrook.edu/~bishop/classes/math401.F09/Beardon-Minda.pdf), §2, p. 11, Theorems 10.2–10.5, pp. 41–43 (uniformization, covering isometry, Schwarz–Pick and density comparison), §12.1 p. 47 (punctured disk density). Koebe growth and distortion as in Y.-T. Siu, [Math 213b, appendix on Koebe's distortion theorem](https://legacy-www.math.harvard.edu/archive/213b_spring_05/bieberbach_part1.pdf), printed p. 10. Also standard polynomial covering continuation over a simply connected critical-value-free domain, and ordinary exterior Riemann mapping of full continua. The rate and separation deductions are written above; the classical inputs are not new results.
* Review: verify that the omitted point is outside the full phase cycle; check the curvature normalization and the direction of density comparison in (5)–(6); check that the first \(k+1\) actual orbit points lie in \(B\); check branch agreement over the **full** \(Q_v\); check the recentered Koebe estimate (9); verify that all minima are over finite families of source-defined compact pieces, not over arbitrary renormalization levels. The proof is analytic, not a finite-depth numerical inference. No synthetic graph or numerical fit is being promoted to a physical assertion.

The new result strengthens the qualitative compactification within its existing native scope; it does not repair the false whole-trace single-prime-end claim. Relative Euclidean gaps do not establish conformal marked-access or obstacle protection. In particular (10) cannot identify different prime ends with the same impression. The constant \(\lambda\) depends on the hyperbolic distance \(D\) to the omitted point; \(A,\kappa,B_\pm\) also depend on the finite charts and their separations. A uniform bound across a family would require separate control of these quantities. It is not legitimate to use this theorem to claim such control, analytic end blowup, an iterated virtual tower, an all-scale marked-width bound, UPTCR or MLC. The 465-entry frozen July ledger and its statuses are not changed. This is a reviewable separate theorem note, not a model-to-physical bridge registration; no new executable is introduced and no test run is claimed.

**Next research obligation:** obtain certified uniform bounds for the finite core geometry in a specified parameter/combinatorics family, and separately transport the full angular footprints and their side labels through a source-defined analytic end blowup. The puncture-distance rate recipe and the two-sided cylinder scale law provide explicit quantities to attack; they do not supply those uniform bounds or the protected transport.

**AI disclosure:** GPT-6.2 used for source reading, mathematical proof search and writing. No independent human specialist review or Lean formalization has been performed. No numerical values of the geometric constants are claimed.