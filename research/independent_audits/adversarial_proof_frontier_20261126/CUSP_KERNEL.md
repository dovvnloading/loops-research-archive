# Exact parabolic cusp blow-up of positive parameter equipotentials

**Target:** H4_RIGIDITY (open), the change-of-ground penalty at the actual main-cardioid cusp. This strengthens [sharp boundary frontier, Theorem 4](../../frontier/sharp_boundary_frontier_20261126/NOTE.md), which proves only two-sided constants. Base main: 59fff186a31bf7def8d7c7e2d60519190585c3bd. Proposed written analytic theorem, no ledger promotion. GPT-6.2 proof search and drafting; independent human review pending.

## 1. Statement

For f_c(z)=z²+c, write c₀=1/4 and use the physical parameter Green function G(c)=2 lim_n 2^(-n) log⁺|f_c^n(0)|. For u>0 let D_u={G<u}, the bounded simply connected positive-level parameter domain, and let r_u(c₀) be its conformal radius at c₀. Write L=log(1/u) and a=π log(2)/L (u<1).

For each α>0 the pointed domains

    Ω_(u,α) = (D_(u^α) - c₀)/a²

converge in the Carathéodory kernel sense at 0 to

    S_(α) = C ∖ [α^(-2), +∞).

The conclusion holds along every sequence u→0 and α(u)→α>0. In particular,

    lim_(u→0) L² r_u(c₀) = 4 π² (log 2)².              (1)

More generally r_(u^α)(c₀)/a²→4/α², locally uniformly for α>0. These are actual parameter domains, not dynamical puzzle models, and no landing/extension at G=0 is assumed.

## 2. Real transit with a controlled error

Let 0<h≤1/8, c=c₀+h², x_j=f_c^j(0), y_j=x_j−1/2, and d_j=y_j²+h². Then y₀=−1/2, y_(j+1)=y_j+d_j. The y_j increase strictly, and eventually exceed every bounded threshold since d_j≥h². Let N be the first index y_N≥1/2. For j<N, −1/2≤y_j<1/2 and d_j≤17/64.

For v in [y_j,y_(j+1)] put d(v)=v²+h². The function sqrt(d(v)) is 1-Lipschitz (Euclidean norm of (v,h)), hence

    (1−sqrt(d_j))² d_j ≤ d(v) ≤ (1+sqrt(d_j))² d_j.

Since sqrt(17/64)< 3/5, these imply d_j/  (25/4) ≤ d(v) ≤ (64/25)d_j. We use the simpler bounds d_j/7 ≤ d(v) ≤ 3 d_j. Also

    |d(v)−d_j| ≤ (2|y_j|+d_j)d_j.

Consequently the integral I_j=∫_[y_j,y_(j+1)] dv/d(v) satisfies

    |I_j−1| ≤ 7(2|y_j|+d_j).

The sum of d_j is y_N−y₀≤1+17/64. To control the sum of |y_j|, observe that |y_j|≤|v|+d_j and hence

    ∫_[y_j,y_(j+1)] |v|/d(v) dv
      ≥ (|y_j|−d_j)/3

when |y_j|≥d_j; the rearranged bound |y_j|≤3∫ |v|/d(v)+d_j holds also in the other case. All these intervals lie in [−1/2,1], and the integral of |v|/(v²+h²) on that interval is O(log(1/h)), by the antiderivative on each side of 0. Summing gives

    |N−∫_[-1/2,y_N] dv/(v²+h²)| = O(log(1/h)).

The integral equals [arctan(y_N/h)+arctan(1/(2h))]/h. Since y_N≥1/2, its difference from π/h is bounded by 4, using 0≤π/2−arctan(t)≤1/t for t>0. Therefore

    N = π/h + O(log(1/h)).                              (2)

The first index J with x_J≥2 differs from N by at most four: y_N≥1/2 and each subsequent increment before reaching 3/2 is at least 1/4. Also J≥N and 2≤x_J≤4+c<5. For x≥2 the iteration satisfies x²≤f_c(x)≤(3/2)x². Taking normalized logarithms yields log 2≤g_c(x_J)≤log 5+log(3/2), where g_c is the dynamical Green function. By the escape identity,

    G(c₀+h²) = 2^(1−J) g_c(x_J),

so

    log(1/G(c₀+h²)) = π log(2)/h + O(log(1/h)).          (3)

All constants here are absolute. The leading transit limit is classical (see attribution below); the direct estimate supplies the error and normalization needed for the domain blow-up.

## 3. Two complementary inclusion mechanisms

Fix a sequence u→0, α(u)→α>0, a=π log(2)/log(1/u), and b=α^(-2). For real R>0, applying (3) at h=a sqrt(R) shows

    log(1/G(c₀+a²R))/L → 1/sqrt(R).

Thus if R<b, the real parameter has G<u^α(u) eventually; if R>b, it has G>u^α(u) eventually.

**Interior disk.** For any |w|≤R, |c₀+a²w|≤c₀+a²R. By induction on actual critical iterates from 0,

    |f_(c₀+a²w)^j(0)| ≤ f_(c₀+a²R)^j(0)

because the majorant orbit is nonnegative. Normalized logarithms preserve the inequality, so the whole closed disk |w|≤R lies in Ω_(u,α(u)) eventually whenever R<b. This is a uniform complex statement.

**Off-ray inclusion.** On C∖[0,+∞) choose the branch v=√(-w) with Re v>0. The parameter c=c₀+a²w has a fixed point with multiplier λ=1−2av: indeed c=λ/2−λ²/4. For any compact set Q in C∖[0,+∞), min_Q Re v>0 and max_Q |v|²<∞; hence |λ|²=1−4a Re v+4a²|v|²<1 uniformly on Q for all sufficiently small a. The parameter is in the main cardioid, thus G=0. This uses the classical attracting-fixed-point characterization of the cardioid (the attracting basin contains the unique finite critical point). No claim about the thin near-ray region is needed.

Let K be any compact subset of S_(α). Its intersection with [0,+∞) is a compact subset of [0,b). Pick R<b so that this intersection lies strictly in |w|<R (if empty, any positive R<b works). Then K∩{|w|≥R} is compact and disjoint from the ray, and the remaining part lies in the included disk. Thus K⊂Ω_(u,α(u)) eventually.

**Exterior obstruction.** For every real R>b, the point R is outside Ω_(u,α(u)) eventually. Moreover the real critical iterates are nondecreasing with positive real c, so G is nondecreasing on c≥c₀. Hence the entire ray [R,+∞) is excluded eventually for each fixed R>b. In particular no open neighborhood of b is eventually contained in the rescaled domains, since any such neighborhood contains a real point R>b.

## 4. Kernel theorem and exact conformal radius

For every sequence considered above, every compact subset of S_(α) is eventually contained, and any open connected neighborhood of 0 having this property is disjoint from [b,+∞): each point greater than b is excluded, and inclusion of b would include one of those points. The same facts hold for every subsequence. Thus the kernel is exactly S_(α), a proper simply connected domain containing 0.

By the classical Carathéodory kernel convergence theorem in its pointed simply connected formulation, the normalized conformal maps to the unit disk converge locally uniformly on S_(α) to its normalized map. The latter is explicit:

    ψ_b(w) = (1−√(1−w/b))/(1+√(1−w/b)),

using the square root of positive real part, with ψ_b(0)=0 and ψ'_b(0)=1/(4b)>0. The square root maps S_(α) conformally onto the right half-plane, and the last fractional-linear map maps that half-plane onto the disk. Differentiating the locally uniform limit gives conformal radius convergence to 4b. Dilation back by a² proves (1) and the stated generalization. Local uniformity in α follows from the sequential version: any countersequence in a compact α-interval has a convergent subsequence, to which the argument applies.

This identifies the exact constant, not merely its order. A bound by the distance to the level boundary alone would miss the factor four; it is the slit kernel that fixes it.

## 5. Source and scope

- The parameter uniformization and positive-level Jordan domain facts are the classical Douady–Hubbard interface as used in [parameter ground transfer](../parameter_ground_transfer_20261126/NOTE.md), §1. The main cardioid description follows from the fixed-point multiplier equation and the attracting-basin critical-point theorem (Fatou).
- The leading real transit π/h is known; see A. Klebanoff, *π in the Mandelbrot set* (2001), and the discussion of Shishikura's parabolic bifurcation theorem at https://mathoverflow.net/questions/215187/is-there-a-reference-for-computing-pi-using-external-rays-of-the-mandelbrot (2015). The argument here does not use either as a premise. The bibliographic discussion is not an exhaustive priority search.
- Standard Carathéodory kernel convergence for normalized simply connected Riemann maps is the only compactness theorem invoked. It is a theorem at positive levels, not an assumption of boundary local connectivity.
- The comparison target is specifically the rough cusp constants of the archive's sharp boundary frontier, §4; no claim that the exact constant or slit limit is new in the wider literature. No other cusp, arbitrary satellite sequence, native carrier, or new local-connectivity case is proved. H4 and all global gates remain open.
