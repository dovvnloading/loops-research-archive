# Sharpness of the multipole exponents: actual planar domains

**Status:** written analytic obstruction to improving the general relative rate in [MULTIPOLE.md](MULTIPOLE.md). This is a domain-level counterexample to a stronger variational estimate, not a counterexample to a dynamical conjecture.

## 1. Claim

For every integer n≥1, there is a fixed regular planar electrode shape K, fixed inner terminal data y, and outer data x=0 such that, as R→∞,

    Q_(n−1)=Q_0=A(y)>0,
    E_R−Q_(n−1) = C_K R^(−2n) + O(R^(−2n−2)),    C_K>0.   (1)

All shapes satisfy the hypotheses of the round-neck theorem (disjoint filled analytic Jordan domains). Thus the exponent 2(N+1) in the uniform error of the N-mode correction is optimal over this class, even with a fixed inner geometry for each N=n−1. The constant in the general relative bound is not claimed sharp. The n=1 obstruction can also be realized by two disjoint real slits.

## 2. Construction with a provably nonzero first allowed moment

Fix n≥1, place 2n equal closed disks centered at the points exp(i jπ/n), j=0,...,2n−1, and choose their common radius positive and small enough that each lies entirely inside the open sector

    |arg z − jπ/n| < π/(2n)

with the argument interpreted modulo 2π. They are disjoint and lie in |z|<2. Assign the constant value (−1)^j on disk j and x=0 at the outer circle. For n=1 use instead two real nondegenerate intervals [1−a,1+a] and [−1−a,−1+a] with 0<a<1/4, respectively at +1 and −1.

Let h=h_y be the exact exterior Dirichlet solution on the sphere. Its symmetries follow from uniqueness: rotation by π/n changes its sign; conjugation leaves it unchanged. Hence h(∞)=m(y)=0. Reflection in either boundary ray of the sector |arg z|<π/(2n) changes the sign (compose conjugation with rotation by ±π/n). Thus h vanishes on those rays and extends continuously to the vertex 0 with value 0. The sector contains only the positive disk (or slit) and is otherwise connected. The maximum principle on the truncated sector, using uniform convergence h→0 at infinity and then letting the truncation radius tend to infinity, gives h≥0 there. The strong maximum principle gives h>0 in the sector away from the electrode. In the slit case both banks are positive, and the same argument applies.

At infinity h has a convergent harmonic expansion with zero constant,

    h(z)=Σ_(m≥1) b_m Re(z^(−m)),

where b_m is real by conjugation symmetry. Anti-rotation implies that b_m vanishes unless m=(2j+1)n for j≥0. There is a first nonzero coefficient because h is nonzero and harmonic continuation from a neighborhood of infinity would otherwise make it identically zero. If its index were m≥3n, then cos(mθ) would take both signs inside |θ|<π/(2n): for example θ=0 and θ=π/m are both interior. For sufficiently large radii the leading term would give a negative value on one of these rays, contradicting strict positivity. Therefore b_n>0. This proves the required nonzero multipole without numerical approximation.

## 3. Exact lower and upper asymptotics

Take a fixed intermediate r=2 and t=r/R. In the notation of MULTIPOLE.md, m(y)=x=0 makes the Q_0 minimizing inner function u^0=u_y, independent of R. Its first n−1 trace pairs vanish, and its nth pair has squared norm |a_n|²=b_n²/(2r^(2n)). Thus the baseline minimizer is admissible with zero correction at every N<n, proving Q_(n−1)=Q_0.

For N=n, let P,D,G,a denote the exact finite-rank data of MULTIPOLE.md §2. The energy bound

    ||D^(1/2)P w||² ≤ ε_1 T(w) ≤ ε_1 ||w||_k²

holds for all w in H_k. Hence ||D^(1/2) G D^(1/2)||≤ε_1. The identity

    (D^(−1)+G)^(-1)
       = D^(1/2) (I+D^(1/2) G D^(1/2))^(-1) D^(1/2)

and the spectral bounds on the positive semidefinite middle term yield

    d_n |a_n|²/(1+ε_1) ≤ Q_n−Q_0 ≤ d_n |a_n|²,

because a has only its nth pair nonzero. Here d_n=2π n ε_n and ε_n=2t^(2n)/(1−t^(2n)), so

    Q_n−Q_0 = 4π n t^(2n)|a_n|² + O(t^(2n+2)).

The omitted-tail inequality E_R−Q_n≤ε_(n+1) Q_n, with Q_n bounded by (1+ε_1)Q_0, gives E_R−Q_n=O(t^(2n+2)). This proves (1) with

    C_K=2π n b_n²>0.

Consequently the relative error (E_R−Q_(n−1))/Q_(n−1) cannot be O(R^(−2n−η)) for any η>0 on this example. This checks the rate by a strict nonzero coefficient, not merely by a failed proof of a better bound.

The construction has more electrodes as n increases; it does not prove an optimal rank/error tradeoff across fixed terminal dimension, arbitrary nonlinear observables, or an actual dynamical tower. It does show the first exponent is sharp even among fixed two-real-slit examples. All harmonic problems here are on explicit regular planar domains; no unproved archive realization is needed for the obstruction. The argument uses the previous variational theorem, standard maximum principle and harmonic power series. AI assistance: GPT-6.2; no independent human review.
