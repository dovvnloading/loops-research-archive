# Spectral ground-loss law at every quadratic Misiurewicz parameter

**Target:** follow-up to [NOTE.md, Theorems 1–3](NOTE.md), H4_RIGIDITY (OPEN). **Result:** written analytic theorem in the actual quadratic parameter plane, with exact discrete-clock limit and a continuous phase profile. It is not a new local-connectivity case. Base main 47806d64c64688bdf27c817f036cfdbfa85ce1d5; this note uses the diagonal identity of the preceding proof commits. No other active PR is assumed merged.

We use Tan Lei's classical Misiurewicz transversality and parameter-dependent linearization, not claim her similarity theorem as new. The additional deduction is an actual rescaling limit for positive equipotential domains and their conformal radii, yielding the local cost of the changing-ground interface.

## 1. Definitions and statement

Let c_* be any quadratic Misiurewicz parameter: the critical point 0 of f_c(z)=z^2+c is strictly preperiodic and eventually lands on a periodic orbit. Let m>=1 be the minimal number of critical-point iterates to that orbit, p>=1 its exact period, z_*=f_(c_*)^m(0), lambda=(f_(c_*)^p)'(z_*), and d=2^p. The orbit is repelling, hence |lambda|>1. Let r_u(c_*) be the conformal radius at c_* of the **actual parameter domain** D_u={G_M<u}, in the normalization of NOTE.md:

    G(c)=2 g_c(0)=g_c(c),
    g_c(z)=lim_(j->infinity) 2^(-j) log^+|f_c^j(z)|.

For clarity, m counts iterates from the critical point, not from the critical value. Tan Lei's l in her Theorem 5.1 and Lemma 5.4 equals m-1.

**Theorem 5 (spectral law).** Put gamma=log|lambda|/(p log 2)>0. There is a continuous positive function R(v), 0<v<infinity, satisfying R(dv)=|lambda| R(v), such that

    |lambda|^n r_(d^(-n) v)(c_*) -> R(v)                (1)

locally uniformly in v>0. Consequently, as u tends to zero,

    r_u(c_*) is comparable to u^gamma,
    r_(du)(c_*)/r_u(c_*) -> |lambda|.                  (2)

The comparison constants can depend on the specified Misiurewicz parameter. If K_(s,t) is the exact centered diagonal kernel of NOTE.md (the point-localized supremum of the ground transfer), then

    K_(s,t)(c_*,c_*) = gamma log(t/s)-(t-s)+O_(c_*)(1)  (3)

uniformly for sufficiently small 0<s<t, and the exact one-return-clock limit is

    K_(u,du)(c_*,c_*) -> log|lambda|.                   (4)

More generally for fixed 0<v<w,

    K_(d^(-n)v,d^(-n)w)(c_*,c_*) -> log(R(w)/R(v)).    (5)

These are actual physical Green-energy transfer quantities. For a nonpolar continuum F contained in a small neighborhood of c_* they bound its penalty from above via the diagonal maximum theorem and can be approached by actual shrinking continua via its continuity statement. The latter is a limit for each fixed pair of levels; a joint rate for a sequence of continua requires the quantitative localization hypothesis in NOTE.md (6).

The exact formula has two distinct clocks: the Green level multiplies by 2^p in one return; the Euclidean/conformal radius multiplies asymptotically by |lambda|. No absolute-period factor is omitted. In particular the exponent two at c=-2 is the special case p=1, lambda=4.

## 2. Imported input, with exact source interface

Tan Lei, *Similarity Between the Mandelbrot Set and Julia Sets*, Communications in Mathematical Physics 134 (1990), 587–617, [author PDF](https://math.univ-angers.fr/~tanlei/papers/similarityMJ.pdf), [DOI](https://doi.org/10.1007/BF02098448). Reopened printed pp.606–609 (PDF indices 19–22) in page images. The proof imports exactly:

* Repelling nature of the eventually periodic critical orbit (Douady–Hubbard, Proposition 3.1, p.595; repeated in proof of Theorem 5.1, p.606).
* Holomorphic continuation z(c), lambda(c) of the marked periodic point and multiplier, and parameter-dependent Koenigs linearization chi_c near z(c), normalized chi_c(z(c))=0 and chi'_c(z(c))=1, with chi_c(f_c^p(z))=lambda(c) chi_c(z) where both sides are defined. Tan Lei Lemma 5.2, pp.606–607.
* The holomorphic entrance function h(c)=chi_c(f_c^(m-1)(c))=chi_c(f_c^m(0)) has h(c_*)=0 and a=h'(c_*) !=0. Tan Lei Lemma 5.4, p.609, Eq.(38), credits Douady–Hubbard for the nontrivial critical-relation transversality. The proof here does not independently reprove it.

The full set-similarity theorem is not invoked to assert convergence of positive Green levels. That extra passage is proved below. No source PDF bytes were downloaded or hash-locked in this pass. The normalization of g_c, G_M is the same as in the parameter-capacity notes; classical continuous dynamical Green functions are justified below using uniform telescoping. Other classical inputs: holomorphic inverse function and open mapping theorems, harmonic maximum principle, and Carathéodory kernel convergence theorem for simply connected plane domains with a common basepoint (standard normalized Riemann-map formulation).

## 3. Actual scaled critical orbit converges on every compact parameter window

Write c_n(w)=c_*+lambda^(-n)w. There exists a uniform small disk of linearizing values |v|<rho and a common parameter neighborhood on which the inverse charts chi_c^(-1)(v) are jointly holomorphic. Shrink the disk and parameter neighborhood as necessary. The return identity is

    f_c^p(chi_c^(-1)(v))=chi_c^(-1)(lambda(c)v)

when both values are inside the disk, by the local identity and the identity theorem on the smaller concentric disk in v. This is a statement about the genuine p-return; it does not replace the polynomial by a linear map outside the local chart.

For w in any sufficiently small closed disk centered at zero, Taylor expansion uniformly gives

    h(c_n(w))=a lambda^(-n)w+O(|lambda|^(-2n)),
    lambda(c_n(w))/lambda=1+O(|lambda|^(-n)).

The latter raised to the nth power tends uniformly to 1, since n|lambda|^(-n)->0 (choose the local logarithm near 1, or use the binomial bound). Thus

    lambda(c_n(w))^n h(c_n(w)) -> a w.

Choose the disk small enough that all final linearizing values are in |v|<rho/2 for large n. Since |lambda(c_n(w))|>1, every preceding value lambda(c_n(w))^j h(c_n(w)), 0<=j<=n, stays inside the chart. Induction using the actual return identity gives

    f_(c_n(w))^(m+pn)(0)
       = chi_(c_n(w))^(-1)(lambda(c_n(w))^n h(c_n(w)))
       -> chi_(c_*)^(-1)(a w).                         (6)

All equalities before the limit refer to actual critical iterates. The small-disk restriction has not been silently removed.

Define the entire Poincaré function P by extending the inverse chart at c_*:

    P(v)=f_(c_*)^(pJ)(chi_(c_*)^(-1)(lambda^(-J)v)),

for any sufficiently large nonnegative integer J. On every compact v-set a single J works, and the return identity makes the expressions for larger J equal. Hence P is entire, P(0)=z_*, P'(0)=1, and

    P(lambda v)=f_(c_*)^p(P(v)).

For w in an arbitrary compact set choose a fixed J so that lambda^(-J)w lies in the small disk of (6). Apply (6) with index n-J and argument lambda^(-J)w; its actual parameter is exactly c_n(w). Follow by J further actual p-returns, which converge uniformly on the resulting compact sets by polynomial continuity. Therefore

    f_(c_n(w))^(m+pn)(0) -> P(a w)                      (7)

locally uniformly on the whole w-plane. The extension uses a fixed J on each compact, not an unbounded number of iterations under a local approximation.

## 4. Uniform escape-profile limit, including positive levels

For any bounded parameter set |c|<=C, the quantity

    |log^+|z^2+c|-2 log^+|z||

is bounded uniformly in all z: for large |z| use |z|^2/2<=|z^2+c|<=(3/2)|z|^2, and on the remaining bounded z-set both expressions are bounded. Telescoping shows that 2^(-j)log^+|f_c^j(z)| converges uniformly with a geometric tail on such parameter sets (in fact with an error independent of z). In particular g_c(z) is jointly continuous, nonnegative, zero exactly on K(f_c), and g_c(f_c(z))=2g_c(z). The latter identity also follows directly by shifting the defining limit. The classical polynomial Green function is harmonic on its positive set; in the connected case the exterior Böttcher coordinate gives g_c=log|B_c(z)| there, with nonzero derivative. We only use harmonicity at c_* in M.

Define the physical rescaled parameter potentials

    H_n(w)=d^n G(c_n(w)).
    
By the exact parameter/dynamical normalization and functional equation,

    H_n(w)=2^(1-m) g_(c_n(w))(f_(c_n(w))^(m+pn)(0)).

Consequently (7) and joint continuity prove locally uniform convergence

    H_n -> H,    H(w)=2^(1-m) g_(c_*)(P(a w)).          (8)

This is a positive-level refinement of the zero-set viewpoint. The factor 2^(1-m) is essential; it is not 2^(-m). The limiting function is continuous and nonnegative with H(0)=0. It is harmonic on {H>0} and satisfies

    H(lambda w)=d H(w).                               (9)

It is positive arbitrarily close to zero: z_* is a repelling periodic point in J(f_(c_*))=boundary K, P'(0)=1, and a!=0, so every neighborhood of zero maps onto a neighborhood of z_* meeting the escaping set. It follows from (9) that H is unbounded. At any point with H(w)>0, H cannot be constant on a neighborhood: the nonconstant holomorphic P(a w) is open and g_(c_*) is nonconstant on every open subset of the basin. The harmonic maximum principle therefore implies that every neighborhood of a point with H(w)=v>0 contains some point with H>v (and some with H<v).

## 5. Carathéodory kernel at every positive level, without a boundary extension

For v>0 let Omega_v be the connected component containing zero of {H<v}. It is a nonempty open connected set and is proper because H is unbounded. The actual rescaled domains are

    E_(n,v)=lambda^n (D_(d^(-n)v)-c_*)
           ={w:H_n(w)<v}.

Each E_(n,v) is a bounded simply connected domain containing zero (indeed an analytic Jordan domain), by actual parameter uniformization. The entire domains, not a selected connected component of the physical plane, occur on the left.

For any compact subset Q of Omega_v, the maximum of H on Q is strictly less than v. By (8) it is eventually contained in E_(n,v). Conversely, if U is any domain containing zero with every compact subset eventually in E_(n,v), then H<=v on U. A point of U where H=v is impossible by the last observation of §4 and openness of U. Therefore U subset {H<v}, and connectedness implies U subset Omega_v. These two directions identify the Carathéodory kernel of every subsequence as exactly Omega_v. It is neither a singleton nor the plane. The usual kernel theorem for simply connected domains gives that Omega_v is simply connected, and the normalized Riemann maps converge locally uniformly on the unit disk to the normalized Riemann map onto Omega_v. In particular their derivatives at zero converge. Scaling conformal radius by |lambda|^n gives the pointwise assertion (1) with

    R(v)=rad(Omega_v,0)>0.

This proof does not infer kernel convergence just from Hausdorff convergence of zero sets; it uses uniform positive-level potentials and the absence of positive-level plateaus. There is no claimed Carathéodory extension of the Riemann maps to their boundaries.

### Uniformity in the positive level

Equation (9) identifies the entire zero-containing components: Omega_(dv)=lambda Omega_v. Hence R(dv)=|lambda|R(v). For any sequence v_j->v>0 the domains Omega_(v_j) have kernel Omega_v. Indeed any compact Q subset Omega_v can be enlarged to a compact connected subset of Omega_v containing Q and zero: take finitely many closed disks covering Q inside Omega_v and connect their centers to zero by finitely many compact paths in that domain. The maximum of H on this enlargement is below v, so it lies in the zero-containing component of {H<v_j} for all large j. Conversely any kernel domain must have H<=v everywhere and hence H<v by the same no-plateau argument. The simply connected kernel theorem now implies R(v_j)->R(v), proving continuity on v>0.

For each n the positive function v -> |lambda|^n r_(d^(-n)v)(c_*) is increasing (conformal radius monotonicity). Its pointwise limit R is continuous, so convergence is uniform on every compact level interval: partition the interval into a finite grid on which the oscillation of R between adjacent grid points is arbitrarily small, take simultaneous convergence at the grid points, and trap intermediate values by monotonicity. No monotonicity in n is assumed.

## 6. Consequences for the physical ground-transfer cost

For u small write u=d^(-n)v with v in [1,d] and n tending to infinity. Uniform convergence in (1), positivity and continuity of R on [1,d], and d^gamma=|lambda| give

    r_u(c_*)/u^gamma = [|lambda|^n r_(d^(-n)v)(c_*)]/v^gamma
                     = R(v)/v^gamma + o(1),

with the error uniform in v. The phase profile v -> R(v)/v^gamma is continuous, positive, and multiplicatively d-periodic. It is not asserted to be constant. This proves the comparability in (2) and (3) via NOTE.md (1). Moreover use (1) uniformly on [1,d^2] for u and du with the **same** index n:

    r_(du)(c_*)/r_u(c_*) -> R(dv)/R(v)=|lambda|.

This proves (2) and (4) without fixing the phase of u. Formula (5) follows directly from (1) and the vanishing of the linear ground change. In particular for fixed integer k>=1 the k-clock loss tends to k log|lambda|. All logarithms are natural. QED.

## 7. Exact genuine parameter examples and bounds

* c_*=-2: 0 -> -2 -> 2 -> 2. Thus m=2, p=1, lambda=4. Gamma=2 and the exact single-clock loss K_(u,2u)(-2,-2) tends to log 4. This strengthens the elementary two-sided radius comparison of NOTE.md by an exact ratio limit.
* c_*=i: 0 -> i -> -1+i -> -i -> -1+i. The exact landing period p=2 and m=2. The multiplier is 4(-1+i)(-i)=4(1+i), modulus 4 sqrt 2, so gamma=5/4. Thus K_(u,4u)(i,i) tends to log(4 sqrt 2). This is a distinct exact exponent, not a synthetic choice of multiplier. For an independent transversality check in this example, the period-two orbit point z(c) near -1+i satisfies z^2+z+c+1=0 and z'(i)=(1+2i)/5. The derivative of f_c^2(0)=c^2+c at i is 1+2i, so the entrance derivative is (4/5)(1+2i)!=0.

For every Misiurewicz point gamma<=2: on taking t small fixed and s->0 in (3), NOTE.md's global upper bound forces that inequality. Alternatively use the actual orbit multiplier bound |f_c'(z)|<=4 at every point of the bounded orbit for |c|<=2. In fact equality holds only for c_*=-2. If gamma=2, every point of the repelling orbit has modulus 2. For each point z on that orbit, |z^2+c_*|=2 and |c_*|<=2. Equality in the reverse triangle inequality forces |c_*|=2 and z^2=-2c_*; hence the next point is -c_*. Every point of the cycle is therefore -c_*, a fixed point, so c_*^2+c_*=-c_* and c_*=-2. Conversely the displayed real example gives gamma=2.

### 7.1 Exact continuous-scale tip constant, not just a discrete ratio

At c_*=-2, the landing point is 2, and the fixed-point continuation b(c) satisfies b(c)^2+c=b(c), b'(-2)=-1/3. Because m=2 and the chart derivative is normalized to 1, the entrance derivative is

    a=(c^2+c)'|_(c=-2) - b'(-2)=-8/3.

The entire Poincare function is P(v)=2 cosh(sqrt(v)), interpreted via its entire power series. Its value and derivative at zero are 2 and 1; the identity P(4v)=P(v)^2-2 follows from cosh doubling, so uniqueness of the normalized local linearization identifies it with the function in Section 3. For f(z)=z^2-2 the Joukowski parametrization gives

    f(w+w^(-1))=w^2+w^(-2),
    g_(-2)(2 cosh(zeta))=|Re zeta|.

The second identity follows directly by iteration when Re zeta is nonzero, and by boundedness when it is zero. Thus (8) gives

    H(w)=(1/2)|Re sqrt(a w)|.

The absolute value makes this independent of either square-root choice. The entire strict sublevel set {H<v} is the image of the vertical strip |Re zeta|<2v under w=zeta^2/a; it is connected, hence is Omega_v. On that strip the odd conformal bijection T(zeta)=tan(pi zeta/(8v)) maps onto the unit disk. For example |tan(x+iy)|<1 exactly when cos(2x)>0, and the principal analytic arctangent on the disk is its inverse on |Re z|<pi/4. The quotient by zeta -> -zeta yields a conformal bijection

    Phi_v(w)=tan^2(pi sqrt(a w)/(8v))

from Omega_v onto the unit disk. It is single-valued by evenness, holomorphic at zero by the even Taylor series, injective because equality of squares of T forces the two strip coordinates to be equal or opposite, and onto because every disk point has a square root in the disk. Its derivative at zero is a(pi/(8v))^2. Consequently

    R(v)=24 v^2/pi^2.

The locally uniform phase theorem now eliminates the discrete phase entirely at this particular parameter:

    lim_(u->0) r_u(-2)/u^2 = 24/pi^2.                (10)

This is in the parameter Green normalization stated in Section 1. In particular, uniformly as 0<s<t->0,

    K_(s,t)(-2,-2)=2 log(t/s)-(t-s)+o(1).

Indeed the difference of the two log-radius errors tends to zero regardless of the relative sizes of s and t. Equation (10) is an exact asymptotic constant for the actual equipotential ground, derived without a boundary derivative or approximation by a model domain at a fixed finite level.

## 8. Scope and next obstruction

This theorem is a written deduction from classical parameter transversality/linearization and the previous exact physical penalty identity; it does not claim priority over Tan Lei or an exhaustive literature search for equipotential-profile refinements. All constants and profiles are parameter-specific. No uniform comparison as Misiurewicz parameters approach an infinitely renormalizable parameter has been proved. In general the limiting function may have a phase-dependent radius; the pure continuous power-law constant is proved here specifically at -2 by the explicit strip quotient in Section 7.1. The actual nested parameter compacts used in H4 are not constructed, and their gains, transfer penalties at non-Misiurewicz anchors, and relative-neighborhood property are not supplied. No H1–H4/UPTCR/MLC status changes; no claim that the classical Misiurewicz local-connectivity theorem is new.

AI disclosure: ChatGPT GPT-6.2 assisted source reading, proof search, derivation, adversarial checking and writing. No independent human specialist review, Lean verification or proof of exhaustive novelty. The analytic proof is intended for review against the exact source interface in §2.
