# Finite-rank multipole hierarchy and intrinsic dipole correction

**Target:** H2_RESPONSE_REALIZATION clauses 2, 3, 10. **Status:** written analytic continuation of [RANK_ONE.md](RANK_ONE.md). This is a hierarchy of controlled finite-rank corrections to an exact inner response; it is not a future-closed finite geometric port construction.

## 1. Statement and nested inequalities

Retain the notation and hypotheses of RANK_ONE.md. Put t=r/R∈(0,1), L=log(1/t), and denote by a_{n,j} the real normalized sine/cosine trace coefficients at |z|=r. For N≥0 define the partially corrected response

    Q_N(y,x)=inf_(u|K=y) [B(u)+k(x−M(tr u))²
                          + Σ_(1≤n≤N,j) d_n a_(n,j)²],
    d_n=2π n (coth(nL)−1),  k=2π/L,

where B, M and the traces are exactly those of the rank-one theorem. Thus Q_0=Q_R there; no part of the infinite exterior baseline energy T is removed. Put

    ε_n = coth(nL)−1 = 2t^(2n)/(1−t^(2n)).

For every N, the actual response E_R satisfies

    Q_0 ≤ Q_N ≤ Q_(N+1) ≤ E_R ≤ (1+ε_(N+1)) Q_N.          (1)

Moreover Q_N−Q_0 is a positive semidefinite quadratic form of rank at most 2N. For the real slit domains under consideration the rank bound improves to N. This controls the relative error in arbitrarily small response directions, not just in a fixed norm of potentials. Increasing N adds finitely many explicit trace observables to the exact infinite-exterior baseline.

Proof of (1): the omitted energy in the full variational integrand is bounded by ε_(N+1) T, which is at most ε_(N+1) times the partially corrected integrand. This holds for each individual trial function by monotonicity of coth(nL). Taking infima and using the nesting proves (1). In particular Q_N converges to E_R in relative Loewner order without any additional compactness argument.

## 2. Exact finite-rank Schur update

Let u^0 be the Q_0 minimizer. By the orthogonality formula of RANK_ONE.md,

    u^0 = u_y + [k/(β+k)] (x−m(y)) v,

with u_y, v, β as defined there. In particular u^0 is linear in (y,x). Let H_k be the Hilbert space of zero-inner-trace functions w on U equipped with norm squared B(w)+k M(tr w)². Its inner product is denoted by ⟨·,·⟩_k. This is coercive by the argument in RANK_ONE.md. The Q_0 integrand at u^0+w equals Q_0+||w||_k² by the Euler equation for u^0.

Define P:H_k→R^(2N) as the vector of the first N real Fourier pairs at the circle, a bounded map by the trace estimate. Let a=P(tr u^0) denote those same coefficients of u^0 (P applied here via its natural extension to all H¹ functions, with the notation tr suppressed when the argument is a function). Let D=diag(d_n,d_n)_(n=1)^N and G=P P^*, where P^* uses the H_k inner product. The matrices D and D^(−1)+G are positive definite for N≥1; G≥0. Then

    Q_N−Q_0 = a^T (D^(−1)+G)^(-1) a.                    (2)

Indeed the residual minimization is inf_w [||w||_k²+(a+Pw)^T D(a+Pw)]. Set v_0=(D^(−1)+G)^(-1)a and w_0=−P^*v_0. Then a+Pw_0=D^(−1)v_0, so w_0 satisfies the Euler equation w_0+P^*D(a+Pw_0)=0, and the quadratic residual is ||w_0||_k²+v_0^T D^(−1)v_0 = v_0^T(G+D^(−1))v_0=a^T v_0. Completing the square or strict convexity proves it is the minimum. Since a is linear in the terminal data, (2) proves positivity and the rank bound. If a vanishes on a particular terminal direction, that direction needs no correction at this order; this is not an assertion that the actual finite-cylinder response equals Q_0 on that direction.

For real slits and real constant data, complex conjugation preserves every electrode individually and preserves B and all the variational integrands. Uniqueness makes u^0 and every constrained minimizer even under reflection, so their sine coefficients vanish. The odd subspace cannot improve the minimization (it contributes nonnegative energy independently by orthogonality under reflection). Restricting H_k to the even subspace proves the rank bound N using the cosine coefficients alone. In particular Q_1−Q_0 is rank at most one on the actual real slit family.

The matrix G is defined by genuine inner-domain elliptic representers, not by geometric graph incidence. Its computation is an additional analytic task; this theorem does not assume that the canonical WAD observes it.

## 3. Explicit intrinsic dipole correction without solving the representer problems

The first-mode correction admits a stronger closed asymptotic with a universal relative remainder. Allow both sine and cosine (the sine coefficient vanishes for real slits). For N=1 write a=(a_c,a_s). Since T(w)≥2π||Pw||²,

    ||G||≤1/(2π),    2π||a||²≤B(u^0)≤Q_0.

Here the first inequality follows from ||P||²≤1/(2π) in H_k. With d=d_1=2π ε_1, equation (2) gives

    0≤ d||a||²−(Q_1−Q_0) ≤ ε_1 d||a||² ≤ ε_1² Q_0.       (3)

For example diagonalize G≥0: (D^(−1)+G)^(-1)=d(I+dG)^(-1); the difference from dI has norm at most d²||G||. No bound on the inverse response matrix is used. Also

    0≤ (d−4πt²)||a||² ≤ [2t⁴/(1−t²)] Q_0.

By (1) the omitted tail after the first mode is bounded by ε_2 Q_1≤ε_2(1+ε_1)Q_0=2t⁴/(1−t²)² Q_0. Combining these inequalities, and noting ε_1²=4t⁴/(1−t²)², gives the two-sided bound

    |E_R − Q_0 − 4πt²||a||²|
                   ≤ [4t⁴/(1−t²)²] Q_0.                  (4)

Although the intermediate definition of a uses an artificial circle, the leading term in (4) is intrinsic. The harmonic Laurent expansions at infinity, in the same physical complex coordinate as the round outer electrode, are

    h_y(z)=m(y)+Re(b_y/z)+O(|z|^(−2)),
    G_K(z)=log|z|−log c(K)+Re(b_K/z)+O(|z|^(−2)),

where G_K is the Green function constructed in RANK_ONE.md. These expansions follow from harmonicity in the inverse coordinate after removing the logarithmic singularity (ordinary convergent harmonic power series in a neighborhood of infinity). The coefficients b_y and b_K are complex numbers; for real slits and real data they are real by reflection.

On |z|=r the trace of u^0 is precisely that of

    h_y + [k_R/(2π)] (x−m(y)) G_K,

since k_R=β k/(β+k) and G_K=(2π/β)v on U. Its first Fourier pair has squared norm

    ||a||² = |b_y+[k_R/(2π)](x−m(y))b_K|²/(2r²).

Indeed the constant logarithmic term contributes no nonzero Fourier coefficient, and the normalized first modes are sqrt(2)cos θ and sqrt(2)sin θ. All higher Laurent terms are orthogonal to the first pair; analyticity in the full exterior of the radius-r circle justifies their evaluation there (K lies strictly inside). Therefore (4) reads

    E_R(y,x) = Q_R(y,x)
       + (2π/R²)|b_y+(x−m(y))b_K/log(R/c(K))|² + error,
    |error| ≤ [4(r/R)^4/(1−(r/R)²)²] Q_R(y,x).             (5)

The coefficient is in physical coordinates and does not depend on the auxiliary r. The remainder bound holds with every r strictly enclosing K. In the real slit case the correction is itself rank at most one, with a nonnegative coefficient. In a reflection-symmetric shape with symmetric data (additional symmetry about the origin, not merely conjugation), both odd Laurent modes vanish and the dipole term is zero; equation (5) correctly gives the improved remainder.

## 4. Actual-family application and boundary

For K_p and R_p from [SPECTRAL.md](SPECTRAL.md), r=2 and t=2/R_p=O(2^(−p)). Formula (5) gives a relative O(16^(−p)) remainder after the intrinsic rank-one neck term and dipole correction, with the inner and dipole invariants of the *actual* shape K_p. More generally (1) yields relative O(4^(−(N+1)p)) for each fixed N, with rank at most N beyond the original rank-one correction. These are all-potential response bounds. They do not claim the same faster rate after replacing K_p by K_*; that shape substitution has its own O(4^(−p)) error. Nor do they assert that the dipole is observable from the buffered WAD (which is zero here).

This closes a finer analytic approximation subproblem of H2 on physical round outer necks, not the global H2 gate: full nonconstant infinite-exterior response and the correct trace identification remain essential inputs. Exact finite matrix updates require solving the indicated elliptic representer problems. We do not assert future-closed port compression, control of non-annular or dynamically unequal footprints, a rigidity theorem, or MLC.

Proof is elementary given the variational/Fourier groundwork of RANK_ONE.md. Classical multipole expansions and Hilbert-space Schur complements are credited as standard; no claim of priority over existing potential theory. GPT-6.2 assisted derivation and audit; no human specialist review or formal kernel check.
