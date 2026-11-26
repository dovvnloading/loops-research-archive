# Exterior neck: exponentially accurate rank-one separation

**Date:** 2026-11-26. **Target:** H2_RESPONSE_REALIZATION, clauses 2, 3, 10 of [network_response_state.md §6](../../mlc_unified/network_response_state.md#6-analytic-response-realization-theorem), and the spectral-floor obstruction relevant to H3_COERCIVITY. **Status:** written analytic theorem for an actual round exterior neck; not a closure of either ledger gate.

At base main 9a70093f4dcd9e4c7733244909d8f918369d1659 the [annular midpoint theorem](../annular_midpoint_response_20261126/NOTE.md) proves the constant-middle-trace comparison 1+sech L for a constant outer electrode, including the actual selected real primitive-tip family. The following different approximation retains the full nonconstant *decaying exterior trace energy* and eliminates only the constant mode. It separates the exterior degeneration as a rank-one term, with relative error coth L−1=O(exp(−2L)), independent of the interior geometry and of any spectral floor. No priority over classical Dirichlet-to-Neumann or capacity methods is asserted.

## 1. Statement

Let K be a nonempty finite union of pairwise disjoint nondegenerate compact real intervals K_i, i=1,...,b, contained in |z|<r. (The same proof works for disjoint analytic filled Jordan domains.) The slit banks and tips are taken in the analytic bordered compactification, using square-root charts at the tips. Fix R>r and write L=log(R/r). Let E_R(y,x) be the actual Dirichlet energy infimum on D_R minus K, with constant values y_i on both banks of each K_i and value x on |z|=R. Energy is ∫|∇u|², without factor 1/2.

On the exterior of K in the sphere, let h_y be the bounded harmonic extension of the inner data, including at infinity, and set

    A(y) = ∫_(C\K) |∇h_y|²,       m(y)=h_y(∞).

These are respectively a nonnegative quadratic form and a linear functional; m is a convex average of the y_i, and ker A consists of constant vectors. Write c(K) for logarithmic capacity in the normalization in which the Green function of the exterior with pole at infinity equals log|z|−log c(K)+o(1). Let

    k_R = 2π/log(R/c(K)),
    Q_R(y,x) = A(y) + k_R (x−m(y))².

**Theorem.** For every real (y,x),

    Q_R(y,x) ≤ E_R(y,x) ≤ coth(L) Q_R(y,x).                  (1)

In particular, as an inequality of response matrices on the same terminal space,

    0 ≤ Λ_R−Λ_Q ≤ [2(r/R)²/(1−(r/R)²)] Λ_Q.               (2)

The approximating response has exactly one new rank-one term beyond the inner exterior response A, and its scalar conductance and coupling functional are intrinsic to K. This is a relative inequality even in directions with arbitrarily small energy. It is not a truncation of the trace to a constant, and does not identify A or m with canonical buffered widths.

## 2. Variational proof of (1)

Use the inner bordered surface U=D_r\K. The real Fourier basis at |z|=r is 1, sqrt(2) cos(nθ), sqrt(2) sin(nθ), orthonormal for dθ/(2π). Write M(a)=a_0 for the mean and a_{n,j} for the two nonconstant coefficients at frequency n. The exact decaying harmonic extension of any H^(1/2) trace a to the infinite exterior cylinder has constant a_0 and mode a_{n,j} exp(−nt), where t=log(|z|/r). Its energy is

    T(a)=2π Σ_(n≥1,j) n a_{n,j}².

On the finite cylinder with outer constant x, the exact harmonic interpolation energy is

    2π/L (x−M(a))² + T_L(a),
    T_L(a)=2π Σ_(n≥1,j) n coth(nL) a_{n,j}².               (3)

Both identities follow by integrating (v')²+n²v²=(vv')' for the solution of v''=n²v; for the constant mode use affine interpolation. They extend from trigonometric polynomials by convergence in H^(1/2) and in energy. The original function outside the collar is not assumed constant, and the same trace a is used on both sides of the seam. Standard H¹ trace gluing across the analytic circle therefore gives exactly

    E_R(y,x) = inf_(u|K=y) [D_U(u)+T_L(tr u)+k(x−M(tr u))²],
    k=2π/L.                                                (4)

Introduce the quadratic form B(u)=D_U(u)+T(tr u), with associated bilinear form B(u,v). It is a Hilbert norm squared on the closed space of H¹ functions having zero trace on K: the gradient norm controls the H¹ norm by Poincaré with nonempty Dirichlet boundary, and the trace term is bounded in H¹ by the trace theorem. The same facts give existence of minimizers on the affine space with inner data y; the latter is nonempty by disjoint smooth neighborhoods of the electrodes in the bordered charts. B has constants as its only kernel before prescribing inner data.

Let u_y minimize B with inner traces y, and let v minimize B with inner traces zero and M(tr v)=1. The latter affine class is nonempty (a smooth function equal to one near |z|=r and zero near K suffices). Set β=B(v)>0. The Euler equations, from arbitrary zero-inner-trace perturbations for u_y and mean-zero such perturbations for v, give

    B(u_y,w)=0,
    B(v,w)=β M(tr w)                                      (5)

for every w of zero inner trace. For the second identity subtract M(tr w)v from w to get an admissible variation. Extend u_y by its decaying exterior harmonic extension. Equation (5) and trace gluing give weak harmonicity across |z|=r; at infinity the exterior Fourier series is harmonic in the inverse coordinate, with constant value M(tr u_y). Regularity and uniqueness of the bounded Dirichlet problem on the compact sphere slit domain follow from the maximum principle (constant analytic boundary data in the resolved charts). This is exactly h_y. Thus B(u_y)=A(y) and M(tr u_y)=m(y). The maximum principle gives m(y) between min y_i and max y_i; by linearity m(y)=Σ ω_i y_i, with ω_i≥0 and Σω_i=1. Zero energy forces a single constant on the connected exterior, so ker A is as stated.

For each prescribed mean s, orthogonality (5) gives the exact constrained minimum

    min_(u|K=y, M(tr u)=s) B(u)
         = A(y)+β(s−m(y))².                               (6)

Indeed the candidate u_y+(s−m(y))v satisfies the constraints; any residual has zero trace on K and zero mean and is B-orthogonal to both terms. Eliminating s yields

    inf_(u|K=y) [B(u)+k(x−M(tr u))²]
         = A(y)+(1/k+1/β)^(-1)(x−m(y))².                  (7)

Since 1≤coth(nL)≤coth L for every n≥1, the integrand of (4) is between the integrand in (7) and coth L times that integrand. Infima preserve both inequalities; no bounded trace amplitude or lower bound on the response eigenvalues is needed.

## 3. Intrinsic identification of the scalar resistance

The quantity 2π/β is exactly log(r/c(K)), not an unknown fitted circuit resistance. Construct G on U as (2π/β)v. Outside |z|=r, extend this function by the decaying extension of its trace plus log(|z|/r). To verify matching normal flux, test against any compactly supported smooth function φ on C\K. The interior plus decaying-tail energy pairing is (2π/β)B(v,φ|U)=2π M(tr φ) by (5): the decaying extension minimizes exterior energy for the trace, hence pairs to zero with zero-trace test residuals (integration by parts, or mode orthogonality). The log term contributes −2π M(tr φ) by integrating its radial derivative on the exterior cylinder; the test has compact support. Thus G is harmonic weakly across the seam, and hence classically away from K. It is zero on K and has expansion at infinity

    G(z)=log|z|−log r+2π/β+O(1/|z|).

At the analytic slit boundary, local harmonic regularity in the square-root charts gives the stated zero boundary values. G is nonnegative by the maximum principle on large disks. Uniqueness of a harmonic function with this boundary condition and logarithmic pole follows because the difference of two such functions extends harmonically over infinity and has zero boundary data. Hence this is precisely the Green function with pole at infinity, and its constant term gives

    c(K)=r exp(−2π/β),    (1/k+1/β)^(-1)=2π/log(R/c(K)).

This also shows directly that the rank-one correction is independent of the arbitrary intermediate circle. Together with (7) and the comparison following it this proves (1)–(2).

## 4. Scope and adversarial checks

* A single concentric disk gives T=T_L=0 at the minimizer and exact radial conductance 2π/log(R/c(K)); common constant data gives zero in both forms. The result retains all exterior Fourier modes in B, not a bounded Fourier-port state. Its finite terminal form is valid for prescribed whole-component electrodes, not for future splittings.
* Dropping the entire nonconstant exterior energy would produce a different inner free-boundary problem; no estimate here permits that substitution. The coth factor compares exact finite-cylinder and exact decaying-cylinder energies, not arbitrary welding maps or dynamical transfers.
* The proof uses an obstacle-free exterior annulus; no analogous assertion is made for unequal footprints, partially prescribed outer traces, nonconstant data, or overlap of collars. No claim of sharpness after terminal minimization is made.
* A single fixed surface with r/R small has the same comparison for all terminal directions, including degenerate limits. This does not imply uniform coercivity of the unreduced response. The next step is to prove the number and rate of collapsing directions on the archive's actual family, using certified inner geometry.
* Classical ingredients: Dirichlet principle, trace theorem, Fourier/Parseval, maximum principle, Green function normalization of logarithmic capacity. The argument is written above, not an import of any disputed KKL theorem. Attribution to Matthew Robert Wesney for archive-specific physical constructions. GPT-6.2 assisted proof derivation and audit; no independent human specialist verification or Lean formalization.
