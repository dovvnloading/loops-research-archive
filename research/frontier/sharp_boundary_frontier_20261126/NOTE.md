# Exact worst-case ground transfer and the quadratic parameter tip

**Base:** main 47806d64c64688bdf27c817f036cfdbfa85ce1d5.
**Target:** H4_RIGIDITY (open), specifically the change-of-ground comparison in [parameter ground transfer](../../independent_audits/parameter_ground_transfer_20261126/NOTE.md), §§2–5, and [parameter capacity increments](../../independent_audits/parameter_capacity_increment_20261123/NOTE.md), §§2–4, 6.2. No ledger promotion. This is a physical parameter-domain result, not a marked-carrier construction.

The previous ground-transfer note derives a universal penalty B(s,L) and an upper bound 4+2 log(L/s) for L=t-s>=s; its round model proves only logarithmic order is necessary. It also shows unbounded loss on actual Mandelbrot compacts at the real tip -2. We isolate the exact optimal penalty functional and then seek sharp quantitative behavior at that actual parameter, rather than duplicate the active satellite-boundary or annular-response PRs #170 and #168.

## 1. Exact diagonal reduction

Use the previous note's normalization: G(c)=G_M(c)=log|c|+o(1), D_u={G<u}, Gamma_u={G=u}, 0<s<t, L=t-s. These are bounded simply connected analytic Jordan domains for positive u, by the classical quadratic parameter uniformization. The Green kernels g_u have -Delta g_u=2 pi delta and zero boundary values. For a nonpolar compact F in M, V_u(F) is the minimum Green energy of a probability on F. Define

    e(F)=V_t(F)-V_s(F)-L,
    H(x,y)=g_t(x,y)-g_s(x,y),
    K(x,y)=H(x,y)-L,
    r_u(x)=conformal radius of D_u at x.

H and K extend continuously across the diagonal on D_s x D_s and are separately harmonic there. Indeed the disk Green formula for a conformal map psi_u:D_u -> unit disk is

    g_u(x,y)=log |1-conj(psi_u(y))*psi_u(x)| - log|psi_u(x)-psi_u(y)|.

The divided difference (psi_u(x)-psi_u(y))/(x-y) extends nonvanishingly across the diagonal; injectivity handles the off-diagonal. In particular

    H(x,x)=log(r_t(x)/r_s(x)).                            (1)

Domain monotonicity gives H>=0. No extension of the parameter uniformization to G=0 is assumed.

**Theorem 1.** For every nonpolar compact F subset M,

    0 <= e(F) <= max_{x in F} [log(r_t(x)/r_s(x))-L].      (2)

The exact supremum over all nondegenerate subcontinua F of M is

    sup_F e(F) = max_{x in boundary M} K(x,x).             (3)

In particular the diagonal bound is optimal over genuine parameter continua, not merely over probability measures or synthetic round domains. There is also the lower bound e(F)>=min_{x,y in F}K(x,y), which may be negative and is then weaker than zero.

**Proof.** Let beta_x be the harmonic-measure probability on Gamma_s with pole x in D_s. Let sigma_s be the uniform-angle probability there, in the external parameter coordinate. As shown in the preceding note, its Green potential in D_t is t-max(s,G), so I_t(sigma_s)=L and this potential is identically L on Gamma_s. Put eta_x=beta_x-sigma_s (a signed zero-mass measure).

We claim the exact Gram identity

    K(x,y)=I_t(eta_x,eta_y).                              (4)

Here I_t is the Green-energy bilinear form. All boundary charges have smooth densities on the compact analytic Gamma_s and finite Green energy in D_t. To justify (4) without assigning a finite self-energy to a point mass, choose probability measures nu_x,nu_y uniform on sufficiently small Euclidean circles centered at x,y, contained in D_s. They have finite energy; the harmonic mean property shows their balayages are beta_x,beta_y exactly. The decomposition (3) in the preceding note applies to any finite-energy probability supported compactly in D_s (its proof uses only that inclusion, not that the support lies in M): extend U_s by zero, subtract its boundary flux, and use the Dirichlet orthogonality. It gives integral integral H dnu dnu = L+I_t(beta_s nu-sigma_s). Apply to nu_x,nu_y and (nu_x+nu_y)/2 and polarize. The cross integral of H equals H(x,y) by the two harmonic mean-value properties, even for intersecting circles because the singularity has canceled. This proves (4). Equivalently it follows by a direct Green balayage identity and polarization.

Consequently K is positive semidefinite, its diagonal is nonnegative, and

    |K(x,y)| <= sqrt(K(x,x) K(y,y)) <= max_{z in F} K(z,z)
       for x,y in F.                                     (5)

The energy difference for any finite-energy probability on F is I_t(nu)-I_s(nu)=L+integral integral K dnu dnu, nonnegative after subtracting L. Comparing the two actual minimizing probabilities (use the s-minimizer for the upper bound and the t-minimizer for the lower bound) yields (2) and the min-kernel lower bound. Finite energy in one ground is equivalent to finite energy in the other for probabilities on F since H is bounded there. In particular no equality of the two minimizers is used.

The continuous function x -> K(x,x) is subharmonic in D_s: for a sufficiently small centered circle C, eta_x is the harmonic average of eta_y for y in C (in the sense of pairing against continuous functions). More explicitly K(x,x) is the double average of K(y,z) on C x C, and (5), or 2 K(y,z)<=K(y,y)+K(z,z), gives the submean inequality. On each component of int M the maximum principle therefore bounds the diagonal by its maximum on the boundary of that component, which lies in boundary M. Compactness gives a maximum on M and hence on boundary M.

For any x in M and sufficiently small epsilon>0, take the component of M intersect closed B(x,epsilon) that contains x. It is compact and reaches the circle of radius epsilon by the classical boundary-bumping lemma for a nonempty proper closed subset of a continuum. For clarity the needed special case follows from components=quasicomponents in compact Hausdorff spaces: if that component misses the circle, a clopen subset of M intersect closed B containing the component and missing the compact circle intersection exists by finite intersection of clopen neighborhoods. It is then both closed and open in M, since it lies strictly inside the ball, contrary to connectedness and the existence of a point of M outside the ball. The component is a nondegenerate continuum, thus nonpolar (capacity >=diameter/4 via projection, as in the preceding capacity note). For these shrinking continua the upper and lower bounds on e converge by continuity of K to K(x,x). Choose x maximizing the diagonal. This proves (3). No local connectivity or local path connectivity has entered the argument. QED.

**Localized, computable refinement.** For x in D_s, choose R>0 with B(x,R) subset D_s and let F subset M intersect closed B(x,delta R), where 0<delta<1. Write a=(1-delta)/(1+delta). The positive separately harmonic kernel H satisfies the disk Harnack bounds twice, so

    a^2 H(x,x)-L <= e(F) <= a^(-2) H(x,x)-L.             (6)

Combine with (2) and zero if stronger. If H vanishes identically in one variable the corresponding Harnack inequality is still valid by nonnegativity. Formula (6) is particularly useful for comparing physical tip intervals to the point limit, without taking an unspecified sequence of capacities. It is not a claim that the equilibrium measure is supported at x.

## 2. Attribution, status, and next proof obligation

Classical inputs: Green energy, disk Green kernel, Dirichlet balayage, Cauchy–Schwarz for the Dirichlet energy, Harnack inequality, and the compact-space component/quasicomponent theorem. See E. B. Saff, *Logarithmic Potential Theory with Applications to Approximation Theory*, Surveys in Approximation Theory 5 (2010), 165–200, [PDF](https://pages.cs.wisc.edu/~deboor/sat/papers/14/14.pdf), §3, equations (3.8)–(3.17), and §1. The prior note supplies the explicit physical uniform-angle potential and the transfer identity; this new argument independently addresses the diagonal, positivity and optimal continuum reduction. No claim that these general Green kernel facts are new in potential theory.

**Status:** written analytic proof of a sharp variational reduction for the actual domains. No physical sequence of connected relative neighborhoods, divergent net-gain schedule, or parameter rigidity is asserted. The next proof obligation in this PR is to establish the precise logarithmic coefficient on actual quadratic parameters, using direct critical-orbit estimates at -2. AI assistance: ChatGPT GPT-6.2; no independent human specialist review.
