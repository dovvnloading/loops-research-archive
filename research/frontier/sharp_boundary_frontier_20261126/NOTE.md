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

## 2. Sharp logarithmic coefficient on the actual Mandelbrot set

**Theorem 2 (physical sharpness).** For every 0<s<t<=1/8,

    2 log(t/s)-log(128)-(t-s)
       <= sup_{F} e(F) <= 4+2 log(t/s),                  (7)

where F ranges over nondegenerate subcontinua of the actual Mandelbrot set. In particular

    lim_{t/s -> infinity, 0<s<t<=1/8}
          sup_F e(F)/log(t/s) = 2.                       (8)

The coefficient two in the earlier universal large-ratio estimate cannot be reduced even for the actual quadratic parameter plane. This is stronger than a round-model order obstruction or the earlier qualitative divergence at -2. It gives actual compact witnesses, not just a boundary singularity of a hypothetical conformal map.

### 2.1. Physical conformal radius at the repelling tip

Write x_*=-2. We prove for 0<u<=1/8

    u^2/2 <= r_u(x_*) <= 64 u^2.                        (9)

Lower bound. The segment I=[-2,0] belongs to M: for c in [-2,0], p=(1+sqrt(1-4c))/2 belongs to [1,2], c=p-p^2>=-p, and f_c([-p,p])=[c,p] subset [-p,p]. The exterior Green function of I, extended by zero on I, is no smaller than G_M by monotonicity (also directly by the minimum principle on the complement of M, with nonnegative boundary values and positive difference log 2 at infinity). The exterior coordinate z=-1+(w+w^(-1))/2 maps |w|=exp(u) to the ellipse centered at -1 with semiaxes cosh u and sinh u; it is the actual level-u curve for I. Its closest point to -2 is its left real vertex: the squared distance from -2 along the ellipse equals X^2+2 cosh(u) X+1+sinh^2(u), X=cos(theta) in [-1,1], an increasing function of X. Thus the open disk B(-2,cosh u-1) is contained in D_u(I) subset D_u(M). Conformal radius monotonicity (Schwarz lemma) and cosh u-1>=u^2/2 prove the lower bound. This does not presume a boundary extension or local connectivity of M.

Upper bound. For 0<d<=1/4 put c=-2-d, a=2+d, and use the actual critical orbit x_j=f_c^j(0). The positive fixed point b=(1+sqrt(9+4d))/2 lies between 2 and 2+d/3, by squaring the latter inequality. The second iterate is x_2=a^2-a=2+3d+d^2. With v_j=x_j-b we have

    (8/3)d <= v_2 <= 3d+d^2 <= 13/16 < 1,
    v_{j+1}=2b v_j+v_j^2 >= 4v_j   (j>=2).

Let m be the first j>=2 with v_j>=1. It exists, m<=2+ceil(log_4(1/v_2)), and x_m>=3. For all subsequent iterates x_{j+1}=x_j^2-a >= (3/4)x_j^2 whenever x_j>=3, because a<=9/4. This also keeps x_j>=3. Therefore for k>=0,

    log x_(m+k) >= 2^k log((3/4)x_m)-log(3/4).

The quadratic parameter normalization is G(c)=lim 2^(-(j-1)) log^+|x_j|, NOT 2^(-j) log^+|x_j|. Taking the limit gives

    G(-2-d) >= 2^(-(m-1)) log(9/4)
             >= sqrt(v_2) log(9/4)/4
             >= sqrt(d)/4.                             (10)

For the last inequality, log(9/4)>=10/13 follows from log x>=2(x-1)/(x+1) for x>=1 (differentiate the difference); (8/3)*(10/13)^2>1. The ceil bound gives the middle inequality, with no floating point iteration. In particular -2-d is outside M.

For 0<u<=1/8 choose d=16u^2<=1/4. Then G(-2-d)>=u, so dist(x_*,C minus D_u)<=16u^2. Koebe's quarter theorem gives r_u(x_*)<=4 dist(x_*,C minus D_u)<=64u^2. This proves (9), including the exponent two, from the physical escape recurrence and elementary segment comparison. It uses neither the inverse parameter boundary derivative nor parabolic asymptotics.

### 2.2. Sharpness and explicit nonpolar witnesses

By (1) and (9),

    K(x_*,x_*) >= 2 log(t/s)-log128-L.                  (11)

This is a lower bound on the true continuum supremum by Theorem 1. The upper bound in (7) is inherited from the earlier ground-transfer theorem: for L>=s it is at most 4+2 log(L/s)<=4+2 log(t/s), and for L<s it is at most pi^2 L/(3s)<4. Division by log(t/s) proves (8), uniformly in the stated range of t.

For an explicit witness rather than a limiting supremum, put ell=log(t/s)>0 and

    epsilon=s^2/[32(1+ell)],   F=[-2,-2+epsilon].

This nondegenerate real interval lies in I subset M. The disk of radius R=s^2/2 around -2 is in D_s by (9)'s disk inclusion proof (conformal radius alone would not imply this). Thus delta=epsilon/R=1/[16(1+ell)] works in (6), and 1-a^2=4delta/(1+delta)^2<=4delta. Since H(x_*,x_*)>=2ell-log128, (6) implies

    e(F) >= 2ell-log128-1/2-L.                          (12)

Indeed a^2(2ell-log128)>=(2ell-log128)-8delta ell >= (2ell-log128)-1/2, even when the lower bound 2ell-log128 is negative. These are actual parameter intervals, with their own minimizing probabilities in each ground. They show sharpness without exchanging any equilibrium limit and infinite ground ratio.

For any strictly decreasing schedule t_0>...>t_N>0 with t_0<=1/8, the sum of the worst-case per-step penalties is at least the telescoping diagonal sum at -2:

    sum_{j<N} sup_F e_{t_(j+1),t_j}(F)
       >= log(r_(t_0)(-2)/r_(t_N)(-2))-(t_0-t_N)
       >= 2 log(t_0/t_N)-log128-(t_0-t_N).              (13)

The supremum here is taken separately at each step; this is not a claim that one chosen nested tower has those losses, or that the lower bounds on a specific MLC tower's gains must dominate (13). It rules out any geometry-free universal penalty budget of smaller cumulative logarithmic order. For the actual diagonal at -2 the corresponding upper bound is 2 log(t_0/t_N)+log128, by the other half of (9).

## 3. Attribution and proof boundary

Classical inputs: Green energy, disk Green kernel, Dirichlet balayage, Cauchy–Schwarz for the Dirichlet energy, Harnack inequality, Schwarz lemma, Koebe quarter theorem, and the compact-space component/quasicomponent theorem. See E. B. Saff, *Logarithmic Potential Theory with Applications to Approximation Theory*, Surveys in Approximation Theory 5 (2010), 165–200, [PDF](https://pages.cs.wisc.edu/~deboor/sat/papers/14/14.pdf), §3, equations (3.8)–(3.17), printed pp.187–188 (both PDF page images independently reopened). The source supplies classical facts, not the claimed sharp coefficient. Quadratic parameter uniformization is inherited with precisely the normalization in the preceding two archive notes. See also their citations and credit Douady–Hubbard. No claim that these general Green kernel facts or the repelling-tip escape exponent are new in the wider literature.

**Status:** written analytic proof of a sharp variational reduction and exact optimal leading logarithmic coefficient in the physical parameter plane. The earlier Fourier penalty upper bound is used as an imported archive argument, not silently reproved. The sharp lower coefficient is independent of that upper bound. No new source bytes were hashed; Saff's page images were read, not a full literature novelty audit. No physical sequence of connected relative neighborhoods, divergent net-gain schedule, or parameter rigidity is asserted. H4, H1–H3, UPTCR and MLC remain open. AI assistance: ChatGPT GPT-6.2; no independent human specialist review or Lean verification.
