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

## 2. Independent global upper bound by inversion and schlicht distortion

**Theorem 2 (all positive ground levels).** For every 0<s<t, every x in M and every nonpolar compact F subset M,

    K(x,x) <= log 4 + 2 log[(1-exp(-t))/(1-exp(-s))],
    e(F)   <= log 4 + 2 log[(1-exp(-t))/(1-exp(-s))]
           <= log 4 + 2 log(t/s).                      (7a)

Unlike the prior 4+2 log(L/s) estimate this bound holds for all ratios, improves the additive constant in the large-ratio asymptotic, and does not use any Fourier-mode bounds. For t near s the prior O((t-s)/s) bound is better; the two are complementary. The coefficient two is optimal on the actual M by the next section.

**Proof.** Let Psi be the conformal external parameter inverse, |w|>1 to C minus M, Psi(infinity)=infinity, Psi(w)/w -> 1. For fixed x in M define

    f_x(z)=1/(Psi(1/z)-x),   0<|z|<1,     f_x(0)=0.

This is a schlicht function on the full unit disk: the denominator is nonzero, the composition is injective, the apparent singularity at zero is removable with f_x'(0)=1, and f_x has no other zero. Let C_x(r)=cap(f_x(closed disk of radius r)), where cap is logarithmic capacity. Inversion about x maps the exterior of D_u, with boundary and infinity included, onto the compact f_x(closed disk of radius exp(-u)). It maps D_u to that compact's exterior in the sphere, taking x to infinity. If phi_u:D_u -> unit disk satisfies phi_u(x)=0, phi_u'(x)>0, the normalized exterior map is w -> 1/phi_u(x+1/w), asymptotic to r_u(x)*w at infinity. Since the derivative at infinity of the exterior map is the reciprocal logarithmic capacity,

    r_u(x)=1/C_x(exp(-u)).                              (7b)

This is exact; neither a boundary extension at |z|=1 nor any estimate on a Julia set is used.

For any schlicht f with f(0)=0 set M_f(r)=max_{|z|=r}|f(z)|. The image of the closed r-disk is a continuum containing zero and lies in the closed disk of radius M_f(r), by the maximum principle. Its capacity is bounded by

    M_f(r)/4 <= cap(f(closed r-disk)) <= M_f(r).          (7c)

The lower bound is the classical continuum diameter bound (projection and Fekete points, as in the archive's capacity note); the upper is monotonicity of logarithmic capacity. The factor four here need not be optimal for a fixed schlicht image.

The following radial ratio bound is a consequence of the ordinary Koebe growth theorem, not an assumption of starlikeness. For z of modulus r in (0,1) use the normalized Koebe transform

    T_z(v)=[f((z+v)/(1+conj(z)*v))-f(z)]
            /[(1-r^2) f'(z)].

It is schlicht, T_z(0)=0 and T_z'(0)=1. The lower growth bound at v=-z gives

    |f(z)|/[(1-r^2)|f'(z)|] >= r/(1+r)^2,
    |z f'(z)/f(z)| <= (1+r)/(1-r).

Therefore along every fixed ray z=r exp(i theta),

    d/dr log|f(r exp(i theta))|
        = Re[z f'(z)/f(z)]/r
        <= 1/r + 2/(1-r).

Integrate from 0<r<R<1 (positive lower endpoint r, not from zero) and maximize over theta:

    M_f(R)/M_f(r) <= (R/r) [(1-r)/(1-R)]^2.             (7d)

Apply (7b)–(7d) with r=exp(-t), R=exp(-s), where R/r=exp(L). It gives

    r_t(x)/r_s(x)
      = C_x(R)/C_x(r)
      <= 4 exp(L) [(1-exp(-t))/(1-exp(-s))]^2.

Taking logs and subtracting L yields (7a) for the diagonal, hence for every F by Theorem 1. The function (1-exp(-u))/u is decreasing on u>0 (its derivative has numerator (u+1) exp(-u)-1<0); this proves the last inequality. QED.

The estimate is elementary, global, and independent of the old Fourier proof; the logarithmic coefficient cannot be reduced uniformly as s tends to zero. No priority claim is made for the use of these classical univalent-function inequalities.

## 3. Sharp logarithmic coefficient on the actual Mandelbrot set

**Theorem 3 (physical sharpness).** For every 0<s<t<=1/8,

    2 log(t/s)-log(128)-(t-s)
       <= sup_{F} e(F) <= log 4+2 log(t/s),                  (7)

where F ranges over nondegenerate subcontinua of the actual Mandelbrot set. In particular

    lim_{t/s -> infinity, 0<s<t<=1/8}
          sup_F e(F)/log(t/s) = 2.                       (8)

The coefficient two in the earlier universal large-ratio estimate cannot be reduced even for the actual quadratic parameter plane. This is stronger than a round-model order obstruction or the earlier qualitative divergence at -2. It gives actual compact witnesses, not just a boundary singularity of a hypothetical conformal map.

### 3.1. Physical conformal radius at the repelling tip

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

### 3.2. Sharpness and explicit nonpolar witnesses

By (1) and (9),

    K(x_*,x_*) >= 2 log(t/s)-log128-L.                  (11)

This is a lower bound on the true continuum supremum by Theorem 1. The upper bound in (7) follows independently from (7a). Division by log(t/s) proves (8), uniformly in the stated range of t.

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

## 4. Neutral cusp: a genuinely different ground-loss scale

The sharp worst-case coefficient in §3 should not be imposed at every boundary point. The actual cusp c_0=1/4 gives a contrasting, much slower diagonal divergence. Here we derive the physical escape profile directly; no parabolic transit or asymptotic-expansion theorem is assumed.

**Theorem 4.** Define A=(log 2)^2/64 and B=1600(log 2)^2. For 0<u<=2^(-100),

    A/[log(1/u)]^2 <= r_u(c_0) <= B/[log(1/u)]^2.        (14)

Consequently, for 0<s<t<=2^(-100),

    |K(c_0,c_0)+(t-s)-2 log(log(1/s)/log(1/t))|
       <= log(102400).                                  (15)

This is the actual point-localized optimal penalty in the limit of shrinking nonpolar cusp intervals, by Theorem 1's continuous-kernel comparison. In particular if t is fixed in the stated range and s tends to zero, the leading order is 2 log log(1/s), not 2 log(1/s).

### 4.1. Uniform complex upper escape estimate

For a real 0<a<=1/8 write c^+=1/4+a^2 and x_j=f_(c^+)^j(0). Set y_j=x_j-1/2. The exact recurrence and initial value are

    y_(j+1)=y_j+y_j^2+a^2,    y_0=-1/2.                 (16)

The sequence is strictly increasing, all y_j>=-1/2, and eventually positive since each increment is at least a^2. The update function y -> y+y^2+a^2 is increasing on [-1/2,infinity). Let k be the first j with y_j>-a. Since y_(k-1)<=-a, we have

    -a < y_k <= -a+2a^2 <= -a/2.

Let m be the first j with y_j>=0. Every update from j=k to m-1 has y_j in (-a,0), and its increment is at most 2a^2. Thus (m-k) 2a^2 >= a/2, i.e. m-k >= 1/(4a). Since k>=1, N=floor(1/(4a)) satisfies N<m, and x_N<1/2.

For any complex parameter c with |c-c_0|<=a^2, one has |c|<=c^+ and, by induction from the critical point 0,

    |f_c^j(0)| <= f_(c^+)^j(0)   for every j.

The majorant orbit is nonnegative. In particular |f_c^N(0)|<1/2. As |c|<1/2, putting M_j=max(1,|f_c^j(0)|) gives M_(j+1)<=(3/2) M_j^2. Iterate the logarithmic inequality from M_N=1 and use the parameter Green normalization. Since N>=1,

    G(c) <= 2^(-(N-1)) log(3/2)
          <= 4 exp[-(log 2)/(4a)].                      (17)

The estimate is uniform on the whole complex disk, not just on the positive real transit path. This uniformity is essential to the lower bound on the conformal radius. The estimate also includes all parameters in M (where G=0).

### 4.2. Real lower escape estimate

On the real majorant orbit (16), let n be the first j with y_j>=1/2. Each step from j<n starts at y in [-1/2,1/2), with d=y^2+a^2<=1/4+1/64<1. For all v between y and y+d,

    v^2+a^2 <= (|y|+d)^2+a^2
             = d(1+2|y|+d) <= 3d.

Hence the integral of dv/(v^2+a^2) over this step is at least 1/3. The consecutive step intervals have disjoint interiors. Summing and bounding by the integral over the whole real line gives

    n/3 <= integral_R dv/(v^2+a^2)=pi/a.

Starting from y_n>=1/2, at most four further updates suffice to reach y>=3/2 (increments at least 1/4). Therefore there is an iterate x_J>=2 with

    J <= 3pi/a+4 <= 10/a

for a<=1/8, using pi<22/7. Thereafter x_(j+1)>=x_j^2 since c^+>0, and the normalization of G yields

    G(c_0+a^2) >= 2^(-(J-1)) log 2
                 >= (log 2) exp[-10(log 2)/a].          (18)

This real parameter is outside M. Equations (17)–(18) are two-sided exponential-in-inverse-square-root escape bounds with explicit constants. They do not claim an exact parabolic transit asymptotic, which would require finer analysis.

### 4.3. Inversion to conformal radius and physical local penalty

For 0<u<=2^(-100) put

    a_-=(log 2)/(4 log(4/u)),
    a_+=10 log 2/log((log 2)/u).

Both lie in (0,1/8]: log(4/u)>=2 log 2, and log((log 2)/u)>(99 log 2) since log 2>1/2. For every |c-c_0|<a_-^2, apply (17) with a slightly smaller radius parameter than a_- that still contains c; this gives G(c)<u. Thus B(c_0,a_-^2) subset D_u. By (18), G(c_0+a_+^2)>=u, so the distance to C minus D_u is at most a_+^2. Schwarz and Koebe quarter give

    a_-^2 <= r_u(c_0) <= 4a_+^2.

For the stated u, log(4/u)<=2 log(1/u) and log((log 2)/u)>=log(1/u)/2. Substitute to obtain (14). The ratio of constants B/A is 102400, and (1) gives (15). All logarithms are natural.

For actual intervals F_epsilon=[1/4-epsilon,1/4], 0<epsilon<1/4, the entire interval lies in M: for c in [0,1/4], p=(1+sqrt(1-4c))/2 is a positive fixed point and f_c([-p,p])=[c,p] subset [-p,p]. The limit of e(F_epsilon) as epsilon tends to zero is exactly K(c_0,c_0), because all points of these continua approach c_0 and K is continuous. More quantitatively, apply (6) with R=a_-^2 for the smaller ground s and any epsilon<R; the resulting two-sided comparison is valid for each actual interval without presuming a limiting ground-independent equilibrium measure.

There is no conflict with Theorem 3: it is a worst-case statement over all parameter continua, whereas (15) is a localized diagonal statement at the actual neutral cusp. Nor does the cusp example establish any new local connectivity case or control a nearby infinitely satellite-renormalizable parameter's escape profile.

## 5. General physical escape-profile interface and H4 application

Let x in M. If for each sufficiently small u one independently certifies positive radii d_-(u)<=d_+(u) with B(x,d_-(u)) subset D_u and at least one point of C minus D_u at distance <=d_+(u), then

    d_-(u)<=r_u(x)<=4d_+(u).

In particular, for uniform constants b>=a>0 and a specified scale function R(u)>0, estimates a R(u)<=d_-(u)<=d_+(u)<=b R(u) imply

    |K(x,x)+L-log(R(t)/R(s))| <= log(4b/a).              (19)

At -2, R(u)=u^2; at 1/4, R(u)=1/[log(1/u)]^2. An analogous uniform estimate for every x in a known compact F would, by (2), provide a physical, geometry-sensitive upper penalty for the previous H4 net-gain criterion. For a fixed x, (6) gives a local comparison whenever the set is actually contained in the stated fraction of an interior ground disk; do not assume such containment from a symbolic address. In particular, demanding that localization for all scales at a boundary point can itself be tantamount to diameter shrinking, so this alone is not a noncircular proof of rigidity.

The exact diagonal characterization and two distinct physical regimes show why a universal scalar estimate without information about the chosen parameter compact can lose the relevant geometry. The repelling tip forces the coefficient two in the general bound, but the neutral cusp does not incur that scale of loss. Actual ground radii or a uniform escape-profile certificate on the target compacts are the inputs needed to exploit the improvement. The divergent gain schedule and connected relative-neighborhood requirement in the previous H4 route remain open.

## 6. Attribution and proof boundary

Classical inputs: Green energy, disk Green kernel, Dirichlet balayage, Cauchy–Schwarz for the Dirichlet energy, Harnack inequality, Schwarz lemma, Koebe quarter theorem, and the compact-space component/quasicomponent theorem. See E. B. Saff, *Logarithmic Potential Theory with Applications to Approximation Theory*, Surveys in Approximation Theory 5 (2010), 165–200, [PDF](https://pages.cs.wisc.edu/~deboor/sat/papers/14/14.pdf), §3, equations (3.8)–(3.17), printed pp.187–188 (both PDF page images independently reopened). The source supplies classical facts, not the claimed sharp coefficient. Quadratic parameter uniformization is inherited with precisely the normalization in the preceding two archive notes. See also their citations and credit Douady–Hubbard. No claim that these general Green kernel facts or the repelling-tip escape exponent are new in the wider literature.

**Status:** written analytic proof of a sharp variational reduction and exact optimal leading logarithmic coefficient in the physical parameter plane, with a contrasting double-logarithmic local loss at the genuine parabolic cusp. The new upper bound is independent of the earlier Fourier estimate, which remains useful for small relative level changes. The classical Koebe growth theorem is used in addition to the quarter theorem. The sharp coefficient uses the new upper and the actual tip lower bound. No new source bytes were hashed; Saff's page images were read, not a full literature novelty audit. No physical sequence of connected relative neighborhoods, divergent net-gain schedule, or parameter rigidity is asserted. H4, H1–H3, UPTCR and MLC remain open. AI assistance: ChatGPT GPT-6.2; no independent human specialist review or Lean verification.
