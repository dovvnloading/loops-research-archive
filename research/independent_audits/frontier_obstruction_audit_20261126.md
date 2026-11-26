# Frontier obstruction audit — 2026-11-26

Status: working research note; no universal MLC gate is promoted by this document. Research assistance: OpenAI GPT-6.2. Human review pending.

## Method

Start from the current main-branch evidence, distinguish finite witnesses from source-defined analytic statements, and seek a proof or a falsifying example for the first nontrivial open implication. Record exact hypotheses, independently check algebra and limiting cases, and retain negative findings rather than silently weakening the target. All claims in this working note require independent mathematical review. The archive's existing source-locked ledger remains unchanged.

## 1. Target and dependency boundary

Target: the residual one-digit pure satellite address S(1/3) S(1/4) S(1/5) ... . Frozen main: 577f1b627cf690561522e52aa563d6a710298661. Relevant existing notes: [residual address](../frontier/residual_satellite_status_20261126/NOTE.md), [growth obstruction](../frontier/cs_growth_hypothesis_20261126/NOTE.md), [ordinary collar obstruction](../frontier/pl_yoccoz_radial_20261126/NOTE.md), [marked lattice obstruction](../frontier/lemma_t_near_parabolic_20261126/NOTE.md), and especially [attachment Julia inequality](../frontier/satellite_component_julia_bound_20261126/NOTE.md), §2 and §4. These are not treated as independent peer review. The latter supplies a useful native holomorphic interface but explicitly cannot bound the next attachment. We now prove quantitative boundary distribution control, rather than another interior estimate.

Let H be a genuine p/q satellite child (q>=2) of a quadratic hyperbolic component of period k. Parameterize H by its child multiplier lambda in the unit disk D. Let tau be the continued logarithm of the repelling parent multiplier with attachment value 2 pi i p/q, and put u=tau-2 pi i p/q. Use exactly the native hypotheses of the attachment Julia note. The imported multiplier-coordinate and local splitting results (Levin, *Multipliers of periodic orbits of quadratic polynomials and the parameter plane*, Israel J. Math. 170 (2009), 285–315, [arXiv:math/0702011](https://arxiv.org/abs/math/0702011), the note's source locators) give Re u>0 and u(t)/(1-t)->1/q^2 as real t->1. The local derivative can equivalently be deduced from the bounded contour index 1/(1-rho^q)+q/(1-lambda) at the parent point, as in that note. The result below is independent of PLY's absolute-period coefficient, and makes no identification with an independently straightened multiplier. Bibliographic metadata was reopened; source proof and PDF page/byte identity were not re-audited here. Everything below the stated analytic interface is proved directly.

## 2. The weighted boundary-exception theorem

**Proposed written analytic theorem (native application conditional only on the already stated genuine-component interface).** Let u:D -> {Re z>0} be holomorphic and suppose u(t)/(1-t)->a, where a>0 is real. Let m be normalized angular measure on the unit circle. For delta>0 set E_delta={zeta: |u*(zeta)|>=delta}, using radial limits in the extended plane wherever they exist. Then

    integral_{E_delta} dm(zeta)/|1-zeta|^2 <= a/delta.           (1)

In particular for the native satellite component a=1/q^2. If I_h={exp(i theta): |theta|<=h}, 0<h<=pi, then

    m(E_delta intersect I_h) <= (4 sin^2(h/2))/(delta q^2)
                            <= h^2/(delta q^2),               (2)
    m(E_delta intersect I_h)/m(I_h) <= pi h/(delta q^2).         (3)

**Proof.** Put v=u/(delta+u). This is holomorphic and lies in the disk with center 1/2 and radius 1/2 (the strict half-plane maps to that disk). Hence v has radial limits v* a.e. (Fatou's theorem for bounded holomorphic functions); u*=delta v*/(1-v*) exists in the extended plane at those same points, including infinity when v*=1. The real part of v is bounded, so the Poisson integral of Re v* is Re v; this follows also by dominated convergence on circles of radius r->1. For real t<1,

    Re v(t)/(1-t) = integral (1+t) Re v*(zeta)/|zeta-t|^2 dm.

The left side tends to a/delta. The integrands are nonnegative, so Fatou's lemma gives 2 integral Re v*/|1-zeta|^2 dm <= a/delta. For finite w=u*(zeta), Re w>=0 and

    2 Re(w/(delta+w))-1 = (|w|^2-delta^2)/|delta+w|^2.

This holds also in the limit w=infinity. Thus 2 Re v*>=1 on E_delta, yielding (1). On I_h, |1-zeta|<=2 sin(h/2)<=h. Since m(I_h)=h/pi, (2) and (3) follow. All integration is with normalized angular measure; the singular point 1 itself has measure zero. No claim about the value at a single angle follows from this argument. QED.

A stronger exact integral identity is available: |zeta-t|^2=(1-t)^2+t|zeta-1|^2, so for t>=1/2 the integrands above are at most 4 Re v*/|1-zeta|^2, which is integrable by the preceding Fatou argument. Dominated convergence therefore gives

    2 integral Re v*(zeta)/|1-zeta|^2 dm = a/delta.              (4)

This is a boundary budget, not simply an unweighted harmonic-measure bound.

**Consequence at the scale of the unresolved address.** Write r=q+1 for the next relative period. For any fixed A>2 pi and epsilon>0, take h=A/r<=pi and delta=epsilon/q. Then

    fraction of I_h with |u*|>=epsilon/q
        <= pi A/(epsilon q r) = O(q^-2).                     (5)

The same estimate holds for any measurable subarc of length comparable to 1/r in this window, with the corresponding length in the denominator. On the complement, the attachment log differs by less than epsilon/q from 2 pi i p/q. For p=1 and epsilon<pi, this implies the 45-degree cone for the normalized log: |Im(tau/(2 pi i))|<=epsilon/(2 pi q), Re(tau/(2 pi i))>=(1-epsilon/(2 pi))/q. The radial size is at most (1+epsilon/(2 pi))/q. This is a period-independent boundary estimate outside a quantitatively small set of angles of the actual component chart. It applies a.e. to radial boundary values, not to the full tuned limb and not automatically to the distinguished rational angle 2 pi/(q+1).

**What this genuinely adds.** The preceding archive note proves a sharp interior Julia disk and a single scalar obstruction to a boundary extension. (1)–(5) quantify the possible angular concentration of large displacement, including unbounded boundary values. They show precisely how thin the exceptional set must be near the root, even when the absolute period is enormous. They cannot certify the next rational attachment: a set of measure zero can contain every prescribed rational. The next section will test that limitation within the full scalar interface and isolate the missing native modulus of continuity. No MLC claim.

## 3. Sharp boundary budget, with a freely localized extremizer

The coefficient 1 in (1) is not optimal. In precisely the same holomorphic half-plane class the best universal coefficient is 2/pi:

    integral_{E_delta} dm(zeta)/|1-zeta|^2 <= 2a/(pi delta).     (6)

Here sharpness means for the non-strict threshold |u*|>=delta. The supremum is the same for the strict threshold >delta, as explained below.

**Proof.** For Re z>0 define the holomorphic function

    F(z)=(1/(2i))*Log((1+i z)/(1-i z)),

where Log has argument in (0,pi). The quotient has imaginary part 2 Re z/|1-i z|^2>0 and real part (1-|z|^2)/|1-i z|^2. Hence F is the arctangent branch analytic in the right half-plane and at zero, with F(z)=z+O(z^3) near zero. Its real part lies in (0,pi/2); in particular the bounded harmonic function

    B(z)=(4/pi) Re F(z)

is >=1 when |z|>=1, and is >=0 everywhere in the half-plane. Equivalently the unit semicircle maps to Re F=pi/4. At imaginary-axis boundary points other than +/-i, the one-sided boundary limits of B are 0 for |z|<1 and 2 for |z|>1; at infinity the limit is 2.

Let b(lambda)=B(u(lambda)/delta). This is bounded harmonic, nonnegative, and b(t)/(1-t)->4a/(pi delta). Its radial boundary function b* exists a.e. by the bounded harmonic Poisson representation. If u* is finite and |u*|>delta, or lies on the semicircle with Re u*>0, or is infinity, then b*>=1. The two endpoint values u*=+/-i delta require care: if v=u/(delta+u), each such value corresponds to a single value of the bounded holomorphic v on the unit circle. The boundary uniqueness theorem for bounded holomorphic functions (Privalov uniqueness; or Jensen's formula applied to v minus that constant) shows each of these level sets has measure zero unless v is constant. The derivative a>0 excludes the constant case. For completeness, if a bounded nonzero analytic function g has radial value zero on a set of positive measure, factor off any zero at the origin, rescale so |g|<=1, and Jensen's inequality gives integral -log|g(r zeta)| dm<=-log|g(0)| for all r<1. Fatou's lemma contradicts the infinite limit on that set. Thus no endpoint convention affects the integral. The Poisson identity, Fatou and the same dominated convergence argument as in (4) give

    integral b*(zeta)/|1-zeta|^2 dm = 2a/(pi delta).

Since b*>=1 a.e. on E_delta, (6) follows. QED.

The sharper versions of (2),(3),(5) are obtained by multiplication by 2/pi. In particular at h=A/r, delta=epsilon/q, the exceptional fraction in I_h is <=2A/(epsilon q r).

**Extremizer.** Set X(lambda)=(1+lambda)/(1-lambda), choose any real x0, and C=4a/delta. For Re X>0 put

    W(lambda)=C/(X(lambda)-i x0),
    u_ext(lambda)=delta*tan(F(W(lambda))/2).

The reciprocal sends the right half-plane into itself, and F maps it conformally onto 0<Re F<pi/2 (the displayed fractional-linear map takes the half-plane onto the upper half-plane, then the log maps to a horizontal strip and division by 2i gives the stated vertical strip). Division by 2 followed by tan maps that strip conformally onto the right half of the unit disk: tan is the inverse of F on 0<Re F<pi/2 and Re F<pi/4 is equivalent to |z|<1. Therefore u_ext is holomorphic with Re u_ext>0 and |u_ext|<delta. As lambda=t->1, X(t)=(1+t)/(1-t), W(t)/(1-t)->C/2, and u_ext(t)/(1-t)->delta*C/4=a.

For zeta=exp(i theta) !=1, X(zeta)=i x with x=cot(theta/2). Away from x=x0 and x=x0+/-C, the boundary value W=-i C/(x-x0) lies on the imaginary axis. If |x-x0|<C, the boundary real part of F(W) is pi/2, so |u_ext*|=delta on the right semicircle. If |x-x0|>C, the boundary real part is zero, so u_ext* lies on the imaginary diameter and has modulus <delta (since the finite imaginary value of F(W)/2 is mapped by tan to i*tanh). At the three excluded points the choice of boundary convention is irrelevant. The exact change of variables is

    dm(zeta)/|1-zeta|^2 = |dx|/(4*pi).

Indeed dx/dtheta=-1/(2 sin^2(theta/2)) and |1-zeta|^2=4 sin^2(theta/2). Consequently the weighted measure of E_delta is exactly 2C/(4*pi)=2a/(pi delta). Equivalently b*=1 on that arc and zero elsewhere. Replacing delta in this construction by delta'>delta, with the same a, gives strict-threshold mass at least 2a/(pi delta'); letting delta' decrease to delta proves the same optimal supremum for >delta.

This extremizer can concentrate all the sharp weighted budget on the interval |x-x0|<C about an arbitrary boundary angle other than 1, and is not claimed to be a quadratic multiplier. It need not satisfy an additional finite PLY disk because its diameter boundary can have Re u=0 away from zero. Section 4 addresses that stronger scalar class.

**Sharp native consequence as an integral upper bound:** every genuine satellite component satisfying the interface of §1 has

    integral_{|tau*(zeta)-2*pi*i*p/q|>=delta}
             dm(zeta)/|1-zeta|^2 <= 2/(pi delta q^2).

The proof uses neither the physical absolute period k nor the recurrence q_(i+1)>=q_i^2. The estimate is exact in the unconstrained scalar class; optimality among genuine quadratic multiplier functions is unknown. This is not the whole-copy estimate needed by CS, and no ledger gate is promoted.

## 4. Simultaneous, compact-invisible boundary spikes even with the PLY disk

The prior archive counterexample concerns one boundary target. The following stronger obstruction preserves a finite tangent disk, the attachment derivative, **strict boundary half-plane positivity away from the root**, holomorphic extension through the whole circle, and arbitrary compact-open proximity to a benign fixed reference function, while putting large displacement at ANY finite collection of prescribed boundary angles. Thus a finite grid of rational attachments cannot be certified by improving only the scalar interior data and adding qualitative analyticity at the boundary.

**Proposed theorem (scalar obstruction, not a family of quadratic polynomials).** Fix a>0, R>0, finitely many distinct zeta_j on the unit circle different from 1. There are rational holomorphic functions u_eta on a neighborhood of the closed disk, with
- u_eta(1)=0, u_eta'(1)=-a;
- |u_eta-R|<R on the closed disk minus {1} (in particular Re u_eta>0 there);
- u_eta -> u_0 compact-open in D, where u_0(lambda)=1/[d+A X(lambda)], d=1/(2R), A=1/(2a), X=(1+lambda)/(1-lambda);
- u_eta(zeta_j) -> 2R simultaneously for every j.

The limiting u_0 is the benign unshifted rational function with the same derivative and disk. At the next root of rotation 1/r, |u_0| <= 1/(A |cot(pi/r)|) for r>2. At a=1/q^2 and r=q+1 this is O(q^-3), whereas each approximating rational function can be arbitrarily close to the tangent-disk diameter 2R at that same root. The approximation is on any fixed compact subdisk, not uniformly on the closed disk, and not exact interpolation at arbitrary interior points.

**Proof.** Write x_j=cot(theta_j/2), so X(zeta_j)=i x_j. First take only the nonzero x_j; if the list is empty, u_0 suffices. Let s_j=sign(x_j), and for a small positive epsilon choose y_j=x_j-s_j epsilon and eta=epsilon^2. Seek

    H_e(X)=d+A X+sum_l epsilon v_l/(X+eta-i y_l),
    u_e(lambda)=1/H_e(X(lambda)).

At each nonzero target, the imaginary part of H_e(i x_j) vanishes exactly if

    sum_l M_jl(epsilon) v_l=A x_j,
    M_jl(epsilon)=epsilon*(x_j-y_l)/(eta^2+(x_j-y_l)^2).

The diagonal is s_j/(1+epsilon^2), and every off-diagonal tends to zero because x_j are distinct. Thus M tends to the invertible diagonal matrix diag(s_j). For sufficiently small epsilon it is invertible and its unique real solution satisfies v_j -> A |x_j|>0. This also proves all v_j are strictly positive eventually, with no numerical inversion assumption.

For Re X>=0 and finite X,

    Re H_e(X)=d+A Re X+
        sum_l epsilon v_l*(Re X+eta)/|X+eta-i y_l|^2>d.

There are no finite poles of H_e on that closed half-plane. Therefore its reciprocal is holomorphic there and |u_e-R|<R is equivalent to Re H_e>d. The Möbius coordinate X has a simple pole at lambda=1, at which H_e=A X+d+O(1/X). Hence u_e extends across 1 with u_e(1)=0 and u_e'(1)=-1/(2A)=-a. It is a rational function and has no poles anywhere on the closed disk, so it is holomorphic on a neighborhood of the closed disk (the radius of that neighborhood is not asserted uniform).

For compact subsets of D, Re X is bounded below by a positive number; all the added terms tend uniformly to zero. This proves the compact-open limit. At nonzero target j, Im H_e=0 by construction. Its real part is

    d + sum_l epsilon v_l eta/(eta^2+(x_j-y_l)^2).

The l=j term equals epsilon v_j/(1+epsilon^2); all others tend to zero. Thus H_e(i x_j)->d and u_e(zeta_j)->2R. If x_j=0, not included in the linear system, every denominator at X=0 stays bounded away from zero for sufficiently small epsilon (all nonzero x_l are fixed), and H_e(0)->d as well. This proves simultaneous convergence at every target, including -1 if specified. QED.

In particular all approximants obey the attachment Julia inequality: this follows from Schwarz–Pick and the derivative, or directly from Re H_e(X)>=A Re X, which gives |u_e|^2 <= (1/A)*(|1-lambda|^2/(1-|lambda|^2))*Re u_e. The finite tangent disk can be the actual PLY disk expressed in the tau-displacement variable (radius R=k log 2/q). No restriction from that disk or from the exact root derivative prevents the described concentration. These are rational functions of the scalar chart, not actual quadratic multiplier functions; their algebraicity alone does not supply the polynomial dynamical relations. The strict inequalities also show that the counterexample does not rely on a second neutral parent multiplier at a nonroot boundary point.

### Sharp order with the additional disk

For a single prescribed angle with coordinate x0, the simpler model u=1/[d+A(X-i x0)] is strictly in the disk for interior lambda and extends analytically through the entire circle (nonroot boundary values are on the tangent circle; choosing d slightly larger than 1/(2R) makes all those values strictly inside the disk). Its exact threshold event at 0<delta<1/d is

    |x-x0| <= sqrt(delta^(-2)-d^2)/A,

so its weighted angular mass is

    (a/pi)*sqrt(delta^(-2)-d^2).

For example d=1/R and delta<=R/2, this is >=sqrt(3)*a/(2*pi*delta), with strict disk inclusion even at the boundary. This has the same a/delta order as the optimal bound (6). When a=1/q^2, delta=epsilon/q, x0=cot(pi/r), r=q+1, and R>=2delta, the interval has x-length comparable to 1/q. In that interval dx/dtheta=-(1+x^2)/2 has magnitude comparable to r^2 for large r. Therefore its angular length is comparable to 1/(q*r^2), and its fraction of a window of angular length comparable to 1/r is comparable to 1/(q*r). The order in (5) cannot be improved in this scalar disk class, even for an exceptional interval centered at the specific next rational attachment. Constants depend on epsilon, not the absolute parent period. The coefficient 2/pi itself was proved optimal only for the full half-plane class, not for a fixed finite tangent disk.

## 5. Pointwise rescue criterion: a repelling continuation disk at scale q^-3

The previous sections distinguish measure control from the actual rational target. Here is a quantitative analytic criterion that *does* yield the missing pointwise estimate without any ordinary PL collar or bound on the magnitude of u on the exterior patch.

**Theorem.** Keep the half-plane interface of §2 and fix zeta on the unit circle other than 1. Assume u extends holomorphically to B(zeta,s) with Re u>0 throughout that open disk, agreeing with the interior u on the overlap; 0<s<=1. Write D0=|1-zeta|. Then

    |u(zeta)| <= 2a s + 8a D0^2/s.                             (7)

Moreover for all w in B(zeta,s/2),

    |u(w)| <= 6a s + 24a D0^2/s.                              (8)

No assumption of univalence of u is needed.

**Proof.** The standard Julia inequality on D for a half-plane map with boundary slope a is

    |u(lambda)|^2 <= 2a*T(lambda)*Re u(lambda),
    T(lambda)=|1-lambda|^2/(1-|lambda|^2).

For clarity this follows by applying the disk-to-half-plane Schwarz–Pick inequality at lambda and real t, subtracting its squared form from 1, dividing by 1-t, and taking t->1 using u(t)/(1-t)->a. Thus |u(lambda)|<=2a T(lambda). Choose lambda_0=(1-s/2)zeta. In B(zeta,s) its disk distance from the center is pseudohyperbolically 1/2. Half-plane Schwarz–Pick gives

    |u(zeta)-u(lambda_0)| <= (1/2)|u(zeta)+conj(u(lambda_0))|.

The triangle inequalities imply |u(zeta)|<=3|u(lambda_0)|. Likewise |u(w)|<=3|u(zeta)| for w in B(zeta,s/2). Since

    T(lambda_0) = [(s/2)^2+(1-s/2)D0^2]/[s-s^2/4]
                <= s/3 + 4D0^2/(3s),

(7) and (8) follow. QED.

**Native criterion on the linear satellite address.** For the genuine child H, let zeta_r=exp(2*pi*i/r), r=q+1, be the next root in H's child multiplier coordinate. Suppose the inverse child multiplier chart and the same parent cycle have a common holomorphic continuation on B(zeta_r,s_q), remaining repelling there. Then the attachment-normalized log extends to this simply connected disk, agreeing with u on the overlap, since the multiplier is nonzero there. The hypothesis is a *repelling multiplier-coordinate neighborhood*, not just analytic continuation of the inverse child parameter chart, and it does not require that the extended points lie in the Mandelbrot set. The native branch identification must be retained.

With a=1/q^2 and D0<=2*pi/r, (7) gives

    q |u(zeta_r)| <= 2s_q/q + 32*pi^2/(q*r^2*s_q).             (9)

Thus if q*r^2*s_q -> infinity, the scaled log q*tau/(2*pi*i) -> 1 for p=1 along these next attachment roots. If s_q>=C/(q*r^2) for a sufficiently large absolute C, (9) also supplies a prescribed fixed cone/radial budget for sufficiently large q. For instance, with C=128*pi^2 and q>=8, q|u|<=1/4+1/4=1/2, which is stronger than needed for the 45-degree cone. This is an eventual scale requirement; for finite small q where the hypothesized lower bound exceeds 1 no such disk is asserted. The critical order of the needed radius is q^-3 for r=q+1. It is independent of absolute period k. In contrast, a qualitative statement that a continuation disk exists for each individual q gives no lower bound of this order.

For a proposed all-copy version, (8) would give the same order of bound at every parameter in a target copy *if* a single inverse native multiplier chart were verified to cover that copy with coordinates in B(zeta_r,s_q/2), and with the same repelling parent branch on the larger disk. This is an additional independent geometric containment and identification hypothesis. No such containment, quantitative native disk, uniform NP entry, or whole-copy estimate is proved here. A sequence of good roots alone is not a singleton intersection argument.

### Scalar scale optimality, including strict boundary positivity

The q^-3 order is not merely an artifact of the two Schwarz–Pick constants. For arbitrary a, delta>0 and zeta!=1 let X(zeta)=i x0, A=1/(2a), d=1/delta and u=1/[d+A(X-i x0)]. Then u(zeta)=delta, u has boundary slope -a at 1 and is holomorphic on the closed disk; it is strictly in the tangent disk of any radius R>delta/2 away from 1. The maximal radius of a repelling half-plane extension is at least

    s0=min(1,D0/2,d*D0^2/(24*A)).

Indeed for |lambda-zeta|<s0, |1-lambda|>=D0/2, |lambda|<=1+s0 and hence Re X> -12s0/D0^2. This gives Re(d+A(X-i x0))>=d/2>0, so the displayed reciprocal is holomorphic with positive real part on the patch. Conversely, for any such extension with s<=1, (7) implies, when delta>2a,

    s <= 8a D0^2/(delta-2a).

Therefore at delta=epsilon/q, a=1/q^2, r=q+1, zeta=zeta_r, these lower and upper bounds are both of order 1/(q*r^2) for large q (use D0=2 sin(pi/r) comparable to 1/r). In the scalar class a nonvanishing scaled displacement q|u|=epsilon is compatible with an extension radius of precisely that order. A bound on a much larger scale forces it to disappear; an arbitrary microscopic analytic neighborhood does not. This does not prove that physical multipliers can realize the extremal scale.

### Independent derivative diagnostic in the boundary coordinate

For an alternative measurable-to-pointwise route set U(x)=u*(zeta(x)), x=cot(theta/2). By (6),

    Lebesgue measure {x: |U(x)|>=delta} <= 8a/delta.           (10)

This is exact because dm/|1-zeta|^2=|dx|/(4*pi). If U is L-Lipschitz on [x0-l,x0+l] and |U(x0)|>=delta, then |U(x)|>=delta/2 whenever |x-x0|<=min(l,delta/(2L)); for L=0 take delta/(2L)=infinity. At threshold delta/2, (10) gives

    min(l,delta/(2L)) <= 8a/delta.                             (11)

In particular l>8a/delta forces L>=delta^2/(16a). At the linear satellite scale delta=epsilon/q this forces L>=epsilon^2/16 on a window of x-radius greater than 8/(epsilon q). On such windows centered at x0=cot(pi/r), the change of angular coordinate has derivative magnitude (1+x^2)/2 comparable to r^2. Uniformly vanishing Lipschitz constants in x on these windows (with sufficiently large radius) would rule out the bad root; a bound on angular derivatives of order o(r^2) suffices. This is a diagnostic, not a proof of such derivative bounds on actual multipliers.

**Research status after §5.** The specific missing native estimate is now localized to a positive-real-part continuation patch on the next child multiplier circle (or an equivalent pointwise mechanism). The weighted sharp theorem is proved on the stated analytic interface and extends the archived interior Julia estimate. The compact-invisible counterexamples prove a limitation of scalar methods, not a counterexample to any genuine satellite rigidity theorem. The continuation threshold is sharp in order within that scalar class. The actual native continuation radius, whole-copy transport and parameter rigidity remain OPEN. No changes to H1–H4, UPTCR, or the source-locked ledger.

## 6. Combining the PLY disk with the Julia derivative: exact lens budget and parabolic index

The previous bounds treated the half-plane condition and the finite tangent disk separately. They can be combined without loss. The following claims about a native multiplier require the PLY disk for the **same attachment-continued logarithm**, not just for some integer-shifted lift. Use the branch-identification hypothesis of the source-defined PLY audit. Let |u-R|<=R on D with finite R>0, set d=1/(2R), A=1/(2a), and retain u(t)/(1-t)->a. Since u is nonconstant, the disk containment is strict in D.

### 6.1 Exact combined interior locus

Define v=u/(1-d*u), so Re(1/v)=Re(1/u)-d>0. It follows that Re v>0 and v(t)/(1-t)->a. Apply the Julia inequality to v and divide by |v|^2:

    Re(1/u) >= d+A Re X,    X=(1+lambda)/(1-lambda).          (12)

This is a sum, not the maximum of the two separate lower bounds. With T=1/Re X, it is equivalent to a tangent disk for u with center and radius

    R_eff(lambda) = 1/(1/R + 1/(a*T(lambda))).                (13)

The locus is exact for this scalar class: at each fixed lambda the entire closed disk except 0 is attained by u=1/(A X+C), where C ranges over complex constants with Re C>=d. The disk condition, attachment derivative and half-plane positivity hold on D for each such u; varying C fills all reciprocals with Re(1/u)>=d+A Re X(lambda). The point 0 is only a limiting value at a fixed interior lambda. This is not a characterization of genuine quadratic multipliers.

### 6.2 Optimal weighted boundary budget with a fixed finite tangent disk

For 0<delta<2R put

    h=d*delta in (0,1),
    L=delta/sqrt(1-h^2),
    t0=pi/4 + arcsin(h)/2.

Then the sharp weighted estimate in the scalar class is

    integral_{|u*|>=delta} dm(zeta)/|1-zeta|^2
        <= a/(2 L t0)
         = 2a*sqrt(1-h^2)/[delta*(pi+2 arcsin(h))].           (14)

The bound is strictly smaller than (6) when h>0. For delta>2R the set is empty a.e.; for delta=2R it has measure zero by boundary uniqueness (u is nonconstant, and the only point of the tangent disk of that modulus is 2R).

**Proof.** Use the same v as in §6.1 and F from §3. For finite v with Re v>0, u=v/(1+d*v), and

    |u|>=delta
    iff (1-h^2)|v|^2 - 2d delta^2 Re v - delta^2 >= 0
    iff |v/L|^2 - 1 >= 2 Re(v/L)*h/sqrt(1-h^2)
    iff Re F(v/L) >= t0.

For the last equivalence, the argument of (1+i w)/(1-i w) for Re w>0 has cotangent (1-|w|^2)/(2 Re w). Cotangent is strictly decreasing on (0,pi), and cot(2t0)=-h/sqrt(1-h^2). Thus b(lambda)=Re F(v(lambda)/L)/t0 is bounded harmonic, nonnegative, and at least one where |u|>=delta. At boundary values the same inequality for b* holds except possibly v=+/-i L, corresponding to two distinct values of the bounded analytic u; these have null boundary level sets by the uniqueness argument in §3. The case v=infinity gives b*=(pi/2)/t0>1. Along the attachment radius b(t)/(1-t)->a/(L*t0). The Poisson integral and nonnegative Fatou/dominated convergence arguments of §§2–3 yield the exact integral a/(2 L t0) of b*, proving (14).

For sharpness put kappa=2t0/pi, C=2a/(L*kappa), X as above, and choose any real x0. Define

    W=C/(X-i x0),
    v_ext=L*tan(kappa*F(W)),
    u_ext=v_ext/(1+d*v_ext).

Here 0<kappa<1, and the same strip parametrization as in §3 shows Re v_ext>0, Re F(v_ext/L)<t0, and hence |u_ext|<delta in D. Its radial attachment slope is a because v_ext(t)/(1-t)->L*kappa*C/2=a. On the arc |x-x0|<C in x=cot(theta/2), Re F(W*)=pi/2, so Re F(v_ext*/L)=t0 and |u_ext*|=delta. On its complement the boundary real part of F(W*) is zero; v_ext* is purely imaginary with modulus strictly below L, hence |u_ext*|<delta. Isolated endpoints are immaterial. The weighted arc mass is 2C/(4*pi)=a/(2 L t0). All scalar conditions hold. This gives equality for the >= threshold. For the strict > threshold use the same construction with delta' decreasing to delta from above (still delta'<2R). As in §3, the extremizer is not asserted to be native and need not extend holomorphically through the entire circle. QED.

### 6.3 Exact parabolic index identity and a two-jet obstruction

In the genuine satellite setting of §1, the root is a parameter c_* where the parent fixed point of the k-return splits into one parent point and q nearby child points for the kq-return. The imported local multiplicity statement is q+1. On the genuine component the inverse chart and parent multiplier are locally holomorphic at lambda=1, by the local satellite derivative and inverse coordinate statement in the predecessor audit. Write s=1-lambda and

    u = s/q^2 + b*s^2 + O(s^3).

Let I be the holomorphic fixed-point index of f_(c_*)^(kq) at that root point, i.e. the residue of dz/(z-f_(c_*)^(kq)(z)). Equivalently it is the small-contour integral divided by 2 pi i. The contour encloses exactly the q+1 points above for nearby parameters. Thus

    I = lim_{lambda->1} [1/(1-exp(q*u)) + q/(1-lambda)]
      = 1/2+q^3*b,

using 1/(1-exp z)=-1/z+1/2+O(z). Define the iterative residue Resit=(q+1)/2-I (this is the standard index normalization at multiplicity q+1). Then the reciprocal residual

    G=1/u - (q^2/2)*X

has a removable singularity at 1 and satisfies the exact identity

    G(1)=q^2/2-q^4*b=q*Resit.                                (15)

In particular (12) gives Re G>=d throughout D, including at 1 by continuity; under the same-lift PLY radius R=k log(2)/q this yields Re Resit>=1/(2*k*log(2)). This is an elementary consequence of the imported local satellite index and same-lift disk; no literature priority, new parabolic-index theorem in dynamics, or uniform lower bound independent of k is claimed.

The spike family of §4 has

    G_e(X)=d+sum_l epsilon*v_l/(X+epsilon^2-i*y_l),

and all added terms vanish at X=infinity. Consequently every spike and its compact-open limit has *exactly the same* u'(1) and u''(1), hence exactly the same formal value of the index expression (15). More generally one may start with a complex constant D1 with Re D1>d, replace d in H_e by D1, choose s_j=sign(A x_j+Im D1), and solve M v=A x_j+Im D1 for targets with nonzero right side (omit the zero targets, where the terms vanish in the limit). The same proof gives G_e(1)=D1 and u_e(zeta_j)->1/Re D1 simultaneously, preserving a strict margin in the PLY disk and any chosen such formal second-order datum. This shows why even knowing the local parabolic index, with no further analytic control, does not generally prevent scalar boundary spikes. For genuine dynamics the index and the entire function G are of course not freely assignable; neither the spike model nor (15) asserts otherwise.

The combination (12)–(15) strengthens the analytic interface and pinpoints how a genuine dynamical estimate on the reciprocal residual might constrain it. The remaining quantitative continuation hypothesis from §5 is not thereby proved.

## 7. Reproduction, hostile proof review, and remaining task

Run from repository root:

    python -B code/verify_frontier_obstruction_20261126.py

Local run with Python 3.13.5, standard library only, deterministic rational arithmetic:

    30 simultaneous spike targets; 240 lens equivalences; 48 continuation inequalities; exact rational checks passed

The tested file's Git blob is a21f8438dcd18c7642c1d621f8e0ca03af4024cb (confirmed against the branch's fetched blob), SHA256 f887c6ae76739c27781351b61349332e5ec5e7234a707c3f054c3b24d62169b9. The verifier uses rational x-coordinates, not a computation of rational external or internal ray angles or genuine multiplier values. It checks exact positive solutions of the spike interpolation systems, their target and compact-interior values, the combined disk, the two-jet algebra, the threshold-circle equivalences and the continuation arithmetic. The continuum proofs, Fatou/Poisson boundary reasoning, sharp extremizers, limiting quantifiers, and dynamical identifications are mathematical arguments in this note, not Python certificates. A separate read-only [CI workflow](../../.github/workflows/frontier-obstruction-audit-20261126.yml) runs the same arithmetic. No full archive test or Lean formalization is claimed. The executable is a standalone code-directory diagnostic, not a new physical bridge certificate or an amendment to the source-indexed proof register.

Adversarial checks retained:

| Possible false inference | Resolution |
|---|---|
| Poisson limit at the singular attachment could hide a boundary atom | Use bounded harmonic test functions and Fatou, then domination via the exact distance identity; the finite budget is established before dominated convergence. |
| Threshold equality or singular imaginary endpoints could invalidate the sharp constant | Boundary uniqueness removes the two ambiguous endpoint levels; the explicit lens extremizer attains equality on a nontrivial arc. Strict thresholds have the same supremum by a limiting construction. |
| Sharp half-plane result might contradict a finite PLY disk | The exact finite-disk bound is (14), with a different lens extremizer; all scalar estimates on the native disk require the same log lift. |
| Compact-open convergence plus holomorphic extension might imply boundary control | Section 4 is an explicit counterexample with positive real part even on the nonroot boundary, and §6.3 preserves the formal second-order datum exactly. |
| The rational chart value at the next root might be a straightened multiplier or a point of the next whole copy | The theorem is about the native parent branch in the genuine child chart. Pointwise continuation is conditional; covering a whole tuned copy requires a separate chart-containment proof. |
| A good sequence of attachment roots implies MLC | No: no shrinking diameters, rigidity, all-copy domain entrance or singleton parameter fiber is obtained. |
| The size of the exceptional set should bound how many specified rational roots fail | No: a finite set has zero angular measure; §4 places spikes at any finite collection of targets. |
| Literature novelty follows from novelty relative to the archived note | No: the half-plane tools are classical, and no exhaustive literature-priority or independent human referee claim is made. |

**Strongest surviving open task.** Let r=q+1 and define s_q to be the supremum of radii at most 1 on which the genuine continued child multiplier chart and the attachment-continued parent cycle yield a holomorphic positive-real-part displacement function about exp(2 pi i/r), compatible with the interior chart. Prove a lower bound s_q >= C/(q*r^2) with sufficient C, or preferably q*r^2*s_q -> infinity, uniformly across the required native sequence. For a whole-copy statement also establish chart containment in the half-radius patch (or another genuine parameter transport with the same quantitative implication). The first estimate would imply the next-root cone/radial budget via (9); the second would give scaled convergence at the next roots. A proof of either native condition is not present here; neither follows from qualitative analytic continuation, the full PLY disk, the root derivative, or the local index alone. The proposed scale is sharp in the scalar class, not proved necessary for actual quadratic dynamics or for alternative routes. It is a sufficient research target, not a redefinition of CS's hypotheses.

Final scope: proposed written analytic results (§§2–3, 6.1–6.2) on the declared native multiplier-coordinate interface, scalar counterexamples (§4 and §6.3), conditional pointwise criterion (§5), elementary native index identity conditional on the local splitting/analytic input (§6.3), exact finite regression only. The relevant front is the residual unbounded satellite address, not a newly closed H1–H4 or UPTCR gate. The literature statements and archive base were scoped to this front; an exhaustive archive and primary-source proof audit was not performed. AI-assisted proof search, derivation, adversarial self-review and coding: OpenAI GPT-6.2. Human specialist review pending. Main, ledger, and all previously assigned theorem statuses remain unchanged.
