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

For zeta=exp(i theta) !=1, X(zeta)=i x with x=cot(theta/2). Away from x=x0 and x=x0+/-C, the boundary value W=i C/(x-x0) lies on the imaginary axis. If |x-x0|<C, the boundary real part of F(W) is pi/2, so |u_ext*|=delta on the right semicircle. If |x-x0|>C, the boundary real part is zero, so u_ext* lies on the imaginary diameter and has modulus <delta (since the finite imaginary value of F(W)/2 is mapped by tan to i*tanh). At the three excluded points the choice of boundary convention is irrelevant. The exact change of variables is

    dm(zeta)/|1-zeta|^2 = |dx|/(4*pi).

Indeed dx/dtheta=-1/(2 sin^2(theta/2)) and |1-zeta|^2=4 sin^2(theta/2). Consequently the weighted measure of E_delta is exactly 2C/(4*pi)=2a/(pi delta). Equivalently b*=1 on that arc and zero elsewhere. Replacing delta in this construction by delta'>delta, with the same a, gives strict-threshold mass at least 2a/(pi delta'); letting delta' decrease to delta proves the same optimal supremum for >delta.

This extremizer can concentrate all the sharp weighted budget on the interval |x-x0|<C about an arbitrary boundary angle other than 1, and is not claimed to be a quadratic multiplier. It need not satisfy an additional finite PLY disk because its diameter boundary can have Re u=0 away from zero. Section 4 addresses that stronger scalar class.

**Sharp native consequence as an integral upper bound:** every genuine satellite component satisfying the interface of §1 has

    integral_{|tau*(zeta)-2*pi*i*p/q|>=delta}
             dm(zeta)/|1-zeta|^2 <= 2/(pi delta q^2).

The proof uses neither the physical absolute period k nor the recurrence q_(i+1)>=q_i^2. The estimate is exact in the unconstrained scalar class; optimality among genuine quadratic multiplier functions is unknown. This is not the whole-copy estimate needed by CS, and no ledger gate is promoted.
