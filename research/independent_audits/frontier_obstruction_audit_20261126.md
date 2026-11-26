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
