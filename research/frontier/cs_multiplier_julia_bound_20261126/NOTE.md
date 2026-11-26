# Attachment-normalized satellite multiplier bounds via the Julia inequality

**Date:** 2026-11-26. **Base main:** f72b326d938360428952c848053bf3ec7c94ec71. **Result:** written analytic theorem on actual satellite hyperbolic components, plus a weighted boundary-exception theorem and a sharp scalar obstruction to a pointwise whole-boundary inference. Pending mathematical review; no ledger promotion. This is a continuation of the residual satellite address S(1/3) S(1/4) S(1/5)..., the [CS radial obstruction](../cs_growth_hypothesis_20261126/NOTE.md), [angular audit](../cs_prop_6_10_angular_20261126/NOTE.md), [PL radial audit](../pl_yoccoz_radial_20261126/NOTE.md), and [q=3,...,9 numerical extension](../cs_multiplier_locus_extended_20261126/NOTE.md). Unlike extending the finite sample census, the estimate below holds for all actual satellite child hyperbolic components, with no growth hypothesis or dependence on absolute parent period.

**Scope:** the parent orbit is the actual dividing orbit continued from the root of a specified satellite child; not an arbitrary period-n root of a polynomial equation, not the attracting child orbit, and not a hybrid-straightened multiplier. The logarithm is normalized by continuation from the attachment, not by a principal-log selection at isolated samples. We do not certify the archived numerical seeds' wake membership, nor identify the continued log with every allowed integer translate of the PLY log on an arbitrary PL tower. This is not an estimate on the full tuned copy, on the prescribed point of attachment to the next satellite child, or on an infinite satellite intersection.

## 1. Analytic setting and exact normalization

Let W be an actual quadratic hyperbolic component of exact period n, t=p/q in (-1/2,1/2] a nonzero reduced rational (q>=2), W_t its satellite child of exact period nq, and c_* their common attachment. Let w be the attracting multiplier of W_t and c(w) its inverse chart on the unit disk D. By the Douady–Hubbard–Sullivan multiplier theorem, c extends homeomorphically to the closed disk and c(1)=c_*.

Let rho(c) be the multiplier of the parent n-cycle continued from W. On the child wake this cycle is repelling and is the marked dividing cycle: the two parameter-ray angles of c_* land together on the continuation of this actual parent orbit. Use Levin, arXiv:math/0702011v1, §4.2 Prop. 1 (printed p.10), §6.1 (p.16). The child closure except c_* lies in the child wake (the wake boundary parameter rays lie outside M except their common landing point). The parent cycle is analytic near c_* because its multiplier rho_*=exp(2*pi*i*t) is not 1. Thus rho(c(w)) has modulus >1 on the open disk and at every nonroot boundary point. It is nonzero throughout. Its holomorphic log tau(w) on the disk is uniquely fixed by tau(1)=2*pi*i*t, via the local root germ. It extends continuously to the closed disk: the nonroot boundary lies in the simply connected child wake, where the nonvanishing parent multiplier has a log, and the root germ gives the continuation near w=1. Define

    h(w) = tau(w) - 2*pi*i*t,       z(w) = tau(w)/(2*pi*i).

Then Re h>0 on D, Re h>0 on the nonroot circle, and h(1)=0. In particular there is no ambiguity from a change of log by 2*pi*i on D.

The exact satellite bifurcation derivative is

    d w/d rho at rho_* = -q^2/rho_*,
    h'(1) = -1/q^2.                                      (1)

See Levin §6.1 Lemma 6.2, equations (29)–(31), and displayed derivative preceding Lemma 6.4 (printed pp.17–18,20). Only the local bifurcation result is used, not the later n-deep continuation or growth hypotheses. For clarity, the local computation: in the centered parent return coordinate x, with delta=rho-rho_*, the q-fold return minus x equals

    (rho^q-1)x + A x^(q+1) + O(delta*x^2) + O(x^(q+2)),  A != 0.

The nonzero q-cycle points approach zero and satisfy A x^q=-(rho^q-1)+o(delta): divide the fixed point equation by x, absorb O(x^(q+1)), and use rho^q-1=O(delta) to get x^q=O(delta). Differentiating in x gives w-1=-q(rho^q-1)+o(delta)=-q^2 delta/rho_*+o(delta). The child cycle multiplier is holomorphic in rho near the bifurcation (the q Puiseux branches are cyclically permuted and have the same multiplier). The inverse function theorem and the root identification give (1) for the child multiplier chart. Thus h extends holomorphically near 1 even though global chart analyticity on the entire boundary is not needed.

## 2. Uniform horodisk theorem

**Theorem A.** For every w in D, put A(w)=|1-w|^2/(1-|w|^2) and B(w)=2 A(w)/q^2. Then

    |h(w)|^2 <= B(w) Re h(w),                            (2)
    |h(w)-B(w)/2| <= B(w)/2,
    |z(w)-t| <= A(w)/(pi q^2).

This is an actual analytic estimate, independent of n. In particular, uniformly over |w|<=r<1,

    |z(w)-t| <= (1+r)/(pi q^2(1-r)).                    (3)

**Proof.** The Cayley transform F=(1-h)/(1+h) is a holomorphic disk self-map, F(1)=1, F'(1)=2/q^2. Schwarz–Pick between w and the real point s in (0,1), in its identity

    |1-conj(F(s))*F(w)|^2 / ((1-|F(w)|^2)(1-|F(s)|^2))
        <= |1-s*w|^2 / ((1-|w|^2)(1-s^2)),

followed by s tending to 1 gives Julia's inequality with coefficient 2/q^2. Since |1-F|^2/(1-|F|^2)=|h|^2/Re h, this is (2). Completing the square yields the disk. Divide by 2*pi; finally A(w)<=(1+r)/(1-r). No numerical or a priori modulus input. QED.

**Stronger centered disk.** For t=1/q, set d=A(w)/(2*pi*q). Then q z belongs to the disk with center 1-i*d and radius d. Therefore

    sqrt(1+d^2)-d <= q|z| <= sqrt(1+d^2)+d.              (4)

At the child center, d=1/(2*pi*q); in particular for every q>=3 the archive's preregistered [0.9,1.2] center prediction follows from (4), for the actual root-normalized orbit. This does not assert a proof of the previously sampled identifications. A sufficient condition for the same norm interval at every point of a chart region is

    d <= min((1-0.9^2)/(2*0.9),(1.2^2-1)/(2*1.2))
      = 19/180.

The condition also implies the sector Re z >= |Im z|: the minimum of Re(qz)+Im(qz) in the disk is 1-(1+sqrt(2))*d>0, and Im(qz)<=0. The norm interval and sector consequently hold simultaneously on the full horodisk A(w)<=(19*pi/90)q. This is the disk tangent to 1 with center 1/(1+C), radius C/(1+C), where C=(19*pi/90)q, intersected with D. The rational sufficient smaller region A(w)<=19q/30 uses pi>3; it contains the centered chart subdisk

    |w| <= (19q-30)/(19q+30).

For each fixed r<1, q z -> 1 uniformly on |w|<=r as q grows. More generally for r_q tending to one with q(1-r_q) tending to infinity, the same conclusion follows. The bound concerns the original parent dividing log, not the NP zero-fixed-point rotation without the required CS identification.

### Optional strengthening when the PLY lift is aligned

CS arXiv:1509.07843v1, printed p.52 (31)–(32) uses the original period n and marked rotation t. If its PLY disk holds for this same continued lift at every point of D, then

    |h|^2 <= (2*n*log(2)/q) Re h,
    Re(1/h) >= a_0=q/(2*n*log(2)).

For G=1/h-a_0 we have Re G>=0, strictly >0 by the minimum principle since G has a pole at 1. The function 1/G is half-plane-valued and has the same simple zero and derivative as h at 1. Applying (2) to 1/G gives

    Re(1/h) >= a_0 + (q^2/2)*(1-|w|^2)/|1-w|^2,
    |h|^2 <= Re h / (a_0 + (q^2/2)/A(w)).              (5)

Thus the two tangent-disk bounds combine additively in reciprocal coordinates, not merely by taking their minimum. This is a conditional strengthening only: the proof does not choose the PLY branch on the full chart from (32)'s existential wording, and (2)–(4) and Theorem B below do not depend on that strengthening.

## 3. Weighted boundary-exception theorem

The bound (2) is not a bound at nonroot points on |w|=1. But the exact attachment derivative controls the measure of exceptions there without requiring boundary derivatives elsewhere.

**Theorem B.** For any T>0 let E_T={e^(i theta): |h(e^(i theta))|>=T}. Let dm=d theta/(2*pi) be normalized arc measure. Then

    integral_{E_T} dm / |1-e^(i theta)|^2 <= 1/(q^2*T).  (6)

Consequently m(E_T)<=4/(q^2*T). For any s>0,

    m(E_T intersect {|1-w|<=s}) <= s^2/(q^2*T).          (7)

**Proof.** Set u(w)=Re[h(w)/(T+h(w))]. This is positive bounded harmonic on D, continuous on its closure, with u(1)=0. Indeed 0<=u<=1 by Re h>=0. Where |h|>=T,
    
    u = (T Re h+|h|^2)/|T+h|^2 >= 1/2,

because twice the numerator minus the denominator equals |h|^2-T^2. By (1), u(r)/(1-r) -> 1/(q^2*T) as real r tends to 1 from below. By the Poisson formula,

    u(r)/(1-r) = integral (1+r)*u(e^(i theta))/|e^(i theta)-r|^2 dm.

The integrand is nonnegative. Fatou's lemma gives 2 integral u(e^(i theta))/|1-e^(i theta)|^2 dm <= 1/(q^2*T). Restriction to E_T gives (6), and |1-w|<=2 or <=s gives the two measure bounds. The endpoint 1 is not in E_T. QED.

**Consequence for the residual sequence.** Taking t=1/q and T=2*pi*delta/q, the set where |qz-1|>=delta has normalized measure at most 2/(pi*delta*q) on the whole boundary. On the small arc |theta|<=2*pi/(q+1), its normalized measure is at most

    2*pi / (delta*q*(q+1)^2).                            (8)

Thus near the next prescribed internal angle the exceptional arc measure is O(q^-3), at fixed delta>0. This is a uniform measure estimate for actual charts, including the nonroot boundary, without an assumed uniform fundamental-annulus modulus. It does not tell whether the **specified** rational angle 1/(q+1) belongs to that exceptional set. A possible next theorem must rule out narrow exceptional peaks at that exact angle (and then control the descendant limb). E.g. a uniform Lipschitz bound of o(q^3) on qz along a comparable neighborhood of that angle would exclude a fixed-size excursion by (8) applied with half the excursion size and an enlarged constant arc; no such boundary derivative estimate is proved here. The measure is multiplier-coordinate arc measure, not parameter-plane length, harmonic measure of the entire Mandelbrot set, or a dimension estimate on the residual fiber.

## 4. Sharp obstruction to promotion from scalar information

The following synthetic examples explain why derivative, positivity, and even the entire scalar PLY disk cannot alone supply pointwise boundary control.

For q>=3, parent period integer n>=1, and any chosen unit-circle point xi !=1, put a=q/n and choose real b so that the imaginary part of (q^2/2)*(1+xi)/(1-xi)+i*b is zero. Define the rational function

    h_syn(w)=1/[ (q^2/2)*(1+w)/(1-w) + a+i*b ]
            =(1-w)/[(q^2/2)*(1+w)+(a+i*b)*(1-w)].

The denominator in the second expression is nonzero on the closed disk: for w!=1 this follows from Re(1/h_syn)>=a>0, and at w=1 it equals q^2. Hence h_syn is analytic on a neighborhood of the closed disk; Re h_syn>0 except at 1, h_syn(1)=0, h_syn'(1)=-1/q^2. It even obeys the stronger bound |h_syn|^2 <= (n/q)*Re h_syn, hence the full scalar PLY bound since 2 log(2)>1. Yet h_syn(xi)=n/q. Set xi=exp(2*pi*i/(q+1)). For z_syn=1/q+h_syn/(2*pi*i), we obtain

    |q z_syn(xi)-1| = n/(2*pi).

The angular sector also fails there whenever n>2*pi. For the actual sequence of absolute parent periods n=product_{j<q, j>=3} j, these synthetic values diverge. This satisfies (2), (6), (7) and the aligned scalar PLY inequality; the bad boundary peaks can be arbitrarily concentrated. More generally the shifted disk (5) is sharp at any fixed w in D in the half-plane function class: use the same formula with a=a_0 and cancel the imaginary part at that w. Without the PLY condition take a=0 and approximate by positive a; the disk constant in (2) cannot be reduced uniformly from root derivative and positivity alone.

This is **not** a quadratic-polynomial counterexample: no realization of h_syn as a parent multiplier of a quadratic family is asserted. Nor does it defeat a geometric proof using additional information about the parameter map, simultaneous multipliers, univalence domains, or the actual satellite orbit. It isolates the first new boundary obstacle for this analytic route.

## 5. Exact arithmetic regression and sources

Run from the repository root:

    node research/frontier/cs_multiplier_julia_bound_20261126/verify.mjs
    python3 -B code/verify_physical_bridges.py

The first command uses only exact BigInt rational arithmetic for synthetic half-plane model disk identities, rational sufficient norm and sector thresholds, harmonic-majorant inequalities, and 15 rational boundary peak witnesses. It also checks that the 35 printed nonroot primary norm observations in the earlier q=3,...,9 results.json are consistent with the enlarged analytic annular bound (using pi>3 and a +/-1e-12 printed-decimal allowance). This is a consistency check on stored values only, not verification of the numerical root identification, prior certificates, or the new analytic proof. The q-dependent chart radii are exact fractions. The same pure verifier function was executed with the GitHub-fetched input data before submission. No third-party package required. CI is read-only; its status is separate from the written proof. Only one METADATA source registration is added; no physical bridge or ledger promotion.

Primary sources, independently read at the displayed locators (no new byte hashes are claimed for these web renderings):
* Genadi Levin, [Multipliers of periodic orbits of quadratic polynomials and the parameter plane](https://arxiv.org/abs/math/0702011), [arXiv rendering](https://arxiv.org/pdf/math/0702011), v1 stamp 1 February 2007 (displayed internal date 4 September 2018), printed pp.1,10,16–18,20. Published Israel J. Math. 170 (2009), 285–315, [DOI](https://doi.org/10.1007/s11856-009-0030-0). The article version was not separately compared. Import DHS multiplier chart, Prop.1 and §6.1 wake and local bifurcation only. No use of Lemma 6.3 or 6.4's n-deep hypothesis.
* Davoud Cheraghi and Mitsuhiro Shishikura, [Satellite renormalization of quadratic polynomials](https://arxiv.org/pdf/1509.07843), v1 stamp 25 September 2015, displayed internal date 19 July 2018, printed p.52 equations (31)–(32). Used for comparison and the optional aligned-lift strengthening; source's PLY estimate is not a whole-copy bound independent of n. See prior archive source locks for exact historical PDF fingerprints; no claim that these renderings have been independently hashed.
* Schwarz–Pick, elementary half-plane Cayley transform, Julia's inequality (derived above), Poisson formula and Fatou's lemma. The two main estimates are mathematical deductions from these and the imported local dynamical interfaces; no claim of priority or exhaustive literature novelty.

**Status and next target.** Written analytic strengthening on actual child hyperbolic component charts and weighted boundary-exception estimate, plus bounded synthetic negative result for scalar promotion. The actual pointwise boundary estimate at the next angle, whole-copy supremum, all-parameter continued PL/NP identification, CS Theorem D extension, rigidity, MLC and JLC remain OPEN. No change to H1–H4, UPTCR, or the atlas. Future work should estimate the actual child chart derivative or a quantitative nonconcentration modulus for the parent log near the next attachment, and then separately control the descendant limb.

**AI disclosure:** ChatGPT GPT-6.2 performed source reading, analytic proof development, counterexample construction and exact arithmetic verifier drafting/execution. No independent human specialist proof audit or Lean verification performed. No claim of endorsement or priority; review the imported interfaces and written arguments before integration.
