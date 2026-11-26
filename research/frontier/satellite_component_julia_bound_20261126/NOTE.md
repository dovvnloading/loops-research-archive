# Satellite hyperbolic components: attachment-anchored Julia bound for the actual parent multiplier

**Status: proposed written analytic result / METADATA; compact multiplier subdisks only.** This is a follow-up to [#139](https://github.com/dovvnloading/loops-research-archive/pull/139), [#142](https://github.com/dovvnloading/loops-research-archive/pull/142), and the weaker radial interface in [#151](https://github.com/dovvnloading/loops-research-archive/pull/151), based on main at f72b326d938360428952c848053bf3ec7c94ec71. For every genuine quadratic satellite hyperbolic component and its continued dividing parent cycle, a Julia inequality gives a period-independent bound on the attachment-normalized log. In particular, it excludes nonprincipal log shifts on the specified q=9 chart points **conditional on their native component and parent-cycle identification**. It does not retrospectively certify those numerical identifications. A sharp scalar obstruction explains why this argument cannot, by itself, give an estimate at the next satellite attachment or across the whole tuned copy. No ledger promotion.

## 1. Target, exact hypotheses and sources

Let W be a hyperbolic component of the quadratic family f_c(z)=z^2+c of period k >= 1. Let H=W(1/q) be its genuine satellite child of period kq, q>=3; the argument works at any reduced p/q with q>=2, with center 2*pi*i*p/q in place of 2*pi*i/q. Let c_* be their common attachment root, and let lambda: H -> D be the multiplier of the actual attracting child orbit, with inverse c(lambda). Thus c(lambda) -> c_* as lambda -> 1. Let rho(c) be the holomorphic continuation of the period-k parent multiplier from that attachment into H, not a multiplier of an independently straightened map. It is repelling on H. Define tau(lambda) as its unique holomorphic logarithm on D normalized by tau(1)=2*pi*i/q in the limit at the attachment; this is not a principal-log assumption. The local analytic continuation at the root and the existence of the log follow from the inputs below and simple connectivity of D. This identifies the attachment lift of this continued parent cycle; no extra claim about physical polynomial-like prime-end/sheet realization is made.

Primary source: G. Levin, *Multipliers of periodic orbits of quadratic polynomials and the parameter plane*, [arXiv:math/0702011v1](https://arxiv.org/abs/math/0702011v1), [rendered PDF](https://arxiv.org/pdf/math/0702011), Israel J. Math. 170 (2009), 285–315, [DOI](https://doi.org/10.1007/s11856-009-0030-0). The PDF is stamped v1 (1 February 2007; internal typesetting date 4 September 2018); printed pp. 1, 16–17, 20 were read in text and page images. Exact versioned PDF bytes were not downloaded or SHA-locked here; the journal edition was not compared.

* Introduction p. 1: the Douady–Hubbard–Sullivan multiplier coordinate is a conformal isomorphism to D with homeomorphic extension to the closed disk; §6.1 p. 16 gives the genuine satellite attachment, continuation of the parent orbit into the child wake and repelling status there. The parent multiplier is locally injective at the nontrivial attachment.
* Lemma 6.2, pp. 17–18, and (30): at the attachment there are exactly q nearby nonparent fixed points of f_c^(kq) near each parent point, constituting the bifurcating child orbit, with the usual q+1 multiplicity at the root.
* §6.1 p. 20, immediately before Lemma 6.4, gives the local derivative d lambda/d rho at rho_*=exp(2*pi*i/q) as -q^2/rho_* (credited there to Guckenheimer–McGehee, reference [9]; Levin also derives it from (30)–(31)). This **local** formula does not require Levin's later n-deep/large-q hypotheses for global continuation of the child cycle in the parent multiplier coordinate. We use neither Lemma 6.3 nor Lemma 6.4.
* For comparison with the pre-existing broad PLY disk only, Levin §5.1 (20), printed p. 12 (text inspected), and Cheraghi–Shishikura §4.5 / Theorem 4.6, as cited by #139/#142. No PLY estimate is used to establish the new bound.

These are imported source statements, not a new proof audit of the foundational multiplier-coordinate theorem. The analysis below is an elementary deduction; novelty in the literature is not asserted. The source names and attachment hypotheses are essential; the numeric data in #142 alone do not prove these hypotheses for a particular algebraically certified sample.

## 2. Attachment derivative and Julia inequality (written proof)

Put u(lambda)=tau(lambda)-2*pi*i/q. Then Re u>0 on D. Local inversion of Levin's derivative gives u(1)=0, u'(1)=-1/q^2, so u(t)=(1-t)/q^2+O((1-t)^2) on the real radius t -> 1. The holomorphic log near the root is uniquely continued through D since the parent multiplier has no zero there. Its real part is log|rho|.

Independent check of the sign and factor q^2: take a small contour around one parent fixed point of the k-return at the attachment. It encloses the single parent fixed point and the q child points of the kq-return for c sufficiently close to c_*. The integral of dz/(z-f_c^(kq)(z)) divided by 2*pi*i stays bounded since the contour avoids zeros at c_* and for nearby parameters. For c in H, these fixed points are simple (repelling parent and attracting child), so by residues
     
    1/(1-rho^q) + q/(1-lambda) = O(1).
     
Consequently (1-lambda)/(rho^q-1) -> q and (tau-2*pi*i/q)/(1-lambda) -> 1/q^2. This also suffices for the limiting argument without analytic inversion. The q count is the imported local splitting, not a count of all fixed points of the global iterate.

For arbitrary lambda in D and real t in (0,1), Schwarz–Pick between the disk and the right half-plane gives

    |(u(lambda)-u(t))/(u(lambda)+conj(u(t)))|
        <= |(lambda-t)/(1-t*lambda)|.

Subtract the squares from 1 and use the exact identities for the disk and half-plane pseudohyperbolic distances:

    4 Re u(lambda) Re u(t) / |u(lambda)+conj(u(t))|^2
        >= (1-|lambda|^2)(1-t^2)/|1-t*lambda|^2.

Divide by 1-t and take t -> 1. Since Re u(lambda)>0, u(lambda) is nonzero and the denominators have nonzero limits. With

    T(lambda)=|1-lambda|^2/(1-|lambda|^2),

the resulting inequality is

    |u(lambda)|^2 <= (2 T(lambda)/q^2) Re u(lambda).             (J)
    |u(lambda)-T(lambda)/q^2| <= T(lambda)/q^2.                 (D)

Thus |tau-2*pi*i/q| <= 2 T(lambda)/q^2, uniformly independent of the absolute period k. In particular for any fixed 0<=r<1 and all |lambda|<=r,

    |tau-2*pi*i/q| <= 2(1+r)/(q^2(1-r)),
    |Im tau-2*pi/q| <= (1+r)/(q^2(1-r)).

The latter is from the disk, not the weaker triangle estimate. For r fixed this is O(q^-2) displacement and gives q*|tau/(2*pi*i)| -> 1 uniformly on those compact subdisks of *every* genuine satellite child, as q -> infinity (and for varying k). More generally (J) implies an O(q^-1) absolute bound whenever T(lambda)=O(q), with convergence of the scaled norm to 1 when T(lambda)=o(q). The estimate also holds on non-tangential approaches to lambda=1 inside D. No ordinary fundamental annulus, IS entrance, uniform straightening, or MLC hypothesis is used.

A sharper normalized radial interval follows by translating and scaling disk (D). Set b=T(lambda)/(2*pi*q). For rotation 1/q the modulus of its normalized center is sqrt(1+b^2), and its radius is b. Hence

    sqrt(1+b^2)-b <= q*|tau/(2*pi*i)| <= sqrt(1+b^2)+b.          (R)

This is a disk bound, not an assertion that these extrema are attained by genuine parameters. For |lambda|<=r the same bounds hold with b replaced by (1+r)/(2*pi*q*(1-r)), using monotonicity. The analytic scalar Julia inequality itself is sharp on the half-plane class: u=(2/q^2)*(1-lambda)/(1+lambda) gives equality in (J). This scalar extremizer is not asserted to be a multiplier.

## 3. Consequence for #142: principality separate from dynamical identification

The extended multiplier audit uses the center and four targets 0.99, -0.95, +0.95i, -0.95i at each q=3,...,9. At q=9 its two ambiguous PLY shift lists belong to minus and minusI. For q>=3 and rotation 1/q, (D) implies -pi<Im tau<pi provided

    T(lambda) < pi*q*(q-2).

This follows directly from |Im tau-2*pi/q|<=T/q^2; it suffices to prove the upper endpoint <pi, which also puts the lower endpoint >-pi. It is a certified branch-selection criterion **for the true continued parent multiplier at c(lambda)**, not an interval path certificate for a numerical seed.

| target | T exact | q=9 radius of (D) | principal at q=9? |
|---|---:|---:|---|
| center | 1 | 1/81 | yes |
| plus | 1/199 | 1/16119 | yes |
| minus | 39 | 13/27 | yes |
| plusI | 761/39 | 761/3159 | yes |
| minusI | 761/39 | 761/3159 | yes |

All five checks use just pi>3 and exact rational comparisons. For the entire disk |lambda|<=0.95 the same criterion holds for every q>=5; for |lambda|<=0.99 it holds for q>=10 (sufficient thresholds). The positive radial target 0.99 has the smaller T above regardless of disk radius. In particular q=9's two PLY-ambiguous target lifts are principal if the samples are the actual named satellite parameters and the certified period-k multipliers belong to the continued parent orbit. This logically removes the independent integer-shift ambiguity **once those hypotheses are met**; it does not certify membership of an algebraic root in H, identify the dividing orbit from its period alone, or verify the numerical continuation in #142. The earlier preregistered verdict remains unchanged. There is no need to certify every point of a connecting path to select the log *after* native component and orbit membership are established.

The prior sampled prediction [0.9,1.2] follows from (R) whenever b<=19/180: the exact inverse thresholds are (1/0.9-0.9)/2=19/180 and (1.2-1/1.2)/2=11/60. This proves that range for the true center and plus target for every q>=3, since pi>3 and T<=1. It also proves the entire |lambda|<=0.95 disk for q>=62, and |lambda|<=0.99 for q>=315 (conservative integer thresholds using pi>3). It does NOT prove the full prediction at the negative or imaginary targets for q=9. This is a bound on a specified subset of the actual component; it neither validates numerical sample identity nor upper-bounds the whole tuned copy.

## 4. First obstruction to extending this to the infinite satellite tail

The hyperbolic component coordinate has |lambda|<1. Its next 1/q_next attachment is at lambda=exp(2*pi*i/q_next), on the boundary away from 1. As lambda tends to such a point from the disk, T diverges. The infinite satellite parameter itself need not belong to the open child component. Passing to a boundary limit of (J) without a uniform estimate for T or a stronger analytic input is invalid.

There is a sharp obstruction to deducing a boundary improvement solely from half-plane positivity, the exact root derivative and even the original PLY-type disk. For any q>=3, R>0, and any target zeta on the unit circle other than 1, write H_0(lambda)=(1+lambda)/(1-lambda). H_0(zeta) is purely imaginary. Define the scalar rational function

    C=1/(2R) - (q^2/2) H_0(zeta),
    u_R(lambda)=1/[(q^2/2) H_0(lambda)+C]
               =(1-lambda)/[(q^2/2)(1+lambda)+C(1-lambda)].

On D, Re(1/u_R)>1/(2R), so Re u_R>0 and |u_R-R|<R. This satisfies a PLY-type tangent disk of arbitrary chosen radius R, and satisfies (J) by the explicit nonnegative remainder below. At 1 the displayed rational form extends holomorphically with u_R(1)=0 and u_R'(1)=-1/q^2. There are no other boundary poles because the real part of the denominator in the reciprocal form is 1/(2R) there. At zeta, u_R(zeta)=2R. This reaches the full tangent-disk diameter even for zeta arbitrarily close to 1, and R can be replaced by any smaller positive radius if strict containment in a larger closed disk at the boundary is desired. For the original period-dependent PLY radius one could take R=k*log(2)/(2q), half the allowed radius, so this data alone cannot yield a period-independent small displacement at the next attachment.

The residual analytic quantity made explicit by (J) is

    G(lambda)=1/u(lambda) - (q^2/2)*(1+lambda)/(1-lambda),
    Re G(lambda)>=0 on D.

This is equivalent to (J), by dividing by |u|^2 and using Re H_0=1/T. The obstruction is the freedom of the imaginary part of G to cancel the reciprocal pole contribution at a boundary point: in the model G=C is constant. It shows why even local holomorphic extension across the circle, with no quantitative control, is insufficient in this scalar class. An actual-dynamical continuation estimate or a bound on the residual reciprocal term on the required region is needed to turn the hyperbolic-component result into an all-copy/infinite-tail estimate. No claim is made that the scalar rational functions arise from quadratic dynamics or satisfy any additional native geometric constraints. This is not a counterexample to a uniform multiplier estimate, to Lemma T, or to CS Theorem D.

## 5. Reproduction and status boundaries

From repository root (Python standard library, no third-party dependencies):

    python -B research/frontier/satellite_component_julia_bound_20261126/verify.py
    python -B code/verify_physical_bridges.py

The exact rational verifier checks the five T factors at q=3,...,9 (35 rows), sufficient branch/radial thresholds, and 135 interior evaluations plus exact boundary saturation for rationally parametrized scalar models (27 models). It performs no dynamical orbit computation, no source verification and no proof of analytic theorems. The first verifier was run locally in Python; the full source-index check is delegated to the read-only PR workflow. Source registration is METADATA only. The note is an independent mathematical argument; the verifier is a regression of arithmetic, not a substitute for review.

Dependencies are the imported genuine-satellite hypotheses and local derivative above, Schwarz–Pick and elementary complex analysis. No ledger node is changed, no standing bridge is registered, and no other PR is assumed merged. Main snapshot f72b326d938360428952c848053bf3ec7c94ec71; repo inputs [#142 NOTE](../cs_multiplier_locus_extended_20261126/NOTE.md), [#146 NOTE](../local_dilatation_construction_20261126/NOTE.md), [#151 NOTE](../lemma_t_near_parabolic_20261126/NOTE.md), CONTRIBUTING.md and RESEARCH_MAP.md were reviewed in the relevant scope.

**Nonclaims:** no unconditional identification of any numerically linked q=9 orbit or sample with the named component, no certified numerical path, no whole-copy bound, no infinite-realization radial estimate, no rigidity, no uniform marked QC comparison or trace estimate (M/T), no new MLC/JLC case. No proof of closure of H1–H4 or UPTCR. We do not claim a new literature theorem, only a proposed written application of classical results to the archive's specific frontier. AI-assisted (ChatGPT GPT-6.2: source comparison, proof derivation and exact verifier); no independent human specialist review has been performed.
