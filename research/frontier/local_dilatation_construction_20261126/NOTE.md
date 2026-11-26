# Verdict: BOUNDED NEGATIVE — equivariant trace extension constructed; uniform marked trace strain OPEN

**Status: OPEN / METADATA (conditional local construction, not a standing physical bridge).** The one missing estimate for the surgery below is Lemma T in §2. It is a quantitative bound on a prescribed trace on a closed periodic subset of the actual linearizing plane, not a request for an already constructed uniform QC neighborhood map. The extension, conjugacy and marking checks are given explicitly. I could not prove T for the actual unbounded satellite tail from the available perturbed Fatou-coordinate estimates. This is not an obstruction to optimal marked dilatation, nor a claim that T is necessary.

## Limits and target

Work at main 6926f2cafe63d26693021cdf3c8b20e9f02f892f, after reading CONTRIBUTING.md, RESEARCH_MAP.md, merged [#140](https://github.com/dovvnloading/loops-research-archive/pull/140), [#143](https://github.com/dovvnloading/loops-research-archive/pull/143) with review comments, and [#142](https://github.com/dovvnloading/loops-research-archive/pull/142) with its review. Target is the open M of #143, not the ordinary collar route of #140. Fix a realized address S(1/3)S(1/4)... with actual degree-two connected parent PL return F_n=f_c^(k_n), k_n=product_{j<n}q_j, q_n=n+2, dividing repelling fixed point a_n, rho_n=F_n'(a_n), and the ordered q_n parent external accesses, with the compatible attachment-continued logarithm tau_n. These are hypotheses about the actual marked objects, not a theorem of realization or of identification of original-plane rays with parent prime ends. See CS (31)–(32), printed p.52. Work away from parabolic attachment points; neighborhood radii may shrink. For an actual-copy estimate the quantifiers below must additionally be uniform in every parameter c in the specified nested copy for which these hypotheses hold. No claim about that stronger version.

Levin's 1990 §1, eqs. (1)–(2), p.273 and Theorem 3, p.277 use conjugacy of neighborhoods of the connected filled sets; this is stronger than a local germ conjugacy. The primary indexed text was reopened and checked; page image timed out. Do not apply that theorem literally to our local extension. Instead use Hubbard's marked torus argument (or the affine calculation in §4). The unmarked same-multiplier germ trick, which does not transport filled-set access germs, is irrelevant.

## 1. Physical trace to be extended

For each n, use an ordinary (not uniformly bounded) hybrid straightening h^0 of F_n to a connected quadratic Q_n, available by CS Theorem 4.2, p.48, reproducing Douady–Hubbard straightening. It identifies the filled sets and transports their local accesses. As in #143, we require the specified parent access orbit and its log lift to agree with CS; we do not infer that identification from a principal log. Let b_n=h^0(a_n). It is a repelling fixed point: the local inverse branch at a_n contracts on a small disk; the conjugate inverse branch at b_n is holomorphic (local injectivity follows from the conjugacy) and its iterates converge uniformly on compact subsets of the image disk to b_n. Cauchy's formula then implies its derivative's powers tend to zero. Write lambda=Q_n'(b_n), |lambda|>1, sigma=log(lambda) in the target marked lift. Suppress n below.

Use holomorphic linearizing coordinates at a,b sending them to zero. For completeness, for a repelling germ with multiplier rho, center the local inverse g at zero; g(w)=rho^(-1)w+O(w^2). Choose |rho|^(-1)<t<|rho|^(-1/2) and a disk on which |g(w)|<=t|w| and |g(w)-rho^(-1)w|<=C|w|^2. Consecutive functions rho^m g^m(w) differ by at most C|rho|^(m+1)t^(2m)|w|^2. The series converges uniformly there, gives derivative 1 at zero, and satisfies psi(g(w))=rho^(-1)psi(w). The holomorphic inverse function theorem gives the desired local chart. Same argument at b. Constants and disks here need not be uniform. In these coordinates the inverse branches are multiplication by rho^(-1), lambda^(-1). Extend h^0 on the punctured planes by equivariance: for each w!=0 choose m sufficiently large that rho^(-m)w is in the local conjugacy chart and set h_lin(w)=lambda^m h_lin(rho^(-m)w) using the local map on the RHS. The conjugacy on overlapping inverse iterates makes this independent of m. Inverse construction gives a homeomorphism; it sends the inverse-continued filled set and its marked access germs to the corresponding sets. At the level of germs the forward and inverse filled-set memberships are equivalent since F is PL and the chosen local points are in its source. Thus saturation is well defined independently of the chosen smaller disk.

Lift this homeomorphism by exp to H:C->C (real plane); the orientation and degree around zero give H(w+v)=H(w)+v where v=2*pi*i. For suitable sigma it also has H(w+tau)=H(w)+sigma. Use compatible marked lifts: translation by v advances the ordered lifted sector labels by q and tau by 1; a marked seed conjugacy preserves this labeling up to a common additive constant, hence its target advance is 1. Thus the primitive core q*tau-v maps to q*sigma-v. This is the integer marking in Hubbard Prop.3.5 p.476. In particular we do not choose sigma independently by minimizing a principal argument. This construction works for the given marked class; if the attachment lift/parent marking is not supplied, no assertion about the CS observable follows.

Let S be the full closed log-plane lift of the inverse-continued local filled set, i.e. the saturation of its punctured linearized germ by all integer powers of rho, then full preimage under exp. It is closed locally in C: every compact subset of the punctured plane can be moved into a fixed small linearizer disk by a common sufficiently large inverse iterate, where filled membership is closed. S is invariant under lattice Lambda=Z v+Z tau. For each of the q marked accesses choose an actual complementary landing arc in the physical germ (not arbitrary model rays), take its punctured linearizer image, all multiplier translates and log lifts. Define E to be the closure of the union of S and those translates of the q arcs. It is nonempty, closed, Lambda-invariant. The target trace is H(E); its arcs are the seed images, representatives of the genuine target accesses, not asserted to be the literal equipotential radial parametrizations. Allow the choices of arcs and seed h^0 to vary with n. We will leave H on E exactly unchanged. This deliberately prescribes more data than just the core class; the construction is not equivalent to the existence of an unmarked torus map.

Let A be the unique real-linear map with A(v)=v and A(tau)=sigma. Put a=Re(tau)>0, b=Im(tau), a'=Re(sigma)>0, b'=Im(sigma). In Cartesian coordinates
     
    A(x+iy)=(a'/a)x+i(y+(b'-b)x/a).
     
Its determinant is a'/a>0. Let kappa(A)=s_max(A)/s_min(A), where s_min,s_max are its positive singular values. Set
     
    u(w)=A^(-1)H(w)-w  (w in E).
     
This is a Lambda-periodic displacement: both H and A have exactly the same increments. Define
     
    L(E,H)=sup_{x,y in E, x!=y} |u(x)-u(y)|/|x-y|,
    B(E,H)=kappa(A)*(1+sqrt(2)L)/(1-sqrt(2)L)
     
with B=+infinity if L>=1/sqrt(2), including L=+infinity. Euclidean distances in the actual complex logarithmic linearizers, not distances in rescaled petal labels. Translations of either linearizer log coordinate do not affect the difference quotient. The two factors of B encode the affine lattice shear and the residual cross-trace strain. This is a *sufficient, deliberately perturbative* criterion; no assertion that a QC trace is Lipschitz, much less a small Lipschitz perturbation, is made.

## 2. Single missing estimate (Lemma T — OPEN)

For each fixed realization c with the parent restrictions, repelling points and compatible markings above, there exist a finite B_*>=1 and an integer N such that **for every n>=N** there exist an ordinary marked seed straightening h^0_n and q_n landing-arc representatives as in §1, for which

    B(E_n,H_n) <= B_*.                                      (T)

For the whole-copy version replace the initial fixed-c quantifier by: there exist B_*,N such that for every n>=N and every c in the specified nested copy M_n for which the parent restriction, repelling dividing point and compatible marking exist, one can choose the seed and arcs with (T). Neither version is proved. Everything else in the local extension argument is elementary once these trace data and (T) are supplied. This is the precise single estimate needed by this particular construction. In particular it is not an estimate at a fixed q with a constant allowed to depend on q. It bounds a displacement difference quotient on a *subset* (including pairs on distinct access boundaries and across translated cells); it does not assume any bounded-dilatation extension off it. It includes a bound on the unmarked affine lattice shape in addition to the cross-trace perturbation. A proof of the affine part alone would already give the radial inequality below but would not construct a marked conjugacy.

## 3. Explicit conditional surgery (no collar)

For any one admissible trace with finite B, let L=L(E,H), delta=sqrt(2)L<1. Write u=(u_1,u_2). Construct scalar extensions on the entire plane by the infimum formula
     
    U_j(w)=inf_{e in E} (u_j(e)+L|w-e|), j=1,2.
     
No extension theorem is needed. Since u is continuous periodic on a closed periodic set, it is bounded (intersect with a compact closed fundamental parallelogram); the infima are finite. At w in E the scalar Lipschitz inequality gives every term >=u_j(w), and the choice e=w gives equality. The triangle inequality gives |U_j(w)-U_j(w')|<=L|w-w'| by comparison of each term and then reversing w,w'. For lambda_0 in Lambda, replace e by e+lambda_0 in the infimum; this proves U_j(w+lambda_0)=U_j(w). Consequently U=(U_1,U_2) is bounded periodic, and |U(w)-U(w')|<=delta|w-w'|.

Define G(w)=w+U(w), H_new=A G. For all w,w',
     
    (1-delta)|w-w'| <= |G(w)-G(w')| <= (1+delta)|w-w'|.
     
G is onto: for a prescribed y, start w_0=y and iterate w_{m+1}=y-U(w_m). Consecutive differences are bounded by delta^m |w_1-w_0|; the sequence is Cauchy and the limit solves G(w)=y. The lower estimate gives injectivity and a Lipschitz inverse. For every t in [0,1], id+tU has the same properties; this isotopy from id proves orientation preservation. G has a.e. derivative with singular values between 1-delta and 1+delta (or use the pointwise metric definition of QC for a bi-Lipschitz homeomorphism). Thus H_new is orientation-preserving, with
     
    Dil(H_new) <= kappa(A)*(1+delta)/(1-delta)=B.
     
Equivalently its metric linear dilatation is bounded by this ratio at every log-plane point. It agrees with H on E because A(w+u(w))=H(w) there; and H_new(w+v)=H_new(w)+v, H_new(w+tau)=H_new(w)+sigma. This is an exact gluing identity on all translated cells, with no product of q local distortion constants.

Exponentiate: h_new_lin(z)=exp(H_new(log z)) is single-valued by the meridian identity, a homeomorphism of C* by the equivariant inverse, and intertwines z->rho*z and z->lambda*z by the second identity. Since U is bounded and Re A(w)=(a'/a)Re w, for some finite constant C_0 (depending on this trace)
     
    exp(-C_0)|z|^(a'/a) <= |h_new_lin(z)| <= exp(C_0)|z|^(a'/a).
     
It extends homeomorphically at 0. On C* the exponential and local log are conformal, so the bound B remains. For an analytic-definition check at 0: on each punctured chart the a.e. derivative norm is bounded by C_1 |z|^(a'/a-1), with finite C_1 since H_new is Lipschitz and the previous upper estimate holds. Its squared integral over radius r is bounded by 2*pi*C_1^2*r^(2a'/a)/(2a'/a), finite since a'/a>0. Integration by parts on punctured disks gives the same weak derivatives across zero: the inner boundary term is O(epsilon^(1+a'/a)) for bounded test functions. Thus it is W^(1,2)_loc and satisfies the a.e. distortion inequality with the same B; no extra distortion from the center. Conjugate back by the two local holomorphic linearizers, restricting to a sufficiently small neighborhood of a whose image lies in the target chart. The resulting germ is an exact dynamical conjugacy.

Marking check: H_new agrees with H on S, and bijectivity implies H_new(S)=H(S), so it takes the entire lifted filled-set germ, not merely selected separator points, to the target. On all chosen landing arcs it agrees with the marked seed H, hence identifies those access germs and the containing complementary components. If represented as prime ends rather than chosen arcs, the induced correspondence is the one specified by those representatives and by the filled-set homeomorphism; no assertion of local connectivity of the entire boundary is used. It respects cyclic order by orientation and maps q*tau-v to q*sigma-v exactly. Restricting after exponentiation preserves the germ correspondence (inverse iterates place every relevant arc tail into the small charts). This verifies the physical observable identification under the stated marking hypotheses. We do not claim the new map is hybrid on the entire filled set or extends to a uniform map of filled-set neighborhoods.

Therefore (T) implies M with K_*=B_*. This is a genuine local, conditional construction with explicit distortion, valid for any q if the estimate holds. For one fixed n, straightening ensures a finite QC seed, but it need not have finite B; even for a fixed map we do not assert this particular Lipschitz surgery succeeds without (T).

## 4. Conditional radial calculation (no appeal to Levin on a bare germ)

Hubbard Prop.3.5 p.476 produces an annulus of modulus pi/(q log 2) in the quadratic multiplier torus with primitive core q*sigma-v. Prop.3.2 p.475 bounds it by 2*pi*Re(sigma)/|q*sigma-v|^2. These are applied only to the connected quadratic with its marked orbit, not directly to the PL germ. With d=q*tau-v, A d=q*sigma-v, and Re(sigma)=det(A)Re(tau), it follows that
     
    s_min(A)^2 |d|^2 <= |A d|^2 <= 2 q log(2) det(A) Re(tau),
    |tau-2*pi*i/q|^2 <= 2 kappa(A) log(2) Re(tau)/q.
     
The second line uses det(A)=s_max*s_min and division by q^2. In particular with K=B_* under T, Re(tau)<=2K log(2)/q. Writing z=tau/(2*pi*i), b=K log(2)/(2*pi), completion of squares yields
     
    |z-(1-i*b)/q| <= b/q,
    q|z| <= sqrt(1+b^2)+b.
     
The direct lattice proof avoids needing modulus distortion of the extended map and shows the bounded affine factor alone suffices for radial control, but not the marked sector conclusion of M. No k_n appears. Conversely a radial bound alone does not control kappa(A) or trace strain. For each prescribed r>0, T would give actual |z_n|<=r once q_n>=(sqrt(1+b^2)+b)/r. This is at most the actual radial input of CS Prop.6.7(b) p.63 (one-digit block G^0=id), not containment of their original full PLY disk and not their QG assumption.

## 5. Attempt to get T from near-parabolic charts, and explicit seam test

IS Main Theorems 1–3, printed pp.13–14, control univalent domain charts and contraction for parabolic and admitted small-rotation near-parabolic renormalization. CS Thm.2.9 p.15 has the corresponding admitted analytic input and output charts. Even if a suitable actual return is represented in this class, a chart change between P composed with two inverse univalent charts intertwines the two expressions by precomposition, not by dynamical conjugacy. The natural next idea is to compare fundamental Fatou-coordinate cells using the interpolation in CS §3.5, Lemma 3.17 and formula (20), p.30: on a translation strip the two sides are joined by an affine interpolation to their lift images. The boundary relation is an intertwining with translation. This is a useful model for gluing, not a simultaneous identification of the physical q marked sector germs of F_n and the straightened Q_n. I did not use the displayed numerical complex-dilatation constant in that lemma (as printed its ratio upper bound exceeds 1); only its interpolation and boundary identity are relevant. No new admission theorem is supplied here. Even granting the analytic admission, the bounds for individual strips are not bounds for the difference quotient of the *dynamical seed trace in the common physical logarithmic coordinates* between two different sectors. Analytic rotation is not automatically the rational combinatorial 1/q, and the next denominator grows only linearly. The estimates opened here do not give (T).

Here is an explicit seam model isolating why the cross-trace requirement is substantive. This is NOT a PL realization, a q-petal theorem or a lower bound on optimal local K.

For integer q>=3 take Lambda generated by v=2*pi*i and tau=(1+2*pi*i)/q, same target lattice, A=id. Take E consisting of all vertical lines at x=m/q and x=m/q+1/q^2, m integer. It is closed and Lambda-invariant. Let s(x) be 1/q-periodic, linear on [0,1/q^2] with s(0)=0, s(1/q^2)=1/q, and linear from 1/q there back to 0 at x=1/q. The seed shear
     
    H(x+iy)=x+i(y+s(x))
     
is an orientation-preserving equivariant homeomorphism with inverse obtained by subtracting s(x). For each fixed q it is bi-Lipschitz (slopes q and -q/(q-1)). On each trace line it is a translation, so within-line distortion and displacement derivative are zero in the residual, but for x=0 and x'=1/q^2 with equal y,
     
    |u(x')-u(0)|/|x'-0|=(1/q)/(1/q^2)=q.
     
In fact L=q, by the global Lipschitz bound on s. Hence B=infinity for this prescribed trace. The shear preserves the set of lines and all complementary strips, and the identity is also a marking-preserving set comparison of dilatation 1. Thus even within this model the failed criterion for this choice of trace is not degeneration of optimal marked dilatation. The model tests precisely the missing *cross-sector* estimate in the chosen interpolation; it says nothing about whether better choices of h^0 and arcs satisfy T for actual maps. Uniform per-petal distortion, without a common-coordinate seam estimate, cannot justify the proposed extension. Nor can the vanishing ordinary collar ceiling from #140 bound L from below.

## 6. Finite #142 certificate comparison (not proof of T)

The table uses only the five certified parent-period cycles at each level (center and four chart points; excludes parabolic root). From results.json the interval endpoints for q times the norm of the **principal** log divided by 2*pi*i are integers in units 1e-12, rounded outward. The row gives the minimum lower endpoint and maximum upper endpoint over those five intervals; not a certified extremum of any parameter locus. Child period is P; parent period p=P/q, NOT rotation numerator.

| q | p | P | min lower | max upper | nonunique primary PLY shifts |
|---:|---:|---:|---:|---:|---:|
|3|1|3|0.959058421740|1.043275477879|0|
|4|3|12|0.965910582461|1.034755847983|0|
|5|12|60|0.972025343526|1.028253396118|0|
|6|60|360|0.976343206977|1.023796328257|0|
|7|360|2520|0.979509071354|1.020573657154|0|
|8|2520|20160|0.981925946823|1.018130454618|0|
|9|20160|181440|0.983831119554|1.016211685416|2|

All these certified principal-log norm upper endpoints are below even the K=1 radial envelope (~1.1163844067). This comparison is just radial compatibility: no certified lift/mark for these values, no bound on Re tau relative to the straightened multiplier, no actual QC dilatation measurement. In particular #142's q=9 minus and minusI endpoint shifts remain ambiguous; #142 is INCONCLUSIVE / EVIDENCE-NOT-PROOF for the CS identification, lift and sampling. The dense-grid data are not certified maxima. No extrapolation.

## 7. Inputs, SHA256, reproduction

Repository inputs at 6926f2cafe63d26693021cdf3c8b20e9f02f892f (SHA256 computed from the base64 GitHub blob bytes, independently checkable with hashlib by the verifier):
     
| Path | SHA256 |
|---|---|
| CONTRIBUTING.md | d218e12ba518a3fb193590a126e638836ce18a5ea5ccabf121f83ef6f6fafdd3 |
| research/frontier/pl_yoccoz_radial_20261126/NOTE.md | 7febfbfb784bac7c164db97c73809d53c7b5631d11ed83e55f543c1721eac0b9 |
| research/frontier/is_local_dilatation_20261126/NOTE.md | b93de77f3533d5637b0723bceb8fba48eb32af2535c2110b0afaa5fc4097a195 |
| research/frontier/cs_multiplier_locus_extended_20261126/NOTE.md | 742ea6af8f531a3f61839075c19d664db3bd47f2a3ee8bfa21b0c88e7ccb16ac |
| research/frontier/cs_multiplier_locus_extended_20261126/results.json | 81d1f21db9392418bf0300d9f7c04f00c6362c95c72c2968aef62df159d69d39 |

Primary texts reopened for this attempt; page images inspected except Levin as indicated. The following PDF SHA256 values are inherited fingerprints from the earlier reviewed CI manifests (not SHA256 of web renderings, nor independently downloaded in this session). Optional verifier flag attempts exact URLs and reports matches or unverified downloads. No new theorem depends on a download succeeding.

* Cheraghi–Shishikura, [Satellite renormalization of quadratic polynomials](https://arxiv.org/pdf/1509.07843) (rendered v1, exact fingerprint URL https://arxiv.org/pdf/1509.07843v1), Theorem 4.2 p.48 (straightening), (31)–(32) p.52 (period and lift), Prop.6.7(b) p.63 (target scope); Thm.2.9 p.15 and §3.5 Lemma 3.17 p.30/formula (20) (comparison attempted, not an imported marked trace estimate). SHA256 71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f.
* Hubbard, [Local connectivity of Julia sets and bifurcation loci: three theorems of J.-C. Yoccoz](https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf), Props.3.2 p.475, 3.5 p.476 (annulus and homology). SHA256 eb28f6376e63683007fee394dee1b4e217d1b8d4fbd43118c2fa7e7f1754bf5d.
* Inou–Shishikura, [The renormalization for parabolic fixed points and their perturbation](https://www.math.kyoto-u.ac.jp/~mitsu/pararenorm/ParabolicRenormalization.pdf), Dec.12 2008, Main Thms.1–3 pp.13–14, comparison of classes, not an imported marked bound. SHA256 7ca4bf1341991f6d02331a121d715d50e0282d84a30520766193830ef96de00c.
* Levin, [Boundaries for multipliers of periodic points of holomorphic mappings](https://www.ma.huji.ac.il/~levin/Levin1990_Article_BoundariesForMultipliersOfPeri), Siberian Math. J. 31 (1990), pp.273–278, eqs.(1)–(2) p.273, Thm.3 p.277. Indexed primary text opened, image and exact bytes UNVERIFIED (direct fetch/image timeout; prior CI certificate hostname mismatch). No insecure download or fabricated hash; no direct application of Thm.3 to the weaker local hypothesis.

Read the review corrections explicitly: [#140 review](https://github.com/dovvnloading/loops-research-archive/pull/140#issuecomment-7183698711), [#143 discussion](https://github.com/dovvnloading/loops-research-archive/pull/143), [#142 review](https://github.com/dovvnloading/loops-research-archive/pull/142#issuecomment-7184197230). Historical source hash provenance #140 run 45762921945 and #143 run 45773704041. #140's ordinary-modulus obstruction is inherited as a scope boundary, not used as a new imported theorem here. No other source required for the constructed elementary extension.

From repo root (Python 3.12, standard library only, no third-party packages):
     
    python3.12 -B research/frontier/local_dilatation_construction_20261126/verify.py
    python3.12 -B research/frontier/local_dilatation_construction_20261126/verify.py --sources /tmp/local-dilatation-sources.json
    python3.12 -B code/verify_physical_bridges.py

Verifier checks the exact locked inputs, #142 table intervals and period schema, exact rational seam model and envelope arithmetic. Optional source URL manifest reports exact PDF byte matches, mismatches or unverified retrieval; network retrieval is not necessary to reproduce the arithmetic. No run computes T or the physical traces. CI is read-only, uses pinned actions and Python 3.12, never writes back. METADATA source registration only as authorized. GPT-6.2 assisted proof search, source checking, derivation and code; no human specialist verification has been performed.

## 8. Explicitly NOT established

* Uniform marked local dilatation for even one actual infinite realization; whole-copy uniformity; Lemma T, including its affine-factor bound on actual multipliers; degeneration of optimal marked K; applicability of the seam model to actual PL dynamics.
* Admission of actual parent returns to the IS analytic class; correspondence of perturbed Fatou cells with all genuine marked external sectors; independent physical prime-end/attachment lift certification; a stronger filled-set-neighborhood conjugacy; uniform ordinary collars; parabolic attachment extension.
* Unconditional radial 1/q bound, any certified whole-copy norm supremum, convergence or angular input, any relaxation of CS QG, Prop.6.10 induction, Theorem D, rigidity/nonrigidity, JLC, MLC or any ledger status change.

**Final mathematical label: BOUNDED NEGATIVE / OPEN / METADATA.** Lemma T is the one unproved estimate for this explicit perturbative extension construction; its failure or non-necessity in abstract examples cannot be promoted to obstruction of M.
