# Lemma T: near-parabolic compactness and the marked reciprocal lattice

**Claim — BOUNDED NEGATIVE (one-step synthetic counterexample only); Lemma T OPEN / METADATA.** The reciprocal change of lattice basis does not preserve the satellite core as the satellite core of the next level. Moreover, even with the *same* IS nonlinearity, arbitrarily small admitted complex rotations, a common synthetic integer access marking and a common reciprocal integer, one bottom NP step can stay analytically admitted for two maps while the affine marked comparison of their two repelling log lattices has condition number tending to infinity. The latter disproves a precise relaxed assertion: no universal bound for the marked affine factor exists over arbitrary pairs in the CS rotated IS class with one admissible bottom output, the same reciprocal digit and the synthetic line marking below, even when their input nonlinearity is identical. This is a genuine counterexample to that relaxed assertion, not a counterexample on actual PL/straightened pairs or on a common infinite NP itinerary. For a compactness argument restricted to those physical pairs, the result is a failure of the stated inference, not an impossibility theorem. A matched reciprocal digit on an already identified, admitted physical tower is sufficient for the radial 1/q estimate; this is conditional, not a proof of entrance or of Lemma T.

**Limits and status:** BOUNDED NEGATIVE / OPEN / METADATA — elementary marked-lattice calculation, one-step synthetic analytic-class counterexample to the relaxed affine assertion, conditional radial implication. The physical compactness route is unestablished, not ruled out. Neither the fixed-realization nor whole-copy T of #146 is proved or disproved. No ordinary fundamental-annulus estimate is used. Work on the branch based on the tree at the preregistration commit 0c97cfc87fe2bcc751ec28320ef50095bb9ce248. CONTRIBUTING.md, RESEARCH_MAP.md November 25–26 audits and the linked NOTE files were retrieved; the target #146 §§1–4 and #143 three-tower and comparison interfaces were examined in detail. Other audit threads are context, not imported proof dependencies. AI-assisted (ChatGPT GPT-6.2); no human specialist verification.

## 1. Marking before compactness

Use the physical hypotheses of [#146 §§1–2](../local_dilatation_construction_20261126/NOTE.md): actual parent degree-two connected PL F_n=f_c^(k_n), k_n=product of preceding q_j, q_n=n+2, repelling dividing point, q_n cyclically ordered complementary access germs, compatible attachment-continued log tau. Q_n is a hybrid straightening, with corresponding log sigma. Set v=2 pi i, a=Re tau>0, a'=Re sigma>0. The real-linear comparison A maps v to v and tau to sigma; its matrix in ordinary real coordinates is [[a'/a,0],[(Im sigma-Im tau)/a,1]]. Its condition number kappa is a lower bound on T's B for every choice of trace. Precisely, #146 §2 requires for each fixed eligible realization c some finite B_* and N such that at every n>=N there exist a marked seed straightening and landing-arc representatives with B(E_n,H_n)<=B_*. Here B=kappa(A)(1+sqrt(2)L)/(1-sqrt(2)L), infinite when L>=1/sqrt(2); a uniform bound entails a uniform gap below that threshold on the full trace (filled-set lift and all chosen access translates, with all-pairs quotient), and a bound on kappa(A). The whole-copy version uses the same B_*,N for all eligible parameters at each n. T is sufficient for the particular surgery, not asserted necessary for optimal marked QC dilatation. The relevant primitive homology class is d=q tau-v.

IS (Dec 12 2008, pp.13–14, Main Theorems 1–3) concerns normalized domain charts P composed with inverse univalent charts, extension to a larger fixed domain, and contraction in the Teichmuller metric on a punctured-domain parameter space (fiberwise for admitted rotations). The domain charts do not conjugate the dynamics, nor do they include the physical trace E, access labels, target Q_n or lattice comparison A. IS expressly distinguishes compact-open convergence from its stronger metric. CS v1 §2.1 pp.8–9, Thm.2.9 p.15, Remark 2.10 and Def.2.11 p.16, §5 p.52 distinguish the invariant nonlinearity from the additional complex rotation requirement: the next reduced rotation need not lie in A(r3). CS Remark 2.10 also says the NP maps need not globally be first-return maps. The precompact normalized charts (larger-domain extensions, Montel/Koebe on the smaller domain) are not compactness in the physical log-trace topology. The full nonzero-rotation space excludes its parabolic limit. Main Theorem 3 is not an unconditional all-bottom admission theorem.

CS (31)–(32) p.52 gives original-plane dividing periods, landing-ray count/rotation and a suitable PLY log; identification of the parent access lift with it is a physical premise; (42)–(43), Proposition 6.2 pp.59–60 and Cor.6.3 p.60 identify the appropriate bottom multiplier on an admitted tower, as *stated* in that paper (not a fresh proof audit). In the one-digit case (38), p.56, gives m_n=1, hence l_n=n-1 and the types are all bottom. This is not a conjugacy of filled-set germs or a transport of the trace; do not replace the actual parent multipliers with recursive PL straightenings. CS Theorem C p.5 is existence for sufficiently high entries, not all realizations; Theorem D p.6 and Prop.6.10 p.67 use QG (44), p.62, including q_(n+1)>=q_n^2 for one-digit blocks, not satisfied here (see #135, #138). A finite initial prefix transfer is not automatic, and starting the tail in the IS class is an unproved premise for arbitrary actual realizations. CS Lemmas 3.24–3.25 pp.42–44 bound the index and compare |alpha| and |beta| and variations at fixed alpha; these are absolute complex bounds, not relative bounds on the positive real parts of the two logarithms in A. Remark 6.9 p.67 proposes stronger precompactness estimates, not a theorem of marked comparison.

### Reciprocal homology calculation (proved algebraically)

For a repelling log tau=v beta, let tau'=v(-1/beta+k), for any integer k such that the successor is repelling, in the oriented chart before any complex conjugation. On the two *formal flat log tori*, multiplication by -v/tau gives an isomorphism:
    
    tau -> -v,
    v   -> tau'-k v,
    q tau - p v -> -p tau' + (p k-q) v.

This follows by substitution; the basis matrix has determinant 1. For p=1 and a matched digit k=q, the old core goes to -tau', a return generator, not to the new core q_next tau'-v (even up to sign). For p=-1, k=-q the same computation gives +tau'. Under CS Def.2.11 the negative side is treated by reflection, replacing beta by -conjugate(beta) and reversing the signed marking; the algebra applies in that reflected chart. These are identities of abstract marked lattices obtained from the multiplier formula, not a claim that the NP operator literally supplies this torus isomorphism on physical filled sets. The old period is exchanged with a meridian and the old meridian is exchanged with a return plus an integer multiple of the new meridian. The next nonzero fixed point is itself a different point from the new zero fixed point. In particular the natural reciprocal re-basing is not a map of the spaces of *same satellite core* marked traces. The full physical marking may conceivably be reconstructed by lifting a tower with extra data; no such theorem follows from chart invariance or Prop.6.2. This is a concrete mismatch for the specific reciprocal re-basing, not a prohibition on other transports. T is not even a function of an unmarked IS chart alone; a proof using physical marked compactness would need an additional identification and a relative estimate.

## 2. One-step bottom example inside IS (proved, synthetic marking only)

We test compactness in a stronger one-step setting than arbitrary linear germs. Fix P(z)=z(1+z)^2 restricted to CS's V, the identity-chart nonlinearity in CS §2.1 pp.8–9. The chart phi=id is normalized at 0 and extends conformally to the entire plane. V contains 0 and -1/3 but not -1. Use the CS precomposition convention A(r) x IS: the domain of f_j is exp(-v alpha_j)V, not the whole cubic plane; its unique critical point there is exp(-v alpha_j)(-1/3), with critical value -4/27. For integer q tending to infinity and j=1,2 put

    gamma_j = 1/q - i/q^j,
    beta_j = 1/(q-gamma_j),
    t_j = (3-exp(v beta_j))/2,
    alpha_j = log(t_j)/(pi i),
    f_j(z) = P(exp(v alpha_j) z).

The log at t=1 is the analytic branch with log 1=0. Here exp(pi i alpha_j)=t_j. If s=exp(v alpha_j)=t_j^2, the nonzero fixed point close to 0 solves 1+s z=1/t_j; differentiating P(s z) gives 3-2 t_j=exp(v beta_j). Thus beta_j is its principal small complex rotation, with Im beta_j<0, hence repelling. For large q, beta_j~1/q and alpha_j=-beta_j+O(beta_j^2), so alpha_j lies strictly in the negative cone A^-(r3), with modulus tending to zero. The maps are in the CS analytic class with *identical* nonlinearity and converge to P on compact subsets of V (domains rotate/scale to V). The nonzero solution z=(1/t_j-1)/t_j^2 tends to 0, lies in the rotated V and the fixed neighborhood W for sufficiently large q, and is the distinguished nonzero fixed point by CS Prop.2.1 p.9. Since Re beta_j tends to 0 positively, reflection gives the small negative-real branch used in the positive-input bottom formula (CS §3.10 p.42). These conclusions use only the elementary expansion of log at 1, not perturbed Fatou-coordinate estimates.

CS Def.2.11 reflects these inputs; P is real, so the reflected rotation at the nonzero point is -conjugate(beta_j). The reduced bottom output rotation is

    -1/(-conjugate(beta_j)) mod Z = q-conjugate(gamma_j) mod Z
                                 = -conjugate(gamma_j).

For all sufficiently large q its norm is <r3 and |Re|>=|Im| (j=1 on the allowed boundary of CS's closed cones, p.9, not the strict cones in IS Main Theorem 3). It is nonzero and its real part is in the principal reduction interval. Thm.2.9 and Def.2.11 therefore give an admitted bottom output in A(r3) x IS for each map, with the improved domain-chart property. No infinite iteration claim is made. Both members have the same absolute reciprocal digit q: the nearest integer to -1/beta_j is -q before reflection and +q after reflection (the corresponding shift k has the opposite sign). The reduced remainder is small in either convention. If strict output cones are desired use gamma_j=1/q-i/(2q^j), giving the same ratio q D_2/D_1 with D_j=X^2+(1/4)q^(-2j). The displayed example uses the CS convention and Theorem 2.9, not a direct invocation of the strict-cone statement of IS Main Theorem 3.

Use the positive, actual pre-reflection beta_j at the repelling nonzero fixed point as synthetic parent logs tau=v beta_1, sigma=v beta_2. Let X=q-1/q, D_j=X^2+q^(-2j). Then

    Re(v beta_j)=2 pi q^(-j)/D_j,
    Re tau/Re sigma = q D_2/D_1 >= q/2   (q>=3).

Since A fixes v, s_max(A)>=1 and det(A)=Re sigma/Re tau, kappa(A)=s_max(A)^2/det(A)>=q/2. No possible residual correction can lower B below this lattice factor. The inequality is independent of charts and of small log translations. Even two rotations with the same real part of the reciprocal, the same integer digit, and admitted outputs can have divergent relative expanding parts. The radial sizes themselves satisfy q|beta_j|<=q/(q-1/q), so the radial estimate and affine bound are strictly different in this model. Indeed both logs approach the marked radial center. The counterexample uses the actual local analytic multipliers of the displayed IS functions; it is not just a counterexample to continuity on all abstract matrices.

One can impose exactly the *synthetic* integer labeling of #146 in linearizing coordinates. For a repelling log tau=a+i b define
     
    ell_tau(x+i y)=(q/(2 pi))*(y-(b-2 pi/q)*x/a).
     
The parallel lines ell_tau=j (j integer) are closed, with ell_tau(w+v)=ell_tau(w)+q and ell_tau(w+tau)=ell_tau(w)+1. Exponentiation gives q disjoint logarithmic spiral germs, cyclically ordered, permuted by the multiplier; strips between them have the same label advances. The linear A satisfies ell_sigma(Aw)=ell_tau(w) and matches the entire synthetic line/strip marking. For this formal trace E and H=A, L=0 and B=kappa(A); for any other equivariant H with these lattice increments, B>=kappa(A). These are arcs in the linearized germs, not proved to be complementary accesses of a connected PL filled set. In particular the two IS functions are not shown to be related by hybrid straightening, nor have the same actual satellite combinatorics, nor to have a common infinite bottom itinerary. This is a counterexample to uniform inference from compactness, one-step admission and synthetic marks alone, *not* a lower bound on optimal physical K nor a counterexample to T. Additional physical restrictions might force the required multiplier comparability.

## 3. What a compactness proof would actually need

The algebra isolates the necessary nondegeneracy. If r=a'/a and s=(Im sigma-Im tau)/a, then
     
    kappa + 1/kappa = (r^2+s^2+1)/r.

This is trace(A^T A)/det(A). Therefore bounded kappa is equivalent to r bounded above and away from zero and |s| bounded; sufficiency follows from the displayed formula, necessity from each nonnegative summand. Compactness of analytic charts gives no such *relative* control as a,a' tend to zero. Even if a suitable family of marked compactifications could be made, a compact parameter set alone does not bound an arbitrary function: one needs local boundedness at its boundary, and for the perturbative trace criterion a uniform gap below 1/sqrt(2) for L after the affine normalization. Compactness of only the chart functions cannot exclude the example in §2. In particular a proof that each trace is QC does not establish a small Lipschitz residual. This obstruction is different from the explicit cross-sector seam example in #146 §5 and from the collar obstruction in #140.

### Weaker radial interface (conditional, not new admission theorem)

Let z_n=tau_n/v be the marked physical log, not a principal-log substitution. Define a single sufficient scalar *marked entrance-and-digit interface* R: for the given fixed actual realization, eventually there is an identified bottom NP step with bottom rotation z_n and a reduced output (or its reflected counterpart) of modulus <=r<1/2 whose reciprocal integer equals the signed combinatorial q_n. Equivalently, in the pre-reflection oriented positive mark, -1/z_n=-q_n+eta_n with |eta_n|<=r. For whole-copy uniformity the same r,N and the interface must hold for every eligible c at each n. Under R,

    |z_n|=1/|q_n-eta_n| <= 1/(q_n-r).

Even more, |z_n-1/q_n|<=r/(q_n(q_n-r)). This is enough for the actual-point analogue of the terminal radial conclusion in #146 §4 and CS Prop.6.7(b) p.63 (G^0=id for one digit), without kappa or surgery. It does not prove the proposition's full PLY-disk conclusion or its QG hypotheses. The first scalar identity is already noted conditionally in #143 §2; we do not claim it as a new theorem. A way to certify its integer (not just a reduction modulo Z) would be a continuous path of admissible, correctly identified and marked input/output rotations to the attachment root, with the reduced output in the fixed disk |eta|<=r along the path. Then -1/z-eta is a continuous integer-valued function and constant on the path; at z=1/q the unique reduced value is 0, so the integer is -q. A boundary approach suffices by taking the limit, with no assertion that NP is defined at the parabolic root. Reflections require changing signs consistently. Neither existence of these paths for actual parameters nor the uniform entrance/identification R is proved; using admissibility of every actual level to prove its own entrance is circular. The two-cone admission alone gives no connection between the reciprocal integer and the physical q. R actually controls displacement from 1/q_n and hence yields eventual angular smallness of this marked z_n; a radial norm estimate alone does not give cone admission, and neither implication controls the separate zero-fixed-point rotation or establishes the next physical entry.

For comparison the affine condition in #146 §4 would give the Hubbard Props.3.2 p.475 and 3.5 p.476 calculation |tau-v/q|^2 <= 2 kappa log(2) Re tau/q, on an actual marked PL/connected-quadratic comparison. No such kappa bound follows here. Levin 1990 Theorem 3 requires the stronger filled-set-neighborhood conjugacy as recorded in #143 and #146; it is not applied to these bare germs. Neither the ordinary fundamental-annulus route nor any BLOT estimate is invoked.

## 4. Hostile self-check / exact nonclaims

* Is the compact class really invariant including the rotation? No: only the nonlinearity is guaranteed; the admission of the next rotation is a separate requirement. The counterexample verifies it for one bottom step only, not all levels. The whole class is precompact in the relevant chart topology, not claimed compact in the Teichmuller metric; both example input charts are literally the identity.
* Does the natural homology re-basing refute all ways to reconstruct marking? No. The calculation is the algebra of the multiplier formula, not a proof that no physical marking can be transported by a tower with extra information. The old satellite core is not the new core; an additional physical marking/trace transfer is necessary for the proposed use of invariant compactness.
* Are the two nonzero fixed points of the IS maps a genuine parent/straightening pair? Not established. They are only local analytic examples. The synthetic q spirals are not external accesses of a PL filled Julia set. They test the information content of the analytic class and one-step integer data, not the extra hypotheses of T. No claim that actual multipliers differ by this ratio or that any actual QC constant diverges.
* Can the small angular perturbations be excluded by just requiring radial control? No, the example already has q|beta| bounded. Can they be excluded by a full common actual infinite itinerary or straightening? Unknown; that is additional information absent from the argument. Do not infer that T fails.
* No unconditional R, no full Lemma T or affine comparison for actual maps, no proof of actual 1/q rate for even one specified infinite realization, no whole-copy estimate, no lift certificate at q=9, no Prop.6.10 repair, no theorem D extension, no rigidity/nonrigidity, no JLC/MLC, no new ledger standing claim. #139/#142 samples remain evidence-not-proof. No ordinary collar route repeated.

## 5. Inputs and reproducibility

Primary theorem texts: PDF renderings reopened; pages inspected visually for IS 13–14 and CS 3,8,15–16,43,52,59–60,66–67. CS rendering stamped arXiv:1509.07843v1, 25 Sep 2015 (internal date July 19, 2018); exact version URL was unavailable through the text viewer, not through the proposed CI. PDF byte checksums below inherited from #146 §7 / its cited reviewed CI, **not independently downloaded in this network-disabled local sandbox**. No Levin PDF relied on as a new dependency; exact bytes previously unverified. Hubbard is the inherited #146 radial dependency, not needed for §2 or R. CI --fetch checks the exact HTTPS downloads against these fingerprints, fails on mismatch/unavailable; no insecure retrieval or generated commits.

| Source (exact URL) | SHA256 | locators |
|---|---|---|
| [CS v1](https://arxiv.org/pdf/1509.07843v1) | 71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f | pp.2–6, §2.1 pp.8–9/Prop.2.1 p.9, Thm.2.9 p.15, Remark 2.10/Def.2.11 p.16, Lemmas 3.24–3.25 pp.42–44, (31)–(32) p.52, (38) p.56, (44) p.62, (42)–(43)/Prop.6.2 pp.59–60, Cor.6.3 p.60, Prop.6.7(b) p.63, Lemma 6.8 p.66/Remark 6.9/Prop.6.10 p.67 |
| [IS Dec 12 2008](https://www.math.kyoto-u.ac.jp/~mitsu/pararenorm/ParabolicRenormalization.pdf) | 7ca4bf1341991f6d02331a121d715d50e0282d84a30520766193830ef96de00c | Main Theorems 1–3 pp.13–14 |
| [Hubbard](https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf) | eb28f6376e63683007fee394dee1b4e217d1b8d4fbd43118c2fa7e7f1754bf5d | Props.3.2 p.475, 3.5 p.476; inherited conditional radial comparison |

Repository input SHA256 (UTF-8 bytes as returned by GitHub at preregistration commit; independent local hashlib check by verifier):
    
| Path | SHA256 |
|---|---|
| CONTRIBUTING.md | d218e12ba518a3fb193590a126e638836ce18a5ea5ccabf121f83ef6f6fafdd3 |
| RESEARCH_MAP.md | 0f8c6984283e404b820da9b83d85dca071513a4288b3fd041e15bb44b8f3dea6 |
| research/frontier/local_dilatation_construction_20261126/NOTE.md | 0f5169927bf3b8a5f78303171c0007632d55d1a3b6c07193dd2113615a27824a |
| research/frontier/is_local_dilatation_20261126/NOTE.md | b93de77f3533d5637b0723bceb8fba48eb32af2535c2110b0afaa5fc4097a195 |
| research/frontier/pl_yoccoz_radial_20261126/NOTE.md | 7febfbfb784bac7c164db97c73809d53c7b5631d11ed83e55f543c1721eac0b9 |
| research/frontier/residual_satellite_status_20261126/NOTE.md | 99d7c409e6d57bd34b784156b6e52bdc8d4c137775f67a551e2755adc2404921 |
| research/frontier/cs_multiplier_locus_numerics_20261126/NOTE.md | 648cb202497dcf4bcb333c1770bb7d840016278dd4b6625d6ecc430a9c67df79 |
| research/frontier/cs_multiplier_locus_extended_20261126/NOTE.md | 742ea6af8f531a3f61839075c19d664db3bd47f2a3ee8bfa21b0c88e7ccb16ac |
| research/frontier/cs_prop_6_10_angular_20261126/NOTE.md | bdb8f6d8440b178adeb880a69638c77c4a08fd7f4f4ce848e898bd47b31c9f83 |

Run from repository root with Python 3.12 (standard library only, no third-party dependencies):

    python3.12 -B research/frontier/lemma_t_near_parabolic_20261126/verify.py
    python3.12 -B research/frontier/lemma_t_near_parabolic_20261126/verify.py --fetch
    python3.12 -B code/verify_physical_bridges.py

The verifier checks exact input bytes (via git show at locked commit, checkout fetch-depth 0), exact rational lattice and labeling identities and ratio inequalities on a fixed finite grid, plus a floating-point sanity check of the displayed P nonzero fixed-point multiplier and the input cones (not a numerical proof of IS admission or of any physical marking). The all-q algebra and large-q asymptotic reasoning are in §§1–2; finite checks are diagnostics, not a proof of T. The source check is strict and separate. CI pinned actions, read-only token, no CI commit. The only existing file edit is one METADATA registration row; no new theorem bridge. No other thread altered.

CI round 2 initially failed at setup-python: Ubuntu 26.04 lacks the 3.12.10 build; the successful Atlas citation resolution run 45806056852 confirmed CPython 3.12.16 on the same runner image. Round 3 pins that patch instead. The original failure did not run the verifier. No mathematical change.


### Independent referee clarification (PR #151)

The final label is BOUNDED NEGATIVE / OPEN / METADATA, not OBSTRUCTED for the physical compactness route. The independently checked source rendering at https://arxiv.org/pdf/1509.07843 is stamped v1 (25 September 2015; internal date 19 July 2018); the exact versioned rendering could not be opened independently. CS pp.5–6, 8–9, 15–16, 42–44, 52, 56, 59–60, 62–63, 66–67, IS pp.13–14, and Hubbard printed pp.475–476 were inspected; Levin Theorem 3 p.277 was read in indexed primary text, direct PDF/page image and bytes unavailable. Exact PDF fingerprints are checked by CI, not independently downloaded by the referee. Proposition 6.2/Corollary 6.3 are used only at their stated admitted-tower interface, not certified anew, and the attachment lift remains an assumption. The identity-chart example defeats the unrestricted one-step assertion, not compactness of any physically realized pair family or of a common infinite itinerary. The homology mismatch alone is not a counterexample to T. All source registration remains METADATA. Review and edits AI-assisted (GPT-6.2); no human specialist certification.
