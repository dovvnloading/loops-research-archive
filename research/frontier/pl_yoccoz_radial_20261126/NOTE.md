# Polynomial-like Yoccoz radial audit

**Final mathematical label: OBSTRUCTED (the sufficient uniform ordinary fundamental-annulus modulus lower-bound route, on actual BLOT satellite cycles); actual uniform 1/q multiplier estimate OPEN. METADATA only.** The audited PL estimates do not prove the requested uniform bound. A uniform positive ordinary fundamental-annulus modulus would suffice, but BLOT precludes it at sufficiently large actual satellite levels satisfying its geometric hypotheses on this address. An explicit modulus-dependent upper envelope derived below also loses its uniform coefficient. This does NOT show that the true multiplier inequality fails, that the actual multiplier constant, optimal straightening distortion, or external expansion must diverge, or that all PL methods are obstructed.

**Limits.** METADATA, no bridge or ledger promotion. The result concerns genuine nested connected quadratic-like returns with the marked satellite access cycle. No realization/uniqueness result for a formal address; no whole-copy bound at parameters without the parent PL hypothesis or the requisite access marking; no angular estimate (#138), verification of the QG hypotheses, Prop.6.2/6.10 entrance or uniform near-parabolic entry, remaining CS induction, Theorem D, rigidity, nonrigidity, or MLC. Finite samples are evidence only. Degeneration of an upper-bound formula is not a multiplier lower bound.

## 1. Physical multiplier and indexing

Following merged #127, #135, #136, #138, #139 and their reviews, let q_n=n+2, p_n=1, k_1=1, k_n=product_{j<n} q_j. CS (31)–(32), printed p.52, refer to the **dividing period-k_n cycle**, not the child period-k_n q_n cycle. Write a_n for the marked dividing point, rho_n=(f^{k_n})'(a_n), z_n=log(rho_n)/(2 pi i) with the access-marked lift. The degree-two parent restriction F=f^{k_n}:U->V has fixed point a_n and exactly that derivative, not a k_n-th root. A conformal change preserves the multiplier. A hybrid straightening is not generally holomorphic near a repelling point (vanishing Beltrami coefficient a.e. on the filled set does not imply that); its polynomial's multiplier need not be rho_n. At the satellite root the marked parabolic lift is 1/q_n; below we work with repelling dividing points. At n=1 the original quadratic is already a polynomial.

CS gives a tangent disk with center p_n/q_n-iR and radius R=k_n log(2)/(2 pi q_n). In Prop.6.7(b), p.63, the one-digit continued fraction 1/q_n has terminal radial test |z_n|; see #136 and #138 for independent angular and entry issues. The desired |z_n-1/q_n|<=C/q_n would imply |z_n|<=(1+C)/q_n and hence eventual radial smallness at any fixed positive radius on the class on which the estimate holds.

## 2. Published results: what the constant actually is

* G. M. Levin, *Boundaries for multipliers of periodic points of holomorphic mappings*, Siberian Mathematical Journal 31 (1990), 273–278, [author PDF](https://www.ma.huji.ac.il/~levin/Levin1990_Article_BoundariesForMultipliersOfPeri), [DOI](https://doi.org/10.1007/BF00970657). §5, **Theorem 3, printed p.277**, and (2), p.273: for a degree-d PL map with connected filled set, a repelling period-l point with r accesses satisfies log|lambda| <= (2 K l/r) log d, where K is the dilatation of a QC straightening conjugacy on neighborhoods of the filled sets. Here l=1, d=2, and r=q_n for a single q_n-access orbit with no other accesses (r>=q_n suffices if there are additional accesses). This is a published PL theorem, but a real log-modulus inequality alone cannot control the argument. Its K is not the collar modulus. Lemma 1 pp.274–275 uses the complex log and canonical access sectors.
* J. H. Hubbard, *Local connectivity of Julia sets and bifurcation loci: three theorems of J.-C. Yoccoz*, in Topological Methods in Modern Mathematics (1993), 467–511, [PDF](https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf), Theorem I.A–B p.470, Props.3.2,3.3 p.475 and 3.5, §3.6 p.476: the polynomial proof gives Re tau/|tau-2 pi i p/q|^2 >= h q/(2 log d) for the appropriate logarithm tau, where h is the number of cycles of accesses. For a single access orbit (h=1) it identifies an annulus of modulus pi/(q log d) in the multiplier torus with primitive slope q log(lambda)-2 pi i p. The maximal modulus for this slope is 2 pi Re log(lambda)/|q log(lambda)-2 pi i p|^2. Throughout this note the ordinary modulus of a round annulus is log(R/r)/(2 pi).
* M. Lyubich, *Dynamics of quadratic polynomials I–II*, Acta Math. 178 (1997), 185–297, [PDF](https://commack.math.stonybrook.edu/~mlyubich/papers/acta.pdf), Proposition 2.5 p.196: if mod(F)>=mu>0 (supremum over representatives of the quadratic-like germ), its hybrid-class Teichmüller distance to its straightening is <=C(mu), depending only on mu, with C(mu)->0 as mu->infinity. The distance is inf log Dil(h), so a single collar m gives a sufficient bound exp(C(m)+epsilon) for every epsilon>0. This is qualitative dependence, NOT a closed-form small-m formula or a lower bound on actual distortion.
* A. Douady and J. H. Hubbard, *On the dynamics of polynomial-like mappings*, Ann. Sci. ÉNS 18 (1985), 287–343, [PDF](https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf), external equivalence p.297: uniformize the exterior of a connected filled set and reflect the covering across its inner circle to obtain a real-analytic expanding degree-d circle map. Their logarithmic width convention on that page is 2 pi times our ordinary modulus.

Sources opened, not citations from memory; Hubbard, Lyubich and DH page renderings inspected. Levin's theorem located in the opened PDF's text (printed page footer; screenshot unavailable). No claim that any of these sources states an explicit closed-form disk coefficient in ordinary m. The following is a derivation, not a quotation of an unpublished formula.

### 2.1 Complex disk via straightening

Take a repelling fixed point with q accesses in one rotation orbit p/q. Put tau=log rho, Re tau>0. Its holomorphic linearizer, punctured and quotiented by multiplication by rho, is the torus C/(2 pi i Z+tau Z), area 2 pi Re tau. A primitive annulus of core displacement q tau-2 pi i p has modulus at most 2 pi Re tau/|q tau-2 pi i p|^2 (flat metric/extremal length, Hubbard Props.3.2–3.3). An orientation-preserving K-QC straightening conjugacy on neighborhoods induces a K-QC map of the local multiplier tori: conjugate the repelling germs in linearizers and extend equivariantly on the punctured planes by multiplication. It preserves the meridian and the marked access core. Hubbard's polynomial annulus pulls back with modulus at least pi/(K q log 2). Hence

    |tau-2 pi i p/q|^2 <= 2 K log(2) Re tau/q,
    |z-(p/q-i K log(2)/(2 pi q))| <= K log(2)/(2 pi q),
    |z-p/q| <= K log(2)/(pi q).

This is the complex PL estimate derived from the published torus proof; its vertical extent agrees with Levin Thm.3. Taking the infimum and using Lyubich gives the same closed disk with K replaced by exp(C(m)); no factor k_n. For n=1 take K=1.

The marked core fixes the integer log ambiguity. Use the parent point whose accesses rotate by p/q in the CS nested-renormalization construction (CS pp.48–49, (31)–(32) p.52). The correspondence of the ordered marked access cycle (including distinct parent prime ends) and its lift is required; an arbitrary original-plane external ray does not automatically identify all distinct parent prime ends. Compare the lifts using this common access marking, not arbitrary principal logs. The same physical germ and meridian give the same lift when that marking agrees. If the marking is not identified, the estimate is for the parent marked access lift only. No universal parameter-boundary continuation is asserted.

## 3. Explicit ordinary-collar envelope (derived, not attributed)

An explicit sufficient estimate can be given without asserting that Lyubich's C(mu) has a published formula. Let F:U->V have connected full filled set J_filled, degree 2, m=mod(V\overline U)>0 and the marked satellite access cycle above. Use Jordan representatives. Uniformize V\J_filled as a round annulus 1<|w|<exp(L), L=2 pi mod(V\J_filled). The unbranched degree-two covering F:U\J_filled -> V\J_filled shows the inner annulus has logarithmic width L/2. The serial modulus inequality yields L/2>=2 pi m. In logarithmic coordinates the inner annulus is the strip 0<Re w<L/2 modulo 2 pi i. Lift its inclusion into the outer annulus to H with

    0<Re H<L, H(w+2 pi i)=H(w)+2 pi i, Re H(iy)=0.

It reflects across the inner circle, and F in the two round coordinates has lift w -> 2w+i theta. Thus the external circle map g has positive angular derivative g'(H(iy))=2/H'(iy), with H'(iy)>0, and expanding periodic access multiplier eta=(g^q)'(xi)>1 (DH p.297).

Let t=min(pi m, pi^2/2), A=pi^2/(2t)=max(1,pi/(2m)); t<L/2. u=Re H is positive for 0<x<=t, vanishes at x=0, is periodic in y, and has average t at x=t: Cauchy–Riemann and the degree-one translation property give mean derivative in x equal to 1. The right-boundary strip Poisson kernel is

    P(x,v)=sin(pi x/t)/(2t[cosh(pi v/t)+cos(pi x/t)]).

This is the half-plane Poisson kernel pulled back to the strip. Its derivative at x=0 is (pi/(4t^2)) sech^2(pi v/(2t)). Convolving with the bounded periodic top data solves the Dirichlet problem by uniqueness on the periodic cylinder. Differentiate at x=0, restrict the nonnegative integral to -pi<=v<=pi, use the mean t, obtaining

    H'(iy)=u_x(0,y)>=A sech^2 A,
    g'<=D(m):=2 cosh^2(A)/A,
    log eta<=q log D(m).

Use the external round-coordinate inverse and a linearizer of g^q at the marked repelling external periodic point. Small closed subsectors of opening pi-2 epsilon on the external side approach the physical landing point by the Lindelöf angular-limit principle (the bounded exterior conformal map has the asymptotic value along the landing access). Quotienting the sector by eta-dilation gives an annulus conformally embedded in the physical multiplier torus. Indeed, if two sector points are identified by rho^j, shrink both by inverse q-returns into the physical linearizer neighborhood; the intermediate finite iterates cycle through distinct external accesses, so j must be a multiple of q. Those identifications are exactly the eta-dilation identifications. Its modulus is (pi-2 epsilon)/log eta and its marked core is q tau-2 pi i p. Let epsilon decrease to zero and apply the same torus area bound:

    pi/log eta <= 2 pi Re tau/|q tau-2 pi i p|^2,
    |tau-2 pi i p/q|^2 <= 2 log eta Re tau/q^2,
    |z-(p/q-i E/(2 pi q))| <= E/(2 pi q),
    E=(log eta)/q <= log D(m).

Tangent disks are nested with increasing E. Thus the explicit, not sharp, sufficient ordinary-modulus bound is

    |z-p/q| <= log D(m)/(pi q),
    |z| <= [sqrt(p^2+(log D(m)/(2 pi))^2)+log D(m)/(2 pi)]/q.

This is an elementary derived bound under the marked-access hypothesis, not a published formula or an optimality assertion. The independent straightening estimate in §2.1 does not depend on this calculation.

## 4. BLOT and the lower-bound question

Blokh–Levin–Oversteegen–Timorin, CMP 406:141 (2025), [version of record](https://publications.hse.ru/pubs/share/direct/1052158150.pdf), [DOI](https://doi.org/10.1007/s00220-025-05303-8), Main Theorem p.2 and satellite/degree hypotheses p.6, audited in #127. For a genuine satellite PL cycle of period k around a repelling base cycle of period k/s, with s>=2 distinct little filled sets meeting at each base point, pairwise intersections only at base points, connected filled sets, non-separation in each member and the degree-two hypothesis,

    m <= mod(U\J_filled) < B(s)=2 pi/log(4(s+1)).

Apply at **parent** level n-1, k=k_n, base period k_{n-1}, s=q_{n-1}=n+1, not q_n. For genuine cycles satisfying the BLOT hypotheses this tends to zero on the linear address; even the supremum over ordinary representatives is <=B(s). Therefore the sufficient hypothesis "there is mu>0 and for every sufficiently large n there is a parent representative with m_{n-1}>=mu" **fails** at sufficiently large actual levels satisfying BLOT, even along one realized infinite address with those hypotheses. A fortiori it cannot hold uniformly across such realizing parameters. This is conditional on genuine cycles with the stated geometry, not a realization theorem for formal combinatorics. Do not substitute an upper bound for m into a decreasing multiplier envelope as if it were a lower bound. Dudko–Lyubich, *MLC at Feigenbaum points*, [arXiv:2309.02107v3](https://arxiv.org/pdf/2309.02107v3), definition pp.2–3, Theorem A p.3, proves ordinary a priori beau bounds for bounded renormalization combinatorics, not this unbounded relative-period address. No other positive uniform ordinary lower bound can be compatible with BLOT on these cycles.

For §3, A>=max(1,log(4(s+1))/4); d log D/dA=2 tanh A-1/A>0 for A>=1. Thus the coefficient log D(m)/pi is at least log D(B(s))/pi, tending to infinity (~log s/(2 pi), up to O(log log s)). This is a lower bound on an **available upper-bound coefficient**, not on the true multiplier or optimal coefficient. BLOT makes this sufficient m-only route nonuniform. It does not prove K or actual external expansion diverges; thin collars of polynomial germs do not force hybrid distortion. The sufficient alternative input sup_n (log eta_n)/q_n<infinity, or sup_n K_n<infinity for §2.1, is not ruled out by BLOT, but not established here. No universal impossibility of a sharper PL inequality is claimed.

Even the weaker terminal requirement |z_n|->0 could follow from q_n m_{n-1}->infinity via §3 (log D=O(1+1/m)), for example m>=c/log(q_n), 0<c<2 pi, compatible asymptotically with BLOT and giving O(log q_n/q_n). Such a lower bound is not established. The uniform 1/q_n scaling is stronger; no failure of actual radial convergence is inferred.

## 5. Comparison with #139

For E>=0 the maximal q|z| in a tangent disk is sqrt(1+(E/(2 pi))^2)+E/(2 pi). At E=log 2 (the polynomial estimate, not asserted for PL) this is about 1.11638. The linear max-radial points from the reviewed summary give the following. E_req=pi q |z-1/q|^2/(-Im z) is the smallest disk parameter containing that individual point. These are not maxima of displacement or E_req over all samples.

|q|child period|q times sampled max|q times displacement at that point|E_req|
|---:|---:|---:|---:|---:|
|3|3|1.04327548|0.06743927|0.270539|
|4|12|1.03475585|0.05457269|0.218656|
|5|60|1.02825340|0.04453696|0.178522|
|6|360|1.02379633|0.03745929|0.150613|
|7|2520|1.02057366|0.03228730|0.130290|

These particular points fit even E=log 2. That does not imply K=1 or every point fits that disk. At B(s) the §3 optimistic envelope has A=1 on the four noninitial rows; the actual m is unknown so the actual envelope may be much larger. The verifier prints the optimistic q|z| coefficients; they are lower bounds on upper envelopes. At q=7 the original CS disk permits |z| about 11.3488, versus observed max about 0.1457962. The marked PL estimate removes the absolute period factor but lacks the uniform modulus input. No extrapolation from finite samples. Numeric checks are not proofs of the conformal arguments.

## 6. Inputs and reproduction

Independent review of head 25d5f8cd5011774a4d540c118d1986818ffab3ec against main def5d4633e1ed0613ced4d11d22626e5114efb19: [full written review](https://github.com/dovvnloading/loops-research-archive/pull/140#issuecomment-7183698711). See merged PRs [127](https://github.com/dovvnloading/loops-research-archive/pull/127), [135](https://github.com/dovvnloading/loops-research-archive/pull/135), [136](https://github.com/dovvnloading/loops-research-archive/pull/136), [138](https://github.com/dovvnloading/loops-research-archive/pull/138), [139](https://github.com/dovvnloading/loops-research-archive/pull/139), including reviews.

* CS [arXiv:1509.07843v1](https://arxiv.org/pdf/1509.07843v1), pp.48–49, 51–52 (Thm.4.6, (31)–(32)), p.63 Prop.6.7: SHA256 71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f (831082 bytes, #136 lock).
* BLOT published PDF above, pp.2,6: SHA256 9d0aa40f94afbfb918fd26dbc96b14727b2a59b84b02da8ad93b6b528061adb0 (1056824 bytes, #127 CI).
* #139 summary.json SHA256 0adb0c726fd7146d9960e432a7b25d2f0532dbd8641cf01ee3e02843603a4bbf (reviewed, verified by script). Raw SHA256 3f6a33759c6bf0129830d3670996dace5c61e53c839b19420077f3fb32bbfe61 (inherited from the #139 review; not newly independently hashed here and not used by this verifier).
* New PDF inputs (Levin pp.273,277; Hubbard pp.470,475–476; Lyubich p.196; DH p.297; DL pp.2–3) identified by exact links above. Their primary texts were read. The independent review records fresh CI byte fingerprints and page counts from [audit run 45762921945](https://github.com/dovvnloading/loops-research-archive/actions/runs/45762921945) and its [source manifest](https://github.com/dovvnloading/loops-research-archive/actions/runs/45762921945/artifacts/15090960950), transcribed in [sources.lock.json](sources.lock.json): CS v1 and BLOT match the inherited locks; Hubbard, Lyubich, Douady–Hubbard and Dudko–Lyubich v3 are recorded as reviewed. The unversioned rendered CS PDF identifies v1; the exact-version CI download matches the inherited hash. Levin 1990 remains **UNVERIFIED byte hash (primary text read)**: SSL certificate hostname mismatch and unavailable page screenshot, no invented hash. The workflow still prints and uploads pl-yoccoz-sources.json with SHA256, URLs, byte counts, and page counts for exact downloads; inherited hashes are checked when downloaded. The committed lock is a record of the review's fingerprints, not a claim that the script checks every new lock entry. A web rendering is not a byte fingerprint. Source fingerprinting is not mathematical verification.

From repo root:

    python3.12 -B research/frontier/pl_yoccoz_radial_20261126/verify.py
    python3.12 -m pip install -r research/frontier/pl_yoccoz_radial_20261126/requirements.txt
    python3.12 -B research/frontier/pl_yoccoz_radial_20261126/verify.py --sources /tmp/pl-yoccoz-sources.json
    python3.12 -B code/verify_physical_bridges.py

Workflow: ubuntu-latest, Python 3.12, pinned PDF parser and actions, contents read, no write-back. The push path filter covers the research directory; the PR filter sees the full research diff, so one branch update can trigger both audit runs. workflow_dispatch available. No suppression of other existing workflows.

**Final mathematical label: OBSTRUCTED (the sufficient uniform ordinary fundamental-annulus modulus lower-bound route, on actual BLOT satellite cycles); actual uniform 1/q multiplier estimate OPEN. METADATA only.** Whole-copy and infinite-tail uniformity remain OPEN. No angular repair, Theorem D, rigidity/nonrigidity, MLC, or ledger status change. GPT-6.2 assisted source reading, derivation, verification code and review-alignment editing; the linked independent review was AI-assisted, not human specialist certification.
