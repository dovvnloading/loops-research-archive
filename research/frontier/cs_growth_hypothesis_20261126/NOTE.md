# CS Theorem D: where cross-level quadratic growth is spent

**Verdict (a): LINEAR GROWTH BREAKS THE METHOD at the full PLY-disk smallness step, Proposition 6.7, Steps 2–3.** For one-digit satellite rotations the exact scalar obstruction is the unbounded ratio of the product of previous denominators to the current denominator, not a sum of reciprocals. Intermediate polynomial and log-corrected linear rates fail too. The recurrence q_(i+1) >= q_i^2 is stronger than necessary for this particular *radial* estimate. A separate angular/induction issue in Proposition 6.10 prevents certifying an extension of Theorem D even for the weaker radial class. Status: **OPEN (MLC); proved elementary estimate obstruction, source-reading audit; conditional transfer only.** No change to the ledger or to another thread.

## Scope, limits and inputs

Target: [merged #135](https://github.com/dovvnloading/loops-research-archive/pull/135), [note](../residual_satellite_status_20261126/NOTE.md) and [review discussion](https://github.com/dovvnloading/loops-research-archive/pull/135#issuecomment-7182397334). Base main e3a58c073981fa9972e6f78f5b4caf5c69e50503. This drills into the proof of the imported sufficient statement, not its necessity in dynamics. The whole class of PL (polynomial-like) parameters must be controlled, not merely the NP (near-parabolic) representative supplied by the existential Theorem C (v1 p.5; author p.4). The intended address consists entirely of t_i=1/q_i, integer q_i>=3, and maximal successive satellite levels. No new claim of rigidity, MLC, JLC, nonrigidity, or counterexample to CS is made. The source-reading is AI-assisted (ChatGPT, GPT-6.2); no independent human mathematical verification performed. The verifier is registered as METADATA, not as a physical bridge.

Two primary editions (printed pages throughout; PDF page index = printed page minus one):
* V: [arXiv:1509.07843](https://arxiv.org/abs/1509.07843), [v1 PDF](https://arxiv.org/pdf/1509.07843v1), [rendered unversioned PDF identifying itself as v1](https://arxiv.org/pdf/1509.07843), 25 Sep 2015 arXiv stamp, internal date July 19, 2018 per #135. The exact versioned URL was UNVERIFIED by web reader (disabled), but the unversioned PDF was opened and the v1 stamp checked. The exact versioned bytes are separately fetched by CI.
* A: [author PDF](https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf), internal date 9 September 2022, 71 pages, not arXiv v2. Opened and compared at the cited locators. Journal publication UNVERIFIED.

SHA256 input fingerprints already recorded by #135 CI (not claimed to be hashes of the web screenshots):

| Input | SHA256 from #135 | Bytes |
|---|---|---:|
| V exact versioned URL | 71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f | 831082 |
| A | b1d6b0952247efc3cd7a6e0602dbb8246b43b9edf7b3c5d0da942cc822246c25 | 851587 |

The fresh CI byte record is [sources.lock.json](sources.lock.json): exact URL, resolved URL, byte count, SHA256, and whether it matches #135. Any unavailable input is marked UNVERIFIED there, not silently treated as matching. Local sandbox DNS failed; fresh byte retrieval is delegated to the branch workflow, not asserted from web rendering. No third-party PDF is committed. The text and byte checks are independent. Both displayed editions have been read in §4.5, §5.1 and the decisive §6.4–6.5 passages. Earlier analytic results are used at their stated interface, not independently reproved.

## 1. Trace of the growth hypothesis

Use k_i=P_(i-1)=product_(j<i) q_j, P_0=1; gamma=log(2)/(2*pi). Distinguish the real rational t_i from the analytic logarithmic multiplier z_i=(log rho_i)/(2*pi*i_complex) of the i-th dividing cycle. The absolute period of that cycle is k_i. This is V Theorem 4.6 pp.51–52, (31)–(32) p.52; A Theorem 4.6 p.51, (4.1) p.51, (4.2) p.52. PLY (Pommerenke–Levin–Yoccoz) gives the following *outer bound*, for a suitable log branch:

    z_i in D_i = closed disk(center=t_i - i_complex R_i, radius=R_i),
    R_i = gamma k_i/q_i.

The quadratic factor log 2 comes from degree 2 of the original polynomial. Replacing absolute period k_i by the relative denominator of the previous return, or applying a degree-two polynomial multiplier bound directly to a PL return in arbitrary geometry, is not justified here.

V Theorem D p.6 and (44) p.62; A Theorem D p.6 and (6.8) p.62: QG_N requires first digit >=N, successive signed CF digits within each level to grow at least by squaring, and first digit of the next level >=q_i^2. For t_i=1/q_i the signed Gauss step G(t_i)=-q_i+q_i=0, so m_i=1, b_(i,1)=q_i (V §6.1 (38) p.56; A (6.1) p.55). No intermediate top NP step: the type is all b (V §6.3 (42)–(43) pp.58–59; A (6.5)–(6.6) p.58). The within-level condition is vacuous and the cross-level condition is exactly q_(i+1)>=q_i^2.

### Audit of the proof uses (including the unused mixed-CF branch)

| Dependency / proof step | V locator | A locator | Role |
|---|---|---|---|
| A(r) cone and NP prerequisites | pp.2–3, Theorem 2.9 / Def.2.11 | pp.2–3, Theorem 2.9 / Def.2.11 | Need complex rotation in 0<abs(alpha)<=r, abs(Re alpha)>=abs(Im alpha); uniform small radius, not average |
| PLY bound | Thm 4.6, (31)–(32), pp.51–52 | Thm 4.6, (4.1)–(4.2), pp.51–52 | supplies absolute-period disk |
| Lemma 6.4 | p.61 | pp.60–61 | magnitude and angular bounds for Gauss cylinder disks; no cross-level assumption |
| Lemma 6.5 | p.62 | p.61 | within a single finite CF of length n, b_(j+1)>=b_j^2 gives abs(x_(j+1))<=abs(x_j)^2(1+C/b_j); telescope and bound exp(sum C/b_j) uniformly; for n=1 identity, no cross-level summation |
| Lemma 6.6 | p.62 | p.62 | distortion of Gauss iterates on cylinder disks; stated without growth condition |
| Proposition 6.7 initial choices and Step 1 | (45)–(48) p.63 | (6.9)–(6.12) p.63 | choose N large; all digits >=N by QG; only uniform high type used in magnitude of rational tails |
| Proposition 6.7 Step 2 | (49) p.63, (50)–(51) p.64 | (6.13)–(6.15) p.63 | **direct cross-level use:** next denominator >= previous square, giving R_i<=gamma/N via telescoping product |
| Proposition 6.7 Step 3 | p.64 | p.63 | one-digit case: part (a) vacuous; part (b) is abs(z)<=r for entire D_i. Ends one-digit proof |
| Proposition 6.7 Steps 4–6 | (52)–(58), pp.64–65 | (6.16)–(6.22), pp.64–65 | m_i>1 only: Gauss inverse radius proportional to r*x_(i,m_i-1)^2; last digit and uniform high type bound distance of rational to truncation |
| Proposition 6.7 Steps 7–8 | (59) and preceding chain, p.66 | (6.23) and preceding chain, p.65 | m_i>1 only: uses (49)/(6.13) to replace k_i/b_(i,1) by k_i/q_(i-1)^2, then (51)/(6.15) to bound it; invokes Lemma 6.5 to control last-digit factor; gets inclusion in inverse Gauss disk and Lemma 6.4 cone at intermediate steps |
| Proposition 6.10 | pp.67–68 | pp.66–67 | imports Prop.6.7 at r=min(r3,r5) for initialization, intermediate top steps and each new bottom induction; uses Lemma 6.8 and the multiplier identification Prop.6.2/Cor.6.3 (A explicit); see gap below |
| Proposition 6.11 | p.68 | p.67 | whole-class NP containment -> singleton via Theorem 5.1; no new QG arithmetic |
| Theorem 5.1 / Cor.5.3 | pp.54–55 | pp.54–55 | connected components in horizontal slice shrink by uniform expansion with rotations in A(r4); no CF rate condition in statement |
| Proposition 4.3 | pp.50–51 | pp.50–51 | singleton nested copies -> parameter LC, independent of growth |

For multi-digit CFs the within-level summability is real, but it is *not* a summability over the successive PL levels. Lemma 6.5 is used at Step 7 only, never at Step 3. The table traces both the direct and downstream uses; no proposed weakening for arbitrary m_i is certified. Theorems A/B and NP contraction/expansion are not re-proved here. The proof interface, rather than an area estimate or modulus bound, is the entrance to a uniform analytic domain.

## 2. Isolate the precise one-digit radial condition

Let S_i=P_(i-1)/q_i. Then

    S_1=1/q_1,
    S_(i+1)=S_i * q_i^2/q_(i+1),
    S_i=(1/q_1) product_(j=1)^(i-1) (q_j^2/q_(j+1)).

The last equality is exact (cancel adjacent factors). This is the product in V (51) and A (6.15), using PLY's k_i, not the product of distortions across renormalizations. QG gives S_(i+1)<=S_i, hence sup_i S_i<=1/q_1<=1/N.

The source chooses all digits sufficiently large and uses a uniform radius budget. A simple sufficient replacement for Steps 1–3, for any fixed 0<r<1/2, is

    sup_i 1/q_i <= r/3,   sup_i gamma*S_i <= r/3.             (RAD-simple)

Then every z in D_i has abs(z)<=1/q_i+2R_i<=r. The exact necessary and sufficient condition for the *full disk* to satisfy part (b) of Prop.6.7 at every level is

    sup_i (sqrt(q_i^(-2)+gamma^2*S_i^2)+gamma*S_i) <= r.      (RAD-exact)

Equivalently, for each i, 1/q_i<=r and gamma*S_i<=(r^2-1/q_i^2)/(2r). Proof: the maximum distance to zero on a closed disk is the distance of its center to zero plus its radius, and squaring the rearranged nonnegative inequality gives the formula. This is sharp for this outer-bound method, not necessarily for the actual multiplier locus. In particular sup_i S_i must be finite and small on the chosen tail. For bounded S_i, resetting the tail at J divides all surviving ratios by P_(J-1), making RAD-simple true for sufficiently large J (bounded S_i also forces q_i->infinity). For an unbounded S_i no fixed finite tail can make it bounded.

For comparison the precise product-bound form is

    q_i >= P_(i-1)/delta for every i
    iff sup_i S_i <= delta
    iff sup_i sum_(j<i) log(q_j^2/q_(j+1)) <= log(delta*q_1).

This is a uniform one-sided bound on partial sums of signed logs, not absolute summability or a p-series. It permits some steps with q_(i+1)<q_i^2. Example: q_1=L, q_2=L^2-1, q_i=L*P_(i-1) for i>=3. Then S_1=1/L, S_2=L/(L^2-1)<=2/L, all later S_i=1/L; first cross-level square fails. Thus radial weakening is strict for fixed start, but requires product-scale growth. It does not by itself extend D (see §4).

A growth threshold: if S_i<=delta<infinity eventually, P_i>=P_(i-1)^2/delta eventually. Choose J with P_J>delta; then P_(J+n)/delta >= (P_J/delta)^(2^n). Consequently q_(J+n+1)>=P_(J+n)/delta and log q_i grows at least on the scale 2^i up to a positive constant depending on the tail. Mere double-exponential order is not a sufficient criterion: the exact product bound decides. E.g. q_i=L^(2^(i-1)) has equality S_i=1/L, while a long pattern of deficits in q_(i+1)/q_i^2 may make S_i unbounded. This threshold is about the absolute period, not q_i comparable to i^2.

## 3. Exact evaluation for all requested regimes

Let L>=3. For linear q_i=L+i-1,

    S_i = (L+i-2)! / ((L-1)! (L+i-1)),
    S_(i+1)/S_i=q_i^2/(q_i+1)>=2   (q_i>=3).

The last inequality follows from q^2-2q-2>=1 at q=3 and increasing thereafter. Thus S_i>=2^(i-1)/L -> infinity on every tail. The smallness gate fails even if all denominators exceed any fixed high-type threshold.

For q_i~i^a (1<a<2), q_i~i*(log i)^2, and ordinary quadratic q_i~i^2, eventually q_i<=C i^3 for some fixed C: for log-corrected linear growth use log i<=i for i>=1. With all q_j>=2, S_i>=2^(i-1)/(C i^3)->infinity. To make this asymptotic inequality exact without floating point, 2^(i-1)>=(i-1 choose 4) for i>=5, and (i-1 choose 4)>=i^4/(16*24) for i>=8. This gives a lower bound i/(384 C) eventually. This also works for any fixed polynomial exponent by choosing a higher binomial term. Any finite prefix reset preserves divergence. Note sum 1/q_i converges for 1<a<=2 and i log^2 i by integral comparison, but that fact is irrelevant to the required product bound. For linear the reciprocal sum diverges, but it is not the reason this proof stops.

For the actual quadratic *cross-level recurrence* q_(i+1)>=q_i^2, q_1>=N, S_i<=1/N exactly; for equality q_i=L^(2^(i-1)), S_i=1/L at all i. Choose L large enough for RAD-simple (or use the paper's N). This passes radial smallness, not the angular check discussed next.

Certified failure: gamma>1/16 follows from log 2=integral_1^2 dx/x>1/2 and pi<4. The bottom point t_i-2*i_complex*R_i in D_i has modulus >=2R_i>S_i/8. Hence whenever S_i>=4, that point lies outside every disk of radius r<1/2. No improved constant in (51)/(6.15), radius/diameter bookkeeping, or choice of fixed r can remedy divergence of S_i. This establishes verdict (a) for the **use of the full PLY disk**. It is not a lower bound on actual multiplier size, and narrower multiplier loci or an entirely new estimate could avoid it; none is supplied here. The distinction is essential: the proof's estimate is insufficient, not proven dynamically optimal.

The exact integer/Fraction regression in verify.py covers L=3,10,100; 64 levels of linear, floor(i^(3/2)), i*(bit_length(i))^2 and i^2 (the latter two plus L; bit-length is a constant-factor log proxy); 10 exact recurrence levels and a non-QG example. The asymptotic proof above covers the entire requested real-exponent and log growth classes, independent of rounding, constants or finite sample. Arithmetic is deterministic; no seeds, tolerances or floating-point tests.

## 4. Separate angular and source-induction limitations (do not silently promote radial gate)

In V p.63 and A p.62 Prop.6.7(a) quantifies 0<=n_i<=m_i-2, so for m_i=1 it says nothing about angle. Part (b) is radial only. Yet in Prop.6.10 (V p.67, A p.67) the proof invokes Prop.6.7 at n_j=0 to infer beta_(l_j+1) in A(r5), then Lemma 6.8. This invocation needs an angular premise when the relevant digit length is one. No such premise follows from the full disk estimate, even for sequences meeting QG.

Indeed the center has real part 1/q_i, imaginary magnitude R_i=gamma*k_i/q_i. For k_i>16 the center is outside the double cone because gamma>1/16. Even a rational witness z=1/q_i-i_complex*k_i/(16 q_i) is inside D_i and outside the cone for k_i>16. The exact condition for a disk tangent at x>0 to lie wholly in the positive 45-degree cone is R<=x/(1+sqrt(2)): the distance of center (x,-R) to line y=-x is (x-R)/sqrt(2), which must be at least R. For R=gamma*k_i*x this condition eventually fails for every infinite sequence q_i>=3, including QG. The disk point is not asserted to be an actual multiplier. Figure 8 illustrates only k=1 (rho_1); it cannot justify subsequent levels. The full-disk angular inference cannot be repaired by increasing q_i alone. A stronger analytic estimate for the actual multiplier or a different admissible NP-domain argument would be needed.

There are additional source-reading cautions:
* V Step 3 calls its radius budget a diameter budget, whereas A Step 3 uses radius r/3 and the full 2r/3 displacement. Both radial conclusions can be justified by choosing N sufficiently large, or by RAD-exact; the numerical factor 2 does not affect divergence. A (6.15) prints the product equality; V (51) prints an inequality at that point, although the product identity is exact. V (45)–(47) use r/2; A (6.9)–(6.11) use r/3 and remove factors 4/3 and 5/4 in the mixed branch. The within-level proof of Lemma 6.5 in both editions uses reciprocal-digit summability; the displayed elementary lower-bound algebra has apparent sign typos, not used here.
* V Lemma 6.8 p.66 has an apparent sign typo (Im beta>=0 despite both multipliers >=1); A p.66 has Im beta<=0. Lemma 6.8 itself assumes f already in A(r1) times the nonlinear class (or the specified quadratic family), plus nonattracting fixed points and beta in A(r5). It cannot be applied merely from radial smallness without checking these hypotheses. V p.67 writes rho_(j+1) in the induction; A p.67 cites Cor.6.3 and writes rho_j, matching its printed identity (Prop.6.2 p.59, Cor.6.3 pp.59–60). The PLY bound for rho_j is tied to t_j, not automatically to t_(j+1). Prop.6.2 explicitly has a rotation-domain antecedent on alpha_(l_k+1); invoking a version of that identification to prove this very domain requires justification. These indexing/domain concerns are noted as printed, not a proof that the theorem is false. The necessary repairs are UNVERIFIED.
* At initialization the text moves from the PLY estimate for beta_1 to alpha in A(r3); even for the quadratic family they are distinct logarithmic multipliers. The actual normalization and appropriate branch must be respected; no claim that the disk bounds alpha directly. The source's Proposition 6.11 uses A(r3) while Theorem 5.1/Cor.5.3 use A(r4); in a conditional application one must arrange the smaller expansion radius from Proposition 3.1, not assume the symbols are interchangeable.
* Theorem 5.1's proof is for a connected component/horizontal curve; the displayed diameter inequality without component restriction would be inconsistent with a Cantor slice containing distinct components. Only the connected-component argument and its stated conditional Cor.5.3 are relevant; a fresh proof of the full geometric rate for weaker assumptions is UNVERIFIED.

Conditional continuation only: if, for every parameter in the nested PL class, a compatible all-bottom tower is defined with each alpha_i in the uniform expansion domain A(r4) of Theorem 5.1 (and consistent multiplier/branch identifications), its connected intersection is a singleton by that theorem / Cor.5.3 and Proposition 6.11; then Proposition 4.3 gives MLC. For geometric rate one must check the finite-level connected inclusion and uniform horizontal expansion. Neither RAD-simple nor RAD-exact establishes these hypotheses. In particular this note is **not** verdict (b) for the complete rigidity theorem. The printed angular issue does not alter the rigor of the independent radial obstruction, and does not refute the original theorem; the source may have an unstated additional argument. The entire analytic construction and any repair are outside this audit. The statement of Theorem D remains as previously recorded.

## 5. Reproduction and boundary

Python 3.12 (CI pinned 3.12.12 container); standard library only. From repository root:

    python3 -B research/frontier/cs_growth_hypothesis_20261126/verify.py
    python3 -B research/frontier/cs_growth_hypothesis_20261126/verify.py --lock
    python3 -B research/frontier/cs_growth_hypothesis_20261126/verify.py --check-lock
    python3 -B code/verify_physical_bridges.py

The second command downloads the two PDFs and regenerates sources.lock.json and arithmetic.json; run only with network. It records failures honestly. The branch CI has contents write permission and commits these two outputs if absent; the PR check verifies them without mutation. No source bytes or cache files are committed. Checks validate finite arithmetic and provenance schema, not the source proof. The matching-hash status, if any, is in the fresh lock. The original article's mathematical proof is not mechanically verified.

**Not established:** an extension of CS D to any new sequence; actual multiplier escape for linear growth; necessity of the PLY outer-disk estimate for another method; a repaired angular implication/induction; any arbitrary multi-digit weakening; rigidity or nonrigidity of the specified residual satellite address; MLC or JLC at that address; uniform moduli or area loss; journal publication status; exact-version web screenshot byte equality. No status of the residual atlas or any model-to-geometry theorem changes. The original #135 scope and finite-prefix limits remain intact.
