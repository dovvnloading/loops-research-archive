# CS Proposition 6.10 — audit of the angular step

**Verdict: BOUNDED NEGATIVE / OPEN for the full QG_N class.** The printed invocation of Proposition 6.7 does not establish the angular conclusion; even quadratic cross-level growth does not repair the full-disk argument. A short index-and-continuation repair of the one-digit induction is given below, **conditional on the multiplier identification Proposition 6.2 as stated** (an erratum-level repair at that interface, not independent certification of that proposition). For mixed continued fractions the terminal top step still requires the inequality (MIX) below. No actual quadratic counterexample or theorem-level gap has been established. No claim that Theorem D or MLC fails.

## Limits, inputs, status

Follow-up to [merged #136](https://github.com/dovvnloading/loops-research-archive/pull/136), including its [review](https://github.com/dovvnloading/loops-research-archive/pull/136#issuecomment-7182829462) and [NOTE](../cs_growth_hypothesis_20261126/NOTE.md). Initial main e4143efbddc55639581ea2471eea93206260eabd. Ledger target CHERAGHI_SHISHIKURA_QG_MLC; no ledger change. Independent of weakening growth rates. Both one-digit signs are included; QG means cross-level squaring, not q_i comparable to i^2. Status: OPEN / SOURCE-READING + exact scalar obstruction + conditional proof repair, METADATA only. AI-assisted (ChatGPT GPT-6.2); no human specialist verification. All pages below are printed pages, not zero-based indices.

Primary inputs, with SHA256 fingerprints inherited from #135/#136 and independently checked by the read-only workflow for this audit (local network DNS unavailable; see committed sources.lock.json). These are exact-version download fingerprints, not hashes of rendered screenshots.

| Source | exact download | bytes | SHA256 |
|---|---|---:|---|
| V: CS, v1 | https://arxiv.org/pdf/1509.07843v1 | 831082 | 71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f |
| A: CS, author edition dated 9 Sep 2022 | https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf | 851587 | b1d6b0952247efc3cd7a6e0602dbb8246b43b9edf7b3c5d0da942cc822246c25 |
| L: Levin, *Multipliers of periodic orbits of quadratic polynomials and the parameter plane*, v4 | https://arxiv.org/pdf/0710.4406v4 | 509484 | 8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd |

V rendered at https://arxiv.org/pdf/1509.07843 (v1 stamp, internal date 19 Jul 2018); exact versioned URL rendering UNVERIFIED. A is not arXiv v2. L read at https://arxiv.org/pdf/0710.4406, including pp.5, 7, 13–14 and Addendum p.1; exact versioned rendering and journal pagination UNVERIFIED. The cited derivative is L (20) p.14, attributed there to [13]; original [13] UNVERIFIED. No PDFs redistributed. The file lock records the previously verified bytes; CI checks equality, never commits. No independent human proof check. The primary-source comparison does not independently certify the analytic NP construction.

## 1. Statement and missing implications (both editions)

Write t_i=p_i/q_i=[(b_{i,j}:epsilon_{i,j})_{j=1}^{m_i}], using signed nearest-integer continued fractions, G(z)=-1/z-[Re(-1/z)]. Here q_i=q_{i,m_i}; k_i=product_{h<i}q_h; l_i=sum_{h<i}m_h (l_1=0). The type kappa has a b then m_i-1 t's for block i (V (42)–(43), pp.58–59; A (6.5)–(6.6), p.58). QG_N (V (44), p.62; A (6.8), p.62) consists of b_{1,1}>=N, b_{i,j+1}>=b_{i,j}^2 and b_{i+1,1}>=q_i^2. Set K_i=M(t_1,...,t_i), the closed tuned copies, and use their images in alpha coordinates M_alpha when writing NP inclusion. A(r) is 0<|z|<=r and |Im z|<=|Re z| (V/A pp.2–3).

**Exact statement in quantified mathematical transcription**, Prop.6.10 V p.67 and A p.66:
    
    Given r3>0 as in Theorem 2.9, exists integer N>0:
    for every <m_i:b_{i,j}:epsilon_{i,j}> in QG_N in (-1/2,1/2],
    for every integer k>=1,
    M_alpha(<m_i:b_{i,j}:epsilon_{i,j}>_{i=1}^k)
        subset Lambda^1_{r3}(<kappa_i>_{i=1}^{l_k}),
    where kappa=kappa(<m_i:b_{i,j}:epsilon_{i,j}>).

V prints Lambda without the superscript/subscript in the statement; A uses Lambda^1_{r3}. The definition of l_k is important: the displayed inclusion concerns the preceding k-1 blocks, not k blocks. The proof seeks to construct the next block inductively; below we use the stronger whole-copy one-digit induction.

Let z_i=(log rho_i)/(2*pi*i_complex) in the PLY branch, where rho_i is the multiplier of the dividing cycle nu_i of absolute period k_i (V Thm.4.6, (31)–(32) pp.51–52; A Thm.4.6, (4.1)–(4.2) pp.51–52). Put gamma=log(2)/(2*pi). The bound is

    z_i in D_i={z: |z-(t_i-i_complex*R_i)|<=R_i},
    R_i=gamma*k_i/q_i.                                          (PLY)

Prop.6.7 (V p.63, A p.62) asserts (a) modulus <=r and angle within pi/4 of the real axis for 0<=n_i<=m_i-2; (b) |G^{m_i-1}(z)|<=r only. No equation number assigned to (a) or (b). QG_N controls this modulus; it does not change the quantifier in (a).

The disputed line of V p.67 is “PLY inequality and Proposition 6.7 with n_j=0, imply that” beta_{l_j+1}=(log rho_{j+1})/(2*pi*i_complex) belongs to A(r5). A p.67 adds “Corollary 6.3, and Proposition 6.7 with n_j=0” and changes rho_{j+1} to rho_j. The next inference is alpha_{l_j+1} in A(r3) by Lemma 6.8 (V/A p.66). These lines have no equation number; their dependencies are PLY (32)/(4.2), Prop.6.7(a,b) and Cor.6.3. V p.67 equation (41)/A p.67 (6.4) also moves from a bound on beta_1 to a bound on the distinct alpha_1 at initialization.

There are **three** domain issues:
* m_j=1: (a) is vacuous, and (b) only gives |z_j|<=r. Neither beta in the cone nor its equality to z_j follows. Prop.6.2 V/A p.59 requires alpha_{l_j+1} in A(r3) *before* identifying beta_{l_j+1}=z_j; Cor.6.3 V/A pp.59–60 retains tower-domain conditions. Applying them outright to prove their own antecedent is circular.
* Lemma 6.8 as stated already assumes f in A(r1) times F0 (or A(r3) times {Q0}); its proof uses the index bound for A(r3) and two nonattracting fixed points, not just f'(0) nonattracting. V prints Im beta>=0; A corrects to <=0. Remark 6.9 V p.67/A p.66 observes quadratic tangency and suggests stronger bounds; it does not state the required unconditional bound.
* For m_j>=2, at the last top input, n=m_j-1, the proof also invokes Prop.6.7 to place alpha in A(r3) (V pp.67–68, A p.67). By (5.4) A p.53 (V p.53, formula following the index identity), this requires, up to the sign-reflection convention of Def.2.11,

    w_j=G^{m_j-1}(z_j) !=0,
    |Im w_j| <= |Re w_j|.                                     (MIX)

  Part (b) supplies radius, not (MIX). Once all earlier inputs in the block are admissible, the last top map itself has been produced, but its rotation is not thereby in A(r3). It cannot be renormalized further using Theorem 2.9 until its admissibility is proved. An estimate for the actual multiplier, not for arbitrary points of D_j, is needed.

Both editions share the angular omission. A's corrected sign/index and extra citation do not close it. A's Prop.6.7 proof uses r/3 rather than r/2 in initial budgets, and corrects the diameter/radius bookkeeping in the one-digit case (V pp.63–64/A p.63). None changes (a)'s range. See #136 for the independent radial audit.

## 2. Exact failure of the full-disk inference, including QG

This section concerns the **stated scalar hypotheses of Prop.6.7**, not realizability as a multiplier of a quadratic polynomial. It is not a counterexample to Prop.6.10 or D.

One-digit positive rotations: choose integer L>=max(N,17) and q_i=L^{2^{i-1}}. Then b_{i,1}=q_i, QG with equality and k_i=q_i/L. Since gamma>1/16 (log 2>1/2 and pi<4), the rational complex point

    z=1/q_i-i_complex*k_i/(16*q_i)

is in D_i (vertical displacement in [0,2R_i]) but violates |Im z|<=|Re z| whenever k_i>16, e.g. i=2. Its modulus is arbitrarily small as L grows: |z|<=1/q_i+1/(16L). The reflected negative case is identical. No choice of uniform N repairs the full-disk inference. The sharp positive-cone inclusion condition for a disk tangent at x>0 with radius R is R<=x/(1+sqrt(2)): signed distance from center (x,-R) to y=-x equals (x-R)/sqrt(2), which must exceed or equal R.

Mixed case already at i=1: choose b>=max(N,17), d=b^2, t=d/(bd+1)=1/(b+1/d). Then G(t)=-1/d, G^2(t)=0, signed digits b,d obey QG; append any QG continuation, e.g. q_2=(bd+1)^2 and q_{i+1}=q_i^2 thereafter. Here k_1=1, q_1=bd+1 and R=gamma/(bd+1). Set

    w=-1/d-2*i_complex/d,
    z=1/(b-w)=1/(A+i_complex*B), A=b+1/d, B=2/d.

Since Re(-1/z)=-A rounds to -b, G(z)=w. Furthermore

    |z-t|^2/(-2 Im z)=B/(2 A^2)=d/(bd+1)^2.
    
The disk condition is |z-t|^2<=-2R Im z. It holds because t=d/(bd+1)<1/17<gamma. But |Im w|=2|Re w| and |w|=sqrt(5)/d tends to zero. This witnesses failure of (MIX) for a point of the exact disk, even with the within-level and cross-level square conditions. n=0 is in the cone for this point, since |Im z|/|Re z|=B/A. The intermediate angle and final radius are thus consistent with 6.7. Again no assertion that z is in the actual multiplier image of any copy. The proof's scalar inference fails, not the claimed dynamical inclusion.

## 3. Index estimate: a genuine short local repair of the beta-angle implication

Use CS Prop.2.1 and index formula (2.2), §2.3; Lemma 3.24 and their explicit application in Lemma 6.8 p.66 of both editions; A (5.3) p.53. When the two distinguished fixed points are simple, distinct and nonattracting and the map is in the domain of the uniform index bound, write their multipliers lambda=e^{2*pi*i_complex*a}, mu=e^{2*pi*i_complex*z} with normalized logs, and |I|<=B4 for I=1/(1-lambda)+1/(1-mu). No angular premise on z is necessary. Indeed

    D(lambda)=1/2-Re(1/(1-lambda))
             =(|lambda|^2-1)/(2*|1-lambda|^2)>=0,
    D(lambda)+D(mu)=1-Re I<=1+B4.

For v=-Im z>=0, e^{4*pi*v}-1>=4*pi*v and
|1-mu|<=2*pi*|z|*exp(2*pi*|z|). Thus for |z|<=r,

    -Im z <= C_r |z|^2,  C_r=2*pi*(1+B4)*exp(4*pi*r).          (INDEX)

The same holds for a. If z nonzero and small enough (C_r |z|<=1/2), then |Im z|<=|z|/2<|Re z|. Also choose delta>0 so that for |z|<=delta, |1-mu|<=min(1/4,1/(2*max(1,B4))). The index identity gives |1-lambda|<=2|1-mu|<=1/2, hence for the principal normalized logarithm

    |a| <= |1-lambda|/pi <=4*exp(2*pi*delta)*delta.             (TRANSFER)

Here the logarithm series gives |log(1+u)|<=2|u| for |u|<=1/2. Choose delta so the final bound is <r3/2 and C_{r3} times that bound is <=1/2 (shrink r3 below 1/2). These choices can also impose any smaller desired uniform radius. This proves strict interior margins for a and z, provided the **index domain and nonattracting assumptions** have been obtained. This is the precise quantitative content behind Remark 6.9. Without those assumptions it is not a proof of admissibility. In particular, (INDEX) is not a general estimate for every PL dividing multiplier without an NP identification.

### 3.1 Conditional continuation repair for the all-one-digit class

Here is a way to avoid using Prop.6.2 outside its antecedent. This is a proof from the stated analytic interfaces; the internal proof of Prop.6.2 (especially its extension on connected components) has not independently been certified. It relies on its stated multiplier identification at every parameter satisfying its hypotheses, not on a claim that the printed proof already established admissibility. We give the induction with a stronger whole-copy assertion, enabling the connectedness argument.

Use the following interfaces: CS Prop.2.1, Thm.2.9, Def.2.11 and Prop.2.12 p.16 (continuous/holomorphic renormalization on each cone component, output in A(infinity) times F0), Prop.6.2 p.59, A (5.3)–(5.4) p.53, (6.4) p.58, §4.2–4.3 pp.48–51 (closed tuned copies and roots), Thm.4.6 pp.51–52, Prop.6.7(b) p.62 (V p.63). For the hyperbolic-component multiplier coordinate and local bifurcation use L §2.1 p.5 (multiplier extends homeomorphically to closed component; wake continuation repelling off that component), §4 p.13 and (20) p.14:

    d rho_child / d rho_parent (root)= -q^2/rho_parent(root).

Here q is the denominator of the attachment. These are statements of the cited sources at the indicated interface. L's reference [13] for (20) is UNVERIFIED independently. All estimates use absolute values and are unchanged by z -> -conjugate(z) in the negative-real normalization of CS Def.2.11. Integers in (5.4) are selected by the local log; near zero they cannot jump while the output stays small.

Choose N uniformly so (PLY) and Prop.6.7 yield |z_j|<=delta on K_j for all j (also |t_j|<=delta); only the actual QG hypothesis is used. At j=1 the two quadratic fixed-point multipliers sum to 2, hence the index sum is zero. On K_1 they are nonattracting (dividing cycle and the other fixed point; CS §4.1, §6.2–6.3), distinct since 0 is not the attachment rotation. Both normalized logs are nonzero. The exact identity beta_1=z_1, A (6.4)/V (41), and (INDEX), (TRANSFER) with B=0 put alpha_1 strictly in A(r3), with margin. No NP hypothesis was used in this quadratic base case. Thus the first bottom output exists throughout the closed copy.

Inductively suppose all j-1 bottom inputs are strictly admissible on K_{j-1}; the j-th map is produced everywhere there by Thm.2.9 and continuous in the indicated parameter charts. Call its rotation a=alpha_j (m_i=1, so l_j=j-1). Let H be the central hyperbolic component of K_{j-1}; its multiplier is rho_j. Let c_* be its root (root of K_{j-1}); let c_j be the root of the child K_j. By the multiplier homeomorphism, there is a boundary arc from c_* to c_j on which rho_j=e^{2*pi*i_complex*s}, with s between 0 and t_j, inclusive. This lies in K_{j-1}; use the signed short arc. Let X be this arc minus c_*, together with K_j. X is connected, since the connected copy meets the arc at c_j. On X the preceding dividing cycle is repelling, since X lies in the child copy off its own root, in the wake of the preceding hyperbolic component and outside that component's closure (L p.5, CS §§4.2–4.3). Thus z_{j-1} is in the strict lower half-plane. By Prop.6.2 at the preceding level and (5.4), a is G(z_{j-1}) modulo the sign reflection; its imaginary part is strictly negative and it cannot be zero on X. Only already-verified domains are used here. The absolute-period PLY bound holds on K_j; on the arc the normalized log z_j is s, real, nonzero and |s|<=delta.

At c_* the preceding multiplier is e^{2*pi*i_complex*t_{j-1}} with t_{j-1}=+/-1/q_{j-1}. By (20), in the local normalized multiplier coordinate

    z_j=-q_{j-1}^2 (z_{j-1}-t_{j-1})
             +O(|z_{j-1}-t_{j-1}|^2).
    
The derivative of G at t_{j-1} is q_{j-1}^2; thus a=-s+O(s^2) (up to sign reflection) on the initial arc. For nonzero sufficiently small s this is strictly in the cone and within radius. The constants in this seed need not be uniform; the following interior margin is uniform.

Let S be the relative open subset of X on which a is strictly in A(r3) (strict radius and angle). On S all hypotheses of Prop.6.2 at level j are verified on K_j, so beta_j=z_j there. On the arc, at a rational nonzero s, the point is the root of the child of K_{j-1} at s. Apply Prop.6.2 to that finite address: its previous block lengths, type, and l_j=j-1 are unchanged, and Prop.6.2 imposes no QG assumption on s. If one uses the convention excluding the root from a PL class, take parameters in that child approaching the root; strict admissibility is open in the already-defined previous tower, and the identification extends by continuity. Density of rational s and Prop.2.12 / Prop.2.1 give the identification on S along the arc as well. Log branches agree locally by smallness; the modulus/angle assertions are invariant under the negative-real convention. In particular both fixed points are nonattracting there: the zero multiplier comes from the preceding repelling dividing cycle via (5.4), and the nonzero multiplier is the identified rho_j (neutral on the arc; nonattracting on K_j by the dividing-cycle hypothesis).

We may now apply (INDEX) and (TRANSFER) on S, where the map is *already* in the index domain. This gives the uniform strict bounds |a|<r3/2, |Im a|<=|a|/2 and the analogous bound for beta_j. Any limit in X is nonzero, as proved above; the small normalized log is continuous at the limit (the multiplier lies away from the log cut). These bounds persist there, putting the limit in S. So S is both relatively open and relatively closed in connected X, and the seed makes it nonempty. Hence S=X. This establishes the j-th bottom admissibility on all K_j, and Thm.2.9 produces the next map there. It is not necessary to renormalize its parabolic output at the root. The induction proves the stronger one-digit finite-level inclusion (and thus the displayed Prop.6.10 inclusion for this subclass). It also supplies the missing beta-angle estimate on the actual one-digit multipliers for which the proof needs it. This is an erratum-level **conditional** repair at the stated Prop.6.2 interface. It is not a proof that the argument of Prop.6.2 itself is correct on all components, and is not offered as an independent proof of Theorem D.

### 3.2 Why this does not settle the whole QG class

For a mixed block the last top rotation must satisfy (MIX), before applying the top renormalization. The one-digit bootstrap uses the identification of the nonzero fixed point with a dividing cycle in an attached copy, at a block entry. The terminal top rotation is not that block entry; Prop.6.2 does not identify the second fixed-point multiplier at every intermediate index. On the already-produced terminal map one would need an independently verified nonattracting second multiplier and a uniform bounded index over a continuation path on which the radius estimate is available. Neither the intermediate-cycle identification nor that continuation step is supplied by Prop.6.7 or the block-entry Prop.6.2. Applying (INDEX) without them repeats the same logical problem. A scalar example in §2 rules out any proof of (MIX) from the *full disk* alone. The possibility that further restrictions on actual multipliers, e.g. from the next attached copy, imply (MIX) remains open here. The precise missing estimate is (MIX) on the actual multiplier locus for the mixed blocks used in the printed induction (with the correct branch, nonzero, and small modulus). A weaker angular domain supported by a strengthened Theorem 2.9 would be a different proof and is not established.

## 4. Other sources and scope of negative result

L §2.3 p.7 (8) is the PLY bound again. L Thm.4 pp.6–7 and the multiplier extension estimates do not immediately give the cone (MIX) uniformly over the full QG class; a uniform deduction from them is UNVERIFIED. L Addendum Thm.1 p.1 uses a condition involving limsup q_m/(product of prior denominators)^2>0, which cannot simply replace CS's hypothesis: for q_{i+1}=q_i^2 and q_1=L, q_i/k_i^2=L^2/q_i tends to zero. That comparison does not rule out other results of Levin for this class. The full hypotheses of independent MLC theorems have not been certified here. IS06 (Inou–Shishikura), Hub93, Pom86, Pet93, Lev91, DH84 and the original derivative reference [13] in L: UNVERIFIED for a proof of (MIX); no claim of exhaustive search of cited sources. CS's source-stated analytic results are not reproved.

If admissibility of the entire tower is established for every parameter in every copy in the needed uniform radius, Prop.6.11 (V p.68/A p.67), Thm.5.1 and Cor.5.3 pp.54–55, and Prop.4.3 pp.50–51 provide the route from shrinking connected horizontal slices to singleton nests and parameter local connectivity. The uniform expansion radius r4 must be respected. Nothing here asserts a failure of the conclusion. Theorem D's printed proof uses Prop.6.10 for the whole class, so the unclosed inference is relevant to that proof, not evidence that the theorem is false.

## Significance

The angular restriction is a genuine entrance condition for the near-parabolic machinery, not a cosmetic improvement of a small multiplier bound. The arithmetic examples show that even square growth leaves enough room in the PLY disk for the wrong angle. The two-fixed-point index removes that freedom when its analytic and dynamical hypotheses are available, and the continuation argument gives a way to avoid circularity at the one-digit entry. The unresolved mixed terminal top step is a narrowly specified target for a proof repair, rather than a reason to reject the imported theorem or infer anything negative about local connectivity.

## Reproduce and boundary

From repo root, Python 3.12 (CI container digest pinned; standard library only):

    python3 -B research/frontier/cs_prop_6_10_angular_20261126/verify.py
    python3 -B research/frontier/cs_prop_6_10_angular_20261126/verify.py --fetch

The first verifies exact rational disk witnesses with gamma replaced by the proven lower bound 1/16, the signed CF recurrence, and finite index-algebra identities. The second checks the committed source-lock bytes against HTTPS inputs; no files are written. Arithmetic is deterministic, no seeds/tolerances. The script does not prove multiplier realizability, certify the analytic source arguments, or check the entire infinite parameter class.

**NOT established:** a counterexample satisfying the actual PL dynamical hypotheses; failure of Theorem D or MLC; a complete full-QG repair or independent certification of Prop.6.2; (MIX) for actual multipliers of mixed blocks; stronger all-class estimates in other cited literature; new growth-rate weakening, rigidity, parameter diameter rates, JLC, or a change to any formal bridge. The result is deliberately confined to the source inference, a proved scalar obstruction, and a conditional one-digit repair.
