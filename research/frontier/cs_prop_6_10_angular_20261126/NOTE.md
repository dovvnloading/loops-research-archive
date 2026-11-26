# CS Proposition 6.10: angular admissibility audit (reviewed)

**BOUNDED NEGATIVE / OPEN (unconditional full QG_N verification); conditional repair at the stated Proposition 6.2 interface; METADATA only.** This is a source-reading and estimate result, not a counterexample to Theorem D or a new MLC/rigidity theorem. The printed scalar inference is invalid even with the quadratic growth hypothesis. The one-digit repair is conditional on the exact finite-prefix multiplier identification in Proposition 6.2. Independent review also finds a coupled continuation of the mixed terminal step and next bottom entry at that same interface; the original claim that MIX remains independently open even at that interface is withdrawn. No independent certification of the dynamical/analytic theorems is claimed.

## Scope and primary evidence

Follow-up to [#136](https://github.com/dovvnloading/loops-research-archive/pull/136), in particular its [review](https://github.com/dovvnloading/loops-research-archive/pull/136#pullrequestreview-6068635003) and [post-merge check](https://github.com/dovvnloading/loops-research-archive/pull/136#issuecomment-7182829462). V denotes [arXiv:1509.07843](https://arxiv.org/pdf/1509.07843) (rendered v1 stamp, 25 September 2015, internal date 19 July 2018); A denotes the [authors' PDF](https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf), internal date 9 September 2022. Both are Cheraghi–Shishikura, Satellite renormalisation of quadratic polynomials. L denotes Levin, [Rigidity and non local connectivity of Julia sets of some quadratic polynomials](https://arxiv.org/pdf/0710.4406), rendered v4 including its addendum. Locators below use printed pages. Exact versioned arXiv URL rendering and equivalence of the rendered bytes to the locked bytes are UNVERIFIED; CI independently downloads and hashes the exact versioned URLs. Journal-version comparison is UNVERIFIED. Source-lock files record byte counts and SHA-256; this authenticates the inputs used by CI, not the mathematics. No human specialist certification.

## 1. Statements, and the inference actually printed

Write t_i=p_i/q_i for the nonzero signed rationals, m_i for signed nearest-integer continued-fraction lengths, k_i=product_{h<i} q_h and l_i=sum_{h<i} m_h (l_1=0). K_i denotes the closed nested satellite copy in the parameter plane, with its lift to the alpha coordinate when using M_alpha. A block consists of a bottom NP step followed by m_i-1 top NP steps. The NP entrance domain is A(r)={a: 0<|a|<=r, |Im a|<=|Re a|} (V/A pp.2–3, Theorem 2.9, Definition 2.11). Output rotations need not be admissible; the output nonlinearity is in F_0. The QG_N hypothesis (V (44), p.62; A (6.8), p.62) is b_{1,1}>=N, b_{i,j+1}>=b_{i,j}^2, b_{i+1,1}>=q_i^2. The actual hypothesis is cross-level squaring, not q_i of polynomial order i^2.

For the dividing cycle of absolute period k_i, use z_i=(log rho_i)/(2*pi*i_complex), with the branch given by PLY. V (31)–(32), pp.51–52; A (4.1)–(4.2), pp.51–52:
    
    D_i = {z: |z-(t_i-i_complex R_i)| <= R_i},
    R_i = gamma*k_i/q_i, gamma=log(2)/(2*pi), z_i in D_i.

With G(z)=-1/z minus the nearest integer to its real part, Proposition 6.7 (V p.63, A p.62) states, for every z in D_i:

    (a) 0<=n_i<=m_i-2: |G^n_i(z)|<=r and |Im G^n_i(z)|<=|Re G^n_i(z)|.
    (b) |G^(m_i-1)(z)|<=r.

Here N is chosen sufficiently large for r. In particular (a) is vacuous for m_i=1. The displayed statement of Proposition 6.10 (V p.67; A p.66), in normalized notation, is

    M_alpha(t_1,...,t_k) subset Lambda^1_{r3}(kappa_1,...,kappa_{l_k})
    for every k>=1 under QG_N for sufficiently large N.

The inclusion concerns the preceding l_k steps, not all steps of block k on its whole copy. At initialization V p.67 / A p.66–67 the printed argument passes from a bound on beta_1 to alpha_1 (V (41), A (6.4), the distinct fixed-point multipliers). At the next entry, V p.67 invokes PLY and Proposition 6.7 with n_j=0 (misindexed rho_{j+1}); A p.67 corrects the index and adds Corollary 6.3. Neither version can infer the sector from 6.7(b) for m_j=1. Lemma 6.8 (V/A p.66), using the index identity V (1) / A (2.2), already assumes membership in the indicated A(r) class; its proof uses the two nonattracting multipliers and the uniform index bound. It does not establish entrance into its own domain. V's printed Im beta>=0 is corrected to <=0 in A. Remark 6.9 notes tangency in the real-beta case, not an unconditional entrance estimate.

The same problem occurs at the last top step when m_j>=2 (V pp.67–68; A p.67): the rotation, up to Definition 2.11 sign normalization, is w_j=G^(m_j-1)(z_j) by the rotation relations (V p.53; A (5.3)–(5.4), p.53). The radius follows from 6.7(b); the missing angular inequality is

    (MIX)  |Im w_j| <= |Re w_j|   (w_j != 0; |w_j|<=r3).

Nonzero is automatic on D_j: away from its single real point t_j, Im z<0 and Im G(z)=Im z/|z|^2<0, so no iterate is zero. At t_j the signed CF has exact length m_j and the last nonzero remainder is +/-1/b_{j,m_j}. These facts apply to all inputs before termination. The missing angular step is not supplied by 6.7(a).

**Exact conditional interface.** Proposition 6.2 (V/A p.59, A corrects the range to k>=1): for alpha in M_alpha(t_1,...,t_k) intersect Lambda^1_{r3}(kappa_1,...,kappa_{l_k}), and additionally alpha_{l_k+1} in A(r3), its conclusion is

    beta_{l_k+1} = (1/(2*pi*i_complex))*log rho_k.

We use the stated identification with the chosen logarithm and sign normalization (reflection z -> -conjugate(z) preserves modulus and the double cone). It has no QG restriction on the finite rational address. In particular it requires admissibility of *all* preceding inputs AND the current bottom input; it cannot be invoked unconditionally to show the latter. Corollary 6.3 assumes an infinite NP tower. The printed proof of Proposition 6.2 itself uses analytic continuation from a root neighborhood on components: the global identification on every indicated parameter is an assumed interface here, not independently proved or certified by this audit.

## 2. Exact scalar obstructions under QG_N

For every N and integer L>=max(N,17), take positive one-digit t_i=1/q_i, q_i=L^(2^(i-1)), so k_i=q_i/L and q_{i+1}=q_i^2. Since log(2)>1/2 and pi<4, gamma>1/16. Thus

    z_i=t_i-i_complex*k_i/(16*q_i) in D_i,
    |z_i| <= 17/(16*L),
    |Im z_i|/|Re z_i| = k_i/16 > 1 for i>=2.

The reflection gives the negative sign. In fact for x>0 a disk tangent at x with center x-iR fits in the right cone exactly when R<=x/(1+sqrt(2)), by distance to the line Im z=-Re z. The full PLY disk need not fit even for arbitrarily small uniform radius.

Mixed example at i=1: take b>=max(N,17), d=b^2, t=d/(bd+1), q=bd+1, k=1. Signed digits have magnitudes b,d, G(t)=-1/d and G^2(t)=0. Continue with positive one-digit q_2=q^2 and q_{i+1}=q_i^2, so the full address satisfies QG_N. Set A=b+1/d, B=2/d, z=1/(A+i_complex B), w=G(z)=-1/d-2*i_complex/d. Nearest integer is -b, |Im z|<=|Re z|, and

    |z-t|^2/(-2 Im z) = d/q^2 < gamma/q = R,
    |w|=sqrt(5)/d, |Im w|=2|Re w|.

The strict inequality uses d/q<1/17<gamma. Thus z is in the actual PLY disk, satisfies the earlier cone and arbitrarily small terminal radius, but violates MIX. Reflection also works. These are exact scalar points of an outer bound, **not** realized quadratic dividing multipliers. They disprove the full-disk inference, not Proposition 6.10.

## 3. Conditional local index estimates and continuation

Use the uniform index bound of Lemma 3.24(a) (V/A p.42) on the stated NP entrance domain; write B for that bound (avoid the inconsistent constant name in Lemma 6.8). For distinct simple nonattracting fixed points with multipliers lambda=exp(2*pi*i_complex a), mu=exp(2*pi*i_complex z), neither equal to one, put

    I=1/(1-lambda)+1/(1-mu), |I|<=B.
    D(lambda)=1/2-Re(1/(1-lambda))=(|lambda|^2-1)/(2|1-lambda|^2)>=0,
    D(lambda)+D(mu)=1-Re I<=1+B.

For |z|<=r, Im z<=0, exp(4*pi*(-Im z))-1>=4*pi*(-Im z), and |1-mu|<=2*pi*|z| exp(2*pi*r). Hence

    -Im z <= C_r |z|^2, C_r=2*pi*(1+B)*exp(4*pi*r).             (INDEX)

The same bound holds for a when small. If |z|<=delta and |1-mu|<=min(1/4,1/(2 max(1,B))), the triangle inequality in I gives |1-lambda|<=2|1-mu|<=1/2. The principal log bound |log(1+u)|<=2|u| for |u|<=1/2 yields

    |a|<=4 exp(2*pi*delta) delta = eta.                        (TRANSFER)

Choose delta small enough that eta<min(r3/2,r4/2,1/4), C_{r3} eta<=1/2, and delta<min(r3,r4,1/4); r4 is the Theorem 5.1 expansion radius. On an *already admissible* input whose two fixed points are known nonattracting, these give |Im a|<=|a|/2 and the analogous estimate for z. In particular strict cone interior for nonzero a,z. No index estimate is applied to an inadmissible input. Proposition 6.7 supplies the uniform delta bound for z_j and the indicated Gauss iterates, increasing N as necessary.

Use CS Proposition 2.1, Theorem 2.9, Definition 2.11 and Proposition 2.12 (continuity in the entrance domain), the block rotation identities V p.53/A (5.3)–(5.4), and the closed tuned copies and dividing cycles of CS §§4.2–4.3, pp.48–49. For the boundary multiplier coordinate and repelling continuation outside the closure of a hyperbolic component in its wake, use L §2.1 p.5; for the local bifurcation derivative use L (20), p.14:

    d rho_child / d rho_parent at the attachment = -q^2/rho_parent(root).

Consequently the normalized logarithms satisfy z_next=-q^2(z_parent-t)+O(|z_parent-t|^2) locally at the attachment. L cites [13] for the derivative; that original proof is UNVERIFIED. We use these source-stated results, not a new proof of them.

### 3.1 The one-digit argument and the finite-prefix invariant

At K_1 both quadratic fixed points are distinct, nonattracting (one dividing and the other repelling); their multipliers sum to 2, so I=0. Use (6.4) A/(41) V and the small PLY logarithm beta_1 to apply the above elementary algebra with B=0. This gives strict smallness of alpha_1 without assuming any NP domain. The same base works for any m_1.

Inductively require, on K_j, that all inputs through l_j+1 are admissible with radius less than r3 and r4, with strict margin at the current bottom input. Assume Proposition 6.2 at this interface. It identifies the nonzero fixed point logarithm at the bottom entry with z_j. On K_j the next bottom output is therefore G(z_j), up to the sign normalization.

Let H_j be the central hyperbolic component of K_j; its root is c_j. Let c_{j+1} be the attachment of the next copy at multiplier exp(2*pi*i_complex*t_{j+1}) of H_j. Take the closed signed short arc of the boundary of H_j from c_j to c_{j+1}, with multiplier exp(2*pi*i_complex*s), s between 0 and t_{j+1}. Let X be that arc minus c_j, together with K_{j+1}. By the multiplier homeomorphism on the component closure and the closed connected tuned copy, X is connected. The preceding dividing cycle rho_j is repelling on X: X is in its wake outside the closure of its parent hyperbolic component. Thus Im z_j<0, and every Gauss iterate in question is nonzero. The next dividing logarithm z_{j+1} is small on X: PLY and 6.7 on K_{j+1}, and z_{j+1}=s on the arc.

For m_j=1 the following bottom rotation is already defined on X, a=G(z_j) up to reflection. Near c_j, G'(t_j)=q_j^2, so L (20) gives a=-s+O(s^2) in the unreflected coordinate. Hence a is strictly admissible on a nonempty initial part of the arc. Let S be the relatively open set of X where a is strictly in A(r3). On S, all earlier inputs and the current input are admissible, so Proposition 6.2 applies on K_{j+1}. At rational s!=0 on the arc apply it to the prefix t_1,...,t_j,s: the prior block lengths and type are unchanged and this parameter is the root of that child copy. No QG assumption on s is needed. The identification extends to the arc in S by rational density and continuity of the multipliers and NP maps on the admissible branches. The sign normalization only reflects logarithms; it preserves the estimates.

Both fixed points at this bottom entry on S are nonattracting: the zero-point multiplier has Im a<0 by the Gauss relation, and the other is identified with the nonattracting dividing multiplier (neutral on the arc). Thus INDEX and TRANSFER give the strict interior margin above, uniformly on S. At a relative limit in X the next rotation cannot vanish because Im G(z_j)<0. Continuity and the uniform margin imply the limit is in S. Hence S is closed as well as open, and S=X. This proves the conditional one-digit induction with a stronger whole-copy bottom-entry invariant; no renormalization at the excluded parabolic root is needed.

### 3.2 Independent reviewer correction: coupled mixed continuation

The original audit treated MIX on the actual locus as a remaining independent obstruction after the preceding conditional repair. That is too strong for the finite-prefix inclusion of Proposition 6.10. The same continuation can be coupled to the last top step and the following bottom entry. This does *not* give MIX on the entire outer disk or assert that the whole of K_j admits the last top step.

For m_j>=2, on K_j apply the bottom step and the earlier top steps with Gauss exponents 1,...,m_j-2 (empty if m_j=2). Their input rotations are nonzero, and 6.7(a) gives the radius and cone required by Theorem 2.9. The last top map is now produced, with rotation w=G^(m_j-1)(z_j) up to reflection, continuous on K_j, 0<|w|<=delta. Its admissibility has not yet been shown. Use the same X as above. On X, Im w<0. Where w is admissible the last top step gives the following bottom rotation a=G(w) up to reflection.

Near c_j, w tends to the last nonzero real CF remainder, within delta. All integer branches are locally constant there because the next real remainders have modulus <1/4, away from ties. The derivative of G^m_j at t_j is q_j^2: G'=1/z^2 and the product of the absolute nonzero real remainders of a signed rational CF is 1/q_j (CS §6.2 p.57, A (6.3)). Thus a=-s+O(s^2), up to reflection, by L (20). In a nonempty initial portion of the arc both w and a are strictly admissible.

Now define S to require *both* w and a strictly admissible. It is relatively open by continuity. On S all inputs through the next bottom are admissible, so exactly the argument of §3.1 with Proposition 6.2, rational roots and density gives the next bottom nonzero fixed-point multiplier z_{j+1}, while Im a<0. INDEX and TRANSFER there give |a|<=eta and |Im a|<=|a|/2. Crucially this implies a uniform interior margin for the preceding terminal w without any identification of the second fixed point of that top map. In unreflected coordinates let a'=G(w); then

    w=-1/(n+a'), n integer, n!=0 (since |w|<=delta<1/4 and |a'|<=eta<1/4),
    |Im w|/|Re w| = |Im a'|/|n+Re a'| <= eta/(1-eta)<1/3.     (INVERSE)

Reflection leaves the inequality unchanged. At any relative limit in X, w is nonzero and continuous, within delta, and strictly inside the cone by INVERSE. The top renormalization is therefore defined there; its rotation a is continuous at the limit and nonzero by Im G(w)<0. The uniform strict margins persist, so the limit lies in S. Thus S=X, proving MIX on the needed K_{j+1} and the next bottom-entry invariant there. The earlier top inputs, which need only weak angular admissibility, were already defined on all K_j; continuity here is relative to their admissible domains. No index bound outside A(r3) is used.

This proves the finite-prefix inclusion at the stated Proposition 6.2 interface for mixed blocks too, **conditional** on that identification (including the rational-root instances), the source-stated continuity/rotation, tuning and bifurcation results. The argument does not independently establish any of these analytic results. It does not require the stronger, unnecessary assertion of terminal admissibility throughout K_j. An unconditional resolution of the full proof, including certification of Proposition 6.2 on all required components, remains OPEN.

## 4. Cross-check and significance

Search of both editions (including §§2–5, the full §6, subsequent Propositions 6.11–6.12 and the end/references; no separate appendix in either rendered edition) found no additional unconditional statement supplying the printed entrance inference. Lemmas 3.24–3.25 use the specified cone domain; Remark 2.10 permits attracting second fixed points for general NP maps. Lemmas 6.4–6.6 are cylinder and distortion estimates: the inclusion in 6.7 Step 8 only supplies the earlier cone. Figure 8 illustrates the first dividing multiplier, not a bound on all actual terminal rotations. Proposition 6.11 uses the containment already asserted in 6.10; 6.12 is existential, not an all-parameter repair. These are source-reading findings, not an assertion that no other argument is possible.

L (8), p.7 supplies the PLY bound; L Theorem 4, pp.6–7 and the multiplier extension in (21), p.14 do not state the required all-copy terminal cone. The L Addendum, Theorem 1, p.1 uses additional denominator conditions, including positive limsup of q_j/k_j^2 for its local-connectivity conclusion; the exact square sequence above has q_j/k_j^2=L^2/q_j ->0, so that criterion does not cover this example. Whether other cited results or refinements give a direct all-copy angular bound is UNVERIFIED. IS06, Hub93, Pom86, Pet93, Lev91, DH84 and L [13] were not opened; independent verification of their contents and a comprehensive alternate proof search are UNVERIFIED.

Theorem D (V/A p.6) uses Proposition 6.10 to put the nested copies in the NP domain, then Proposition 6.11 (V p.68/A p.67), Theorem 5.1 (p.54), Corollary 5.3 (p.55) and Proposition 4.3 (pp.50–51) for shrinking, rigidity/local connectivity. The missing angle is a real logical gap in the printed invocation, not a numerical threshold adjustment. At the stated multiplier-identification and analytic interfaces the continuation above is an erratum-level repair of this step; without those interfaces independently established, the full published proof is not independently certified by this audit. This does not show that the theorem is false, that an infinitely satellite-renormalizable parameter is nonrigid, or that MLC fails. No new rigidity, MLC, JLC, rate theorem or bridge follows from the scalar witnesses.

## 5. Reproducibility

Run python3 -B research/frontier/cs_prop_6_10_angular_20261126/verify.py (and add --fetch for the locked exact primary PDF bytes). Original exact Fraction checks are retained, with reflected witnesses, signed CF termination and derivative products, and inverse-Gauss margin samples added by the reviewer. The lower rational bound 1/16 for gamma is justified above. Finite exact samples test the displayed arithmetic, not all infinite addresses or analytic continuation. --fetch checks exact URL, resolved URL, PDF magic, length and SHA-256 against sources.lock.json. The workflow is pinned, read-only, and does not commit or rewrite lock files. It runs on the PR and on relevant main pushes. No bridge ledger change except this verifier's METADATA registration.
