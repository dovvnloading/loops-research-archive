# Canonical marked Wave at the near-−2 real primitive tips: definition, certified bounds, and the remaining gap

**Audit dated 2026-11-16. STATUS: PARTIAL, NOT A CANONICAL-WIDTH THEOREM.** This is a new-only audit. It proves a quantitative limit for an **explicit orbit-defined round Wave witness**, and gives finite exact-arithmetic enclosures for that witness and a separate **upper envelope**. It does **not** compute the unrestricted maximal KKL Wave, prove convergence of its width, prove nonconvergence, or certify a numerical value of the canonical limiting width. In particular the interval \`0.2604925 < W_∞* < 0.7749233\` below is an intentionally **coarse two-sided bound**, not a computed canonical width. No pre-existing proof, verifier, or native generator has been changed.

## 1. Source-faithful definition (and a non-definition to avoid)

Let \`f_c(z)=z²+c\`, \`x_j=f_c^j(0)\`, \`G_p=f_{c_p}^p\`, and let \`T_p=[x_{2p},x_p]\` and \`U_p=D(0,R_p)\`, with \`R_3=1/4\`, \`R_p=2^{-p}\` for \`p≥4\`. The original physical \`p=3\` marked slit is pinned in [\`native_wave_transfer/SPECIFICATION.md\`](../../native_wave_transfer/SPECIFICATION.md). For each family member the cut order is

\`x_{2p}<x_{5p}<x_{3p}<0<x_{6p}<α_p<x_{4p}<x_p\`, \`G_p(α_p)=α_p\`;

\`Ω_p=U_p\T_p\` carries the ten inner-circle ideal atoms \`I_0,…,I_9\`. In their cyclic convention \`I_1\` and \`I_9\` are opposite slit-side accesses to \`(x_{5p},x_{3p})\`, and \`I_0\` is the left terminal atom. The fixed parent base is the **three-atom multi-interval** \`B=(I_9,I_0,I_1)\` and the intended crest is \`I_0\`. An outer entire-component atom is not part of this base.

The following comes from **Kahn–Kapiamba–Lyubich (KKL), [arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272v1)**, not from a new convention:

1. **Appendix A.1, ideal marking:** proper paths have endpoints in marking intervals; a path subordinate to a multi-interval of length at most **two** is excluded. The base of a Wave is the *smallest* multi-interval to which all leaves of the lamination are subordinate. Its two ends are the smallest endpoint multi-intervals, and its **crest is base minus the ends**. Thus the specified base and crest force the ideal endpoint type \`I_9\`/\`I_1\` and the nontrivial left-tip homotopy class. They do **not** force any Euclidean center, radii, or prescribed circles.
2. **Appendix A.2.1–A.2.3:** \`W(S)\` is the **conformal/extremal width of the lamination**, invariant under conformal change of chart. A canonical weighted arc diagram is a distinct construction; it must **not** be silently substituted for an individual maximal marked Wave or for a chosen logarithmic annulus.
3. **Appendix A.3.1:** the **covering** \`f_*\` transports the proper paths and ideal atoms under \`G_p:V_p\T'_p→Ω_p\`; here the *covering* atom table is \`f_*(S_s)=I_{s mod 10}\`.
4. **Appendix A.3.2, definition of restriction and Lemma A.11:** the **immersion** \`ι:V_p\T'_p→Ω_p\`, \`T'_p=[-x_p,x_p]\`, induces a **set-valued proper-path restriction** \`ι*\`, *not* the covering map. For this family's pullback marking its ten cyclic blocks are \`P_0=[18,19,0,1,2]\`, \`P_1=[3,4]\`, \`P_2=[5]\`, \`P_3=[6]\`, \`P_4=[7,8,9]\`, \`P_5=[10]\`, \`P_6=[11,12,13]\`, \`P_7=[14]\`, \`P_8=[15]\`, \`P_9=[16,17]\`. Restriction discards components that are not paths in the source marking or are subordinate to a *single* \`ι*I\` block. Lemma A.11 gives a reciprocal-width inequality for prescribed surviving children, **not** an extremal-width identity for all parent leaves.

The **intrinsic candidate** asked for here, conditional on identifying the physical real slit with the complete KKL ideal marking, is the supremum

\`W_p* := sup{ W(S): S is an A.1-admissible Wave on (Ω_p,I), base(S)=B, I_0⊂crest(S) }\`.

A larger sup is not created by freely changing radii: every candidate uses the **same** marked Riemann surface. Appendix A.3.2 governs how a parent is **restricted**; it does not require that *every* A.1 parent leaf have two children. If the phrase “admissible” additionally demands two surviving proper children, define separately

\`W_p*,2 := sup{W(S): S as above, and ι*S has both prescribed proper restriction classes}\`, so \`W_p*,2≤W_p*\`.

This avoids the logically incorrect use of A.3.2 to delete legitimate **parent** Waves. The two classes of parent Waves share all bounds below; we make **no equality claim** for these two suprema. In either definition an actual numerical computation requires an extremal problem over *all* admissible laminations, not a selected annulus. The source-induced slit/prime-end marking and the claim that no additional complex tree accesses intervene remain **cited interpretation inputs**, just as in the merged family notes.

The circular A.1 parent leaf has (upper/lower) ideal endpoints at the same physical real impression \`q∈(x_{5p},x_{3p})\`. Its crossing left intersection \`w∈(-x_{4p},x_{2p})\` is inside the new source attachment. The source *proper* crossing restrictions have pairs \`(S_3,S_1)\` and \`(S_19,S_17)\` and source shortest arc lengths **3 and 3**. An avoiding comparison has \`(S_3,S_17)\` with shortest arc length **7** (NOT 3). Pushing by **\`f_*\`** gives \`(I_3,I_1)\`, \`(I_9,I_7)\` and \`(I_3,I_7)\`, with target short lengths **3, 3, 5**. A.1 excludes spans of length ≤2; A.3.2 separately discards one-block immersion restrictions. Do not conflate these rules or the two maps. The analytic log-rectangle identification for these round leaves uses KKL Appendix A.2 and the original physical proof; the integer arithmetic checks geometry and the symbolic aspect-ratio calculation, **not** a new formal proof of extremal-length theory.

## 2. Certified *round* lower witnesses: theorem, value, rate

Set (all quantities are orbit/real cut quantities)

\`m_p=(x_{2p}+x_{5p})/2\`, \`r_in,p=(x_{5p}-x_{2p})/2\`,

\`r_gate,p=min{ -α_p−m_p , x_{4p}+m_p }\`, and

\`W_p^rad=log(r_gate,p/r_in,p)/(2π)\`.

Strict source-cut inequalities imply \`0<r_in,p<r_gate,p\`. Every circle \`|z-m_p|=r\` with \`r_in,p<r<r_gate,p\` has both real endpoints in the prescribed crossing gate, and the center/radius convention is **invariant only under positive affine rescaling**. The existing ten-period audit gives strict whole-disk image margins for \`3≤p≤12\`; this new verifier checks them **again** from the old untrusted dyadic parameter packets and fresh \`2^-512\` interval orbits, fixed-point brackets and whole-disk Taylor propagation. In particular \`W_p*≥W_p^rad\` and \`W_p*,2≥W_p^rad\` **under the cited KKL slit/rectangle identification**.

For \`p≥13\` the merged [all-period note](../real_primitive_tip_family_all_p_20261116/NOTE.md) proves the needed real cut order, \`-2≤τ≤1/4\` chart, \`|τ_p|<1.795\`, \`3/20<|A_p|4^{-p}<17/100\`, and \`h_p(w)=A_p G_p(w/A_p)=w²+τ_p+e_p(w)\` with \`|e_p(w)|<88·4^{-p}\` on \`|w|≤2.1\`. The entire closed gate disk satisfies \`|z|≤x_{4p}<x_p\`, so \`|A_p z|≤|τ_p|<2\`; thus \`|h_p(A_p z)|<4+2+88·4^{-p}<7\`. Consequently \`|G_p(z)|<7/|A_p|<(140/3)4^{-p}<(3/5)2^{-p}\` for \`p≥13\`. Its real center is in \`V_p\` by the already certified real branch, so the **whole disk** lies in the proper central component. This supplies an all-period valid **round witness**, without importing any generator under \`research/native_wave_transfer/\`. The verifier rationally checks the worst-case numerical inequality at \`p=13\`; the displayed analytic bound makes it monotone for larger p.

To prove its limit, let \`g_τ(u)=u²+τ\`, \`u_j(τ)=g_τ^j(0)\` and let **\`τ*\`** be the unique zero of \`u_6(τ)+u_3(τ)\` in \`[-1.795,-1.785]\`. This is the *renormalized period-three tip* of the limit map, **not** the physical \`p=3\` parameter \`c_3\`. Let \`a*=(1−sqrt(1−4τ*))/2\` be the negative fixed point. The rescaled physical cuts converge to \`−u_j(τ*)\` (since \`A_p<0\`), and the rescaled physical \`α_p\` converges to \`−a*\`. Therefore the limiting round ratio is the **explicit algebraic number**

\`R_rad,∞ = min{ 2a*+u_2+u_5, -2u_4−u_2−u_5 } /(u_2−u_5)\`;

the first branch is strictly active, so \`W_rad,∞=log(R_rad,∞)/(2π)\`.

**Quantitative proof.** The new verifier partitions the entire τ interval into 64 rational subintervals and proves \`d(u_6+u_3)/dτ>8\` using outward \`2^-512\` arithmetic, plus \`|u_j'|<30\` for \`j≤5\`. The all-p note's orbit comparison gives \`|h_p^j(0)−u_j(τ_p)|≤88(4^j−1)4^{-p}/3\`. Since the physical tip equation is \`h_p^6(0)+h_p^3(0)=0\`, the mean value theorem gives \`|τ_p−τ*|≤15246·4^{-p}\`. The negative fixed-point difference is \`<5900·4^{-p}\`: apply \`|e_p|≤88·4^{-p}\` and \`|(h_p(w)−w)'|>5/2\` on \`[-1,-4/5]\` and the model derivative \`|a'(τ)|≤5/13\`. The verifier checks the rational inequalities. Applying \`min\`'s 1-Lipschitz property to the two gate numerators, with the strictly certified model denominator \`u_2−u_5>3/20\` and physical denominator \`>13/100\` for \`p≥13\`, gives

\`|R_rad,p−R_rad,∞| < 150000000·4^{-p}\` and \`|W_rad,p−W_rad,∞|<7000000·4^{-p}\` for **all p≥13**.

The constants are intentionally loose at the first large period; this is a rigorous *round witness* convergence theorem, **not** the desired \`|W_p*−W_∞*|\` result.

## 3. Separate certified conformal *upper envelope* (not an attained Wave)

All A.1 parents in this base/homotopy class lift to paths connecting the **opposite slit sides** of \`(x_{5p},x_{3p})\` in the universal cover of \`Ω_p\`. Thus the full lifted proper-path family is a **superset** of every permitted Wave lamination, even after A.3.2 restriction. By conformal monotonicity its extremal width \`Q_p\` obeys \`W_p*≤Q_p\` and \`W_p*,2≤Q_p\`. The **inequality**, not equality, is used here.

Write \`m=(x_{2p}+x_p)/2\`, \`r=(x_p−x_{2p})/2\`, and \`J(ζ)=m+(r/2)(ζ+ζ^{-1})\`. The Joukowski chart maps \`|ζ|>1\` conformally to the complement of the physical slit \`[x_{2p},x_p]\`. The two opposite slit-side electrode subintervals are represented by angles \`±[a,b]\` (modulo π), where

\`a=acos((m−x_{5p})/r)\`, \`b=acos((m−x_{3p})/r)\`, and \`0<a<b<π\`.

For the **whole-plane** slit, its simply connected universal cover is the upper half-plane; the four boundary endpoints of the selected lifts have the standard quadrilateral cross-ratio parameter \`k_∞=(b−a)/(b+a)\`. The Schwarz–Christoffel complete elliptic integral formula gives the *full-path* upper envelope

\`Q_plane = K(k_∞)/K(sqrt(1−k_∞²))\`, where \`K(k)=∫_0^{π/2}(1−k² sin²θ)^{-1/2} dθ\`.

This is a **real conformal modulus**, but not a maximal KKL Wave: it contains families that need not survive the A.3.2 pullback filter. The finite disk \`U_p\` has a smaller domain. Set \`A=(R_p−m)/r\`, \`B=(R_p+m)/r\` (for this family \`m>0\`); the physical Joukowski domain is sandwiched between exterior annuli with outer radii

\`ρ_- = A+sqrt(A²−1)\` and \`ρ_+ = B+sqrt(B²+1)\`.

For an annulus of logarithmic height \`L=logρ\` the full lifted path family has the exact quadrilateral formula

\`Q(L)=K(k_L)/K(sqrt(1−k_L²))\`, \`k_L=sinh(π(b−a)/(2L))/sinh(π(b+a)/(2L))\`.

This follows by lifting the annulus to a strip, exponentiating to the upper half-plane, then using the four endpoints and the Schwarz–Christoffel rectangle integrals. Therefore **\`Q(logρ_-)≤Q_p≤Q(logρ_+)≤Q_plane\`**, and particularly \`W_p*≤Q(logρ_+)\`. The interval verifier rigorously encloses the two \`Q(logρ±)\` values; it **never** identifies the lower annular \`Q\` with a lower bound for a restricted KKL Wave.

The calculations use rational Machin π enclosures, the alternating arctangent series (with a positive bounded remainder), the positive-coefficient logarithm and sinh series, and the complete-elliptic hypergeometric series \`2K(sqrt(m))/π=Σ[(2n choose n)/4^n]² m^n\`, with a rational geometric tail. All operations round out on a \`2^-512\` integer lattice; \`--write\` must be requested to update **new-only** \`results.json\`. In particular there are **no binary floating-point proof premises**, and decimal brackets are strictly expanded rational intervals.

In the limit \`|A_p|R_p> (3/20)2^p→∞\`, the rescaled domains exhaust the plane slit, and the cut coordinates converge at rate \`O(4^{-p})\` as shown above. The two annular logarithmic heights satisfy \`L=p log2+O(1)\`; \`sinh(t)/t=1+O(t²)\` then gives \`Q(logρ±)−Q_plane=O(p^{-2})\` for the **full-path envelope** (the finite cut perturbation is \`O(4^{-p})\`). Thus **\`Q_p→Q_∞\`**, where \`Q_∞\` is the limiting plane-slit full-path envelope computed above. No constant in this asymptotic \`O\` assertion is used for a width certificate; its finite enclosures are in the verifier. Crucially this does not imply \`W_p*→W_∞*\`, because both the parent Wave subfamily and its admissible restrictions can be proper subfamilies of the lifted full-path class.

## 4. Certified ledger, numeric-only distinctions and missing theorem

All numbers below are **strict rational interval enclosures**, displayed as decimals for readability. Read \`results.json\` for the underlying scaled integers with outward one-unit guards. Every finite p=3…12 row is recomputed from the old dyadic \`c_p\` packet: the endpoints of \`P_p\` have opposite strict signs, its full-hull derivative is strictly negative, the signed orbit/cut order holds, and \`α_p\` is bracketed by a whole-interval monotonicity and bisection proof. Disk images are proven for entire disks, not sample points.

| p | **round** \`W_p^rad\` (strict) | **upper** \`Q(logρ_+)\` (strict) | Status |
|---:|---:|---:|---|
| 3 | (0.2516729, 0.2516732) | (0.5967637, 0.5967640) | finite exact |
| 4 | (0.2584721, 0.2584724) | (0.6080487, 0.6080490) | finite exact |
| 5 | (0.2600034, 0.2600037) | (0.6811880, 0.6811883) | finite exact |
| 6 | (0.2603715, 0.2603718) | (0.7182629, 0.7182632) | finite exact |
| 7 | (0.2604624, 0.2604627) | (0.7377890, 0.7377893) | finite exact |
| 8 | (0.2604850, 0.2604853) | (0.7489371, 0.7489374) | finite exact |
| 9 | (0.2604907, 0.2604910) | (0.7558001, 0.7558004) | finite exact |
| 10 | (0.2604921, 0.2604924) | (0.7602937, 0.7602940) | finite exact |
| 11 | (0.2604924, 0.2604927) | (0.7633845, 0.7633848) | finite exact |
| 12 | (0.2604925, 0.2604928) | (0.7655967, 0.7655970) | finite exact |
| ∞ (g_τ*) | (0.2604925, 0.2604928) | \`Q_∞∈(0.7749230,0.7749233)\` | **not** \`W_∞*\` |

The limiting parameter \`τ*∈(−1.7903276,−1.7903273)\` and round radius ratio \`R_rad,∞∈(5.1383080,5.1383083)\` are also certified. If the KKL slit/prime-end interpretation applies, the only legitimate **canonical width conclusions** from this work are the inequalities

\`W_p^rad ≤ W_p*,2 ≤ W_p* ≤ Q_p ≤ Q(logρ_+)\`, and

\`0.2604925 < W_∞*,2 ≤ W_∞* < 0.7749233\` for the **specified limiting marked plane slit**. The limiting lower bound is a round witness; the upper is a different full-path family. This wide interval is not a “computed canonical value.” The numerical value obtained by **floating-point-only** nonlinear optimization (if ever run) would be **numerical-only** until a new verified extremal argument exists; none is presented here.

**OPEN: (i)** prove the actual KKL maximal lamination for the fixed base/crest, accounting for the A.3.2 allowable pullback classes; **(ii)** show a conformally invariant continuity principle for that constrained lamination, with a quantitative error, or exhibit genuine nonconvergence; **(iii)** enclose the *canonical* finite \`W_p*\` for p=3…12 tightly enough to count as a computation, and enclose the *canonical* \`W_∞*\` tightly. The all-period realization, Rouche and finite strip upper bound do **not** discharge these. A convergence or failure-of-convergence statement for \`W_p*\` would be scientifically unjustified here.

## 5. Reproduce and review

Run from repository root:

\`\`\`sh
python research/independent_audits/real_primitive_tip_family_canonical_width_20261116/verify.py
python -m unittest discover -s research/independent_audits/real_primitive_tip_family_canonical_width_20261116 -p 'test_*.py' -v
python research/independent_audits/real_primitive_tip_family_all_p_20261116/verify.py
python research/independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py
\`\`\`

The dedicated \`.github/workflows/real-primitive-tip-family-canonical-width.yml\` also re-runs native-manifest, research-validation and Lean regressions independently of their existing path filters. Tests detect shifted dyadic brackets, nonadjacent brackets, illegal analytic series inputs, and nonsensical calls that would equate the round witness with the full-path envelope. It does not claim that the Python verifier formally proves theorems of complex analysis or the KKL ideal-boundary identification; the exact arithmetic **verifies its finite numerical premises**, and the written proof supplies the stated analytic reductions.

**Hostile-review stop rules:** a path that no longer has the base \`I9,I0,I1\` is outside the supremum; a subannulus width is not maximal; a \`f_*\` label cannot replace an \`ι*\` block; an avoiding path's source short arc has length 7; an annular \`Q(logρ_-)\` lower bound for *all paths* cannot be asserted as a KKL Wave lower bound; a \`K(k)/K(k')\` formula from a four-terminal quadrilateral is not automatically the constrained maximum; numeric-only optimizers cannot certify canonical widths; and the limiting \`τ*\` is not the physical \`c_3\`. Any attempted proof crossing one of these gaps requires new justification, not more decimal digits.
