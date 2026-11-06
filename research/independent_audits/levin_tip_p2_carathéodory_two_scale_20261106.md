# Levin (p2) at the nonattracting tip by uniform Carathéodory access

**Research audit, 2026-11-06.** This supplies a source-level *analytic* argument for Levin's condition (p2) for both existing round-disk renormalizations at the real Misiurewicz tip, and determines finite, actually eligible pieces of their **different** renormalization-angle maps. The finite period-three angle classification is independently checked by exact arithmetic and a Lean proposition. The complex topology, subhyperbolic local connectivity, Carathéodory extension and Levin's theorems are **imported classical mathematics, not formalized in Lean**. No KL puzzle/sheet groupoid, complete ray-fiber classification, UPTCR, H1–H4 or MLC is proved here. Independent specialist review is still needed.

## 1. The precise (p2) representative and quantifiers

Genadi Levin, [*Rays to Renormalizations*](https://arxiv.org/pdf/2010.15386), arXiv:2010.15386v2, **printed p. 3, (p1)–(p2)**, defines the additional condition as follows (paraphrased, preserving quantifiers):

> There must **exist** a representative \(W_*,W_{*,1},g)\) of the specified polynomial-like renormalization, and **exist** \(b_*>0\), such that **every** point \(z\) of \(\partial W_{*,1}\) lying on **any ambient-polynomial external ray** that has **at least one accumulation point** in \(K_g\) has ambient Green level \(G_f(z)\ge b_*\).

The boundary in the quantified clause is the **source** \(\partial W_{*,1}\), not just the target \(\partial W_*\). The potential is for the **ambient degree-two polynomial** \(f\), not for the polynomial-like return \(g=f^p\). An ambient ray may cross either boundary multiple times. Levin's p. 3 puzzle-thickening paragraph supplies a *sufficient construction*, not an extra requirement that every representative must be puzzle-shaped.

Here \(f(z)=z^2+c_{\rm tip}\), the uniquely isolated real root documented in [the tip audit](period27_misiurewicz_tip_ray_access_20261106.md), with critical point 0 strictly preperiodic (preperiod 10, eventual **repelling period 9**). The [complex 3/9 audit](nonattracting_tip_complex_two_scale_20261106.md) proves, using exact dyadic margins and classical Rouché/Riemann–Hurwitz/connectedness inputs, that for \(p=3,9\),

\[
U_3=D(0,1/4),\quad U_9=D(0,1/32),\qquad
g_p=f^p:V_p\longrightarrow U_p
\]

are proper, degree-two polynomial-like restrictions, with **Jordan** \(V_p\Subset U_p\), connected \(K_p\Subset V_p\), and \(K_9\subset K_3\subsetneq K(f)\). Hence **the explicit representative for (p2) is**
\[
(W_*,W_{*,1},g)=(U_p,V_p,f^p)\quad(p=3,9).
\]
This is not an assertion that the round boundaries avoid the ambient Julia set.

## 2. The missing simple lemma: locally connected ambient Julia sets

**Lemma (uniform Green boundary separation).** Let \(P\) be a polynomial with connected, **locally connected** filled Julia set \(K(P)\). Let \(g=P^r:V\to U\) be a polynomial-like restriction with compact \(K_g\subset V\). Then \((U,V,g)\) satisfies Levin's condition (p2).

**Proof.** Since \(K(P)\) is connected, its normalized inverse Böttcher map
\[
\psi:\{w:|w|>1\}\longrightarrow\mathbb C\setminus K(P)
\]
is a conformal bijection. Since \(K(P)\) is locally connected, Carathéodory's theorem extends \(\psi\) continuously over \(|w|=1\); write \(\gamma(\theta)=\psi(e^{2\pi i\theta})\) for the landing point of the ray of angle \(\theta\). This is a continuous landing map for **every** ambient ray (not a claim of unique landing *angle* per Julia point).

The compact sets \(K_g\) and \(\partial V\) are disjoint; put
\[
\delta:=\operatorname{dist}(K_g,\partial V)>0.
\]
For \(0<t\le1\), define the actual uniform near-landing modulus
\[
\omega(t)=\max_{\substack{\theta\in\mathbb R/\mathbb Z\\0\le s\le t}}
\left|\psi(e^{s+2\pi i\theta})-\gamma(\theta)\right|.
\]
Compact uniform continuity of the extended Böttcher map gives \(\lim_{t\downarrow0}\omega(t)=0\). Choose any integer \(N\ge1\) satisfying \(\omega(2^{-N})<\delta\), and set the **strictly positive uniform ambient Green margin**
\[
\boxed{b_*=2^{-N}>0.}
\]
For every ambient ray \(R_\theta\) with a limit point in \(K_g\), Carathéodory landing implies \(\gamma(\theta)\in K_g\). Every point \(z=\psi(e^{s+2\pi i\theta})\) on that ray with \(0<s\le b_*\) then lies at distance less than \(\delta\) from \(K_g\) and hence cannot lie on \(\partial V\). As the ambient Green potential satisfies \(G_P(z)=s\), **every** intersection with \(\partial V\) has \(G_P(z)>b_*\), establishing (p2). This excludes *all* low-potential crossings, not just the first crossing or only rational rays. \(\square\)

**Why local connectivity is valid at this exact tip.** The critical point is strictly preperiodic to a repelling cycle, so it is nonescaping and the polynomial is subhyperbolic by the usual critical-orbit criterion; see **John Milnor**, [*Dynamics in One Complex Variable*, Theorem 14.4](https://abel.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf). The same source's Theorem **17.3** gives connected \(K(f)\), **17.5** gives local connectivity of connected subhyperbolic \(K(f)\), and **17.4(c)** identifies this with the continuous boundary extension of the inverse Böttcher map. The older [Douady–Hubbard Orsay notes](https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf), Chapter 4, also state that critically preperiodic polynomials have connected locally connected filled Julia sets.

Apply the lemma **separately for p=3 and p=9** using the proven \(K_p\Subset V_p\). It yields margins \(b_3,b_9>0\) for the **same ambient Green function**. \(\min(b_3,b_9)>0\) works simultaneously. This is an existence proof with a definite modulus-of-continuity prescription for choosing a positive \(b_p\), **not a computed numerical/dyadic lower bound**: no finite algorithm for evaluating the supremum \(\omega\) or distance \(\delta\) is claimed. Such a numerical bound is *not* part of Levin's existential (p2) statement.

**Important boundary distinction:** The proof does **not** require \(\partial V_p\) to be disjoint from the ambient Julia set. A boundary point in \(J(f)\) has ambient Green potential zero, but is not an *external-ray point*, and low-potential segments of rays **landing in \(K_p\)** cannot reach it. Therefore the possibility \(\partial V_p\cap J(f)\ne\varnothing\) is not a counterexample to (p2).

## 3. Actual two-scale Levin ray maps and eligible portrait rays

With **(p1)** from the complex-domain audit and **(p2)** above, Levin **Theorems 1–3** (printed pp. 5–6) apply at each \(p\). Let
\[
\Lambda_p=\{\theta\in\mathbb R/\mathbb Z:
 R_\theta(f)\text{ has a limit point in }K_p\}.
\]
The ray correspondence defines the genuine source-specific angle map
\[
\Pi_p:\Lambda_p\to\mathbb R/\mathbb Z,\qquad
\Pi_p(2^p\theta)=2\Pi_p(\theta)\pmod1,
\]
which is onto, finite-to-one and extends to a continuous monotone circle map of degree one. For internal degree two, Levin Theorem 3(e)'s straightening rotation \(k/(2-1)\) is zero modulo one. These maps are **not** the exterior \(f^6\) map and are **not** KL localization-sheet functors.

The [18-angle landed portrait](levin_tip_ray_correspondence_20261106.md) provides two known rays at each \(x_{10},\ldots,x_{18}\). From the *actual complex phase disjointness* in the 3/9 audit, one may determine their eligibility, not just guess it:
- At scale **9**, \(x_9\in K_9\) and \(x_{9+j}=f^j(x_9)\) lies outside \(V_9\) for \(1\le j\le8\). Only \(x_{18}=f^9(x_9)\in K_9\) among those nine portrait points. Thus **exactly two of the 18 recorded rays** are in \(\Lambda_9\): \(114/511,397/511\).
- At scale **3**, \(x_{9+3k}\in K_3\), \(k=1,2,3\), whereas the other six portrait points lie in the disjoint phase-1 or phase-2 images of \(V_3\). Thus **exactly six of the 18 recorded rays** are in \(\Lambda_3\): at \(x_{12}\), \(110/511,401/511\); at \(x_{15}\), \(142/511,369/511\); at \(x_{18}\), \(114/511,397/511\).

This is an eligibility classification **within the 18 already certified rays**, not a claim that these are all ambient rays accumulating on either \(K_p\).

### Period nine: an unconditional, noninjective fiber

The point \(x_{18}\) is a repelling fixed point of \(g_9=f^9\), hence in \(J_9\). Both ambient angles \(114/511\) and \(397/511\) are fixed by multiplication by \(512\). The internal doubling map has just one fixed angle, zero. Theorem 3(b) therefore gives
\[
\boxed{\Pi_9(114/511)=\Pi_9(397/511)=0.}
\]
This **is** a noninjective fiber of an actually established Levin map (conditional only on the separately identified classical analytic theorems), not a collision of an unrelated ambient \(f^6\) angle map.

### Period three: a *different*, separated pair of internal accesses

The points \(x_{12},x_{15},x_{18}\) form a repelling **3-cycle for \(g_3=f^3\)**. All six eligible ambient angles are fixed under \((\times8)^3\); their internal images under \(\Pi_3\) are therefore in \(\{0,1/7,\ldots,6/7\}\). They **cannot** map to zero: an internal angle-0 ray is fixed under the quadratic straightening, so its singleton landing point would be fixed by \(g_3\), whereas each of these three points has least \(g_3\)-period 3 (Levin Theorem 1 preserves landing sets).

Write \(a=7\Pi_3(110/511)\) and \(b=7\Pi_3(114/511)\) as nonzero residues modulo 7. The six ambient angles occur in ascending circular order
\[
110,\ 114,\ 142,\ 369,\ 397,\ 401\pmod {511}.
\]
Semiconjugacy under multiplication by 8 gives their corresponding internal residues in that order:
\[
[a,\ b,\ 4b,\ 2a,\ 4a,\ 2b]\pmod7.
\]
A continuous **monotone degree-one extension** (Levin Theorem 3(d)) must preserve their weak cyclic order, so these six residues have **at most one strict circular descent**. Exact enumeration of \((a,b)\in\{1,\ldots,6\}^2\) gives the **unique solution** \((a,b)=(4,5)\). See [the Python exact checker](verify_tip_levin_transport.py) and the \`three_scale_monotone_forced\` theorem in [TipRayPortrait.lean](../../TipRayPortrait.lean).

| Ambient angle | Landing point | Internal \(\Pi_3\) |
|:--|:--|:--|
| 110/511 | \(x_{12}\) | 4/7 |
| 114/511 | \(x_{18}\) | **5/7** |
| 142/511 | \(x_{15}\) | 6/7 |
| 369/511 | \(x_{15}\) | 1/7 |
| 397/511 | \(x_{18}\) | **2/7** |
| 401/511 | \(x_{12}\) | 3/7 |

Hence the two physical rays at \(x_{18}\) are **separate internal period-three rays** for the outer renormalization, but are sent to **the single internal fixed angle zero** by the inner period-nine renormalization:
\[
(\Pi_3(114/511),\Pi_3(397/511))=(5/7,2/7),\qquad
(\Pi_9(114/511),\Pi_9(397/511))=(0,0).
\]
This comparison concerns **two different codomains** (the two quadratic straightenings) and is not a claim of a commuting map between those codomains.

## 4. Proof trust, reproducibility, and still-open obligations

Run from the repository root:

~~~sh
lake build TipRayPortrait TipComplexMargins
python research/independent_audits/verify_tip_ray_portrait.py --check-manifest
python research/independent_audits/verify_tip_complex_domains.py --check-manifest
python research/independent_audits/verify_tip_levin_transport.py
~~~

The new finite check establishes only the modular dynamics, selected eligibility **index arithmetic** and unique cyclic-order solution. It does not formalize Carathéodory, repelling landing, Julia set local connectivity, Levin's theorem or KL puzzle geometry. The source of the analytical connection is the above **uniform Carathéodory lemma**, not a numerical test.

**Remaining limitations:** no numerical dyadic \(b_p\), no exhaustive classification of *all* \(\Lambda_p\) ray fibers, no source-faithful Kahn–Lyubich **primitive** puzzle/separator/shallow/deep time/closed pullback/access table, no based localization sheet/coset groupoid, and no naturality identification between that groupoid and \(\Pi_3,\Pi_9\). Those separate objectives remain in [Issue #29](https://github.com/dovvnloading/loops-research-archive/issues/29). The 465-entry source-locked ledger, H1–H4, UPTCR and the global MLC status are **unchanged**.

**Attribution and scope:** This new argument, finite checker and Lean finite implication were prepared with OpenAI GPT-6. All classical sources are cited separately; they do not imply endorsement or external referee verification.
