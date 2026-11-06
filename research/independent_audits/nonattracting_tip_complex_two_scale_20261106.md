# Two actual complex quadratic-like returns at the nonattracting Misiurewicz tip

> **Later addendum (2026-11-06):** The separate source-level condition Levin **(p2)**, called open in this pre-existing domain certificate, is now met by the same explicit U₃,V₃ and U₉,V₉ representatives via [a new uniform Carathéodory/Green-potential argument](levin_tip_p2_carathéodory_two_scale_20261106.md). The potential bound is positive by compact uniform continuity, but no numerical dyadic bound is computed. This original note's p2-open conclusion reflects its earlier date, not the latest proof state. The KL prime-end/sheet transport and global MLC gates remain open.

**Audit date: 2026-11-06.** Exact finite inequalities are independently checked in [TipComplexMargins.lean](../../TipComplexMargins.lean) (kernel-recomputed) and [verify_tip_complex_domains.py](verify_tip_complex_domains.py) (signed integers at resolution 2^-224). The complex-analytic interpretation below invokes **classical Rouché, Riemann–Hurwitz, and polynomial-like connectedness theorems**; these are NOT yet formalized in Lean. Neither Levin (p2), a Kahn–Lyubich source puzzle, localization sheets, nor MLC is established here.

## Exact parameter and real return data

Let \(f(z)=z^2+c_{\rm tip}\), where \(c_{\rm tip}\) is the unique real zero of
\[
P_{18}(c)+P_9(c)=0,\quad P_0=0,\quad P_{j+1}=P_j^2+c
\]
in the rational bracket
\[
-607918036626757496169199575185708826140/2^{128}
<c_{\rm tip}<
-607918036626757496169199575185708826139/2^{128}.
\]
The [prior tip audit](period27_misiurewicz_tip_ray_access_20261106.md) establishes strictly preperiodic critical dynamics (preperiod 10, eventual **repelling period nine**), with \(K(f)=J(f)\) by the classical Misiurewicz criterion. Put \(x_j=f^j(0)\). The source-certified real restrictive intervals satisfy
\[
 I_3=[x_6,x_3],\quad I_9=[x_9,x_{18}]\subset\operatorname{int}I_3,\quad
 f^3(I_3)=I_3,\quad f^9(I_9)=I_9.
\]
For the second equality, \(x_{18}=-x_9\) implies \(x_{19}=x_{10}\), \(x_{27}=x_{18}\), and the unique turning point under the return is \(0\) with \(f^9(0)=x_9\); the endpoint images cover the required extrema.

## The complex theorem with its imported analytic ingredients

Define \(U_3=D(0,1/4)\), \(U_9=D(0,1/32)\). For \(p\in\{3,9\}\), let \(V_p\) be the connected component containing 0 of the inverse image \(f^{-p}(U_p)\) lying inside \(U_p\).

**Theorem.** At this exact **nonattracting** parameter:

1. Both \(V_p\Subset U_p\) are Jordan disks and \(f^p:V_p\to U_p\) is a proper degree-two quadratic-like map with exactly one simple critical point, 0.
2. The domains obey
   \[
   \overline{V_9}\subset D(0,27/1024)\Subset U_9
   \subset V_3\Subset U_3.
   \]
3. The complex phase images \(f^j(V_3)\) for \(0\le j<3\) are pairwise disjoint, as are \(f^j(V_9)\) for \(0\le j<9\), and
   \[
   f^{3k}(U_9)\subset V_3\ (k=0,1,2),\qquad
   f^j(V_9)\subset f^{j\bmod3}(V_3)\ (0\le j<9).
   \]
4. Their filled Julia sets \(K_3,K_9\) are connected; \(I_p\subset K_p\), and
   \[
   K_9\subset K_3\subsetneq K(f).
   \]
   Consequently both scales satisfy the **Levin (p1) connected, proper quadratic-like renormalization input**, not automatically his separate condition (p2).

### Exact Rouché margins

The polynomial identity
\[
f^j(z)=x_j+a_jz^2+h_j(z),\quad
a_1=1,\ a_{j+1}=2x_ja_j,\quad
h_1=0,\ h_{j+1}=2x_jh_j+(a_jz^2+h_j)^2
\]
implies the analytic majorant recurrence
\[
 T_1(R)=0,\qquad
 T_{j+1}(R)\le 2|x_j|T_j(R)+
            (|a_j|R^2+T_j(R))^2
\]
for \(|z|\le R\). Every \(x_j,a_j\) is enclosed by signed outward dyadic intervals for *all* parameters in the exact \(2^{-128}\) bracket. All positive-error products round up, and the leading \(|a_p|R^2\) rounds down. The source-circle test
\[
\boxed{|a_p|R^2>|x_p|+T_p(R)+R_{\rm target}}
\]
has the following **strict conservative rational margins**, in decimal truncation:

| Source radius | Target radius | Strict certified positive margin |
|---|---|---:|
| \(1/4\), return 3 | \(1/4\) | \(>0.127132476\) |
| \(1/32\), return 9 | \(1/32\) | \(>0.021187404\) |
| \(27/1024\), return 9 | \(1/32\) | \(>0.002966858\) |

The old *attracting-center* \(13/512\) shrink has a **nonpositive lower bound** at this different tip, so the old radius certificate does not transfer. This does NOT prove a domain at \(13/512\) impossible. The strictly larger \(27/1024\) circle repairs the inequality.

For any \(|w|<R_{\rm target}\), Rouché's theorem compares \(f^p(z)-w\) with \(a_p z^2\) on the source circle: exactly **two roots counted with multiplicity** lie inside the circle. The interval certificate checks that \(f^j(U_p)\) never meets 0 for \(1\le j<p\), hence \(f^p\) has the sole critical point 0 on that source, with local degree two and critical value \(x_p\in U_p\). Branching over this value puts both preimages in one connected component. The strict boundary condition gives properness and compact containment. Because no critical point lies on the preimage of the target boundary, this component has smooth finite boundary. Riemann–Hurwitz yields \(\chi(V_p)=2\chi(U_p)-1=1\), hence the connected planar domain is a Jordan disk. The third Rouché test counts all two roots **already inside** \(D(0,27/1024)\), forcing \(\overline{V_9}\) into that smaller disk.

### Strict phase separation and true complex refinement

Using the same expansions, the stage-\(j\) image of each source disk is enclosed by a complex disk centered at \(x_j\) of radius \(|a_j|R^2+T_j(R)\). Exact interval-gap calculations give:
\[
 \mathrm{minGap}_{3}>0.927889313,\qquad
 \mathrm{minGap}_{9}>0.003222141.
\]
For the nine inner phases it is essential to use the **shrunken** radius \(27/1024\), because only \(V_9\), not the full \(U_9\), is certified inside that circle.

A separate four-time computation for the *whole* \(U_9\) proves
\[
 f^j(U_9)\subset U_3\quad(j=0,3,6,9),
 \qquad \mathrm{minClearance}>0.052357673.
\]
For \(k=0,1,2\), the connected set \(f^{3k}(U_9)\) therefore lies in \(f^{-3}(U_3)\cap U_3\). It contains the real orbit point \(x_{3k}\in I_3\subset V_3\), so it is inside the **central component** \(V_3\). All nine physical inner phase images thus refine the corresponding outer phase images by inclusion.

### Critical nonescape, filled-set connectivity and strict nesting

The invariant real interval \(I_p\subset U_p\) contains 0 and satisfies \(f^p(I_p)=I_p\), so it lies in \(V_p\) and every return stays there. Hence \(I_p\subset K_p\) and the unique critical point does not escape the polynomial-like restriction. The classical quadratic-like connectedness criterion implies \(K_p\) is connected. The three-block inclusion \(f^{3k}(U_9)\subset V_3\) shows \(K_9\subset K_3\). The ambient bounded critical value \(x_1=c_{\rm tip}\) has absolute value \(>1/4\), hence lies in \(K(f)\) but outside \(K_3\), proving strictness.

## Reproduction and exact trust boundary

~~~sh
lake build TipComplexMargins
python research/independent_audits/verify_tip_complex_domains.py --check-manifest
~~~

The [manifest](../../results/tip_complex_domains.json) records all six rational margin floors. Lean recomputes the tip orbit, expansion coefficients, strict Rouché bounds, old-radius negative control, phase gaps, intermediate critical exclusions and four nested outer-return containments, in the already audited signed interval engine. **Lean does not formalize the complex-analysis theorems above**, the real-root IVT proof at this new tip, or the global connectedness theorem. The latter are mathematical deductions with explicitly named external inputs, and independent specialist review remains advisable.

## The next genuine source obstruction

This closes a previously missing **complex-realization layer** at a nonattracting example and supplies the hypotheses of Levin's **(p1)**, subject to the named classical complex-analysis results. It leaves the *independent* **(p2) positive Green-potential source-boundary crossing** requirement OPEN. Consequently, the forced \(114/511,397/511\) fiber in the [Levin angle note](levin_tip_ray_correspondence_20261106.md) is still **conditional**. The selected round disks are not claimed to be an applicable Kahn–Lyubich dividing puzzle: source separator \(P\), shallow \(q\), deep \(nq\), closed pullbacks, prime-end sides \(O/\xi/\eta\), based sheet/coset groupoid and compatible 9-to-3 natural transformation all remain in [Issue #29](https://github.com/dovvnloading/loops-research-archive/issues/29). The source-locked global MLC ledger is unchanged.

**Attribution:** Original real-tip proof: prior November 6 audit; complex-domain method: [the earlier attracting-center complex certificate](complex_two_scale_quadratic_like_certificate_20261105.md), now independently re-evaluated at a different nonattracting parameter; angle-correspondence source: Genadi Levin, [Rays to Renormalizations](https://arxiv.org/abs/2010.15386) Theorems 1–3. OpenAI GPT-6 produced this specific certificate, Lean code and note. No external referee confirmation or MLC claim is made.
