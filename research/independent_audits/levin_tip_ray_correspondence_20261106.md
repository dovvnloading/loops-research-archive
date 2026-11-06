# The overlooked ray-correspondence interface at the real Misiurewicz tip

> **2026-11-06 progress addendum:** The new [nonattracting complex 3/9 certificate](nonattracting_tip_complex_two_scale_20261106.md) now constructs concrete connected proper quadratic-like restrictions at the tip, using Lean-certified finite bounds plus Rouché/Riemann–Hurwitz. This supplies Levin **(p1)** under those named classical analytic inputs. **(p2) remains open**, so the renormalization-ray map and forced angular fiber remain explicitly conditional. Earlier text below records the pre-certificate frontier.


**Research audit, 2026-11-06.** Mathematical status: exact nine-cycle angular portrait (Lean kernel + independent integer/rational regression), with ray landing inherited from a cited theorem of Zakeri. The proposed **renormalization-ray projection is conditional** on substantial complex-geometric hypotheses that this archive has **not** verified. No KL sheet/prime-end functor or global MLC gate is claimed.

## 1. A source that actually covers connected quadratic Julia sets

Genadi Levin, *Rays to Renormalizations*, arXiv:2010.15386v2 (2021), printed pp. 3–6, is a better starting point for the missing external-access interface than an unmarked six-iterate physical ray map. Read **assumptions (p1), (p2)** on printed p. 3 and **Theorems 1–3** on printed pp. 5–6.

- **(p1)** Requires a connected proper polynomial-like filled set \(K_g\subsetneq K_P\) with \(g=P^r\) near \(K_g\). A real restrictive interval alone is NOT (p1).
- **(p2)** Requires a polynomial-like representative \((W_*,W_{*,1},g)\) and a **positive Green-level lower bound** for ambient rays meeting its source boundary and accumulating on \(K_g\). This can be arranged in an appropriate Yoccoz puzzle construction, but neither the explicit domains nor their boundary crossing bound have yet been supplied at the tip.
- With **both** conditions, Levin Theorem 1 associates ambient rays to polynomial-like rays, preserving accumulation sets and the relevant prime end. Theorem 2(a) lifts access to an actual ambient ray. Theorem 3 gives a finite-to-one, continuous, monotone (after extension) angle semiconjugacy on a **proper compact ray-angle subset** \(\Lambda_r\), not on the entire ambient circle.

For the intended *degree-two* period-nine renormalization the source relation is
\[
  \Pi_9(512\theta)=2\,\Pi_9(\theta)\pmod1
  \qquad(\theta\in\Lambda_9).
\]
For period three it is \(\Pi_3(8\theta)=2\Pi_3(\theta)\). Here the ambient multiplier is the degree of \(P^r\), while the **internal** multiplier is the **quadratic-like degree 2**. Thus the previously studied \(f^6\) map on full-plane exterior rays is NOT itself a Levin renormalization projection. The 2022 Petersen–Zakeri theorem about external-angle correspondence has an important degree/disconnectedness restriction; the special case of **connected degree-two ambient polynomial** should be sought in Levin instead.

**Canonical-angle observation.** Levin Theorem 3(e) allows a rotation ambiguity \(k/(m-1)\) for degree \(m\). For \(m=2\) this is an integer rotation and is trivial modulo one. Therefore, *if the map exists*, the angular correspondence does not depend on a choice of normalized quadratic straightening in the way the higher-degree case can.

Primary sources: [Levin, arXiv:2010.15386](https://arxiv.org/pdf/2010.15386), especially pp. 3, 5–6; [Petersen–Zakeri 2022](https://doi.org/10.1112/jlms.12572) for comparison. No author endorsement or peer review is implied.

## 2. Exact nine-cycle ray-access portrait

At the previously certified nonattracting tip \(c_{\mathrm{tip}}\), the critical orbit \(x_j=P_{c_{\mathrm{tip}}}^j(0)\) has **preperiod 10**, period **9**, and a repelling nine-cycle. Zakeri, *External Rays and the Real Slice of the Mandelbrot Set*, Theorems 3.1/3.3, gives actual dynamical rays landing at \(x_1=c_{\mathrm{tip}}\) with angles
\[
  \theta_-={116791\over261632},\qquad
  \theta_+={144841\over261632}.
\]
Since the ambient dynamical ray of angle \(\theta\) maps to the ray of angle \(2\theta\), both rays with angles \(2^{j-1}\theta_\pm\bmod1\) land at \(x_j\) for all \(j\ge1\). This uses actual ray landing/naturality, not numerical ray pictures.

After nine forward doublings the angles enter a *primitive period-nine* cycle:
\[
  2^9\theta_-={283\over511},\quad
  2^9\theta_+={228\over511}\pmod1.
\]
Thus both of the earlier archive's period-nine *candidate* characteristic fractions are **actually landed dynamical rays at the repelling point \(x_{10}\)** of the new, nonattracting tip. They are not thereby proved to be characteristic **parameter-root** rays for the old attracting center.

Here is the complete exact landed-pair table (the entries in each row are in ascending circular order):

| Landing point | Ambient ray angles |
|---|---|
| \(x_{10}\) | \(228/511,\ 283/511\) |
| \(x_{11}\) | \(55/511,\ 456/511\) |
| \(x_{12}\) | \(110/511,\ 401/511\) |
| \(x_{13}\) | \(220/511,\ 291/511\) |
| \(x_{14}\) | \(71/511,\ 440/511\) |
| \(x_{15}\) | \(142/511,\ 369/511\) |
| \(x_{16}\) | \(227/511,\ 284/511\) |
| \(x_{17}\) | \(57/511,\ 454/511\) |
| \(x_{18}\) | \(114/511,\ 397/511\) |

Each angle has *least* doubling period nine. All **18 angles** are distinct and all nine chords connecting each landed pair are **pairwise unlinked**. These claims are formally reduced by the Lean kernel in [TipRayPortrait.lean](../../TipRayPortrait.lean) without proof holes and independently rechecked by [the exact standard-library regression](verify_tip_ray_portrait.py). The checked [manifest](../../results/period27_tip_ray_portrait.json) holds the exact pair list.

**Scope:** the statements give *at least* the two named rays landing at each of nine points; no assertion is made that they are the only rays, that the chord portrait is a complete Hubbard tree, or that any pair provides a KL dividing puzzle boundary. Notably these endpoints are **postcritical**: using them blindly as vertices of a KL puzzle which must avoid the critical orbit would be invalid. The genuine KL dividing fixed point and its pullbacks remain separate construction targets.

## 3. A forced noninjective fiber of any qualifying renormalization ray map

The certified real period-nine restrictive interval is
\[
 I_9=[x_9,x_{18}], \qquad f^9(I_9)=I_9.
\]
Its positive endpoint \(x_{18}\) is a repelling fixed point of \(f^9\). The exact ambient rays landing there have angles \(114/511\) and \(397/511\). Both are **fixed under the ambient return**:
\[
 512(114/511)\equiv114/511,\quad
 512(397/511)\equiv397/511\pmod1.
\]

**Conditional theorem.** Suppose at this exact parameter a connected degree-two polynomial-like restriction \(f^9:V_9\to U_9\) has been produced with \(I_9\subset K_9\subsetneq K(f)\), and it admits a representative satisfying Levin's **(p2)**. Then \(x_{18}\in J_9\), because it is a repelling periodic point of the return. Both displayed ambient rays belong to Levin's admissible ray set \(\Lambda_9\); Theorem 3 supplies \(\Pi_9\) on this set. Semiconjugacy forces
\[
 \Pi_9(114/511)=2\Pi_9(114/511),\qquad
 \Pi_9(397/511)=2\Pi_9(397/511)\pmod1.
\]
Doubling on the circle has **only one fixed angle, zero**. Consequently
\[
 \boxed{\Pi_9(114/511)=\Pi_9(397/511)=0.}
\]
The two distinct external accesses would therefore be a **noninjective, source-defined renormalization-ray fiber** on the ninth return, not merely a collision under \(f^6\). This conclusion is a theorem *conditional on explicitly itemized geometric inputs*, not proof those inputs exist.

The Lean statements [two_fixed_rays_forced_to_one_internal_angle](../../TipRayPortrait.lean) and [tip_phase_eighteen_forced_fiber](../../TipRayPortrait.lean) kernel-prove the algebraic logical implication for arbitrary rational internal angle grids. They **do not construct** \(\Pi_9\), verify the imported complex-analysis hypotheses, or identify the based localization sheet/coset groupoid of Paper 1.

## 4. The next decisive experiment and first-failure ledger

1. **Build \(V_9\Subset U_9\) at the nonattracting tip** and certify proper degree two and *connected* \(K_9\), using the actual \(c_{\mathrm{tip}}\) rather than importing the old attracting-center disk estimates. Require \(I_9\subset K_9\) (particularly \(x_{18}\)).
2. **Check Levin (p2), not just (p1)**: explicitly supply a representative and a uniform positive Green-potential lower bound for source-boundary intersections of every qualifying ambient ray. The source describes a suitable puzzle-thickening method; implement its hypotheses.
3. **Identify \(\Lambda_9\) and \(\Pi_9\)** and compare the forced \(\{114/511,397/511\}\) fiber to the source's almost-injectivity classification. Record any additional rays/accesses or a failed p2 as the first obstruction.
4. **Repeat at the three-return scale** and construct the inter-scale *natural transformation*. There is **no theorem here** identifying a \(\Pi_9\)-fiber with a \(\Pi_3\)-fiber or a KL localization cover groupoid. The six-iterate ordinary ambient angle map is not a substitute.
5. **Keep source eligibility straight:** the current nonattracting tip has \(K=J\), unlike the earlier period-27 center, but a real interval certificate alone does not grant every KL primitive/nest hypothesis.

| Gate | State after this audit |
|---|---|
| Nine actual dynamical landing pairs from source + exact angular arithmetic | Verified (analytic ray input imported; finite algebra Lean-checked) |
| Unlinked 18-angle chord portrait and least angular period nine | Lean-checked |
| Forced double-ray fiber for any qualifying \(\Pi_9\) | Lean-checked conditional implication |
| Quadratic-like \(3/9\) complex domains **at the tip**, Levin (p1)/(p2) | Open |
| Realized \(\Pi_9,\Pi_3\), compatible prime-end/sheet transport | Open |
| MLC ledger gates H1–H4, UPTCR | Open / unchanged |

**Reproduce:** run \`lake build TipRayPortrait\` and \`python research/independent_audits/verify_tip_ray_portrait.py --check-manifest\` from the repository root. These only prove finite logic and arithmetic *as encoded*. Geometric applicability requires the separately named hypotheses and independent specialist review.
