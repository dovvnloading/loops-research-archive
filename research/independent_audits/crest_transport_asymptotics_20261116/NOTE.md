# Crest transport on the real primitive-tip family: full circular collars and asymptotics

**Audit 2026-11-16. Status: FINITE INTERVAL THEOREM, CONDITIONAL CONFORMAL INTERPRETATION, NUMERICAL ASYMPTOTIC CONJECTURE.** This additive audit does **not** prove an all-period positive transport bound, a vanishing theorem, or an unrestricted KKL-maximal Wave. It does not edit either source audit or native wave transfer. All displayed finite enclosures below are computed in `verify.py` and locked byte-for-byte in `results.json`.

## Precisely which optimum?

Let \(f_c(z)=z^2+c\), \(G_p=f_c^p\), \(x_j=f_c^j(0)\), and select the distinguished branch \(x_{6p}=-x_{3p}>0\) with the ordered cuts of the merged [crest audit](../crest_transport_tip_family_20261116/NOTE.md) and the [physical finite-tip audit](../real_primitive_tip_family_unconditional_20261116/NOTE.md). The **given parent** is the actual \(p=3\) Wave \(d=-9/64\), \(3/256<r<1/64\), or, for \(p\ge4\), the *chosen, noncanonical* Wave \(d=-3x_p/4\), \(x_p/16<r<(p-1)x_p/(8p)\). The full-parent width is conditionally \(\log R_p/(2\pi)\), where \(R_3=4/3\) and \(R_p=2(p-1)/p\). In particular, the older small certified bin collars were **not** the full admissible collars.

For **this fixed circular parent and the same selected q-side terminal branches**, the admissible radii are exactly those for which the first imaginary-axis crossing, on the marked branch \(-1/8<u=\cos\theta<1/4\), has positive upper imaginary image and its third real return \(t_3(r)\) lies **strictly** between \(-x_p\) and \(-x_{4p}\); the source/target q and w gates, genuine four-step marked paths, central properness, complex disk and terminal target gates must also hold. The verifier proves that, for the finite periods listed, all these *other* gates hold throughout the resulting interval. This yields a **unique maximal connected circular collar** \(C_p^*=(a_p^*,b_p^*)\) in the specified parent. The qualified quantity is
\[
 c_p^* :=\sup_{(a,b)\subset C_p^*}\frac{2\pi}{\log R_p}
 \int_a^b\frac{dr}{r\,\arccos u_p(r)}
 =\frac{2\pi}{\log R_p}\int_{a_p^*}^{b_p^*}\frac{dr}{r\,\arccos u_p(r)}.
\]
The integral identity and its interpretation as **actual descendant conformal width** are **conditional** on the imported locally connected slit/prime-end realization, KKL proper restriction/surviving path subfamily, complex univalence and exact logarithmic-strip conformal-width hypotheses. The rational computations, real dynamics, Rouché margins, disk enclosures and *conditional* optimization of that integral are finite theorems independent of those analytic hypotheses. This is **not** a supremum over arbitrary centres, all KKL descendants, or the unrestricted canonical/maximal KKL Wave.

## Certified complete circular-collar data

The table gives outward rational enclosures for \(c_p^*\). Every decimal endpoint represents an **exact fraction** with denominator \(10^5\); each row is strictly inside the indicated outer enclosure, and the true integral ratio is between the endpoints, not sampled or merely optimized on 512 bins. The endpoint radii themselves are rationally bracketed at up to 55 bisections in `results.json`. For \(p\ge4\), the radial variable is \(s=r/x_p\); for \(p=3\) the radii are absolute. The lower endpoint is the parent inner circle for \(p\ge6\), and a collision with the source cut \(-x_{4p}\) for \(p=3,4,5\). The **upper endpoint for every period** is the strict collision \(t_3(r)=-x_p\), *not* a chosen bin endpoint.

| \(p\) | Certified \(c_p^*\) interval | Active lower bound | Terminal upper normalized \(b_p^*/x_p\) (illustrative decimal only) |
|---:|:---:|:---|---:|
| 3 | (0.98017, 0.98038) | \(t_3=-x_{4p}\) | 0.06939717 |
| 4 | (0.62810, 0.62818) | \(t_3=-x_{4p}\) | 0.06700756 |
| 5 | (0.52758, 0.52764) | \(t_3=-x_{4p}\) | 0.06652580 |
| 6 | (0.47562, 0.47566) | \(s=1/16\) | 0.06641495 |
| 7 | (0.44735, 0.44740) | \(s=1/16\) | 0.06638787 |
| 8 | (0.43006, 0.43010) | \(s=1/16\) | 0.06638115 |
| 9 | (0.41809, 0.41813) | \(s=1/16\) | 0.06637947 |
| 10 | (0.40920, 0.40924) | \(s=1/16\) | 0.06637905 |
| 11 | (0.40231, 0.40235) | \(s=1/16\) | 0.06637894 |
| 12 | (0.39680, 0.39684) | \(s=1/16\) | 0.06637892 |
| 13 | (0.39229, 0.39233) | \(s=1/16\) | 0.06637891 |
| 14 | (0.38853, 0.38857) | \(s=1/16\) | 0.06637891 |
| 15 | (0.38534, 0.38538) | \(s=1/16\) | 0.06637891 |
| 16 | (0.38261, 0.38265) | \(s=1/16\) | 0.06637891 |

For \(p=9,\ldots,16\), the **new** independently checked signed local parameter root, full physical cut order, named inverse-cut images, unique real fixed \(\alpha\), degree-two central Rouché margin \(>1/25\), and **pairwise-disjoint full complex phase disks** extend the earlier \(p\le12\) finite certificates. Roots are isolated by strict rational endpoint signs in adjacent \(2^{-256}\) brackets and negative derivative on the entire rational seed interval, not by trusting decimal seed values. Uniqueness is **local to each chosen seed**; no global uniqueness in the entire real parameter window is claimed. Prior \(p\le12\) root branches are crosschecked against the frozen source certificates. The full parent and all remaining gates are then checked with interval arithmetic for each period.

## Why these are global optima **within the declared circular family**

The bound on \(G_p'\) is obtained without expanding a degree-\(2^p\) polynomial. If \(d_k=f_c^k(d)\), \(A_k=(f_c^k)'(d)\), and \(D_k,E_k\) bound respectively \(|f_c^k(d+h)-d_k|\) and \(|(f_c^k)'(d+h)-A_k|\) for \(|h|\le b_{\rm parent}\), the outward recursions are
\[
 D_{k+1}\le2|d_k|D_k+D_k^2,\qquad
 E_{k+1}\le2|d_k|E_k+2D_k(|A_k|+E_k),\qquad
 A_{k+1}=2d_kA_k.
\]
For each parent, the verified strict inequality \(15(A_p^{\rm low}-E_p)>4E_p\) gives a positive real derivative, a strictly increasing real axis-crossing function in \(u\in[-1/8,1/4]\), positive imaginary-half-plane image, and \(\operatorname{Im}(G_p'(z)e^{i\theta})>0\) at the unique angular root. Implicit differentiation of \(\operatorname{Re}G_p(d+re^{i\theta})=0\) then yields the **strict identity**
\[
 \frac{d}{dr}\operatorname{Im}G_p(d+re^{i\theta(r)})
 =\frac{|G_p'(d+re^{i\theta(r)})|^2}{\operatorname{Im}(G_p'(d+re^{i\theta(r)})e^{i\theta(r)})}>0.
\]
The real itineraries show \((f_c^{p-1})'(c-Y^2)<0\) and \(G_p'(t_2)<0\), so \(t_2(r)=G_p(iY(r))\) increases while \(t_3(r)=G_p(t_2(r))\) **strictly decreases throughout the entire parent**. Consequently \(-x_p<t_3<-x_{4p}\) defines one and only one interval (intersected with the parent radii), bounded by the two independently certified terminal sign changes. On \((-x_p,-x_{4p})\), \(G_p\) is increasing and maps its endpoints to \(x_{2p}\), \(x_{5p}\), respectively, so \(t_4\in(x_{2p},x_{5p})\) for **every** interior radius—even arbitrarily close to the terminal cuts. The new verifier separately proves all the other q/w gate and disk tests on the **entire enclosing** collar, not just one sampled point. Positive integrand then proves the full collar maximizes the stated integral.

The angular integration uses 512 **whole-radius** interval bins on the maximal guaranteed *inner* endpoint bracket. Binwise inclusion bounds \(u\) without assuming \(u>0\), and the *outside* slivers between endpoint brackets are added to the **upper** bound with a strictly positive global angle lower bound. Lower bounds omit slivers. Machin's formula for \(\pi\), an alternating arctan remainder, a sign-symmetric arcsin Maclaurin remainder and positive atanh logarithm tails are rational; the root polynomial, disk recurrence, endpoint signs, quotient and final \(10^{-5}\) outward rounding contain **no floating-point proof step**. Thus the optimum does not depend on the original fixed bin selection. No spurious cancellation between the two q-side descendants or between old-edge slit sides is assumed.

**Typed marking** is reconstructed independently on every period. The covering operation \(G_*\) is \(S_s\mapsto I_{s\bmod10}\). The distinct immersion pullback \(\iota^*\) has cyclic blocks \([18,19,0,1,2],[3,4],[5],[6],[7,8,9],[10],[11,12,13],[14],[15],[16,17]\). It cannot be substituted for \(G_*\). The two terminal paths are upper \((S_0,S_3)\mapsto(I_0,I_3)\) with closed crest \(I_1\cup I_2\), and lower \((S_{17},S_0)\mapsto(I_7,I_0)\) with closed crest \(I_8\cup I_9\); the old-edge carriers \(I_1\) and \(I_9\) are opposite accesses to the **same** physical edge \(E_0=(x_{5p},x_{3p})\). The initial crest \(I_0\) and intermediate \(I_2,I_8\) carry no old edge. The unselected third-stage w endpoint is **not** assigned a globally fixed atom.

## Quantitative near-\(-2\) evidence and the open limit

A rigorous *finite* distortion inequality follows by writing \(G_p(z)=x_p+A_pz^2+E_p(z)\) and propagating the whole-disk Taylor remainder \(T_k\) from the exact squaring recurrence
\[
 T_{k+1}=2|x_k|T_k+(|A_k|R^2+T_k)^2,
 \quad R=5x_p/4,\qquad |E_p(z)|\le T_p\ (|z|\le R).
\]
Hence, for each certified \(p\), \(H_p(t):=G_p(x_pt)/x_p\) obeys the **proved finite enclosure**
\[
 |H_p(t)-(1-\kappa_pt^2)|\le T_p/x_p,
 \qquad \kappa_p=-A_px_p,
 \qquad |t|\le5/4.
\]
For \(p=9\), \(1.79034809<\kappa_9<1.79034810\), error \(<53449287\cdot10^{-12}\); at \(p=16\), \(1.79032749<\kappa_{16}<1.79032750\), error \(<3262\cdot10^{-12}\). All the finite integer bounds are checked by the verifier. **No uniform error estimate valid for all \(p\) follows from testing eight additional periods.**

For context, the exact Chebyshev semiconjugacy at \(c=-2\) is \(f_{-2}(2\cos\theta)=2\cos(2\theta)\). If \(c=-2+\epsilon\), \(x_j=2\cos\theta_j\), and the angles stay on a consistent real branch with both cosine arguments in \((-1,1)\), the elementary mean-value theorem gives the *explicit, rigorous local distortion*
\[
 |\theta_{j+1}-2\theta_j|
 \le \frac{|\epsilon|}{2\sqrt{1-M_j^2}},\qquad
 M_j=\max\{|\cos(2\theta_j)|,|\cos(2\theta_j)+\epsilon/2|\}<1.
\]
The denominator becomes small near endpoint angles. This inequality alone does **not** justify multiplying the finite estimates into an all-period complex \(C^1\) theorem or KKL path survival. That missing uniform distortion/prime-end control is the remaining asymptotic proof obligation.

**Numerical conjecture, NOT certified as \(p\to\infty\):** let \(\kappa\approx1.7903274919993457\) be the root near 1.79 of \(Q_\kappa^6(0)+Q_\kappa^3(0)=0\), \(Q_\kappa(t)=1-\kappa t^2\). The q-side limiting imaginary height at the upper terminal gate and the outer radius are predicted by
\[
 Y_\infty^2=\frac{\sqrt{2/\kappa}-1}{\kappa},\quad
 z_\infty=-\sqrt{\frac{1-iY_\infty}{\kappa}},\quad
 s_\infty=|z_\infty+3/4|\approx0.0663789098162239.
\]
Write \(u_\infty(s)\) for the small root of \(\operatorname{Re}Q_\kappa(-3/4+s(u+i\sqrt{1-u^2}))=0\). Then numerically
\[
 A_\infty=2\pi\int_{1/16}^{s_\infty}\frac{ds}{s\arccos u_\infty(s)}
 \approx0.2405255277163131,\qquad
 c_\infty=\frac{A_\infty}{\log2}\approx\boxed{0.3470049860435258}.
\]
The data are consistent with \(A_p=A_\infty+O(4^{-p})\), so **conjecturally**
\[
 c_p^*=\frac{A_\infty}{\log(2-2/p)}+O(4^{-p})
 =c_\infty\left(1+\frac1{p\log2}+O(p^{-2})\right)+O(4^{-p}).
\]
Thus the proposed asymptotic transport does **not** degenerate for this selected family: the normalized terminal collar converges to \((1/16,s_\infty)\) with positive logarithmic length. The conspicuous decrease in \(c_p^*\) is primarily the **chosen parent normalization** \(\log(2-2/p)\nearrow\log2\), plus exponentially smaller geometric changes. The limiting conclusion and claimed \(O(4^{-p})\) rate are numerical conjectures, **not** proved for every real primitive tip or unrestricted Wave. A true all-period theorem requires a certified quantitative complex-domain Chebyshev/C¹ estimate, persistence of genuine KKL pullbacks, endpoint transversality, Koebe/noncancellation and prime-end width comparison uniformly in \(p\).

## Reproduction, CI and hostile-review boundary

From repository root (Python 3.12+, standard library only):

```sh
python research/independent_audits/crest_transport_asymptotics_20261116/verify.py
python -m unittest discover -s research/independent_audits/crest_transport_asymptotics_20261116 -p 'test_*.py' -v
python research/independent_audits/crest_transport_tip_family_20261116/verify.py
python research/independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py
lake build TipKKLTreeMarking TipNativeProperRestriction
```

The new verifier is **read-only by default**; `--write` deliberately regenerates its locked JSON. The dedicated `.github/workflows/crest-transport-asymptotics.yml` checks the finite recomputation, seven adversarial tests, source regressions and existing Lean finite targets, and requires the unchanged research-validation/weighted Lean workflows at the exact PR SHA. Python does not formalize physical KKL/prime-end realization or conformal width; Lean's unchanged discrete models do not prove these complex-analytic hypotheses either.

Hostile-review cases addressed: a wrong nearby real root; adjacent 256-bit parameter cells and local derivative; two-to-one global covering versus degree-two *central* restriction; separately recomputed \(G_*\) versus \(\iota^*\); full parent versus selected optimum; uniqueness of the first angular gate and monotonicity of \(t_3\); strict open boundary cuts and small endpoint slivers; upper/lower **same-edge** slit incidence; the unselected third-stage endpoint; negative angular cosines and sign-symmetric arcsin; the last real return at the two terminal cuts; complete complex phase disks; and outward transcendental tails. **Still open:** canonical KKL-maximal collars, uniformly quantified all-\(p\) analytic/physical realization, rigorous \(c_\infty\), and any universal Wave transport conclusion beyond this fixed chosen family.
