# Two exact obstructions at the certified period-3/period-9 complex window

**Date:** 2026-11-05. **Status:** Two elementary analytic theorems with exact signed-integer interval certificates; not a proper quadratic-like renormalization, not an external-ray/prime-end atlas, and not a result toward closing MLC itself.

**Run:** From the repository root,

~~~sh
python research/independent_audits/verify_real_nested_3_9.py
python research/independent_audits/verify_complex_window_obstructions.py
~~~

The new certificate reuses the existing outward-rounded dyadic interval arithmetic (precision \(2^{-224}\)), requires only the Python standard library, and makes no sampling or floating-point assumptions.

## 1. Setup and terminology

Let \(f_c(z)=z^2+c\). The earlier [two-scale real certificate](real_quadratic_3_9_restrictive_certificate_20261105.md) isolates a unique real root \(c_*\) of \(f_c^{27}(0)=0\) in

\[
\frac{K}{2^{128}}<c_*<\frac{K+1}{2^{128}},
\qquad K=-607890580437450502081459824019535455703.
\]

Put \(x_j=f_{c_*}^{\,j}(0)\). The real restrictive intervals are

\[
I_3=[x_6,x_3],\qquad I_9=[x_9,x_{18}],
\qquad x_6<x_9<0<x_{18}<x_3.
\]

The previous certificate proved the real restrictions, disjoint pre-return phases, and finite complex phase collars for parameters satisfying \(|c'-c_*|<2^{-26}\). It did **not** certify quadratic-like properness or compatibility with the Kahn–Lyubich source geometry.

**Terminology warning:** *Paper 2's H3* means its standing hypothesis \(K(f)=J(f)\). This is **not** the independent program-level ledger obligation named \(\mathrm{H3\_COERCIVITY}\). Neither becomes proved here.

## 2. Theorem: the entire certified complex parameter disk is attracting

**Theorem A (uniform period-27 attracting window).** Set

\[
\delta=2^{-26},\qquad r=2^{-13},\qquad
D=\{c'\in\mathbb C:|c'-c_*|<\delta\}.
\]

For every \(c'\in D\), let \(F_{c'}=f_{c'}^{27}\). Then

\[
\boxed{
\sup_{|z|\le r}|F_{c'}(z)|<\frac{3r}{8}.
}
\]

Consequently \(F_{c'}\) is a strict contraction on the closed disk \(|z|\le r/2\), with Lipschitz constant *less than* \(3/4\). Its unique fixed point there belongs to an attracting cycle of **exact period 27** under \(f_{c'}\); the critical orbit of \(0\) converges to this cycle. In particular

\[
\{|z|<r/2\}\subset \operatorname{int}K(f_{c'}),
\qquad K(f_{c'})\ne J(f_{c'})
\quad\text{for every }c'\in D.
\]

Thus the **entire** complex parameter disk used for the finite phase-collar theorem violates Paper 2 H3. In fact the disk lies inside a period-27 hyperbolic component.

**Proof.** The signed-integer certificate first verifies the opposite strict signs of \(f_c^{27}(0)\) at the dyadic endpoints and a strictly negative parameter derivative throughout the bracket, fixing the unique \(c_*\).

For \(0\le j\le27\), let \(X_j\) be the outward \(2^{-224}\)-dyadic interval enclosing \(x_j\), and take the exact upper bound

\[
M_j=\max\{|\inf X_j|,|\sup X_j|\}.
\]

Each relevant \(M_j<2\). For arbitrary \(c'\in D\) and \(|z|\le r\), write

\[
e_j=|f_{c'}^{\,j}(z)-f_{c_*}^{\,j}(0)|.
\]

The polynomial identity

\[
f_{c'}(u)-f_{c_*}(v)
=(u-v)(u+v)+(c'-c_*)
\]

gives the rigorous recurrence

\[
e_0\le r,\qquad
e_{j+1}\le e_j(2M_j+e_j)+\delta.
\]

The certificate iterates this recurrence as **upper** dyadic integers: if \(E_j\) is represented as an integer in units of \(2^{-224}\), then

\[
E_0=r,\qquad
E_{j+1}=
2^{-224}\left\lceil
\frac{E_j(2M_j+E_j)}{2^{-224}}
\right\rceil+\delta.
\]

(The displayed formula is in value units; the script implements the equivalent integer product and ceiling division, so there is no floating-point ambiguity.) The checked strict inequality is

\[
\boxed{8E_{27}<3r}.
\]

Since \(x_{27}=0\) exactly, the first assertion follows.

By Cauchy's estimate applied on disks of radius \(r/2\) centered at points \(|z|\le r/2\), this bound gives

\[
|F_{c'}'(z)|\le \frac{2}{r}
\sup_{|w|\le r}|F_{c'}(w)|<\frac34 .
\]

The image of the closed \(r/2\)-disk lies in the smaller \(3r/8\)-disk, so the contraction theorem yields a unique attracting fixed point \(a_{c'}\) of \(F_{c'}\) there; the orbit of \(0\) under \(F_{c'}\) converges to it.

Because \(F_{c'}(a_{c'})=a_{c'}\), the least \(f_{c'}\)-period divides 27. The only proper positive divisors are 1, 3, and 9. For each \(j\) in that set, the interval certificate also checks

\[
\inf_{x\in X_j}|x| > E_j+r/2,
\]

so

\[
|f_{c'}^{\,j}(a_{c'})-a_{c'}|
\ge |x_j|-E_j-|a_{c'}|>0.
\]

Thus its exact period is 27. Finally, the \(r/2\)-disk is forward invariant under \(f_{c'}^{27}\), and its intermediate images under the finitely many maps \(f_{c'}^j\), \(0\le j<27\), are bounded. Every point in the disk therefore has a bounded full forward orbit, proving \(K(f_{c'})\) contains an open disk. The unique finite critical point \(0\) is attracted to the cycle. \(\square\)

**Corollary A.1 (an eightfold larger H3-exclusion window).** There is a stronger parameter-exclusion statement that does not require the specific \(3/4\)-contraction constant. Set

\[
\Delta=2^{-23},\qquad R=2^{-11}.
\]

For **every** complex parameter \(|c'-c_*|<\Delta\), the same 27-step complex-error recurrence, now beginning with \(E_0=R\) and using parameter error \(\Delta\), verifies the exact strict integer inequality \(16E_{27}<15R\). Consequently

\[
\boxed{\sup_{|z|\le R}|f_{c'}^{27}(z)|<\tfrac{15}{16}R<R.}
\]

The entire closed \(R\)-disk is forward invariant under the 27th iterate. Its finite intermediate images are bounded, so its interior lies inside \(K(f_{c'})\). Therefore **Paper 2 H3 fails on the larger \(|c'-c_*|<2^{-23}\) parameter disk**, which has eight times the radius of the earlier phase-collar disk. The code asserts this larger bound independently of the smaller-window contraction estimate. The stronger \(\lvert F'\rvert<3/4\) bound and the elementary exact-period argument above are only claimed on the smaller window; no additional dynamical conclusion is silently assigned to the larger disk.

**Interpretation.** This is a *parameter-class exclusion for one source hypothesis*, not an obstruction to Mandelbrot local connectivity. It strengthens the earlier observation that the center alone fails \(K(f)=J(f)\): nearby parameters throughout the *certified* complex collar disk fail it too, and the corollary excludes a still larger explicit neighborhood. A nonattracting Paper-2-compatible example cannot be selected *within the larger disk*.

## 3. Theorem: the naïve thin-stadium quadratic-like domain fails

For \(\epsilon>0\), define the open equal-width complex stadium around the real interval \(I_p\) by

\[
U_p(\epsilon)=
\{z\in\mathbb C:\operatorname{dist}(z,I_p)<\epsilon\},
\qquad p\in\{3,9\}.
\]

Let \(W_p(\epsilon)\) denote the connected component containing \(0\) of
\((f_{c_*}^{\,p})^{-1}(U_p(\epsilon))\).

**Theorem B (critical-value boundary inflation).** For both \(p=3\) and \(p=9\), and for **every** \(0<\epsilon\le2^{-21}\),

\[
\boxed{W_p(\epsilon)\not\subset U_p(\epsilon).}
\]

In particular, using the same thin stadium as the target of the canonical first-return preimage component cannot yield a quadratic-like pair \(W_p\Subset U_p\). This includes the \(2^{-40}\) stadiums of the earlier finite-horizon collar theorem.

**Proof.** At the exact center, the critical value of \(f^3\) is \(x_3\), the **right endpoint** of \(I_3\), and the critical value of \(f^9\) is \(x_9\), the **left endpoint** of \(I_9\).

Fix \(p\in\{3,9\}\), \(0<\epsilon\le2^{-21}\), and \(t\in[0,2\epsilon]\). Since \(c_*\) is real, \(f_{c_*}(it)=c_*-t^2\) is real and so are all later iterates. The first error relative to the critical orbit is exactly

\[
|f_{c_*}(it)-x_1|=t^2\le4\epsilon^2.
\]

The existing exact orbit bounds give \(|x_j|<2\) for \(0\le j\le8\). As long as the error is at most 1, it grows by at most a factor of 5 per subsequent iterate. An induction, bootstrapped using the bound below, yields

\[
|f_{c_*}^{\,p}(it)-x_p|
\le4\cdot5^{p-1}\epsilon^2
\le4\cdot5^8\epsilon^2
<\epsilon,
\]

because the exact integer inequality

\[
4\cdot5^8=1{,}562{,}500<2^{21}=2{,}097{,}152
\]

is verified in the script. As \(x_p\in I_p\), every point of the vertical segment \(\{it:0\le t\le2\epsilon\}\) maps into \(U_p(\epsilon)\). The segment therefore lies in the *same* preimage component \(W_p(\epsilon)\) as \(0\).

But \(\operatorname{dist}(2i\epsilon,I_p)=2\epsilon>\epsilon\), since \(0\in I_p\). Thus \(2i\epsilon\in W_p(\epsilon)\setminus U_p(\epsilon)\). \(\square\)

**Interpretation.** A thin neighborhood around an interval whose endpoint is a quadratic critical value is not automatically stable under taking a first-return inverse component. The quadratic behavior in the imaginary direction pushes the preimage beyond the equal-width collar. This is a **no-go for these particular target domains**, not a no-go for polynomial-like renormalization itself.

## 4. What to attempt next

A genuine next positive construction must solve **two distinct tasks**, rather than silently promoting finite-phase separation to quadratic-like properness.

1. **At the center:** design source-adapted complex Jordan domains \(V_3\Subset U_3\) and \(V_9\Subset U_9\) that genuinely support proper degree-two returns, with verified boundary separation and nested little filled Julia data. These domains cannot simply be the thin equal-width stadium/preimage pairs rejected by Theorem B. The center remains a useful *complex renormalization testbed*, notwithstanding its failure of Paper 2 H3.
2. **For a Paper-2-compatible application:** select a parameter **outside the larger (2^{-23}) exclusion disk** (or otherwise change the source setting) and independently prove the full geometric hypotheses, including \(K(f)=J(f)\), closed puzzle-pullback separation, exact retimed root arrows, ray/prime-end transport, sheet/coset data and protected obstacles. Theorem A rules out rescuing H3 by remaining inside the old \(2^{-26}\) parameter disk.

Do not infer that the second task follows from the first, or that either solves any of the source-locked program's global \(H1/H2/H3/H4\), UPTCR, or MLC gates.

## 5. Reproducibility and review boundary

- **Inputs:** the original exact \(2^{-128}\) parameter bracket, outward \(2^{-224}\) integer enclosure code, and the already certified restrictive intervals.
- **New checks:** 27-step *complex modulus error majorants* with outward ceiling division; strict \(8E_{27}<3r\); exclusion of periods \(1,3,9\); exact thin-stadium numerical threshold.
- **Analytic interpretation:** the elementary complex difference identity, Cauchy's estimate, contraction mapping theorem, critical-orbit boundedness, and the explicit vertical-segment obstruction.
- **Not automated:** a proof assistant does not kernel-check Cauchy's theorem or the stated analytic inference. The attached integer test certifies the finite inequalities, not a whole formalization of complex dynamics.
- **Status:** no change to the released papers, 465-entry ledger, source lock, or MLC claims. Independent specialist review is still appropriate before publication.

The result is deliberately a first-failure certificate: it tells a future construction **which parameter window and which domain shape cannot satisfy the intended source application**, while preserving the still-open positive complex renormalization task.

**AI-assistance disclosure:** This research increment was drafted with OpenAI GPT-6 under the repository steward's direction. The arithmetic checks were run in an isolated local Python environment and connected GitHub Actions; the analytic proofs are supplied explicitly for human inspection. No independent human mathematical verification or external specialist review is represented as completed by this increment.
