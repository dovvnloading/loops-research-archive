# A transversal phase-to-parameter return at the actual two-scale Misiurewicz tip

**Date:** 2026-11-07. **Result:** a nonzero source-defined **holomorphic parameter transversality** for the archive's real period-3/9, strictly preperiodic Misiurewicz polynomial; a local continuum of true critical-orbit return-phase windows at physical times `10+9n`; a general **two-term analytic return multiplier law** with an independently certified, unusually large nonlinear correction; and a local persistence statement for the existing finite 3/9 polynomial-like domain tests. This is **independent of KKL's Wave Lemma**. It does not construct a global marked localization, a virtual-Molecule tower, uniform H3 coercivity or MLC.

**Existing source-certified input:** [the archive's exact real 3/9 Misiurewicz tip](./period27_misiurewicz_tip_ray_access_20261106.md), the interval checker [`verify_period27_misiurewicz_tip.py`](./verify_period27_misiurewicz_tip.py), and the [nonattracting complex 3/9 polynomial-like certificates](./nonattracting_tip_complex_two_scale_20261106.md). The parameter has been isolated to a width `2^-128`, its critical point has exact preperiod `10` and repelling return period `9`, and the source-certified scalar `G'(c_tip)` lies in `(-71,-70)`. Local repelling-cycle continuation and Koenigs linearization are classical dynamical systems results; they are derived in the normalized form needed here. The general Misiurewicz scaling phenomenon is established literature, so originality/prioritization of the present *specific* phase calibration requires independent evaluation.

## 1. A transversality identity hidden in the original orbit relation

Define the actual critical-orbit polynomials

\[
P_0(c)=0,\quad P_{j+1}(c)=P_j(c)^2+c,\quad f_c(z)=z^2+c,
\]

and let `c_*` be the unique real zero of

\[
G(c):=P_{18}(c)+P_9(c)=0
\]

in the **existing exact bracket**

\[
\boxed{
\frac{-607918036626757496169199575185708826140}{2^{128}}
<c_*<
\frac{-607918036626757496169199575185708826139}{2^{128}}.
}\tag{1.1}
\]

The known identity `P18(c_*)=-P9(c_*)` and the evenness of `f_c` give `P19(c_*)=P10(c_*)`. Set

\[
 z_*=P_{10}(c_*),\qquad F_c=f_c^{\circ9},\qquad
 \lambda_*=(F_{c_*})'(z_*)\in(3,4).
\]

Since `λ_*≠1`, the analytic implicit-function theorem supplies a unique analytic repelling fixed-point continuation `z(c)` satisfying

\[
F_c(z(c))=z(c),\quad z(c_*)=z_*.
\]

Define the **physical landing displacement**

\[
\Delta(c)=P_{10}(c)-z(c).
\tag{1.2}
\]

### Theorem 1.1 — exact certified nonzero landing transversality

At the actual `c_*`,

\[
\boxed{\Delta'(c_*)=
\frac{\big(P_{18}(c_*)-P_9(c_*)\big)
      \big(P'_{18}(c_*)+P'_9(c_*)\big)}{\lambda_*-1}.}
\tag{1.3}
\]

Moreover, using **outward integer interval arithmetic only**,

\[
\boxed{-1.181<\Delta'(c_*)<-1.180<0.}
\tag{1.4}
\]

The logarithmic parameter derivative of the authentic return multiplier is independently certified as

\[
\boxed{-500<\frac{\lambda_*'}{\lambda_*}<-490,}
\qquad \lambda(c)=\partial_zF_c(z(c)).
\tag{1.5}
\]

**Proof.** There is an *exact identity for every parameter*, not just at `c_*`:

\[
\begin{aligned}
F_c(P_{10}(c))-P_{10}(c)
 &=P_{19}(c)-P_{10}(c)\\
 &=P_{18}(c)^2-P_9(c)^2\\
 &=\big(P_{18}(c)-P_9(c)\big)G(c).
\end{aligned}\tag{1.6}
\]

Differentiate the fixed-point relation `F_c(z(c))=z(c)` at `c_*` to eliminate the parameter derivative of `F_c` in the derivative of the left side of (1.6). Since `P10(c_*)=z(c_*)`, this gives

\[
\left.\frac d{dc}\big(F_c(P_{10}(c))-P_{10}(c)\big)\right|_{c_*}
=(\lambda_*-1)\big(P'_{10}(c_*)-z'(c_*)\big)
=(\lambda_*-1)\Delta'(c_*).
\]

At the root `G(c_*)=0`, the derivative of the right side of (1.6) is exactly `(P18-P9)G'`, proving (1.3). The existing exact certificate has `P9(c_*)<0`, `P18(c_*)=-P9(c_*)>0`, `G'(c_*)∈(-71,-70)`, and `λ_*∈(3,4)`, so transversality is strictly negative **even without floating point**.

The companion independent dyadic checker refines the ratio by enclosing all `P_j,P'_j` on the entire isolating rational interval at integer scale `2^-256`; dividing the exact signed numerator and positive denominator bounds gives (1.4). A *second independent differential route* computes `P19'-P10'` and confirms the product factorization, rather than simply trusting the same derivative calculation twice.

For (1.5), start with the exact interval for

\[
z'(c_*)=P'_{10}(c_*)-\Delta'(c_*).
\]

Let `z_0=z(c)`, `z_{j+1}=f_c(z_j)` for `0≤j<9`. Along the actual repelling cycle all `z_j(c_*)` are nonzero. Hence

\[
\frac{\lambda_*'}{\lambda_*}
=\sum_{j=0}^{8}\frac{z_j'(c_*)}{z_j(c_*)},\qquad
 z_{j+1}'=2z_j z_j'+1.
\tag{1.7}
\]

The same dyadic enclosure calculus, initialized with the independently certified `z'(c_*)`, gives the strict rational bounds (1.5); all nine signed denominator intervals are verified to avoid zero. No choice of an invented transition matrix enters either derivative. \(\square\)

## 2. A general two-term return normal form

The next lemma is stated at the right level of generality so that it can be tested on other *actual* renormalization returns, without importing a global prime-end boundary quotient.

### Theorem 2.1 — uniform transversal repelling-return parameter windows

Let `F_c(z)` be a real-analytic family of holomorphic maps, `a(c)` a real-analytic marked critical-orbit value, and `z(c)` a real-analytic repelling fixed point of `F_c` such that, at `c=c_*`,

\[
 a(c_*)=z(c_*),\quad \lambda_*:=\partial_zF_{c_*}(z(c_*))>1,
 \quad D:=\frac d{dc}[a(c)-z(c)]_{c_*}<0.
\tag{2.1}
\]

Choose a sufficiently small one-sided real target interval `J=[z(c_*)-\eta,z(c_*)-\eta/2]` with `η>0`. Let `g_c` be the unique inverse branch of `F_c` defined near `z(c)` and fixing it. Let `\Phi_c` be the normalized analytic Koenigs coordinate satisfying

\[
\Phi_c(z(c))=0,\quad \Phi'_c(z(c))=1,
 \quad\Phi_c(g_c(y))=\lambda(c)^{-1}\Phi_c(y).
\]

Then for every sufficiently large integer `n`, and every `t∈J`, there is a **unique** real parameter `c_n(t)` near `c_*`, with `c_n(t)>c_*`, such that

\[
\boxed{a(c_n(t))=g_{c_n(t)}^{\circ n}(t).}\tag{2.2}
\]

It satisfies

\[
 \boxed{F_{c_n(t)}^{\circ n}(a(c_n(t)))=t.}\tag{2.3}
\]

Define the **nontrivial local phase profile**

\[
 B(t)=\frac{\Phi_{c_*}(t)}{D}>0,
 \qquad B'(t)=\frac{\Phi'_{c_*}(t)}D<0.
\tag{2.4}
\]

Uniformly for `t∈J`,

\[
\boxed{c_n(t)-c_*
 =B(t)\lambda_*^{-n}
 -\frac{\lambda_*'}{\lambda_*}B(t)^2
     n\lambda_*^{-2n}
 +O(\lambda_*^{-2n}).}\tag{2.5}
\]

In addition `λ_*^n(c_n(t)-c_*)→B(t)` in `C¹(J)`. Thus parameter intervals between two fixed exit phases have sharp **width proportional to `λ_*^-n`**. The nonlinear `nλ_*^-2n` correction vanishes only when the multiplier is parameter-stationary to first order.

**Proof.** By the real inverse-function theorem and `λ_*>1`, shrink the complex neighborhood so that all `g_c` are defined, map it into itself and contract uniformly. The attracting Koenigs theorem gives the stated `\Phi_c`, depending analytically on `c` after normalization `\Phi'_c(z(c))=1`. In particular, with `q=λ_*^-n`, uniformly in nearby `c` and `t∈J`,

\[
 g_c^n(t)-z(c)
 =\Phi_c(t)\lambda(c)^{-n}
   +O(\lambda(c)^{-2n}).\tag{2.6}
\]

The error and its first `t`-derivative are uniform, since `\Phi_c^{-1}(w)=z(c)+w+O(w²)` uniformly. The function `a(c)-g_c^n(t)` converges in `C¹` in `c` to `a(c)-z(c)`; its derivative is close to `D<0`. Its value at `c=c_*` is positive for `t<z(c_*)` because `g_{c_*}^n(t)<z(c_*)`. At a fixed, sufficiently close `c>c_*`, it is eventually negative. The IVT and strict derivative bound supply the unique root (2.2), and imply `δ_n=c_n-c_*=O(q)`. The real inverse branch is monotone, so (2.3) follows and its `n` successive `F_c` iterates traverse the chosen local phase segment without leaving the inverse-branch neighborhood.

Taylor-expand `a(c)-z(c)=Dδ+O(δ²)`, `\Phi_c(t)=\Phi_{c_*}(t)+O(δ)`, and

\[
 \lambda(c)^{-n}=q\left[1-n\frac{\lambda_*'}{\lambda_*}\delta
 +O(n\delta²+n²\delta²)\right].
\]

Equation (2.6) at the root gives

\[
 D\delta=\Phi_{c_*}(t)q
 -\Phi_{c_*}(t)\frac{\lambda_*'}{\lambda_*}nq\delta
 +O(q²).
\]

Substituting its first-order solution `δ=B(t)q+O(nq²)` yields the second term
`-(λ_*'/λ_*)B(t)²nq²`, proving (2.5). All implicit functions are real-analytic in `t`; differentiating the normalized equation and using `D≠0` gives the uniform `C¹` limit. \(\square\)

This is the return-normal-form analogue of the independent [Chebyshev continuum theorem](./chebyshev_phase_parameter_windows_20261107.md). Its coefficient convention matches that theorem: at `c=-2` and one-step `F=f`, `λ_*'/λ_*=-1/6`, so (2.5) gives `+B² n16^-n/6`.

## 3. Apply the theorem at the real 3/9 tip — a new positive local parameter calibration

Take the source-certified polynomial `f_c(z)=z²+c` at `c_*`, the return map `F_c=f_c^9`, the marked orbit value `a(c)=P_{10}(c)`, and the repelling continuation `z(c)` above. Theorem 1.1 checks every hypothesis of Theorem 2.1. In particular, it gives a **real phase interval** `J` and a unique analytic curve of **actual quadratic parameters** `c_n(t)>c_*` for all large `n` and `t∈J`, such that

\[
\boxed{f_{c_n(t)}^{10+9n}(0)=t.}\tag{3.1}
\]

All `c_n(t)` are in `M` because for any real `-2≤c≤1/4`, the real interval `[-β(c),β(c)]` is forward invariant and contains `0`. Their parameter-phase expansion is exactly (2.5), with the **source-measured** facts

\[
 \boxed{3<\lambda_*<4,
 \qquad -1.181<D<-1.180,
 \qquad 490<-\lambda_*'/\lambda_*<500.}\tag{3.2}
\]

Consequently the coefficient of the first nonlinear clock correction lies strictly between

\[
 \boxed{490\,B(t)^2
 \ <\ -\frac{\lambda_*'}{\lambda_*}B(t)^2
 \ <500\,B(t)^2,}\tag{3.3}
\]

an order of magnitude that **cannot** be inferred by freezing `F_c` at `c_*`. The multiplier in (3.2) is the genuine nine-iterate multiplier of the old archive's period-3/9 tip; no artificial finite-state transfer is used.

### Separate but useful persistence of the two finite geometric stage domains

The existing [complex 3/9 certificate](./nonattracting_tip_complex_two_scale_20261106.md) gives strictly positive **finite Rouché and phase-disk margins** for `f_{c_*}^3` and `f_{c_*}^9`. Every tested polynomial expression and circle inequality is continuous in `c`, so the same finitely many **strict** inequalities persist throughout a sufficiently small, nonzero complex parameter disk around `c_*`. The usual Rouché/Riemann–Hurwitz argument therefore still supplies local proper degree-two source restrictions at periods `3` and `9` for nearby parameters, with the original source/target round disk radii. Hence for all sufficiently large `n`, the **new real phase curves** `c_n(t)` lie within a common parameter neighborhood where both finite restrictions exist.

This is an **open analytic-domain statement**, not a claim that the nearby *little filled Julia sets remain connected*, that the full original Kahn–Lyubich marking persists, or that two nested renormalization cycles realize the same protected-tower data. Those dynamical identifications remain separate requirements.

## 4. Reproducibility, source hygiene, and next actual gate

Run

```sh
python -m py_compile research/independent_audits/verify_period9_tip_phase_transversality.py
python research/independent_audits/verify_period9_tip_phase_transversality.py --check-manifest
```

This independent standard-library checker uses signed dyadic outward interval arithmetic at `2^-256`, encloses all `P_j,P'_j` through index `19` over the exact `2^-128` source bracket, verifies the `G` endpoint signs and derivative, recomputes the real 9-cycle multiplier, proves (1.4), checks the two independent derivative factorizations, and computes (1.5) from the actual differentiated **nine-step real orbit**. No floating-point number certifies any sign. The deterministic manifest is only a finite check; the uniform analytic return theorem is the written proof above.

**Actual next high-impact objective:** transport the source-defined 3/9 external-ray and KL localization markings along this explicit continuum of physical phase windows, with an analytic continuation criterion for the proper-side access record. The source's known native sheets and their infinite monodromy cannot be replaced by coarse angle words. That is a more direct challenge to the independent cross-scale `H1_MARKED_CONSTRUCTION` program than further KKL Wave arithmetic. A failure would give a **real, source-labeled first-obstruction**; success would produce stage-aligned marked carriers over a nontrivial parameter family.

**Scope and attribution.** This result is local to a finitely renormalizable Misiurewicz tip with nearby parameter clocks; the global UPTCR, H1–H4 and MLC gates remain OPEN. Existing source results for the exact tip, its two renormalization domain certificates, and its landing rays retain their original authorship and imported analytic dependencies. The general local repelling linearization and Chebyshev scaling are classical. OpenAI GPT-6 assisted the new transversality observation, analytic derivation, exact integer verification and presentation. Independent specialist review and novelty/priority assessment remain necessary.
