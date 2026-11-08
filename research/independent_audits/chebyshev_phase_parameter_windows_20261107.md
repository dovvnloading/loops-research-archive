# A continuum of exact critical-orbit exit phases inside the Mandelbrot set

**Date:** November 7, 2026. **Status:** self-contained quantitative theorem for the **actual real quadratic family** near the Misiurewicz endpoint `c=-2`, with a uniform analytic proof, explicit first and second-order constants, and independent outward-integer certificates of a family of algebraic parameters. **This is a deliberate shift away from KKL's prime-end/Wave mechanism.** The theorem gives a physical, non-synthetic parameter-to-future-phase calibration that the archive's abstract counter/compactification machinery did not previously possess. It does **not** close `H1_MARKED_CONSTRUCTION`, `H2_CALIBRATION`, `H3_COERCIVITY`, the virtual-Molecule interpolation, or MLC.

## Motivation, scope and attribution

The archive's [`virtual_language_memory.md`](../mlc_unified/virtual_language_memory.md) proves that exact future-dependent return clocks cannot be eliminated merely because a present-day symbolic signature has finitely many states. That is an abstract obstruction; its original proof does not supply a continuum of genuine quadratic parameters exhibiting a **uniformly calibrated, future-readable clock**. The present theorem realizes such a clock in the actual nonescaping critical orbits, and computes both the phase scale and the first nonlinear correction.

The Chebyshev identity `f_{-2}(2 cos θ)=2 cos(2θ)`, local hyperbolic linearization and the general multiplier-four scaling phenomenon near `c=-2` are classical. Related geometric scaling of period-`n` centers near `-2` is in earlier complex-dynamics literature (e.g. Stony Brook dissertation material on Misiurewicz points). Our claim of contribution is the **precisely chosen continuum of first-exit targets** and the completely derived **uniform two-term parameter profile** with its independent exact integer certificates, not discovery of the general scaling principle or a new Mandelbrot-local-connectivity parameter class. The current independent Julia-bundle literature (e.g. Yueyang Wang, arXiv:2610.11793, October 2026) also warns that fiberwise and parameterwise topology need not automatically imply joint control; we do not import its theorems into this calculation.

## 1. Actual real phase windows

Fix the real polynomial

\[
 f_c(z)=z^2+c,\qquad -2\le c\le-\frac95,
 \quad x_0(c)=0,\quad x_{j+1}(c)=f_c(x_j(c)).
\]

Let `T=[1,3/2]` be the **fixed** continuum of exit levels. Put

\[
 x_2(c)=c^2+c,\quad
 \beta(c)=\frac{1+\sqrt{1-4c}}2,\quad
 \lambda(c)=2\beta(c),\quad
 g_c(y)=\sqrt{y-c}.
\]

Here `β(c)` is the positive repelling fixed point, with `λ(c)>1`, and `g_c` is the positive real inverse branch fixing `β(c)`. For each integer `n≥1` and each `t∈T`, consider the equation

\[
 \boxed{x_2(c_n(t))=g_{c_n(t)}^{\circ n}(t).} \tag{1.1}
\]

### Theorem A — exact and unique physical exit-window curves

For every `n≥1`, equation (1.1) has **exactly one** solution

\[
 \boxed{-2<c_n(t)<-9/5,\quad c_n\in C^1(T),\quad c_n'(t)<0.}\tag{1.2}
\]

These are real parameters **inside the actual Mandelbrot set**. At every such parameter the critical orbit after its second iterate decreases strictly until its prescribed first level `t`:

\[
 \boxed{x_2(c_n(t))>x_3(c_n(t))>\cdots>x_{n+1}(c_n(t))>x_{n+2}(c_n(t))=t.}\tag{1.3}
\]

(When `n=1`, the chain has the corresponding two terms.) The parameter curves `c_n(t)` decrease toward `-2` as `n→∞`, uniformly in `t∈T`, and the parameter interval

\[
 I_n=[c_n(3/2),c_n(1)]\subset\mathcal M\cap\mathbb R
\]

parametrizes an entire nontrivial interval of **real physical exit phases** after exactly `n` near-repeller steps. No symbolic/artificial transition map is substituted for `f_c`.

**Proof.** For `c∈[-2,-9/5]`, the interval `[1,β(c)]` is invariant under the increasing inverse branch `g_c`. Moreover `g_c(y)>y` for `1≤y<β(c)` because `y²-y+c<0` between the two real fixed points. The inverse iterates satisfy `t<g_c(t)<⋯<g_c^n(t)<β(c)`.

Let `F_n(c,t)=c²+c-g_c^n(t)`. At `c=-2`, `x_2=2=β(-2)>g_{-2}^n(t)`, so `F_n(-2,t)>0`. At `c=-9/5`, `x_2=81/25-9/5=36/25` and `g_c^n(t)≥g_c(1)=sqrt(14/5)>36/25`, hence `F_n(-9/5,t)<0`.

To prove **uniqueness**, write `v_j=∂_c g_c^j(t)`. Then

\[
 v_0=0,\qquad v_{j+1}=\frac{v_j-1}{2g_c^{j+1}(t)}.
\]

Since `g_c^{j+1}(t)≥sqrt(14/5)`, define

\[
 \gamma=\frac1{2\sqrt{14/5}}<0.3,
 \quad |v_j|\le\frac\gamma{1-\gamma}<0.43.
\]

As `2c+1≤-13/5`, we have

\[
 \partial_c F_n=2c+1-v_n\le-\frac{13}5+\frac\gamma{1-\gamma}<0.
\]

The intermediate-value theorem and strict monotonicity give a unique root; the implicit-function theorem gives `C¹`. Since `∂_t g_c^n(t)>0`, implicit differentiation yields `c_n'(t)=∂_t g_c^n(t)/∂_cF_n<0`. Applying `f_c` successively to (1.1) traces the strictly increasing inverse chain **backwards**, proving (1.3).

Every `c∈[-2,-9/5]` lies in `M`: the interval `[-β(c),β(c)]` is forward invariant because `f_c([-β,β])=[c,β]⊂[-β,β]` (indeed `c≥-β(c)` for `c≥-2`). It contains `0`, so the critical orbit is bounded. Finally, for every fixed `c>-2`, `g_c^n(t)→β(c)>x_2(c)`; uniformity in `t` follows from the uniform inverse contraction. Since `F_n(-2,t)>0` and `F_n` decreases in `c`, its roots converge to `-2` uniformly. \(\square\)

## 2. Uniform two-term scaling and a limiting phase-to-parameter law

Define the **Chebyshev exit angle** and its parameter coefficient

\[
 \theta(t)=\arccos(t/2),\qquad
 a(t)=\frac38\theta(t)^2,\quad t\in T.
\tag{2.1}
\]

### Theorem B — sharp physical phase scaling, including the nonlinear clock correction

Uniformly in `t∈T` as `n→∞`,

\[
 \boxed{c_n(t)+2
 =a(t)4^{-n}+\frac{a(t)^2}{6}\,n16^{-n}
 +O(16^{-n}).}\tag{2.2}
\]

The error constant is independent of `t` and `n`. The rescaled maps converge **also in their first derivatives**:

\[
 \boxed{
 4^n(c_n(t)+2)\longrightarrow a(t)
 \quad\text{in }C^1(T),\qquad
 a'(t)=-\frac{3\arccos(t/2)}{8\sqrt{1-t^2/4}}<0.}\tag{2.3}
\]

Thus, for any `1≤s<t≤3/2`, the actual phase-window parameter length has the sharp asymptotic

\[
 \boxed{c_n(s)-c_n(t)
 =\bigl(a(s)-a(t)\bigr)4^{-n}
 +O(n16^{-n}).}\tag{2.4}
\]

In particular, for the exactly specified target `t=1`,

\[
 \boxed{c_n(1)+2
 =\frac{\pi^2}{24}4^{-n}
 +\frac{\pi^4}{3456}\,n16^{-n}
 +O(16^{-n}),}\tag{2.5}
\]

where `π⁴/3456 = (π²/24)²/6`. The limiting rescaled parameter separation for target levels `1` and `3/2` is the **strictly positive** constant

\[
 \boxed{a(1)-a(3/2)
 =\frac{\pi^2}{24}-\frac38\arccos(3/4)^2.}\tag{2.6}
\]

**Proof, with all clocks and normalizations fixed.** At `c=-2` the inverse branch is explicitly Chebyshev:

\[
 g_{-2}^{\circ n}(t)
 =2\cos\!\left(\frac{\theta(t)}{2^n}\right).
\tag{2.7}
\]

Consequently `F_n(-2,t)=2-2cos(θ/2^n)≤θ(t)^2 4^{-n}`. The strict lower bound on `-∂_cF_n` from Theorem A and the mean-value theorem imply

\[
 0<c_n(t)+2=O(4^{-n})
\tag{2.8}
\]

**uniformly** for `t∈T`.

We next prove the needed **parameter-uniform inverse Koenigs estimate** directly, avoiding an unlicensed global linearization theorem. For `c` in a sufficiently small real neighborhood of `-2` and `t∈T`, let

\[
 y_j=g_c^{\circ j}(t),\quad e_j=\beta(c)-y_j>0,
\quad \lambda(c)=2\beta(c).
\]

The exact quadratic inverse relation yields

\[
 e_{j+1}=\frac{e_j}{\beta+y_{j+1}},\qquad
 A_n(c,t):=\lambda^n e_n
 =e_0\prod_{j=1}^n\frac{\lambda}{\beta+y_j}.
\tag{2.9}
\]

The uniformly contracting inverse iterates give `e_j≤C\gamma^j` with some `γ<1` independent of `c,t`. Each product factor is `1+O(e_j)`, so the product converges uniformly to a **positive** function `A(c,t)`. Differentiating the inverse iteration shows `∂_t e_j=O(\gamma^j)` and `∂_c e_j=O(j\gamma^j)` on a sufficiently small neighborhood. Therefore the product also converges in `C¹` in `(c,t)`, so

\[
 A(c,t)=A(-2,t)+O(c+2)\quad\text{uniformly on }T.
\]

The product tail after index `n` is `1+O(\sum_{j>n}e_j)=1+O(e_n)`. Since the finite products are bounded, `e_n≤C\lambda^{-n}`, hence

\[
 \boxed{e_n(c,t)=A(c,t)\lambda(c)^{-n}
          +O\bigl(\lambda(c)^{-2n}\bigr)}\tag{2.10}
\]

uniformly, with the analogous differentiated estimate in `t`. By (2.7),

\[
 \boxed{A(-2,t)
 =\lim_{n\to\infty}4^n[2-2\cos(\theta(t)/2^n)]
 =\theta(t)^2.}\tag{2.11}
\]

Set `δ=c_n(t)+2` and `q_n=4^{-n}`. At the root, `x_2=g_c^n(t)`, so

\[
 \beta(c)-x_2(c)=e_n(c,t).
\]

Taylor expansion at `c=-2` gives the **transversality** and multiplier laws

\[
 \beta(-2+\delta)-x_2(-2+\delta)
   =\frac83\delta+O(\delta^2),
\]

\[
 \lambda(-2+\delta)=4-\frac23\delta+O(\delta^2),
\qquad \lambda^{-n}=q_n\bigl[1+\tfrac n6\delta
  +O(n\delta^2+n^2\delta^2)\bigr].
\tag{2.12}
\]

Since `δ=O(q_n)` by (2.8), equations (2.10)–(2.12) imply

\[
 \frac83\delta
 =\theta^2q_n +\frac{\theta^2}{6}nq_n\delta
   +O(q_n^2).
\tag{2.13}
\]

The first term gives `δ=a(t)q_n+O(nq_n²)` with `a=(3/8)θ²`. Substituting it back into the second term and dividing by `8/3` yields (2.2): the coefficient of `nq_n²` is

\[
 \frac38\cdot\frac{\theta^2a}6=\frac{a^2}{6}.
\]

The uniform `C¹` convergence in (2.3) follows by differentiating the exact root equation, using the `C¹` convergence of `A` and the uniform convergence `∂_c g_c^n(t)→β'(c)` on this compact domain. Equivalently, in (2.13) differentiate in `t` and use the nonvanishing `8/3` transversality. The derivative of the second term contributes `O(nq_n²)`, hence `4^n c_n'(t)→a'(t)` uniformly. Equation (2.4) follows by subtracting (2.2) at two exit levels; (2.5) follows from `θ(1)=π/3`. \(\square\)

## 3. Consequence for the independent protected-tower program

This theorem gives a **positive geometric object**, not a synthetic finite automaton: the entire real interval `I_n⊂M` has a distinguished physical `n`-step critical shadowing itinerary. The width shrinks at the exact **multiplier-four** rate and has a nonzero limiting phase profile `a(t)`. Consequently:

1. A parameter marker that retains only a fixed-resolution real coordinate cannot distinguish all future exit targets for arbitrarily large `n`: their separation is `Θ(4^{-n})`. This is an exact failure of fixed-scale *phase observability*, not a claim that every symbolic renormalization encoding requires exponentially many states.
2. The sharp correction `n16^{-n}` records the accumulated variation of the **repelling multiplier with the parameter**. It cannot be derived by simply freezing the derivative at four. This identifies a concrete analytic clock error that a future phase-to-parameter calibration must accommodate.
3. Both exit levels and all witnessing parameters are in the **actual** quadratic dynamics, with the parameters inside `M`, unlike exterior parabolic transit models. This supplies an exact, nonstationary test family for future-observable compactifications and analytic response charts.
4. The result is at a **finitely renormalizable / preperiodic** tip, not at an infinitely renormalizable virtual-Molecule tower. It neither provides nested protected Julia carriers nor establishes a uniform quantitative H1/H2 transition across general tower regimes. In particular it does not prove local connectivity at a new parameter (classical Misiurewicz results already cover `-2`).

The useful next question is whether a *source-defined multi-scale marked return phase*, for example the existing **nonattracting period-3/9 Misiurewicz tip** in this repository, has an analogous **uniform parameter-to-phase map** with a nonzero transversality and complete protected-access transport. This would test the virtual-program transition geometry directly, without relying on the KKL Wave Lemma.

## 4. Exact reproducibility and trust boundary

Run from repository root:

```bash
python -m py_compile research/independent_audits/verify_chebyshev_phase_parameter.py
python research/independent_audits/verify_chebyshev_phase_parameter.py --check-manifest
```

The verifier checks **all 126** target/time cases with `t=1,5/4,3/2` and every `n=1,...,42`; the deterministic manifest records twelve representative time indices per target and the full test count. It brackets each unique `c_n(t)` using **outward integer square-root intervals** at dyadic resolution `2^-256` and additionally checks both endpoint signs with an **independent forward critical-orbit interval calculation**. The integer bracketing uses no floating-point approximation to make its sign decisions. Its separately evaluated Chebyshev cosine formula and first/second-order constants are regression comparisons; the uniform infinite-`n` and `C¹` proof is the written analysis above, not a consequence of finitely many numeric tests. The first constant at `t=1` is independently enclosed with exact rational Machin-arctangent bounds for `π`.

**Status discipline:** The global ledger remains unchanged. This is an independently sourced analytic positive result for a concrete unbounded-clock family in `M`. It is not new global MLC and has not received an independent specialist mathematical review. OpenAI GPT-6 assisted theorem discovery, analytic proof, exact-integer code, and exposition; the classical Chebyshev/Koenigs dynamics remains credited to its existing literature.
