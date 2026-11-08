# Annular contact resistance: an exact exponential crossover and attachment saturation dichotomy

**Date:** 2026-11-07. **Scope:** a complete asymptotic theorem for the **full, free-outer-boundary** sheet-opposed annular condenser from the archive's merged [attachment-condenser note](./kkl_attachment_sheet_condenser_and_two_scale_limit_20261107.md), with a separate source-conditional application to complete KKL attachment arcs. This extends that note's yes/no nondegeneration criterion by calculating the **previously unknown crossover value** and a sharper reciprocal-capacity expansion. It is **not** a KKL canonical Wave/WAD estimate, a native critical-return acyclicity proof, or MLC. The ingredients (logarithmic equilibrium measures, conformal energy and Dedekind eta modularity) are classical; the combined calculation and its particular KKL interface are contributions within this archive, not independently established mathematical priority.

**Sources:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §6.1 Proposition 6.5 (full attached-component boundary) and the source covering/immersion distinction; the [actual expanding quadratic attachment atlas](./kkl_misiurewicz_actual_expanding_attachment_atlas_20261106.md) and [merged PR #46](https://github.com/dovvnloading/loops-research-archive/pull/46). For the equilibrium-measure representation of condenser capacity, see classical logarithmic-potential theory and, as background, Dimitrios Betsakos, *On the equilibrium measure and the capacity of certain condensers* (2002). All formulas below are derived for our **specified mixed-boundary cylinder**, not transferred from a different boundary-value problem.

## 1. Definition and main theorem

Let `A_h=(0,h)×(R/2πZ)`, `τ(t,θ)=(t,θ+π)`. On its **inner** circle take the two disjoint, closed, deck-exchanged arcs

\[
A_\ell=[-\ell/2,\ell/2],\qquad B_\ell=\tau A_\ell,\qquad 0<\ell<\pi.
\]

Define the *full family* condenser capacity (equal to its full connecting-curve extremal width in the archive's convention)

\[
W_h(\ell)=\min\left\{\int_{A_h}|\nabla u|^2:\operatorname{Tr}_0u=1\text{ on }A_\ell,
\ \operatorname{Tr}_0u=0\text{ on }B_\ell\right\}.
\tag{1.1}
\]

All remaining portions of the inner circle and the **entire outer boundary** are free (natural Neumann conditions). In particular this is **not** the pinned-outer response from PR #44.

**Theorem 1 (quantitative contact-resistance expansion).** Uniformly in the simultaneous regime

\[
0<h\le1,\qquad 0<\ell\le h/4,
\]

there is a universal constant `C_0` such that

\[
\boxed{\left|\frac1{W_h(\ell)}-\frac{\pi}{2h}
-\frac{2}{\pi}\log\frac{4h}{\pi\ell}\right|
\ \le C_0\left[\left(\frac\ell h\right)^2+\ell^2+e^{-\pi^2/h}\right].}
\tag{1.2}
\]

Consequently, **if** `h↓0` and `ell/h→0`, the remainder in the bracket tends to zero and

\[
\boxed{\frac1{W_h(\ell)}=\frac\pi{2h}+\frac2\pi\log\frac{4h}{\pi\ell}+o(1).}
\tag{1.3}
\]

The two leading terms are the **bulk thin-cylinder resistance** and **boundary-contact spreading resistance**, in *series*. The additive constant `log(4/π)` inside the logarithm is determined, not fitted. The theorem supplies the missing critical-scale value left open by the archive's earlier iff threshold; the physical origin of its boundary-value problem remains restricted as stated in §6.

**Corollary 2 (complete exponential crossover).** For any `h_n→0` and `ell_n→0` with

\[
h_n\log(1/\ell_n)\longrightarrow C\in[0,\infty],
\]

one has

\[
\boxed{\frac{W_{h_n}(\ell_n)}{h_n}\longrightarrow
\frac1{\pi/2+(2/\pi)C},\qquad \text{with the value }0\text{ for }C=+\infty.}
\tag{1.4}
\]

When `0<C<∞`, exponential decay of `ell_n` implies `ell_n/h_n→0` and (1.3) proves the claim. For `C=0`, the previous merged theorem gives the same value `2/π` even if `ell_n/h_n` does **not** tend to zero; for `C=∞` its logarithmic cutoff gives zero. In the exactly critical scaling `ell(h)=exp(-C/h)` with `C>0`, the finer expansion also yields

\[
\boxed{\frac h{W_h(e^{-C/h})}=\frac\pi2+\frac{2C}\pi+
\frac{2h}\pi\log\frac{4h}\pi+o(h).}
\tag{1.5}
\]

**No overextension:** With `ell` fixed and `h→0`, the correct limit is `2/(π−ell)` from PR #46, **not** `2/π`. The hypothesis `ell→0` in (1.4) is essential. The large-rotation parabolic KKL stage has *not* been shown to produce a family `ell(h)` at all.

## 2. Exact reciprocal-capacity duality and the source of positivity

Let `u_h` be the unique condenser minimizer. By `u↦1-u∘τ` and uniqueness it satisfies `u_h∘τ=1-u_h`. The weak maximum principle gives `0≤u_h≤1`. On the interiors of the two smooth Dirichlet electrodes the outward normal derivative has a definite sign (boundary maximum/minimum principle); the flux is zero on the free boundary portions. The mixed-boundary endpoint singularity is locally integrable, and the finite-energy normal trace has **no point-mass terms**. Thus the positive flux from `A_ell` and its negative deck translate define nonnegative finite measures of equal mass

\[
I=\mathcal E(u_h)=W_h(\ell).
\]

Normalize the positive flux on `A_ell` to a probability measure `µ`; the complete normalized signed flux is `q=µ−τ_*µ`. Its total mass is zero. For any probability measure `ν` on `A_ell` whose Fourier response below is finite, Cauchy–Schwarz with the potential minimizer gives `1≤sqrt(W_h)sqrt(R_h(ν))`; the normalized equilibrium flux yields equality. Therefore the **exact** reciprocal-capacity principle is

\[
\boxed{\frac1{W_h(\ell)}=
\min_{\substack{\mu\ \mathrm{probability}\\\mathrm{on}\ A_\ell}}
R_h(\mu),\qquad
R_h(\mu)=\frac4\pi\sum_{\substack{n\ge1\\n\ \mathrm{odd}}}
\frac{\coth(nh)}n|m_n(\mu)|^2,}
\tag{2.1}
\]

with `m_n(µ)=∫_{A_ell}e^{-inθ}dµ(θ)`. Measures of infinite response are allowed in the infimum with value `+∞`. The Fourier multiplier follows from solving the **free-outer** Neumann-to-Dirichlet problem; it is precisely the signed charge response of PR #46. The duality can also be obtained from standard convex Hilbert-space duality; the positivity restriction on `µ` is justified by the *actual* equilibrium flux, **not** assumed for arbitrary signed test charges.

## 3. The universal logarithmic contact kernel and its minimizer

Split `coth(nh)=1+[coth(nh)-1]`. For `|t|<π`, Abel summation of the odd Fourier series gives

\[
K_0(t):=\sum_{n\ge1,\ n\ \mathrm{odd}}\frac{\cos(nt)}n
=\frac12\log\left|\cot\frac t2\right|.
\tag{3.1}
\]

At distances `|t|≤ell≤1/4` one has

\[
K_0(t)=\frac12\log\frac2{|t|}+\varepsilon(t),
\qquad |\varepsilon(t)|\le C_1t^2.
\tag{3.2}
\]

This is elementary Taylor control of `(t/2)cot(t/2)`; the diagonal is treated by the integrable logarithmic kernel, not by assigning a finite value to `K_0(0)`.

Classical one-dimensional logarithmic capacity says the equilibrium probability measure on `[-ell/2,ell/2]` is the arcsine law

\[
d\mu_*(\theta)=\frac{d\theta}{\pi\sqrt{(\ell/2)^2-\theta^2}},
\qquad \min_\mu\iint\log\frac1{|\theta-\varphi|}
\,d\mu(\theta)d\mu(\varphi)=\log\frac4\ell.
\tag{3.3}
\]

For completeness, substitute `θ=(ell/2)cos s` to see the arcsine potential is constant `log(4/ell)` on the whole electrode; the logarithmic kernel is conditionally positive for zero-mass differences of probabilities, proving minimality. It follows that

\[
\boxed{\min_\mu\iint K_0(\theta-\varphi)
\,d\mu(\theta)d\mu(\varphi)
=\frac12\log\frac8\ell+O(\ell^2).}
\tag{3.4}
\]

The constant `8` inside the logarithm comes from the **actual continuum contact geometry**, not a discrete network. The arcsine trial law gives the matching upper bound, and uniform (3.2) gives the lower bound for *every* probability measure.

## 4. The thin-cylinder kernel and its exact modular product

Define the absolutely convergent thermal kernel

\[
T_h(t)=\sum_{n\ge1,\ n\ \mathrm{odd}}
\frac{\coth(nh)-1}{n}\cos(nt).
\tag{4.1}
\]

Since `1−cos(nt)≤n²t²/2`, for `0<h≤1` and `|t|≤ell`,

\[
0\le T_h(0)-T_h(t)
\le\frac{t^2}2\sum_{n\ \mathrm{odd}}n(\coth(nh)-1)
\le C_2\frac{\ell^2}{h^2}.
\tag{4.2}
\]

The final inequality follows by splitting at `n≤1/h` (use `coth(nh)-1≤1/(nh)`) and `n>1/h` (use exponential decay). Thus the thermal energy of *every* probability charge on the short arc differs from `T_h(0)` by at most `C_2(ell/h)^2`.

There is a more precise identity than the usual Euler–Maclaurin estimate. Expanding `coth(nh)-1` into geometric series and summing the odd logarithms yields

\[
T_h(0)=\sum_{k\ge1}\log\coth(kh)
=\log\frac{\eta(2ih/\pi)}{\eta(ih/\pi)^2},
\tag{4.3}
\]

where `η` is the Dedekind eta function. Applying the standard modular identity `η(-1/τ)=sqrt(-iτ)η(τ)` gives the *exact* convergent product

\[
\boxed{
T_h(0)=\frac{\pi^2}{8h}+\frac12\log\frac h{2\pi}
+\sum_{k\ge1}\left[\log(1-e^{-k\pi^2/h})
-2\log(1-e^{-2k\pi^2/h})\right].}
\tag{4.4}
\]

The final sum is `O(exp(-pi²/h))` for `0<h≤1`. In particular

\[
T_h(0)=\frac{\pi^2}{8h}+\frac12\log\frac h{2\pi}
+O(e^{-\pi^2/h}).
\tag{4.5}
\]

This modular calculation fixes the constant that elementary `O(1)` splitting would otherwise leave undetermined. The code independently evaluates the original `log coth` product and the modular product.

## 5. Proof of Theorem 1 and the series-resistance law

For a probability `µ` on `A_ell`, insert the two kernels into (2.1):

\[
R_h(\mu)=\frac4\pi\iint
\bigl(K_0(\theta-\varphi)+T_h(\theta-\varphi)\bigr)
\,d\mu(\theta)d\mu(\varphi).
\tag{5.1}
\]

Uniformly in every such `µ`, (3.2) and (4.2) imply

\[
R_h(\mu)=\frac4\pi\left[
\frac12\log2+T_h(0)+\iint\frac12\log\frac1{|\theta-\varphi|}
\,d\mu d\mu
\right]+O\!\left(\ell^2+(\ell/h)^2\right).
\tag{5.2}
\]

The `O` constant is universal. Taking the minimum, the arcsine law (3.3) yields *both* bounds on the minimum, so

\[
\frac1{W_h(\ell)}=\frac4\pi\left[T_h(0)+\frac12\log\frac8\ell\right]
+O\!\left(\ell^2+(\ell/h)^2\right).
\tag{5.3}
\]

Substitute (4.5) and simplify the logarithms:

\[
\frac4\pi\left[\frac{\pi^2}{8h}+\frac12\log\frac h{2\pi}
+\frac12\log\frac8\ell\right]
=\frac\pi{2h}+\frac2\pi\log\frac{4h}{\pi\ell}.
\]

A useful *one-sided* refinement is available before applying the eta formula. Since `x cot x≤1` for `0<x<π/2`, the error `ε(t)` in (3.2) is nonpositive; likewise `T_h(t)≤T_h(0)`. Thus the arcsine trial and the universal lower bounds give the explicit signed bracket

\[
\boxed{0\le\frac4\pi\left[T_h(0)+\frac12\log\frac8\ell\right]
-\frac1{W_h(\ell)}
\le C_3\left(\ell^2+(\ell/h)^2\right).}
\tag{5.4}
\]

This bracket explains why the reciprocal-resistance expansion has no unknown `O(1)` constant: the upper and lower continuum charge bounds **coincide to `o(1)`** whenever `ell/h→0`. It also supplies a deterministic negative/positive numerical control independent of the PDE solver.

This proves (1.2)–(1.3), with no guessed effective network and no pointwise prime-end landing assumption. The broad crossover formula (1.4) follows as described after its statement, using the already proved edge regimes from PR #46.

**Strength relative to PR #46:** (i) exact crossover *value*, not merely survival/failure; (ii) a universal additive `o(1)` formula for reciprocal capacity in the exponentially small access regime; (iii) an exact multiplicative constant `4/π` in the contact logarithm; and (iv) an explicit division between universal annular bulk resistance and short-access logarithmic resistance.

## 6. A source-native terminality-or-condenser dichotomy: what it does and does not prove

Let an **actual** connected degree-two KKL `f`-covering have a complete attached-component Carathéodory boundary `B_X` supplied by Proposition 6.5, and assume that this boundary is a **single source inner-circle closed arc** with conformal angular span `ell_X∈(0,2π]`. Let `D` be a well-typed original marked input with `B_X⊂iota^*D`; all assertions below are made only in this explicitly stated source category.

1. If `ell_X≥π`, the degree-two pushforward `f_*(B_X)` is the full target circle. Therefore `Phi(D)=C`: **immediate saturation**. This requires no WAD, deck character, width calibration, or local connectivity.
2. If `0<ell_X<π`, `B_X` and its deck translate `τ B_X` are disjoint, so they define a **genuine source-covering sheet-opposed full condenser**, with the unique minimizing potential forced deck-odd by the electrode symmetry. For any sufficiently small conformal source collar its width is `W_h(ell_X)`. If a sequence of actual stages also supplies `h_j→0`, `ell_{X,j}→0`, and `h_j log(1/ell_{X,j})→C`, Theorem 1 gives the exact normalized condenser response (1.4).

This is a *conditional source-native dichotomy* between immediate saturation and existence of a **separately defined** positive sheet-odd condenser. It does **not** assert that a canonical KKL Wave contains, equals, or dominates the full connecting curve family. In particular, **positive full-condenser width is not a positive lower bound for an arbitrary Wave subfamily**, and an attached block is not guaranteed to be a single closed arc in every non-LC stage. None of the hypotheses about the actual angular access scale is claimed universally verified.

For the archive's **actual Misiurewicz** (non-prime-primitive) quadratic, `B_X` is a complete analytic arc of *fixed* angle `ell_X=4πθ≈1.99194`. It therefore belongs to branch 2 for every sufficiently small collar; PR #46's fixed-`ell` limit `2/(π−ell_X)` applies. One must **not** pretend its fixed `ell_X` realizes the newly analyzed shrinking-access limit. This difference is an explicit adversarial typing control.

## 7. Remaining high-value proof obligation

The next potential bridge to Issue #40 is now sharply stated. At a genuine prime-primitive stage, determine the actual conformal angular spans of the **whole** source-eligible attached Carathéodary blocks (not only planar attachment points). Then either:

- a block covers half the source circle and a properly typed input saturates immediately; or
- a shorter block gives a genuinely nonzero deck-odd *full* condenser, whose normalized response is determined by the two-scale product `h log(1/ell)` when both scales shrink.

**Two separate missing theorems are essential** before claiming native WAD nonreturn: prove that genuine proof-used Waves control the relevant sheet-opposed full-condenser family in the **correct extremal-width inequality direction**, and prove the corresponding analytic access-size/modulus bounds across the actual parabolic tail. These are the next source-grounded tests. An equivalence between a synthetic boundary word and an attached block is not accepted; the true `iota^*` proper-path relation and all complete attachments remain necessary.

**Reproducibility:** `python research/independent_audits/verify_annular_contact_crossover.py --check-manifest`. This checker verifies the original Fourier and modular products independently, the fixed contact-equilibrium constant, explicit reciprocal-resistance brackets, and a countercontrol showing the exponential formula cannot be applied to fixed-size electrodes. It does **not** machine-prove continuum equilibrium duality, elliptic endpoint regularity, or the source's non-LC attachment identification. Those are written arguments for independent specialist review.

**Status:** direct analytic proof for the model condenser; conditional native saturation/energy dichotomy. The KKL Wave Lemma, Issue #40, H1–H4, and MLC remain OPEN; neither a global novelty claim nor a specialist referee certification is made. Authorship of the KKL source inputs remains with Kahn, Kapiamba and Lyubich; the new source-aware synthesis and checker were assisted by OpenAI GPT-6.
