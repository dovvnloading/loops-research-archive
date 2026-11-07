# Issue #40 — electrical-response lens: sharp-cut no-go and smooth ideal-gate realization

**Date:** 2026-11-07. **Classification:** rigorous general conformal-energy / Hilbert-space lemmas; an exact explicit annular three-gate example with certified coercivity and a reproducible spectral regression; **proposed** interface to Kahn–Kapiamba–Lyubich (KKL) prime-end/WAD dynamics. This is **not** a proof of the original non-LC cut-return atlas, a width coercivity inequality, bounded Wave critical visits, or MLC. None of the general Dirichlet or Schur-complement facts below is asserted to be a newly discovered theorem in analysis.

**Motivation.** KKL [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §§2.6–2.7, 5.42, 6.1 and Appendix A.2–A.3, uses actual ideal-boundary markings, weighted arc diagrams (WAD), and a covering `f` / immersion `iota`. The archive's [Issue #40](https://github.com/dovvnloading/loops-research-archive/issues/40) has not identified a complete source-faithful critical-cut first-return atlas or a positive dual-WAD witness. The present note explores a *distinct analytic representation*: test the actual surface through finite-dimensional Dirichlet quadratic forms, without deciding whether every planar impression has a unique prime end.

**Prior art / scope.** Dirichlet's principle, extremal length, Neumann-to-Dirichlet maps and Schur/Kron reduction are classical (e.g. Rajala, *Extremal length and duality*, Expositiones Mathematicae 2025; Dörfler–Bullo, *Kron reduction of graphs with applications to electrical networks*, IEEE TCAS 2013). Our contribution here is a carefully typed formulation for the particular *ideal-marked annular interface*, a sharp-cut falsification, a thin-modulus degeneration theorem, and an explicit three-terminal exact lower spectral certificate. These are not automatically KKL Wave widths.

## 1. Why raw 0/1 voltages at a marked cut are invalid

Work on the conformal cylinder `A_h=(0,h) × (R/2πZ)` for any `h>0`, with Euclidean Dirichlet form

`a(u,v)=∫_{A_h}(u_t v_t+u_θ v_θ) dθ dt`.

Set the **outer** boundary value `u(h,θ)=0`. Give the **inner** boundary the step-voltage `g(θ)=1` on `0<θ<π`, `g(θ)=0` on `π<θ<2π`. Its Fourier coefficients with `ĝ_n=(2π)^(-1)∫ g e^(-inθ)` are `ĝ_0=1/2`, and `ĝ_n=(1-(-1)^n)/(2π in)` when `n≠0`. The energy of the harmonic extension, if finite, is

\[
\mathcal E_h(g)=2\pi\left(\frac{|\hat g_0|^2}{h}+\sum_{n\ne0}|n|\coth(|n|h)|\hat g_n|^2\right).
\tag{1}
\]

For odd `n`, `|ĝ_n|=1/(π|n|)`, so

\[
\mathcal E_h(g)\ge \frac4\pi\sum_{\substack{n\ge1\\n\text{ odd}}}\frac1n=+\infty.
\tag{2}
\]

Thus sharp adjacent marked-atom *Dirichlet voltages* have no finite-energy harmonic representative, even in a smooth annulus. This is a **no-go for that naive electrical terminalization**, not for KKL's genuine local extremal-width definitions.

For a Poisson-smoothed step `g_ε` with `ĝ_{ε,n}=e^{-ε|n|}ĝ_n`, the energy satisfies

\[
\mathcal E_h(g_\epsilon)=\frac{2}{\pi}\log(1/\epsilon)+O_h(1)
\quad (\epsilon\downarrow0).
\tag{3}
\]

Indeed `coth(nh)-1` has an exponentially summable contribution, and `Σ_{n≥1,odd}x^n/n=(1/2)log((1+x)/(1-x))` for `x=e^{-2ε}`. The divergence comes from **two jump endpoints**, not an irregular Julia impression. A direct finite Dirichlet-to-Neumann matrix with piecewise-constant sharp voltages cannot be the missing native-Wave bridge.

## 2. A finite-energy, exact continuum terminal response

Let `H={u∈H¹(A_h;R): trace u(h,·)=0}` with energy inner product `a`; the outer Dirichlet condition ensures coercivity by Poincaré. Choose real `ψ_1,…,ψ_m` in `C¹(S¹)` (or smoother) which are nonnegative, normalized `∫ψ_i=1`, nonzero and have **pairwise disjoint compact supports inside the marked open ideal arcs**, avoiding every cut. Define continuous boundary-average functionals

\[
L_i(u)=\int_0^{2\pi}\psi_i(\theta)\operatorname{Tr}_{t=0}u(\theta)\,d\theta.
\tag{4}
\]

By the trace theorem and Riesz representation, unique `w_i∈H` satisfy `a(w_i,u)=L_i(u)` for every `u∈H`. Their **Neumann-to-Dirichlet Gram matrix** is

\[
G_{ij}:=a(w_i,w_j)=L_i(w_j).
\tag{5}
\]

The `L_i` are independent because their supports are disjoint and nonempty; hence `G` is symmetric **positive definite**. For prescribed average values `L_i(u)=v_i` the unique minimizer and its exact energy are

\[
 u_v=\sum_i (G^{-1}v)_i w_i,\qquad
\boxed{\min_{L(u)=v}a(u,u)=v^T G^{-1}v.}
\tag{6}
\]

This is a continuum identity; no resistor graph, boundary LC, or guessed prime-end quotient is involved. The ideal annulus can be conformally uniformized even when its planar inner boundary lacks local connectivity; the probes are specified **on its ideal circle** and transported by the chosen conformal chart. The matrix depends on the chosen probes, which must be recorded as part of the data, and it is not canonical in the KKL sense.

Fourier diagonalization yields an exact absolutely convergent formula, with `ψ̂_i(n)=(2π)^(-1)∫ψ_i e^{-inθ}`:

\[
\boxed{G_{ij}=2\pi\left[h\,\hat\psi_i(0)\overline{\hat\psi_j(0)}+\sum_{n\ne0}\frac{\tanh(|n|h)}{|n|}\hat\psi_i(n)\overline{\hat\psi_j(n)}\right].}
\tag{7}
\]

The complex products are conjugate-symmetrized; the final matrix is real symmetric. Equation (7) follows by solving the harmonic mode equation with Neumann input `ψ_i` at `t=0` and outer Dirichlet zero.

**Exact Kron consistency.** Partition `v=(x,y)`, and write `K=G^{-1}` in matching blocks. If the `y`-terminal constraints are forgotten and their values are allowed to relax, then

\[
\min_y (x,y)^T K(x,y)= x^T\big(K_{xx}-K_{xy}K_{yy}^{-1}K_{yx}\big)x
= x^T (G_{xx})^{-1}x.
\tag{8}
\]

The final equality is the block-inverse identity. It is exact **for the original continuum variational problem**, so terminal elimination is well defined without separately choosing a discretization. No assertion about equality with WAD packet widths is made.

## 3. Three separated genuine ideal-gate probes, with explicit positive lower bound

Take `h=log 2`, interval width `ℓ=π/3`, and starts `a_1=0`, `a_2=π/2`, `a_3=π`. The three supports `[a_i,a_i+ℓ]` are separated. Define the `C¹` compactly supported normalized bumps

\[
\psi_{a}(\theta)=\begin{cases}
\ell^{-1}(1-\cos(6(\theta-a))),&a\le\theta\le a+\ell,\\
0,&\text{otherwise.}
\end{cases}
\tag{9}
\]

They vanish with first derivative at each endpoint. Their Fourier coefficients satisfy

\[
\hat\psi_a(0)=\frac1{2\pi},\qquad
|\hat\psi_a(1)|=\frac{54}{35\pi^2},\qquad
\hat\psi_a(n)=e^{-ina}\hat\psi_0(n).
\tag{10}
\]

Since `tanh(log 2)=3/5`, retaining **only Fourier modes n=0,±1** in (7) gives a lower matrix bound

\[
G\succeq G^{(1)}=\alpha\mathbf1\mathbf1^T+\beta
\begin{pmatrix}1&0&-1\\0&1&0\\-1&0&1\end{pmatrix},
\quad
\alpha=\frac{\log2}{2\pi},\quad
\beta=\frac{34992}{6125\pi^3}.
\tag{11}
\]

Indeed all omitted Fourier modes add positive-semidefinite Gram contributions. The antisymmetric vector `(1,0,-1)` has eigenvalue `2β`. In the orthogonal symmetric 2-plane the block has trace `3α+β` and determinant `2αβ`; hence its smaller eigenvalue is at least `2αβ/(3α+β)`. This latter lower bound is also below `2β`. Consequently

\[
\boxed{G\succeq \frac{2\alpha\beta}{3\alpha+\beta}I_3
\quad\text{with the explicit coefficient approximately }0.0789056.}
\tag{12}
\]

This lower bound is **analytically certified**, independent of truncating the infinite Fourier series or fitting a toy network. In particular `K=G^{-1}` is defined and has `‖K‖_2≤(3α+β)/(2αβ)`. Numerical Fourier truncations are supplementary checks, not the positivity proof.

For `n≥12`, Fourier integration gives the uniform estimate `|ψ̂_a(n)|≤144/(π² n³)`. Hence the absolute error in **each** entry of the Fourier truncation `G^(N)` for `N≥12` satisfies

\[
\boxed{|G_{ij}-G^{(N)}_{ij}|\le\frac{13824}{\pi^3N^6}.}
\tag{13}
\]

This is obtained by bounding the positive-mode tail by `4π Σ_{n>N}|ψ̂_0(n)|²/n` and using `Σ_{n>N}n^{-7}≤1/(6N^6)`. It gives a rigorous reproducible precision budget for actual analytic terminal experiments.

## 3a. An obstruction to UNIFORM smooth-gate coercivity in thin annuli

The preceding positive constant is for the fixed modulus `h=log 2`. It is **not** uniform in the conformal modulus. This reveals a second failure mode that a finite graph can conceal.

**Theorem 3.2 (thin-modulus degeneration, despite smoothing).** Keep the three fixed, pairwise disjoint probes (9), but allow the cylinder height `h>0` to tend to zero. Write `G_h` for the true continuum Gram (7). Then in Loewner order

\[
\boxed{0\prec G_h\preceq\frac{9h}{2\pi}I_3,\qquad
\frac1h G_h\longrightarrow\frac9{2\pi}I_3\quad(h\downarrow0).}
\tag{14}
\]

In particular **every** eigenvalue of `G_h` approaches zero and no positive lower spectral bound is uniform over annuli of arbitrarily small modulus. The inverse constrained-voltage energy `vᵀG_h^{-1}v` instead diverges on each fixed nonzero terminal vector as `1/h`.

**Proof.** In Fourier formula (7), the multiplier for `n=0` is `h`, while for `n≠0` it is `tanh(|n|h)/|n|≤h`. Therefore, by the exact Plancherel identity,

\[
0\prec G_h\preceq h\left(\int_0^{2\pi}\psi_i\psi_j\,d\theta\right)_{ij}.
\]

The supports are disjoint, and each normalized cosine arch satisfies

\[
\int_0^{2\pi}\psi_i^2\,d\theta
=\ell^{-2}\int_0^{\ell}(1-\cos 6t)^2dt
=\frac3{2\ell}=\frac9{2\pi}.
\]

For each fixed Fourier mode, its multiplier divided by `h` tends to 1. Every divided multiplier is bounded by 1; because the probes lie in `L²`, dominated convergence of the Fourier series gives `h^{-1}G_h→(∫ψ_iψ_j)=9/(2π)I_3`. Eigenvalue convergence and the energy statement follow. □

**Research consequence.** An inequality `lambda_min(G_h)≥epsilon>0` based only on three smooth ideal-gate probes is **false without a lower modulus bound**. This is a concrete physical-annulus obstruction, not a numerical countermodel. A more appropriate KKL comparison must either (i) normalize by local modulus, (ii) compare a generalized eigenvalue using simultaneous source/target responses, or (iii) exploit geometrically proved width/flux inequalities. None of those native calibrations is established here. This also cautions against reading the fixed-modulus value `0.0789056` as a universal constant across a parabolic tail.

## 4. Source-type compatibility: exact area counting, but no WAD theorem

For a proper unbranched holomorphic covering `f:S'→S` of degree `d` and any finite-energy real function `u` on `S`, conformal invariance plus the area formula imply

\[
\boxed{\mathcal E_{S'}(u\circ f)=d\,\mathcal E_S(u).}
\tag{15}
\]

For a holomorphic immersion `i:S'→S` with finite multiplicity almost everywhere and integrable pullback energy,

\[
\boxed{\mathcal E_{S'}(u\circ i)=\int_S N_i(z)|\nabla u(z)|^2\,dA(z),}
\tag{16}
\]

where `N_i(z)` is the number of preimages counted with multiplicity. This is a **physical interior identity**: it does not assume a continuous quotient of non-LC prime ends. For an embedding, it reduces to energy on the actual image. It tracks the missing or multiplied *interior* energy exactly, but by itself says nothing about whether a missing attachment has a **uniform positive fraction** of the relevant harmonic energy.

**Crucial unmatched interfaces:** (i) the selected smooth-probe Dirichlet energy must be compared quantitatively with KKL's canonical WAD/Wave modulus, respecting parallel/series laws; (ii) the actual immersed source may not have uniform finite sheet multiplicity near every non-LC end; (iii) a source cut with positive WAD width may have tiny or uncharged energy in this surrogate; (iv) proving positive loss or a uniform spectral gap **cannot** be obtained from (14)–(15) alone. No WAD transport or KKL interval-growth theorem is promoted.

## 5. The next discriminating analytic experiment

Choose one source-defined surviving critical gate from the root-free finite graph in the archive, with a verified ideal annulus uniformization at one **actual** KKL stage. Place smooth probe supports strictly inside its neighboring marked open arcs and a protected opposite-side arc. Compute a finite response Gram and the pullback Gram after `f` and `iota`, retaining actual sheet multiplicities and full attached-component regions. Test whether a **stage-uniform** inequality on the *correct geometric WAD sector* survives the q→∞ parabolic tail. A persistent positive generalized eigenvalue gap would be a candidate dual-width coercivity lemma; a vanishing gap is an explicit obstruction requiring a different geometric representation.

**Negative controls:** a sharp step voltage has infinite energy, probes supported only on one accessible region may miss a zero-sector gate, and an arbitrary finite network's Schur complement is **not** evidence for an actual KKL immersion. Any future promotion requires a conformally natural width calibration and the genuine `iota^*` proper-path census.

**Reproducibility:** Run `python research/independent_audits/verify_smooth_gate_response.py --check-manifest`. The verifier reconstructs the analytic Fourier coefficients, checks the spectral lower certificate and absolute tail bound, checks terminal forgetting against an independently evaluated 2-terminal response, tests sharp-step logarithmic divergence, and verifies a covering-energy identity on smooth functions. It additionally checks the thin-modulus asymptotic with the same exact Fourier response. No script claims to check KKL's analytic gates or WAD widths.
