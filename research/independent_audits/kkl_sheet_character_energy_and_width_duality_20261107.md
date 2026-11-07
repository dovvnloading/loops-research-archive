# A sheet-character Dirichlet defect and smooth-charge calibration to genuine extremal width

**Date:** 2026-11-07. **Status:** rigorous covering/variational theorems with a directly applicable conditional-on-cover-topology formula for the native KKL `f` leg and a physically realized degree-64 external quadratic cover; exact and certified finite tests. This is **not** the Kahn–Kapiamba–Lyubich (KKL) critical-cut immersion, a WAD equivalence, an all-scale gap, or a proof of MLC. The general Hilbert projection, conformal area, Dirichlet–Thomson, and capacity/modulus principles are classical; what is new *within this archive* is their sheet-sensitive interface, sharp test and adversarial comparison with PR #44. No independent novelty/priority claim is made.

**Source interfaces:** [KKL, arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §§2.6–2.7, 5.9, 6.1, Appendix A.1–A.3 (actual WAD/ideal markings; no global single-valued immersion boundary map); [PR #44's smooth-gate continuum model](./kkl_smooth_gate_dirichlet_response_20261107.md); the archive's [actual physical period-27 exterior 64-sheet projection](./period27_exterior_ray_pullback_20261106.md). Capacity = extremal width for the **full connecting curve family**, with the exact convention `W=1/extremal length`, is classical, e.g. Ahlfors' *Conformal Invariants* and the mixed Dirichlet–Neumann treatment cited in Anić–Mateljević–Šarić (2002). This equality does **not** identify any proper subfamily of curves with a canonical KKL Wave.

## 1. Real physical holomorphic cover, NOT an abstract replacement for KKL

For any quadratic `f_c(z)=z²+c` with connected filled Julia set, the classical normalized Böttcher isomorphism `φ:C\K(f_c)→{|w|>1}` satisfies `φ(f_c(z))=φ(z)²`. In particular it applies to the archive's rigorously certified period-27 real center `c_*`. Fix an arbitrary `a>0`, cylinder height `h>0`, and an integer `p≥1`, `d=2^p`. Put

\[
S'_{a,h}=\{a<\log|\phi(z)|<a+h\},\qquad
S_{da,dh}=\{da<\log|\phi(z)|<d(a+h)\}.
\]

The **actual** holomorphic `f_c^p:S'_{a,h}→S_{da,dh}` is a regular unbranched degree-`d` covering. The conformal cylinder coordinates `t=log|φ|-a∈(0,h)`, `θ=argφ mod 2π` carry it to

\[
(t,\theta)\longmapsto(dt,d\theta\pmod{2\pi}),
\]

with deck generator `τ(t,θ)=(t,θ+2π/d)`. Every boundary component here is a **positive-potential smooth equipotential**, so this physical theorem uses no Julia-boundary local connectivity, landing, prime-end identification, or KKL immersion `iota`. For `p=6`, this is the genuine **64-to-1 physical external** covering already known in the archive; it is NOT a 64-sheet KL interior localization statement.


### 1a. Direct application to the **native KKL covering leg**

This is not restricted to the exterior quadratic model. In KKL §2.1 the map `f:U'→U` of a ψ-ql pair is a **double branched covering**. KKL §6, immediately before §6.1, explicitly sets `T'=f^{-1}(T)` and says that the restricted `f:V'=U'\T'→V=U\T` is a holomorphic **covering**, while `iota:V'→V` is an **immersion**. Thus the branch point has been removed from the `f`-leg. Whenever the actual source `V'` is connected and the restriction has degree two (the standard annular setting), `f` has a canonical deck involution `τ`. On the real, actually given source Riemann surface, choose a corresponding boundary component to pin at zero and let `H(V')` be the energy completion of its finite-energy traces. Then every `u∈H(V')` has the **native** decomposition

\[
\boxed{\mathcal E_{V'}(u)
=2\mathcal E_V(v)+\mathcal E_{V'}\left(\frac{u-u\circ\tau}{2}\right),
\quad \frac{u+u\circ\tau}{2}=v\circ f.}\tag{1a}
\]

This is a theorem for the *real holomorphic `f`-covering part* of KKL, under the stated connected-degree-two and compatible energy-boundary hypotheses. It neither assumes local connectivity nor collapses distinct prime ends. If `V,V'` are uniformized as nested conformal annuli, the same formula (3.2) with `d=2` computes optimal smooth ideal-boundary probe constants for their genuine `f`-leg. The annular height is then the **actual** conformal modulus, not an arbitrary numerical constant.

**Critical separation:** `Phi=f_*iota^*` is *not* just this covering. The genuine `iota^*` is defined through proper paths and full attached-component Carathéodory boundaries, and it does not automatically intertwine the deck involution or preserve the signed probe mismatch. Consequently (1a) is **not** the positive WAD nonreturn theorem of Issue #40. If the source complement has more than one connected component, apply the energy splitting to a verified connected regular cover, not by asserting a deck involution that does not exist on a disconnected component.

## 2. Exact sheet-blind projection and loss identity

Let `H_h={u∈H¹((0,h)×S¹;R):Tr_{t=h}u=0}` with Dirichlet inner product `a_h(u,v)=∫(u_t v_t+u_θ v_θ)dt dθ`, and energy `E_h(u)=a_h(u,u)`. Define the **invariant/deck-blind projection**

\[
P_0u=\frac1d\sum_{j=0}^{d-1}u\circ\tau^j.
\]

**Theorem 2.1 (exact deck-character defect on a real holomorphic cover).** For each `u∈H_h`, there is a unique descended `v∈H_{dh}` on the target cylinder with `P_0u=v∘f_c^p`, and

\[
\boxed{E_h(u)=d E_{dh}(v)+E_h(u-P_0u).}\tag{2.1}
\]

The last term is precisely the squared Dirichlet distance to the space of functions descending to the target. It is zero iff `u` is deck-invariant, and is strictly positive for any `u` that takes different values on a set of positive measure in a deck orbit. Equivalently the complexified energy admits an orthogonal sum over the `d` deck characters, and the defect is the sum of **all nontrivial character energies**.

**Proof.** Each `τ^j` is an orientation-preserving conformal isometry of the cylinder, hence a unitary action on `H_h` for `a_h`. Its finite-group average `P_0` is a self-adjoint idempotent, so `u=P_0u+(1-P_0)u` is orthogonal in the energy inner product. An invariant `H¹` function descends under a finite unbranched covering. The conformal area formula gives `E_h(v∘f_c^p)=dE_{dh}(v)`. These statements imply (2.1). For character projections `P_j=d^{-1}Σ_l exp(-2πijl/d)U_{τ^l}`, orthogonality of roots of unity gives the asserted decomposition. Since the outer Dirichlet condition excludes nonzero constants, the defect vanishes iff the difference vanishes in `H_h`. □

**Critical limitation.** The existence of 64 sheets alone does **not** force a positive defect: every descended potential has zero defect. Positivity requires *actual non-descending boundary information*. A scalar target Gram never supplies that information without sheet-sensitive probes or character-resolved traces.

## 3. A sharp, finite-energy sheet-difference certificate

For `N≥1`, take the nonnegative normalized Fejér probe

\[
\rho_N(\theta)=\frac1{2\pi}\left(1+2\sum_{n=1}^N\left(1-\frac n{N+1}\right)\cos n\theta\right),
\quad\int\rho_N=1,
\]

and let `δ_d=2π/d`. This probe is smooth and periodic (it is **not compactly supported**; increasing `N` concentrates it but does not make it a marked-atom indicator). Define a measured *adjacent-sheet difference*, on the source inner equipotential,

\[
\Delta_{d,N}(u)=\int_0^{2\pi}\rho_N(\theta)\bigl(u(0,\theta)-u(0,\theta+\delta_d)\bigr)d\theta.
\tag{3.1}
\]

Every invariant potential has `Δ=0`. Define the explicit finite quantity

\[
\boxed{R_{d,N}(h)=\frac2\pi\sum_{n=1}^N
\frac{(1-n/(N+1))^2[1-\cos(2\pi n/d)]\tanh(nh)}n.}\tag{3.2}
\]

**Theorem 3.1 (optimal, strictly positive sheet-energy defect).** For every `u∈H_h`,

\[
\boxed{E_h(u-P_0u)\ge\frac{|\Delta_{d,N}(u)|^2}{R_{d,N}(h)}.}\tag{3.3}
\]

The denominator is finite and strictly positive for every `d≥2,N≥1,h>0`, and the coefficient `1/R` is **optimal**: equality is attained by a harmonic source potential with outer boundary zero, inner Neumann flux `ρ_N(θ)-ρ_N(θ-δ_d)`, and zero invariant part. More generally,

\[
\boxed{E_h(u)\ge dE_{dh}(v)+|\Delta_{d,N}(u)|^2/R_{d,N}(h).}\tag{3.4}
\]

**Proof.** Write `q(θ)=ρ_N(θ)-ρ_N(θ-δ_d)`. Its Fourier coefficients are
`q̂_n=(2π)^(-1)(1-|n|/(N+1))(1-exp(-inδ_d))` for `1≤|n|≤N`, zero elsewhere, and `q̂_0=0`. In the Dirichlet energy Hilbert space `H_h`, the Riesz representer of `u↦∫q·Tr_0 u` has Fourier trace `q̂_n tanh(|n|h)/|n|` (outer boundary Dirichlet, source inner flux `q`). Its squared norm is

\[
2\pi\sum_{n\ne0}\frac{\tanh(|n|h)}{|n|}|\hat q_n|^2=R_{d,N}(h).
\]

Because `q̂_n=0` whenever `d|n`, this representer is orthogonal to every deck-invariant potential. Therefore `Δ(u)=Δ((1-P_0)u)` and Hilbert-space Cauchy–Schwarz gives (3.3). Choosing `u` proportional to the representer attains equality. The `n=1` term proves `R>0`. Combining with (2.1) proves (3.4). □

**Explicit exact sharp constants at `h=log 2`.** For `d=2,N=1`, `tanh(log2)=3/5`, so

\[
R_{2,1}(\log2)=\frac3{5\pi},\qquad
\boxed{E_h(u-P_0u)\ge\frac{5\pi}{3}|\Delta_{2,1}(u)|^2.}\tag{3.5}
\]

For the physical **64-sheet** cover at `N=1`,

\[
R_{64,1}(\log2)=\frac{3}{10\pi}(1-\cos(\pi/32)).
\]

Using `1-cos x≤x²/2` yields the elementary *certified* bound

\[
\boxed{E_h(u-P_0u)\ge\frac{20480}{3\pi}|\Delta_{64,1}(u)|^2.}\tag{3.6}
\]

This is sharp up to the stated cosine inequality for the **global** low-frequency probe. The constant cannot be interpreted as uniform local-gate coercivity: for such a low-frequency probe, physically allowed sheet-adjacent mismatches may themselves shrink with `d`. The verifier also tests `N=256`, a much more concentrated but still globally supported finite-spectrum probe. Nonzero sheet mismatch is a **hypothesis**, not a consequence of a two-sheet covering or a source limb crossing.


### 3a. A *modulus-independent* source-sheet trace obstruction (stronger than a single probe)

Let `g(θ)=Tr_{t=0}u(θ)` and define `ĝ_n=(2π)^(-1)∫g(θ)e^(-inθ)dθ`. The true source deck average deletes precisely the modes whose integer frequency is **not** divisible by `d`. This gives a complete, rather than just one-probe, trace inequality.

**Theorem 3.2 (character-resolved boundary-energy bound).** For every real finite-energy `u∈H_h` and every `d≥2`, with `P_0` the actual deck average,

\[
\boxed{
E_h(u-P_0u)\ge
4\pi\sum_{\substack{n\ge1\\d\nmid n}}
 n\coth(nh)|\hat g_n|^2
\ge
4\pi\sum_{\substack{n\ge1\\d\nmid n}}n|\hat g_n|^2.}
\tag{3.7}
\]

The first inequality is **sharp for the harmonic extension** of the noninvariant boundary trace with zero outer boundary. The second estimate is **independent of annular modulus and covering degree** once the source trace is expressed in its natural angular Fourier coordinates. It is a quantitative obstruction to losing *nontrivial deck characters*, not to the mere existence of multiple sheets.

**Proof.** By the character projection, the inner trace of `(1-P_0)u` has Fourier coefficients `ĝ_n` exactly when `d∤n`, and zero coefficients otherwise. The harmonic extension of a fixed trace `g_-` with outer value zero minimizes Dirichlet energy, and its `±n` modes contribute exactly `4π n coth(nh)|ĝ_n|²` (the same mode computation as PR #44's equation (1)). Finally `coth(nh)≥1`. □

For the **native connected degree-two `f`-cover**, `P_0u=(u+u∘τ)/2` and the first odd Fourier coefficient is necessarily noninvariant. Thus, on *that actual covering leg*,

\[
\boxed{E_h(u_{\rm odd})\ge4\pi\coth(h)|\hat g_1|^2\ge4\pi|\hat g_1|^2.}\tag{3.8}
\]

This coefficient's **modulus** does not depend on the arbitrary angular origin of the chosen annular uniformization. It also equals the optimal strength of the rotated `N=1` Fejér pair: if `Δ_{2,1,α}` uses `ρ_1(θ-α)`, then `sup_α|Δ_{2,1,α}(u)|=2|ĝ_1|`. The harmonic first odd mode attains equality in the first bound. For a particular unrotated probe with `h=log2`, equation (3.5) gives `5π/3` as the sharp `|Δ|²` coefficient; for *any* `h>0` it gives the uniform estimate `E_h(u_odd)≥π|Δ_{2,1}(u)|²`.

**Exact limitation:** `ĝ_1` can vanish even for strongly non-descending data (e.g. a pure third harmonic at `d=2`), and a native WAD cannot be assumed to produce any specified nonzero Fourier mode. One must either measure the full noninvariant trace norm in (3.7), or prove that an actual source-labeled arc packet forces a specific mode/charge mismatch. No universal sheet-*induced* positivity follows solely from degree two.

## 4. An actual (limited) bridge from smooth probes to conformal width

The PR #44 response fixes the **entire outer boundary at zero**. That response is useful for outer-to-inner conductance but **cannot** be directly used as a lower bound for width between two portions of the *same* inner boundary, where the outer boundary is *free*. Here is the correctly typed alternative.

Let `A,B` be disjoint closed arcs on the inner equipotential circle with positive angular separation, and let `Γ(A,B)` be the family of **all rectifiable curves inside the annulus connecting them**. The usual condenser identity says `W(Γ(A,B))=Cap_h(A,B)`, the infimum of `E_h(u)` over `u∈H¹(A_h)` whose traces are `1` on `A` and `0` on `B`; traces elsewhere, including the outer boundary, are free (mixed Neumann). Constants are quotiented when defining the energy space, not prescribed at the outer boundary.

Choose normalized nonnegative smooth or `C¹` probes `ψ_A,ψ_B` supported in `A,B` (with endpoint zero values where needed); put `q=ψ_A-ψ_B`, which has zero mean. With Fourier normalization `q̂_n=(2π)^(-1)∫q e^(-inθ)`, set

\[
\boxed{R_h^{\rm free}(q)=2\pi\sum_{n\ne0}\frac{\coth(|n|h)}{|n|}|\hat q_n|^2.}\tag{4.1}
\]

**Theorem 4.1 (smooth-charge lower bound for a genuine full extremal-width family).** If `R_free<∞`, then

\[
\boxed{\mathcal W(\Gamma(A,B))\ \ge\frac1{R_h^{\rm free}(q)}.}\tag{4.2}
\]

**Proof.** Work in `H¹(A_h)/R` with the Dirichlet form as a Hilbert inner product. Because the charge has total mass zero, `ℓ_q(u)=∫q·Tr_0u` is continuous on the quotient. Its Neumann Riesz representer has Fourier multiplier `coth(|n|h)/|n|` for `n≠0` and is orthogonal to constants; hence its squared norm is (4.1). Every condenser-admissible `u` has `ℓ_q(u)=1`. Cauchy–Schwarz therefore gives `E_h(u)≥1/R_free`. Taking the infimum and using the standard capacity/full-extremal-width identity gives (4.2). This proof does **not** assert that a proper subfamily of `Γ(A,B)` has the same width. □

**An explicit true width interval, not a toy resistor network.** Set `h=log2`, `ℓ=π/3`, `A=[0,ℓ]`, `B=[π,π+ℓ]`, and choose `ψ_A(θ)=ℓ^{-1}(1-cos6θ)` on `A`, zero outside, `ψ_B(θ)=ψ_A(θ-π)`. Both are normalized `C¹` and have disjoint supports (one can shrink the electrode arcs slightly beyond the supports if desired). Parseval gives `∫(ψ_A-ψ_B)^2=9/π`. Since `coth(nlog2)≤5/3`, (4.1) gives `R_free≤15/π`. A competing piecewise-linear angular voltage, equal to 1 on `A`, 0 on `B`, linearly interpolated in the two angular gaps and constant in the radial variable, has energy `3log2/π`. Thus

\[
\boxed{\frac\pi{15}\le \mathcal W(\Gamma(A,B))\le\frac{3\log2}\pi.}\tag{4.3}
\]

The Fourier series evaluates to `R_free≈2.49272565469`, hence the *stronger certified-via-tail* bound `W≥1/(R_free^(256)+92160/(π³256^6))≈0.40116729176`. The exact analytic tail follows from `|ψ̂_A(n)|≤144/(π²n³)` for `n≥12`, previously proved in PR #44. The numeric value illustrates, but does not replace, the exact series and bound.

### Concrete failure of using the WRONG outer-boundary condition

For the same single probe `ψ_A`, the PR #44 pinned-outer response obeys `G_AA≤9h/(2π)`, so its relaxed one-terminal minimization (average on `A` fixed at 1 **and outer boundary pinned at 0**) has energy at least `2π/(9h)`. At `h=log2`,

\[
\underbrace{2\pi/(9\log2)}_{>1.007}
\quad>\quad
\underbrace{3\log2/\pi}_{<0.662}
\quad\ge\quad Cap_h(A,B).
\]

Thus **using the pinned-outer minimal energy as a lower bound on the inner-arc-to-inner-arc width is false even on the standard smooth annulus**. The direction of boundary-condition relaxation matters; the mixed-Neumann signed-charge response in Theorem 4.1 repairs this particular mismatch. This is a correction to any *proposed application* of PR #44, not a contradiction of any theorem asserted there.

## 5. The missing native KKL step, now testable and falsifiable

Theorems 2–4 are bona fide analytic identities; Section 1a applies the deck decomposition directly to the authentic KKL **covering** leg under the specified connected-degree-two hypotheses, and for `p=6` the cover is the *actual physical quadratic map on positive Green levels*. They do **not** yet furnish a WAD nonreturn theorem for `F_* = f_* iota^*`:

1. **Actual sheet-labeled wave constraints:** exhibit a genuine KKL critical gate and a source-admissible potential/trace whose **two real inverse sheets** have a source-imposed `Δ≠0`. Two distinct sheet labels or a collision alone does not force different harmonic potentials.
2. **Correct curve family:** identify the charged conformal condenser with the **actual canonical WAD/Wave family** or give a proved domination/overflow direction. For `Γ_wave⊂Γ(A,B)`, the inequality `W(Γ(A,B))≥1/R_free` does **not** lower-bound `W(Γ_wave)`.
3. **Immersion and attachments:** the external physical map has no internal attached Julia-tree components, and the native `f`-leg decomposition does not describe the native immersion. Before importing the probe-current inequality (3.3) into KKL's non-LC `iota^*`, account for every complete Carathéodory attachment, monodromy and *proper-path* lift; there is no manufactured global prime-end quotient.
4. **Uniformity across stages:** the constants depend on collar height, probe width and sheet degree. A modulus-normalized, source-certified comparison is required before using them in a parabolic tail.

**Research decision:** The strongest proposed next lemma is a *native wave-to-sheet-current witness*: a source-defined positive bivertical WAD at a surviving critical cut must induce a **nonzero, controlled smooth signed boundary-current mismatch on the proper holomorphic collar**, or else contribute a separately quantified escaped/vertical WAD width. Prove the actual map between these data, with closed-crest/access typing. If this fails on even one genuine source-defined gate, record the first-failure crosscut or attached component. Unlike enumerating more finite intervals, this would connect the source's width to a coercive, sheet-faithful analytic quantity.

**Attribution / evidence:** Classical Dirichlet and extremal-width results belong to their original authors; classical Böttcher coordinate provides the physical quadratic cover; KKL's WAD/immersion framework belongs to Kahn–Kapiamba–Lyubich. OpenAI GPT-6 assisted this combined continuum/physical audit, algebra and test code. The archive's Issue #40, interval-growth repair, parabolic Wave amplification, H1–H4 and MLC remain OPEN. No independent mathematical referee or research-priority claim is made.
