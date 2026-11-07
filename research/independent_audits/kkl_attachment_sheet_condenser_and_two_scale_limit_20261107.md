# A genuine attachment-born sheet-character condenser, and the two-scale failure of uniform width

**Date:** 2026-11-07. **Status:** a rigorous conformal two-electrode theorem; an application to the **actual holomorphic slit/preimage pair** of the archive's repelling Misiurewicz quadratic; and a sharp two-parameter thin-collar obstruction. This supplies a **forced odd-sector signal for a deliberately defined full condenser**, not for the canonical Kahn–Kapiamba–Lyubich (KKL) Wave/WAD. No global MLC, native prime-primitive return acyclicity, or WAD coercivity is asserted. The analytic variational tools are classical; the geometry/attachment calibration and singular-limit separation are new *connections in this archive*, not a claim of general mathematical priority.

**Source crosswalk.** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §6.1, especially Proposition 6.5 and the paragraph before it (a genuine holomorphic covering `f` and a **different** immersion `iota` on the complements); Appendix A.2–A.3 for canonical WADs, ideal intervals, open/closed pullback. Archive [exact expanding attachment atlas](./kkl_misiurewicz_actual_expanding_attachment_atlas_20261106.md) supplies the same actual repelling polynomial, complete added-tree boundary `B_X`, exact Joukowski charts and the *actual* `f_*` and `iota^*`. Companion [sheet-character energy and width duality](./kkl_sheet_character_energy_and_width_duality_20261107.md) gives the correctly typed free-boundary charge estimate. The results here are about the **full connecting-curve family** in a collar; no full/subfamily width identification is made.

## 1. A sheet-odd potential that is FORCED, rather than assumed

Consider a connected degree-two holomorphic annular covering. In compatible conformal circular coordinates on a **source** collar, write

\[
A_h=(0,h)\times(\mathbb R/2\pi\mathbb Z),\qquad
\tau(t,\varphi)=(t,\varphi+\pi),\quad h>0.
\]

The source-to-target cover sends `(t,phi)` to `(2t,2phi mod 2pi)`. On the **source ideal inner boundary** choose a nonempty proper closed arc `A` of angular length `0<ell<pi`. Its deck translate `tau A` is disjoint. Fix an angular origin with

\[
A=[-\ell/2,\ell/2],\qquad
\tau A=[\pi-\ell/2,\pi+\ell/2]\pmod{2\pi}.
\]

Let `Gamma_h(A,tau A)` be the **entire** family of rectifiable curves in the collar joining the two inner arcs. Its conformal width is the mixed-boundary condenser capacity

\[
W_h(\ell)=\inf\left\{\int_{A_h}|\nabla u|^2:\ u\in H^1(A_h),\ \operatorname{Tr}_0u|_A=1,\ \operatorname{Tr}_0u|_{\tau A}=0\right\}. \tag{1.1}
\]

No value is imposed on the rest of the inner boundary or on the **outer** collar circle. In particular we do **not** use the pinned-outer energy of PR #44/45. The voltage traces on two positive-length, disjoint arcs have a finite-energy admissible extension, and the minimizer is unique by strict convexity once the electrodes fix constants.

**Theorem 1.1 (forced sheet character).** Let `u_h` be the unique minimizer in (1.1). Then

\[
\boxed{u_h\circ\tau=1-u_h,\qquad
P_0u_h=\tfrac12,\qquad
\mathcal E_{\rm odd}(u_h-\tfrac12)=W_h(\ell)>0,}\tag{1.2}
\]

where `P_0=(1+tau^*)/2`. Moreover **every** admissible, not necessarily harmonic, potential `u` satisfies

\[
\boxed{\mathcal E_{\rm odd}\left(\frac{u-u\circ\tau}{2}\right)\ge W_h(\ell).}\tag{1.3}
\]

*Proof.* The involutive transform `u↦1-u∘tau` interchanges the two prescribed electrode values and preserves the Dirichlet form and the free outer boundary. Uniqueness of the minimizer implies (1.2)'s first equality. Averaging the equality gives `P_0u_h=1/2`, so all its Dirichlet energy is odd. For arbitrary admissible `u`, the potential

\[
\tilde u=\tfrac12+\tfrac12(u-u\circ\tau)
\]

is admissible, deck-antisymmetric around `1/2`, and has energy exactly the odd-sector energy of `u`. Minimality gives (1.3). Positivity is justified by the continuous signed boundary charge in Theorem 1.2 below. \(\square\)

The point is **not** that every positive-width family forces an odd mode: deck-invariant electrode data admit a deck-invariant minimizer of positive width. Here the **swapped electrode geometry** forces nonzero odd energy, without prescribing a Fourier coefficient or assuming a sheet mismatch in advance. Which actual KKL Waves produce such electrodes remains OPEN.

## 2. An exact continuum lower certificate, and a uniform-in-angle upper test

Let `q_ell` equal `+1/ell` on `A`, `-1/ell` on `tau A`, and `0` elsewhere. This is a **signed Neumann charge** in `L²`, not a discontinuous Dirichlet voltage. It has zero mean. With `sinc(x)=sin(x)/x`, the nonzero Fourier coefficients are

\[
\widehat q_n=\begin{cases}
\pi^{-1}\operatorname{sinc}(n\ell/2),&n\text{ odd},\\
0,&n\text{ even}.
\end{cases}
\]

Its free-outer-boundary Neumann-to-Dirichlet energy response is finite and positive:

\[
\boxed{R_h(\ell)=\frac4\pi\sum_{\substack{n\ge1\\ n\text{ odd}}}
\frac{\coth(nh)}{n}\operatorname{sinc}^2(n\ell/2).}\tag{2.1}
\]

**Theorem 1.2 (quantitative finite-height forcing).** For all `h>0`, `0<ell<pi`,

\[
\boxed{\frac1{R_h(\ell)}\le W_h(\ell)\le\frac{2h}{\pi-\ell}.}\tag{2.2}
\]

*Proof.* Every admissible `u` has `int q_ell Tr_0(u)=1`. In `H¹(A_h)/R`, the squared Riesz norm of this linear functional is exactly (2.1), by Fourier separation with homogeneous Neumann condition on the outer boundary and free conditions on the uncharged inner parts. Cauchy–Schwarz gives `E(u)≥1/R_h`, and (2.1) converges absolutely because `sinc(n ell/2)=O_ell(n^-1)` and `coth(nh)` is bounded for fixed `h`. For the upper bound, take the angular function `g_*` equal to 1 on `A`, 0 on `tau A`, and **linear** across each of the two angular gaps of length `d=pi-ell`. Extend it constantly in the radial direction. Its angular energy is `2/d`; its collar energy is `2h/d`, establishing the upper bound. \(\square\)

These are actual conformal continuum bounds. The particular charge is not asserted optimal: `1/R_h` can be strictly less than `W_h`.

## 3. SHARP THIN-COLLAR LIMIT: nonzero odd width density, vanishing raw width

**Theorem 3.1 (exact small-modulus limit).** For **fixed** positive `ell<pi`,

\[
\boxed{\lim_{h\downarrow0}\frac{W_h(\ell)}h=\frac2{\pi-\ell}.}\tag{3.1}
\]

Thus the full condenser has strictly positive modulus-**normalized** sheet-odd width density, while `W_h(ell)→0` even though the two electrodes remain disjoint.

*Proof.* The radial-constant competitor of Theorem 1.2 gives `limsup W_h/h≤2/d`, `d=pi-ell`. Let `u_h` be the minimizing harmonic potential, with free outer boundary, and write `g_h=Tr_0 u_h`. By the Markov truncation `u↦min(1,max(0,u))` and uniqueness, `0≤g_h≤1`. Hence the `g_h` are uniformly bounded in `L²(S¹)`; choose a weakly convergent subsequence `g_h⇀g`. The values 1 and 0 on the two fixed positive-measure electrode arcs pass to the weak limit. For the harmonically optimal free-outer extension of any trace, Fourier separation gives

\[
\frac{W_h(\ell)}h
=4\pi\sum_{n\ge1} \frac{n\tanh(nh)}h\,|\widehat g_h(n)|^2.
\tag{3.2}
\]

Each fixed Fourier coefficient converges under weak `L²`, and `n tanh(nh)/h→n²`. Fatou applied first to finite sums and then letting their cutoff grow yields

\[
\liminf_{h\downarrow0}\frac{W_h}h
\ge 4\pi\sum_{n\ge1}n^2|\widehat g(n)|^2
=\int_0^{2\pi}|g'(\varphi)|^2\,d\varphi.
\]

In particular `g∈H¹(S¹)` (the zero-frequency constant costs no angular energy). On each of the two complementary gaps, `g` must change by magnitude 1. By one-dimensional Cauchy–Schwarz each gap contributes at least `1/d`, hence the right side is at least `2/d`. Together with the upper bound this proves (3.1). Since this applies to every sequence `h↓0`, the limit exists. \(\square\)

The unique limiting angular trace is the linear-gap `g_*` (in the natural weak/energy variational sense). Its Fourier coefficients are `ĝ_*(0)=1/2`, `ĝ_*(n)=2cos(n ell/2)/(pi(pi-ell)n²)` for odd `n` and zero for nonzero even `n`, giving the independent identity `4pi sum_{odd n≥1} n²|ĝ_*(n)|²=2/(pi-ell)`.

## 4. A SECOND, independently fatal degeneration: attached access shrinks

**Theorem 4.1 (vanishing-electrode and noncommuting limits).** Fix `h>0`. Put `rho=min(h/2,pi/4)`. Whenever `0<ell<rho`,

\[
\boxed{W_h(\ell)\le\frac\pi{\log(\rho/\ell)}.}\tag{4.1}
\]

Consequently,

\[
\boxed{
\lim_{\ell\downarrow0}\lim_{h\downarrow0}\frac{W_h(\ell)}h=\frac2\pi,
\qquad
\lim_{h\downarrow0}\lim_{\ell\downarrow0}\frac{W_h(\ell)}h=0.}\tag{4.2}
\]

Moreover the **explicit diagonal** `ell(h)=(h/4) exp(-1/h²)` for `0<h<1` satisfies

\[
\boxed{\frac{W_h(\ell(h))}h\le\frac{\pi h}{1+h²\log2}\longrightarrow0.}\tag{4.3}
\]

*Proof.* In the source collar place a Euclidean half-disk of radius `rho` centered on `(t=0,phi=0)`. Since `rho≤h/2` and `rho≤pi/4`, it lies inside the collar and is disjoint from the opposite electrode. Use a test potential equal to 1 for radius `r≤ell`, equal to `log(rho/r)/log(rho/ell)` for `ell<r<rho`, and 0 outside. Its trace is 1 on all of `A` (which has half-width `ell/2`) and 0 on all of `tau A`. Integration over the half-annulus gives energy exactly `pi/log(rho/ell)`. This proves (4.1) and the fixed-`h` limit 0. The other iterated limit follows from Theorem 3.1 as `ell↓0`; combining yields (4.2). For `0<h<1`, `rho=h/2` and `rho/ell(h)=2exp(1/h²)`, giving (4.3). \(\square\)

**Consequence for a parabolic tail.** Even when an actual attached prime-end interval is disjoint from its deck translate, the two arrows `f`/`iota` do NOT force a stage-uniform positive width, nor does merely dividing by annular height repair this. A useful native WAD coercivity theorem must control **both collar modulus and attachment access size/capacity** (or supply a stronger transverse quantity). This is a mathematically sharp two-parameter counterexample to an over-optimistic use of the PR #45 modulus-independent pinned-outer sheet trace inequality. It is **not** a counterexample to KKL's actual Wave Lemma, whose wave families and boundary conditions are different.

## 5. Why two complementary boundary responses may survive where one fails

For an annular cylinder and an arbitrary nonzero Fourier mode `n`, the boundary Dirichlet-to-Neumann multipliers with **outer Dirichlet-pinned** and **outer Neumann-free** conditions are, respectively,

\[
\Lambda_{\mathrm{pin},h}(n)=n\coth(nh),\qquad
\Lambda_{\mathrm{free},h}(n)=n\tanh(nh).
\]

Their product is **exactly** `n²` for every `h>0`. On the nonconstant trigonometric polynomials this gives the operator identity

\[
\boxed{\Lambda_{\mathrm{pin},h}\Lambda_{\mathrm{free},h}
=-\partial_\varphi^2.}\tag{5.1}
\]

Consequently for any smooth real mean-zero inner trace `g`, Cauchy–Schwarz gives

\[
\boxed{\mathcal E_{\mathrm{pin},h}(g)\,
\mathcal E_{\mathrm{free},h}(g)
\ge\Bigl(4\pi\sum_{n\ge1}n|\widehat g(n)|^2\Bigr)^2.}\tag{5.2}
\]

The right side is conformally angular `dot H^{1/2}` energy, independent of collar height. A single nonzero Fourier mode attains equality. This is a **classical separation-of-variables / reciprocal-polarization identity**, not a new general PDE theorem. It suggests that a future KKL obstruction should seek **two source-valid transverse width channels** rather than charge a single pinned-outer current as if it were a free-boundary wave. The archive has *not* identified the pinned response with an actual KKL WAD channel.

## 6. Actual holomorphic polynomial: the attached tree boundary IS an electrode

Use the archive's [actual Misiurewicz source atlas](./kkl_misiurewicz_actual_expanding_attachment_atlas_20261106.md): the unique root `c∈(-8/5,-3/2)` of

\[
H(c)=c^3+2c^2+2c+2=0,\qquad P_c(z)=z^2+c,\qquad b=c^2+c.
\]

The **genuine** postcritical tree is `T=[c,b]`, its full preimage is `T'=[c,-c]`, and it has one real excess branch `X=(b,-c]` attached at `x=b`. The exact Joukowski chart and its source-to-target polynomial identity are

\[
\Psi_{T'}(w)=-\frac c2(w+w^{-1}),\quad
\Psi_T(w^2)=\frac{c+b}{2}+\frac{c^2}{4}(w^2+w^{-2}),\quad
P_c(\Psi_{T'}(w))=\Psi_T(w^2).
\]

The source cover therefore has deck involution `w↦-w`. The **whole actual Carathéodory boundary of the added component**, born in the genuine immersion pullback when its old root access is included, is

\[
B_X=\{e^{i\varphi}:|\varphi|\le 2\pi\theta\},
\qquad \theta=\frac{\arccos(-c-1)}{2\pi}\in(0,1/4).
\]

Its source angular size is `ell_X=4pi theta<pi`, and `B_X∩tau B_X=∅`. For every sufficiently small positive `h`, the physical polynomial source complement contains the **real** Joukowski collar `1<|w|<e^h`, mapped under `P_c` by `w↦w²`. Thus the full connecting condenser between **the actual entire attachment block** `B_X` and its true deck translate is a *genuine holomorphic-model instance* of Theorems 1.1–4.1. Its minimizer is **forced sheet-odd** and

\[
\boxed{\lim_{h\downarrow0}\frac{\mathcal W(\Gamma_h(B_X,\tau B_X))}h
=\frac2{\pi(1-4\theta)}\ \approx 1.739655969676542.}\tag{6.1}
\]

The value follows from the exact algebraic parameter and elementary `arccos`, not from an arbitrary finite resistor network. The positive signal is an **electrode-contrast measurement we chose** from actual source geometry; it is *not* forced merely by the existence of the attached component to appear in an unrelated native Wave. This example is **outside** the prime-primitive renormalization category targeted by KKL, as explicitly stated in the original atlas.

**Conditional native interface.** The same theorem applies to any real KKL connected degree-two `f`-cover whose source inner ideal boundary contains a source-defined complete attached Carathéodory **arc** `B_X` with deck-angular size `<pi`. Its genuine `iota^*` must separately certify that block and its precise access eligibility. This constructs a positive, sheet-odd full-collar condenser *for that attached arc*, without local connectivity or a pointwise boundary extension of `iota`. It does **not** imply a positive canonical bivertical WAD or critical-return nonperiodicity. The actual native access may have deck-angular size `≥pi` or involve non-simple intervals, in which case this specific opposed-electrode construction is **inapplicable**.

## 7. Exact next acceptance test

The necessary missing statement is now more geometric than Fourier-analytic:

> Given a genuine KKL short critical Wave and an actual connected source `f`-cover, can one locate **two disjoint electrode regions exchanged by the deck involution** whose potential contrast is required by the *actual canonical wave arc family*, and whose finite-height collar width has a stage-uniform relative capacity after its geometric scales are accounted for?

To establish it one must (a) identify full, typed `iota^*` attachment blocks and adjacent source sectors, (b) show a **domination in the right direction** from the *canonical* WAD path family to the constructed full condenser (subfamilies may have strictly smaller widths), and (c) control the ratio between the actual attachment angular scale and annular modulus or replace it with a certified transverse-polarization comparison. Neither prime-end collisions nor nonzero sheet count alone satisfies (a)–(c). If the ratio degenerates like the diagonal example (4.3), that is a first-failure certificate for this proposed *energy* method, not for the source Wave theorem.

**Formal status and attribution.** The condenser theorems and asymptotic limits have written analytic proofs; the bundled regression verifies the algebraic covering, Fourier multipliers, bounds, symbolic limits, and deterministic manifest. It does NOT check PDE compactness, the actual native WAD relation, non-LC prime-end correspondence or the full MLC proof. Classical conformal capacity, Fourier boundary operators, Böttcher/Joukowski coordinates, and elementary Dirichlet variational symmetry receive standard attribution; KKL's covering/immersion/WAD framework belongs to the cited authors. Research synthesis and tests assisted by OpenAI GPT-6. Independent referee scrutiny and novelty assessment remain open. **Issue #40, `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`, Wave amplification, H1–H4 and global MLC remain OPEN.**