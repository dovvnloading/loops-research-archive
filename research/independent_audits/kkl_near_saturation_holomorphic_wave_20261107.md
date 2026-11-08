# From almost-saturated attachments to actual marked Waves: a holomorphic narrow-gap theorem

**Date:** November 7, 2026. **Research status:** a new *within-the-archive* holomorphic, sheet-sensitive Wave construction with an exact conformal-width formula, a rigorous canonical-WAD lower bound under an explicitly refined ideal marking, and a genuine quadratic one-parameter realization. This works on a true quadratic-like covering/immersion pair, **but not in the prime-primitive, periodically repelling KKL class**. It is not an actual critical-return nonperiodicity theorem, a uniform parabolic-tail estimate, or MLC. The underlying extremal-length and canonical buffer statements are classical / from Kahn–Kapiamba–Lyubich; independent originality or priority is not asserted.

## Source and the reversal of the preceding lens

Primary source: Kahn–Kapiamba–Lyubich, *MLC for parabolically bounded primitive renormalization*, **arXiv:2606.27272v1**, Appendix A.1 (a path is admissible only if not subordinate to a marked multi-interval of length at most two; definition of a Wave, its proper base, end intervals and crest), Appendix A.2.2–A.2.3 (valid WADs and canonical maximality `W_valid(alpha) <= W_can(alpha)+2`), §6.1 and Proposition 6.5 (covering versus immersion, whole excess-component boundary). The archive's [exact Misiurewicz attachment atlas](./kkl_misiurewicz_actual_expanding_attachment_atlas_20261106.md) supplies the same **algebraic Joukowski identity** for one fixed parameter; here it is shown to hold for a *whole holomorphic parameter interval*, with a new nearly saturated geometry. The merged [contact-resistance paper](./kkl_annular_contact_resistance_crossover_20261107.md) instead treats **small attached arc** `ell -> 0`, where its full condenser can be tiny. The new regime is the opposite limit `ell -> pi^-`.

A crucial conceptual change is that we do **not** infer a Wave from an arbitrary full condenser. We exhibit a legitimate **one-packet lamination of actual simple proper paths**, measure *its own* width exactly, and then use the source's canonical maximality. This supplies a source-valid calibration for the chosen marking and arc class without assuming the full condenser is a KKL Wave.

## 1. A genuine one-parameter holomorphic slit/attachment pair

For any `0 <= epsilon <= 1/4`, set

\[
 c=-1-\epsilon,\quad b=c^2+c=\epsilon(1+\epsilon),\quad P_c(z)=z^2+c,\quad T=[c,b].
\tag{1.1}
\]

Since `c<0<=b<=-c`, the critical point lies in `T`, and direct endpoint/monotonicity checks show

\[
\boxed{P_c(T)=T,\qquad P_c^{-1}(T)=[c,-c]=:T',\qquad X:=T'\setminus T=(b,-c].}
\tag{1.2}
\]

For example, `P_c(c)=b`, `P_c(0)=c`, and `P_c(b)=b^2+c\in[c,b]`. The full preimage is real because `z^2\in[0,b-c]=[0,c^2]` for `P_c(z)\in T`. Thus **one genuine excess tree segment** attaches to `T` at its right tip `x=b`. This `T` is a selected *invariant real slit carrier*, **not** claimed to be the complete postcritical Hubbard tree of every `P_c` in the interval.

Take `U=D(0,5)` and `U'=P_c^{-1}(U)`. The pair `(P_c,inclusion):U'\rightrightarrows U` is a proper quadratic-like covering plus a holomorphic immersion, and `U'\Subset U`, since `|z|^2<5+|c|<=25/4` implies `|z|<5/2<5`. In particular the actual complements `V'=U'\setminus T'`, `V=U\setminus T` have a genuine degree-two covering `P_c:V'->V` and a separately defined, nonproper inclusion immersion `iota:V'->V`.

Write exact Joukowski coordinates for their inner ideal/Carathéodory circles:

\[
\Psi_{T'}(w)=-\frac c2(w+w^{-1}),\qquad
\Psi_T(v)=\frac{c+b}{2}+\frac{c^2}{4}(v+v^{-1}),
\qquad |w|,|v|>1.
\tag{1.3}
\]

The algebraic identity

\[
\boxed{P_c(\Psi_{T'}(w))=\Psi_T(w^2)}\tag{1.4}
\]

holds **for every** `epsilon` in (1.1), because `c+b=2c+c²`. Thus the actual source ideal covering is angular doubling and its deck involution is `tau(w)=-w`; no synthetic boundary quotient is assumed for the inclusion `iota`.

The complete source Carathéodory side block of the actual added segment `X` is

\[
\boxed{B_X=\{e^{i\theta}:|\theta|\le\arccos\epsilon\},\qquad
\ell_\epsilon=2\arccos\epsilon,\quad
 d_\epsilon:=\pi-\ell_\epsilon=2\arcsin\epsilon.}\tag{1.5}
\]

Indeed on `|w|=1` the physical landing map is `(-c)cos(theta)` and the added component corresponds to `cos(theta)>=b/(-c)=epsilon`. For `epsilon>0`, the two closed arcs `B_X` and `tau B_X` are disjoint, separated by **two equal gaps** of angular length `d_epsilon`. At `epsilon=0`, `ell=pi`, each closed block maps under angular doubling onto the **full target ideal circle** (and the translated blocks meet at their endpoint accesses). This is *genuine immediate-cover saturation* only for a correctly typed input whose immersion pullback contains the **whole** closed `B_X`.

**Physical collar:** For `0<h<=1/4`, the Joukowski collar `1<|w|<e^h` lies in the actual `V'` uniformly for all `epsilon<=1/4`: `|Psi_{T'}(w)|<|c|cosh h <=(5/4)cosh(1/4)<1.3`, so `|P_c(Psi)|<1.3²+1.25<5`. In coordinates `(t,theta)=(log|w|,arg w)` this collar is precisely `(0,h)×S¹`, with conformal area/Dirichlet energy preserved.

## 2. Actual admissible, finite-marking Wave packets around each gap

Fix `0<h<=1/4` and `0<epsilon<sin(h/2)`; then `r_0:=arcsin(epsilon)=d_epsilon/2<h/2=:R`. Split the inner source ideal circle into **six** open marking atoms, plus their marked cuts:

\[
\begin{aligned}
I_0&=(-\ell/2,\ell/2),\\
I_1&=(\ell/2,\pi/2),\quad
I_2=(\pi/2,\pi-\ell/2),\\
I_3&=(\pi-\ell/2,\pi+\ell/2),\\
I_4&=(\pi+\ell/2,3\pi/2),\quad
I_5=(3\pi/2,2\pi-\ell/2).
\end{aligned}\tag{2.1}
\]

The entire outer ideal boundary is a seventh marking interval. This is a **deliberately selected legitimate ideal marking** under KKL Appendix A.1; it is **not asserted to be** the original small-Julia vertex-side marking used in KKL §6.

For each `r_0<r<R`, consider the physical conformal image under `Psi_{T'}` of the *Euclidean half-circle in the flat log cylinder*

\[
\gamma_r(s):\qquad t=r\sin s,\qquad
\theta=\frac\pi2+r\cos s,\qquad 0<s<\pi.
\tag{2.2}
\]

The endpoints are `theta=pi/2 ± r`, one strictly inside `I_0=B_X^\circ` and the other inside `I_3=(tau B_X)^\circ`. The paths are disjoint, simple, rectifiable, and proper relative to the inner ideal boundary; different `r` give disjoint semicircular leaves. Their homotopy classes stay on the **short positive gap** side of the inner boundary. The minimal connected marked base uses `I_0,I_1,I_2,I_3`, whose combinatorial length is **four**; its two minimal end intervals are `I_0,I_3`, and its crest contains the nonempty intermediate `I_1,I_2` block. Neither orientation around the inner circle can connect these end atoms through a marked multi-interval of length at most two: the opposite side also has two intervening atoms `I_4,I_5`. Thus **every leaf meets the actual Appendix A.1 admissibility condition**; the family is an *active, proper-base marked Wave* on the actual `V'` with this marking, not the formerly retracted two-atom Wave counterexample.

Let `S_+={gamma_r:r_0<r<R}`. There is an analogous `S_-` around the other gap centered at `3pi/2`; the two half-annular regions are disjoint. Their leaves belong to distinct simple annular winding classes and have disjoint physical supports.

### Theorem 2.1 (exact conformal width, not a proxy)

For either valid Wave packet,

\[
\boxed{\mathcal W(S_+)=\mathcal W(S_-)=\frac1\pi\log\frac R{r_0}
=\frac1\pi\log\frac h{2\arcsin\epsilon}
=\frac1\pi\log\frac h{d_\epsilon}.}\tag{2.3}
\]

The union has width exactly `2*W(S_+)`.

**Proof.** Conformal invariance allows us to work in the flat source cylinder. In polar coordinates about `(t=0,theta=pi/2)`, each leaf is `r=constant`, `0<s<pi`, with Euclidean arclength `ds_eucl=r ds`. If a Borel metric `rho` is admissible for these leaves then `int_0^pi rho(r,s) r ds >=1` for a.e. `r`. Cauchy–Schwarz implies `int_0^pi rho(r,s)^2 r ds >=1/(pi r)`. Integrating over `r_0<r<R` gives the lower bound `W>=pi^{-1}log(R/r_0)`. It is attained by the explicit metric `rho=1/(pi r)` on that half-annular sector, zero elsewhere: every leaf has rho-length exactly 1, and its energy is exactly the right-hand side. The same holds around the opposite gap; since the two corresponding sectors are disjoint, the two independent admissibility conditions add exactly, yielding the width of the union. Extension by zero outside the collar shows that the same widths are measured in the **full actual source surface** `V'`, not only in a freely chosen computational subdomain. `□`

### Theorem 2.2 (actual canonical WAD has a nonzero, explicitly bounded channel)

Let `alpha_+` be the admissible marked homotopy class represented by `S_+`, on `(V',I)` with marking (2.1). Then its **actual canonical WAD on this marked Riemann surface** obeys

\[
\boxed{W_{\rm can}^{V',I}(\alpha_+)\ \ge\ 
\left[\frac1\pi\log\frac h{d_\epsilon}-2\right]_+,\qquad [x]_+=\max(x,0).}\tag{2.4}
\]

The same inequality holds for the opposite packet `alpha_-`.

**Proof.** The family in (2.2) is a genuine marked lamination, so its induced one-class WAD `W_{S_+}` is *valid* (Appendix A.2.2). The canonical maximality inequality of Appendix A.2.3 is `W_{S_+}(alpha_+) <= W_can(alpha_+)+2`. Insert the **exact** computed width (2.3), and use nonnegativity of canonical WAD weights. This includes the source's two-unit buffer correction rather than ignoring it. `□`

Consequently, holding `h>0` fixed and taking `epsilon↓0`, the specific valid Wave width and its canonical channel **diverge** at least logarithmically:

\[
\mathcal W(S_+) =\frac1\pi\log(1/\epsilon)+O_h(1),\qquad
W_{\rm can}(\alpha_+)\ge\frac1\pi\log(1/\epsilon)-O_h(1).
\tag{2.5}
\]

This is a direct source-valid Wave/WAD calibration for this selected marking on a true holomorphic quadratic-like pair. It does **not** show that the original KKL prime-primitive marked carrier has this end geometry or that a proof-used critical Wave contains the packet.

## 3. A sharp whole-condenser counterpart: an alternative to shrinking-access analysis

Let `W_h(ell)` denote the **full free-outer-boundary** condenser width between `B_X` and `tau B_X`, as in the merged PR #46 and PR #49. It contains both explicit packets. Since the packets occupy disjoint half-annular sectors, Theorem 2.1 gives

\[
\boxed{W_h(\ell_\epsilon)\ge\frac2\pi\log\frac h{d_\epsilon}}
\quad\text{whenever }d_\epsilon<h.\tag{3.1}
\]

For the converse asymptotic, prescribe on the source **inner** boundary the voltage trace `g_d` equal to 1 on `B_X`, 0 on `tau B_X`, and linear across each intervening gap of length `d`. Let its harmonic extension have **free outer boundary**, not pinned outer voltage. Its nonzero Fourier coefficients are

\[
\hat g_d(n)=\frac{\sin(n\pi/2)}{\pi n}\,\operatorname{sinc}(nd/2),\qquad n\ne0
\tag{3.2}
\]

(up to an immaterial sign convention), with `hat g_d(0)=1/2`. Thus the energy of this admissible competitor is

\[
\boxed{E_h(g_d)=\frac4\pi\sum_{\substack{n\ge1\\n\ \rm odd}}
 \frac{\tanh(nh)}n\operatorname{sinc}^2(nd/2).}\tag{3.3}
\]

For each fixed `h>0`, the difference between `tanh(nh)` and 1 contributes a bounded sum. Splitting the remaining harmonic series at `n≈1/d`, using `sinc^2(x)=1+O(x^2)` for `x≤1` and `|sinc(x)|≤1/|x|` for `x≥1`, gives

\[
E_h(g_d)=\frac2\pi\log(1/d)+O_h(1).\tag{3.4}
\]

Combined with (3.1), this proves the **sharp opposite extreme** of the previous contact-resistance theorem:

\[
\boxed{\lim_{\epsilon\downarrow0}
\frac{W_h(\ell_\epsilon)}{\log(1/\epsilon)}=\frac2\pi
\qquad\text{for every fixed }0<h\le1/4.}\tag{3.5}
\]

At fixed small `h`, the full condenser width **blows up** when its two electrode blocks almost reach half-circles, contrasting with the `ell->0` regime of PR #49 where it vanishes. Equation (2.3) independently proves that a full half of this logarithmic blow-up is carried by two explicitly marked, disjoint **Wave leaves**, not inferred through a speculative WAD-full-condenser inequality.

## 4. The exact dual exponential: a genuinely holomorphic high-width family

Fix `C>0`. For `0<h<=1/4`, define

\[
 d(h)=h e^{-C/h},\quad \epsilon(h)=\sin(d(h)/2),\quad
 c(h)=-1-\epsilon(h),\quad
 \ell(h)=\pi-d(h).
\tag{4.1}
\]

This is an explicit real-analytic family of genuine quadratic maps `P_{c(h)}` and their invariant slit carriers, each with *proper* source attachment `ell(h)<pi`, and an ordinary conformal collar of height `h`. But for the actual marked semicircle Wave `S_+(h)`, the exact formula (2.3) gives

\[
\boxed{\mathcal W(S_+(h))=\frac{C}{\pi h}\ \xrightarrow[h\to0]{}\infty,\qquad
W_{\rm can}(\alpha_+(h))\ge\frac{C}{\pi h}-2.}\tag{4.2}
\]

The source attached block still maps to a **proper** target arc for every `h>0`; at the parameter limit `epsilon=0` its half-circle closed image saturates. This is an exact “**wide Wave just before saturation**” realization from one actual holomorphic covering/immersion geometry, not a polynomial-fit or a synthetic transition automaton.

Compare with PR #49's *other* exponential boundary layer: when `ell(h)=e^{-C/h}` (tiny attachment), its full condenser width is of order `h`; here when the **gap** is `d(h)=h e^{-C/h}` (nearly half-circle attachment), the bona fide Wave width is of order `h^{-1}`. These are different and noninterchangeable geometric mechanisms.

## 5. Precise trust boundary and next native theorem

1. **Not KKL's original prime-primitive stage.** `c=-1-epsilon` for small positive `epsilon` lies in the attracting period-two regime; the carrier `T=[c,b]` is invariant but not claimed to be the small-Julia Hubbard tree of a prime-primitive, periodically repelling renormalization. The marking (2.1) is a deliberately refined legitimate Appendix A ideal marking, **not** the source's original vertex-side marking at such a stage.
2. **Source-compatible Wave, not guaranteed native critical Wave.** This theorem establishes an actual *marked Wave* and its canonical WAD lower bound on the real holomorphic source surface `V'`. A KKL §6 critical visit additionally requires the **original** marking, a short crest, source-defined closed pullback and return, and canonical WAD/Wave transport across the immersion. None is asserted.
3. **No uniform all-stage consequence.** The new bound is useful when there is an actual pair of nearly touching, deck-translated *complete* attachment arcs and a compatible marked homotopy packet. In the native non-LC class, individual attached boundaries can have more complicated structure, and the end intervals need not agree with original marking atoms. A sheet count or planar root alone does not guarantee this geometry.
4. **Endpoint caution:** at `epsilon=0` the attached arc spans exactly `pi`; its **closed** covering image is the entire target circle and the two electrodes cease to be disjoint. Neither the condenser nor the admissible opposed-electrode Wave may be extrapolated through this collision by inserting a fictitious positive gap.
5. **No conclusion about MLC.** The full native Wave amplification, Issue #40, H1–H4, universal protected-tower closure, and global MLC remain open in this archive.

**Next source-defined acceptance test:** On one *actual prime-primitive* KKL stage, use Proposition 6.5 to identify the complete source Carathéodory attachment block and both deck-side accesses. If it spans `>=pi`, prove real closed-input saturation. If it is shorter and a **genuine original marked packet with a protected two-gap sector** exists, transfer the semicircle argument via a conformal collar and apply the source's canonical WAD maximality to produce a positive original-marking horizontal Wave witness; otherwise write down the exact gap/crosscut or marking obstruction. The missing comparison becomes a *specific geometric packet-existence/marking condition*, not a blanket assertion that arbitrary full condensers dominate Wave widths.

## Reproducibility

`python research/independent_audits/verify_near_saturation_wave.py --check-manifest` performs exact rational checks of the full holomorphic Joukowski identity across five parameters and multiple source coordinates, independent angular-gap and marking checks, exact extremal-metric deformation tests, a Fourier-series upper versus **two disjoint packet** lower bound, and the dual-exponential formula. Its deterministic JSON manifest is checked byte-for-byte. The Python program does **not** prove PDE regularity, original KKL-vertex marking compatibility, or the native analytical proof; the exact semicircle extremal-width proof is written above.

The result's geometric and harmonic tools are classical; KKL's definitions/maximality theorem remain theirs. OpenAI GPT-6 assisted deriving and verifying this archive-specific holomorphic example. No specialist peer review or independent priority claim has yet been established.
