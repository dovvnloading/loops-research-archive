# Real primitive-tip family: canonical marked-Wave gain versus serial loss

**Status — 2026-11-16.** **Proved (conditional on the previously declared physical ideal-marking identification M):** an exact source/target definition, the *loss-or-equality* inequality for every **leafwise two-child** Wave and for its pairable-parent supremum, equality for the specified round witness, and explicit **two-sided certified but sign-indefinite** enclosures for the *unrestricted* canonical marked extremal defect. **OPEN:** the sign of that unrestricted defect for **every** period, the attainment of the three independent suprema, and strictness for the pairable optimum. **Numerical-only:** approximate putative optimizers or conjectural signs; *none is used here*. `verify.py` is read-only and certifies only rational/interval arithmetic and finite marking incidence, **not** complex-dynamical identification or conformal-geometric theorems.

Primary sources: [KKL, arXiv:2606.27272v1, Appendix A.1, A.2.1–A.2.3, A.3.1–A.3.2](https://arxiv.org/html/2606.27272v1); merged [family theorem](../../tip_family_theorem/THEOREM.md) and [hostile ledger](../../tip_family_theorem/AUDIT.md); [canonical slit-width audit](../real_primitive_tip_family_canonical_width_20261116/NOTE.md); [proved sandwich](../real_primitive_tip_family_canonical_width_sandwich_20261116/NOTE.md) and its [read-only interval verifier](../real_primitive_tip_family_canonical_width_sandwich_20261116/verify.py). No previous source file has been edited.

## 1. Three meanings of "canonical" and the actual marked surfaces

For every integer `p >= 3` choose **only** the distinguished root `c_p` of `P_p(c)=x_{6p}(c)+x_{3p}(c)=0` in the piecewise chart of THEOREM.md; `x_j=f_{c_p}^j(0)` is the **physical** iterate, `f_c(z)=z^2+c`, and `G_p=f_{c_p}^p`. Do not replace `x_{jp}` with `x_j`. Put

- `U_p=D(0,R_p)`, `R_3=1/4`, `R_p=2^-p` for `p>=4`; `V_p` is the central degree-two component of `G_p^{-1}(U_p)`;
- `T_p=[x_{2p},x_p]`, `T'_p=[-x_p,x_p]`; `Omega_p=U_p\T_p` and `Omega'_p=V_p\T'_p`;
- `alpha_p` is the dividing real fixed point of `G_p`, with `x_{2p}<x_{5p}<x_{3p}<0<x_{6p}<alpha_p<x_{4p}<x_p` and `-x_p<-x_{4p}<x_{2p}<x_{5p}<-alpha_p<x_{3p}<x_{6p}<alpha_p<-x_{5p}<-x_{2p}<x_{4p}<x_p`.

The target **inner** slit prime-end circle has ten atoms `I_0,...,I_9`, the source twenty `S_0,...,S_19`; each outer ideal circle has **one whole-component** atom, not another ten or twenty. Retain the **identification M** of the sandwich NOTE `1: `I_9,I_1` are opposite accesses to `(x_{5p},x_{3p})`, `I_0` is the left-tip terminal atom, and the twenty source sides have the physical cut order just specified. This identification imports the cited complex-analytic/prime-end argument, not a conclusion of real interval arithmetic; all claims about *physical* KKL Waves below depend on it. The statements are unconditional for these explicitly constructed marked slits.

The **unrestricted extremal marked parent width** (the notation of the merged sandwich) is

\[
P_p=W_p^*:=\sup_{\mathcal S} W(\mathcal S),\qquad
\operatorname{base}(\mathcal S)=(I_9,I_0,I_1),\qquad
I_0\subset\operatorname{crest}(\mathcal S).
\tag{1.1}
\]

The supremum ranges over **A.1-admissible Waves** in `Omega_p`. The endpoints are in `I_9,I_1`, their homotopy class is subordinate to the **left** three-atom arc, and a path subordinate to at most two atoms is *forbidden*. This is a supremum, **not a claimed maximizing lamination**.

The two **source child types**, in the *source* marking, are

\[
B_+=(S_1,S_2,S_3),\quad \text{crest }S_2,\qquad
B_-=(S_{17},S_{18},S_{19}),\quad \text{crest }S_{18}.
\tag{1.2}
\]

Let `C_p^+`, `C_p^-` be the **independent** suprema of widths of A.1-admissible source Waves on `Omega'_p` with precisely these bases and crests. This definition permits candidates not simultaneously obtained by restricting one parent; this independent optimization is essential to the defect question. Complex conjugation identifies the source domain and the two marked child classes, so

\[
C_p^+=C_p^-=:C_p>0,\qquad
D_p:=C_p^{+\,-1}+C_p^{-\,-1}-P_p^{-1}=2/C_p-1/P_p.
\tag{1.3}
\]

**Naming warning.** `P_p` and `C_p` are *unbuffered supremal marked A.1 Wave widths*, called "canonical maximal marked" in the earlier audits. They are **not** KKL's literally **canonical WAD/lamination** of Appendix A.2.3: there KKL removes square buffers and assigns an arc weight `max(0, full lifted quadrilateral width - 2)`. In fact the certified upper envelopes in ``4–5 below are `<2` for all three of these particular arcs. Thus their **A.2.3 canonical buffered arc weights vanish**. There is no positive inverse-weight harmonic question for those literal buffered canonical arcs. The well-defined positive defect (1.3) is the distinct, previously posed **supremal A.1-Wave** question. Do not conflate an unbuffered full-path envelope, a maximal marked A.1 Wave, and the buffered canonical WAD.

## 2. A.3.2 restriction is not A.3.1 covering pushforward

The source ideal interval pullbacks under the **identity immersion** `iota:Omega'_p -> Omega_p` are the following ten *consecutive* source blocks:

| Target | `iota^* I_j`, ordered source atoms |
|---|---|
| `I_0` | `(S_18,S_19,S_0,S_1,S_2)` |
| `I_1` | `(S_3,S_4)` |
| `I_2` | `(S_5)` |
| `I_3` | `(S_6)` |
| `I_4` | `(S_7,S_8,S_9)` |
| `I_5` | `(S_10)` |
| `I_6` | `(S_11,S_12,S_13)` |
| `I_7` | `(S_14)` |
| `I_8` | `(S_15)` |
| `I_9` | `(S_16,S_17)` |

The attached source interval is `T'_p\T_p=[-x_p,x_{2p})`; `S_19,S_0,S_1` lie **inside** the non-fully-proper block `iota^*I_0`, with the attached sides mapping to **target interior**, not pointwise to the target ideal circle. Proper restrictions are the components of `gamma∩Omega'_p` with proper source ideal endpoints; discard the short (`<=2` atom) and single-`iota^*I_j`-block components according to A.3.2. No arbitrary parent is promised two survivors by this rule.

For the actual round **crossing** curves of `3, the upper restriction has endpoints `(S_3,S_1)` (crest `S_2`) and the lower `(S_19,S_17)` (crest `S_18`). Both have **inclusive source shortest span 3** and endpoints in **different immersion blocks**, so both survive. The **avoiding** comparison `(S_3,S_17)` has source short span **7** and is not a two-child crossing. These paths are proper **source** paths even though the immersion is not proper on every attached side. They need no invented pointwise map from attachment sides into target ideal endpoints.

Separately, the **unbranched degree-two covering** `f_* = (G_p)_*` satisfies `f_*(S_j)=I_(j mod 10)`; it sends crossing pairs to `(I_3,I_1)` and `(I_9,I_7)` (target inclusive spans **3,3**), and the avoiding pair to `(I_3,I_7)` (span **5**). The cover-pushed child *bases* are `(I_1,I_2,I_3)` and `(I_7,I_8,I_9)`, **not** the source A.3.2 bases; covering does not define the surviving restrictions. All assertions above concern the specified proper path/homotopy classes, not every pointwise curve or all future iterates.

## 3. The general serial inequality, its direction, and what strictness needs

We use `W(Gamma)=inf_{rho: integral_gamma rho ds>=1} integral rho^2 dA`, KKL's extremal **width** (not extremal length). For path families living in *disjoint parallel* subdomains with independent endpoint constraints, admissible density minimization decouples and `W(Gamma_1 union Gamma_2)=W(Gamma_1)+W(Gamma_2)`. **Parallel widths add**. For a *series* family in which **every parent path** contains one path from each of two child families with disjoint embedded interiors, choose nearly extremal densities `rho_+`, `rho_-` on the two children. For nonnegative `t_++t_-=1`, the density `t_+rho_+ + t_-rho_-` (extended by zero) is admissible for the parent and its area is at most `t_+^2 W_+ + t_-^2 W_-` in the limit. Minimizing gives

\[
W(\mathcal S)\le W_+\oplus W_-:=\frac{W_+W_-}{W_++W_-},\qquad
\boxed{W_+^{-1}+W_-^{-1}-W(\mathcal S)^{-1}\le0}.
\tag{3.1}
\]

This is precisely the **loss-or-equality** direction of KKL **Lemma A.11** when its leafwise-survival and injectivity hypotheses hold. It is **not** a gain inequality, and not a theorem for an A.1 parent with one surviving restriction. For a positive-width independent child pair `C_p^+,C_p^-`, take the supremum over **pairable parents** (those for which every leaf has both prescribed proper children) to get

\[
P_{p,\mathrm{pair}}^*\le C_p^+\oplus C_p^-=C_p/2,
\qquad 2/C_p-1/P_{p,\mathrm{pair}}^*\le0.
\tag{3.2}
\]

`P_{p,pair}^* <= P_p` holds, but **equality of these two suprema is OPEN**. The optional `W_{p,2}^*` in the sandwich can be read as `P_{p,pair}^*` only with this explicit **every-leaf** quantifier. The inequality for the unrestricted `P_p` is not supplied by A.11. Equivalently,

\[
D_p>0\iff P_p>C_p/2,\quad D_p=0\iff P_p=C_p/2,\quad D_p<0\iff P_p<C_p/2.
\tag{3.3}
\]

Thus proving `P_p=P_{p,pair}^*` would **rule out strict gain**, but neither that equality nor the opposite comparison is known here. A.11 also does **not** make (3.1) strict. Rectangles of horizontal width `L` and serial heights `h_+,h_-` give exact equality `Wparent=L/(h_++h_-)`, `W_±=L/h_±`. Adding a **third** positive serial slab to the parent, with the same two specified restrictions, gives strict **loss** `D=-h_extra/L`. Both examples are purely extremal-length facts, not claims about the true tip-family optimizer.

The actual round witness supplies **equality in this family**: set `m_p=(x_{2p}+x_{5p})/2`, `r_0=(x_{5p}-x_{2p})/2`, `r_1=min(-alpha_p-m_p,x_{4p}+m_p)`. The entire interval `r_0<s<r_1` gives a proper parent leaf `m_p+s exp(it)` cut into two source semicircular leaves. The certified whole-disk gate and (2.1) of the sandwich ensure all are proper; logarithmic rectangles have widths

\[
L_p=\log(r_1/r_0),\quad W_p^{rad}=L_p/(2\pi),\quad
W_{p,+}^{rad}=W_{p,-}^{rad}=L_p/\pi=2W_p^{rad};\quad D_p^{rad}=0.
\tag{3.4}
\]

The last equality is **only for those three paired log-rectangle laminations**, not for (1.3). Physical KKL interpretation still uses the A.2.1 conformal-width identification from the earlier proof.

## 4. Independent upper envelopes for the two source children

**New geometric upper inclusion.** Since `Omega'_p` is contained in the plane-slit complement `C\[-x_p,x_p]`, use the Joukowski map `J(zeta)=x_p(zeta+zeta^-1)/2` and its logarithmic cover `zeta=exp(s+it)`, `s>0`. The endpoints of the **upper child** lie on the same (upper) slit side: its left interval is `(-x_{4p},x_{2p})` and its right interval `(x_{5p},-alpha_p)`. Reflect `t` to `pi-t`; the lifted boundary intervals have the ordered endpoints

\[
a=\arccos(x_{4p}/x_p),\quad
b=\arccos(-x_{2p}/x_p),\quad
c=\arccos(-x_{5p}/x_p),\quad
d=\arccos(\alpha_p/x_p),\qquad 0<a<b<c<d<\pi.
\tag{4.1}
\]

All A.1 source child waves with precisely base `B_+` and crest `S_2` lift to paths joining **these** two intervals. Wiggling, noncircular paths and every potential source optimizer are included. The same argument in the conjugate lower half-plane covers `B_-`. The full lifted half-plane quadrilateral has the standard Schwarz–Christoffel width

\[
E_p=\frac{K(k_p)}{K(\sqrt{1-k_p^2})},\qquad
k_p^2=\frac{(b-a)(d-c)}{(c-a)(d-b)},\qquad K(k)=\int_0^{\pi/2}\frac{dt}{\sqrt{1-k^2\sin^2t}}.
\tag{4.2}
\]

To compare **physical** and lifted widths, periodize the square of a finite-area density on the chosen lift: `rho(pi z)^2=sum_n tilde_rho(z+2*pi*i*n)^2`. Tonelli preserves the area, and the projected density is no smaller along the selected lifted path; thus its path length remains admissible. This gives the **upper** bound, without incorrectly asserting equality under a covering,

\[
2W_p^{rad}\le C_p^+=C_p^-\le E_p,\qquad
W_p^{rad}\le P_p\le Q_p\le Q(L_{+,p}).
\tag{4.3}
\]

Here `Q(L_+)` is the **parent** certified full lifted-path upper envelope from the sandwich note `5. Neither `E_p` nor `Q(L_+)` is asserted to be attained by an admissible Wave. The *competitor* lower bounds in (4.3) are explicit round semicircle and full-circle A.1 families. In particular, calling the upper all-path family a "child competitor Wave" would be a type error.

For the **uniform** large-period estimate, enlarge those source endpoint intervals to `(-x_p,x_{2p})` and `(x_{5p},x_{3p})` respectively. Put

\[
a_0=0,\quad b_0=\arccos(-x_{2p}/x_p),\quad
c_0=\arccos(-x_{5p}/x_p),\quad
d_0=\arccos(-x_{3p}/x_p).
\tag{4.4}
\]

The same quadrilateral formula gives `E_p <= E_p^coarse`; enlarging the electrodes is an upper, **not lower**, comparison. For `p>=13` apply the certified all-period normalized-orbit error box from the sandwich note equation (5.3): with `q=4^-p`, `xi_j=(-A_p)x_{jp}` and the limiting normalized orbit `u_j`,

\[
|\xi_1+u_1|\le15246q,\quad
|\xi_j+u_j|\le\left(30\cdot15246+\frac{88(4^j-1)}3\right)q\quad(j=2,3,5).
\tag{4.5}
\]

`-A_p>0` is a **positive affine** normalization; the four ratios in (4.4) are unchanged. The `p=13` box contains every `p>=13` box, and the *rational outward 2^-512* calculation of (4.2)/(4.4) gives

\[
\boxed{E_p\le E_p^{coarse}<5/4=1.25\quad\text{for all }p\ge13.}
\tag{4.6}
\]

This bound uses **no** unproved all-period control of the dividing point `alpha_p` or `x_{4p}`: those two cuts were deliberately enlarged away. The strictly positive endpoint gaps and interval monotonicity are explicitly tested.

## 5. Certified two-sided defect bounds (and no fabricated sign)

For any certified strict parent endpoints `l_p<W_p^{rad}` and `P_p<u_p`, and any upper child envelope `C_p<e_p`, equations (4.3) give, entirely by reversing **positive** denominators,

\[
\boxed{\frac2{e_p}-\frac1{l_p}<D_p<\frac1{l_p}-\frac1{u_p}.}
\tag{5.1}
\]

The **lower** side uses an explicit parent *lower* competitor and the two child *upper* full-path bounds. The **upper** side uses the two explicit child *lower* competitors and the parent *upper* full-path bound. There is **no** monotonicity-based justification for swapping any of these four directions. The finite `l_p,u_p` come from the exactly certified strict `1e-7` sandwich rows; `e_p` is (4.2), recomputed in `verify.py` using the pinned dyadic root brackets, a separately interval-isolated `alpha_p`, elementary inverse-trigonometric series and rigorous elliptic series remainders.

| `p` | **Certified strict enclosure** for unrestricted `D_p` | Sign |
|---:|---:|:--|
| 3 | `-1.919 < D_3 < 2.298` | **OPEN** |
| 4 | `-1.838 < D_4 < 2.225` | **OPEN** |
| 5 | `-1.820 < D_5 < 2.379` | **OPEN** |
| 6 | `-1.816 < D_6 < 2.449` | **OPEN** |
| 7 | `-1.815 < D_7 < 2.484` | **OPEN** |
| 8 | `-1.814 < D_8 < 2.504` | **OPEN** |
| 9 | `-1.814 < D_9 < 2.516` | **OPEN** |
| 10 | `-1.814 < D_10 < 2.524` | **OPEN** |
| 11 | `-1.814 < D_11 < 2.529` | **OPEN** |
| 12 | `-1.814 < D_12 < 2.533` | **OPEN** |
| **every `p>=13`** | **`-2.25 < D_p < 2.57`** | **OPEN** |

The final row is **all-period**, not interpolation: the sandwich's individual strict `0.26<P_p<0.78` for `p=13,14,15,16`, its all-period `p>=17` proof (including the radial-rate boundary check at `p=17`), and (4.6) imply `0.52<C_p<1.25` for every `p>=13`. The *exact rational* inequalities

\[
-2.25<\frac2{1.25}-\frac1{0.26}<D_p
<\frac1{0.26}-\frac1{0.78}<2.57
\tag{5.2}
\]

complete the tail. In particular every interval **strictly contains zero**. Its midpoint, sign, or apparent convergence is **not** a numerical prediction for the canonical defect.

## 6. Exact remaining extremal problem and verification boundary

The unresolved question is **not** a failure to compute the harmonic ratio of the round circles (that ratio is exactly one). It is the global comparison of **independently optimized** marked conformal classes:

1. Determine the supremum `P_p` of **all** parent A.1 laminations subordinate to `I_9,I_0,I_1` in `U_p\T_p`, *without silently requiring two immersion children*, including possible near-optimizing avoiding leaves and deck/projection obstacles.
2. Determine the supremum `C_p` of A.1 source laminations with base `S_1,S_2,S_3` in `V_p\T'_p` (its conjugate has the same width), and decide whether the independently optimal source laminations are jointly realizable as proper restrictions of one parent.
3. Compare `P_p` to `C_p/2` (the **exact** sign test (3.3)). Separately decide whether `P_p=P_{p,pair}^*`; equality of those parent suprema would rule out gain by (3.2), but is **not equivalent** to `P_p=C_p/2`. Characterize any strict serial loss or excess unrestricted parent width. No finite atom table, whole-disk existence proof, coarse full-path upper envelope or KKL A.11 supplies the missing attainment/compactness/composition argument.

**Certified by `verify.py`:** separate source/target blocks and inclusive spans, physical root/cut-order interval premises for `p=3..12` (reusing the immutable upstream exact packets), both child quadrilateral angle and cross-ratio intervals, strict rational defect bounds, the `p=13` normalized box containing the tail, and strict zero-weight `<2` upper-envelope gates. All arithmetic is `Fraction` plus the prior **outward `2^-512`** routines; it reruns the prior sandwich packet **read-only** and rejects drift. **Not machine proved:** the physical ideal marking M, the homotopy-lift inclusions, the KKL Lemma A.11 application, Schwarz–Christoffel and density periodization as analytic theorems, the all-period complex dynamics imported from earlier work, or any canonical optimizer. No Monte Carlo, finite-difference, floating-point optimizer or guessed sign is relabeled as a certificate.

## 7. Hostile review checklist / disposition

- **No universal two-child assumption:** `P_p` permits A.1 avoiding paths; (3.2) is only for *leafwise paired* parents. Supremum/inverse direction checked twice.
- **Three distinct constructions:** upper and lower **immersion** restrictions, plus the independent **cover**; the nonproper attached sides are not fabricated as target ideal endpoints. The avoiding source span is **7**, not the historically erroneous 3; its covering span is **5**.
- **Not the buffered canonical WAD:** the canonical A.2.3 arc weights are zero; treating `P_p` as that quantity would make the reciprocal defect ill-defined. `Q`, `E_p` are upper **families**, not attained Waves.
- **No hidden p=12/13 seam:** exact source dyadics `3..12`, certified normalized tail from `13`, explicit `13..16` and `17` parent-rate checks. Model boxes are scaled by `-A_p>0`, never reversed.
- **No proof from decimals:** table endpoints are *strict rational* inequalities independently checked against outward intervals, not rounded mpmath outputs. CI compiles, reruns, tests adversarial changes, and checks unchanged predecessor snapshots.
- **Unresolved:** no asserted strict gain or strict loss for `D_p`; no assertion that all KKL actual canonical arcs have positive weight; no all-period optimizer/continuity inference. A successful workflow is an arithmetic regression gate, not an analytic peer review.

**Disposition:** the certified result is a **two-sided sign-indefinite enclosure** plus a genuine **one-sided loss theorem for pairable laminations**. Any claim that the unrestricted canonical maximal Wave strictly amplifies is **OPEN**, not established by the round equality or the present estimates.
