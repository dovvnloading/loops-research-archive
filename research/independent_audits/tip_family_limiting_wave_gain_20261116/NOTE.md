# Limiting primitive-tip Wave gain: a bounded-quadrilateral certificate

**2026-11-16 — RESULT: STRICT POSITIVE UNBUFFERED INDEPENDENTLY OPTIMIZED DEFECT IN THE LIMITING MARKED MODEL, AND UNIFORMLY FOR EVERY PHYSICAL PERIOD `p >= 13`.** Subject to the same **physical ideal-prime-end identification M** explicitly isolated in the merged sandwich and gain audits, the new bounded parent competitor proves

\[
\boxed{D_\infty>0.696>0,\qquad
       D_p=2/C_p-1/P_p>11/126>0\quad(p\ge13).}
\]

Here `P` and `C` are **unbuffered suprema over A.1-marked Waves**, as defined by the prior [canonical gain audit](../tip_family_canonical_wave_gain_20261116/NOTE.md). This is **not** strict gain for a single leafwise-pairable parent, nor for KKL's *buffered canonical WAD arc weights*. No optimizer is asserted. Our analysis proves the sign without claiming convergence of the unrestricted finite-period suprema to their limiting-domain counterparts.

**Arithmetic:** [verify.py](verify.py) re-executes the previously merged certified gain/sandwich verifiers, uses integer outward `2^-512` intervals with rational Taylor/elliptic remainders, and independently checks the new limiting quadrilaterals and the *entire* all-period parent semidisk gate. [test_verify.py](test_verify.py) probes reversed cuts, invalid radii and reciprocal signs. **Analytic, not machine-proved:** Schwarz–Christoffel rectangle foliations, conformal invariance, the geometric admissibility proof below, and M. The printed rational intervals are certificates **of their arithmetic premises**, not of these analytic theorems. No floating-point optimizer or numerical-only datum enters any proof.

## 1. Exactly which limiting maps, domains, cuts and marks?

Let `f_c(z)=z^2+c`; `G_p=f_{c_p}^p` with the **distinguished** period-`p` tip root and chart of [the all-period audit](../real_primitive_tip_family_all_p_20261116/NOTE.md), not an arbitrary root of `x_{6p}+x_{3p}=0`. Write

\[
G_p(z)=x_p+A_pz^2+E_p(z),\quad A_p<0,\quad
\tau_p=A_px_p,\quad q_p=4^{-p}.
\]
The analytic normalization is
\[
w=A_pz,\qquad h_p(w)=A_pG_p(w/A_p)
  =w^2+\tau_p+e_p(w).
\tag{1}
\]
It is **orientation-preserving as a complex map**, but its negative real multiplier **reverses real cut order**. Its limit is `g(w)=w^2+tau_*`, where `tau_*` is the unique root in `(-1795/1000,-1785/1000)` of
\[
u_0=0,\quad u_{j+1}=u_j^2+\tau_*,\quad u_6+u_3=0.
\tag{2}
\]
The root is certified by the prior exact interval isolation and derivative signs. For geometrically **positive real scale**, use instead
\[
\lambda_p=-A_p>0,\quad \xi=\lambda_p z=-w,\qquad
\widehat G_p(\xi)=\lambda_pG_p(\xi/\lambda_p)=-h_p(-\xi)
\longrightarrow \widehat G_\infty(\xi)=-\xi^2-\tau_*.
\tag{3}
\]
Thus the two conventions are **not the same renormalized formula**. Put
\[
X_j=-u_j,\qquad
\alpha_\infty=-\frac{1-\sqrt{1-4\tau_*}}2.
\]
In the `xi` chart the normalized *target* and *source* marked slit domains are, precisely,
\[
\Omega_\infty=\mathbb C\setminus[X_2,X_1],
\qquad
\Omega'_\infty=\mathbb C\setminus[-X_1,X_1].
\tag{4}
\]
The normalized map `-xi^2-tau_*` sends the entire source slit onto the target slit: `[-X_1,X_1] -> [X_2,X_1]`. The source slit is strictly longer on the left. The end `infinity` is an ideal **single outer component**, not ten/twenty replicated atoms.

**Marked electrodes, including both source child types.** On the target *opposite sides* of the real subinterval `(X_5,X_3)`, the two electrodes are `I_9,I_1`; the included left-tip terminal atom `I_0` is the crest. The source upper child has electrodes on the same upper slit side `(-X_4,X_2)` and `(X_5,-alpha_infinity)`, with base `(S_1,S_2,S_3)` and crest `S_2`. Its conjugate is the lower child with base `(S_17,S_18,S_19)` and crest `S_18`. All intervals are **open at atom junctions**. As before, the parent-width supremum `P_infinity` and the two independent child suprema `C_infinity^+,C_infinity^-` are taken over A.1 Waves in (4), not over arbitrary projected full-lift paths. Conjugation proves `C_infinity^+=C_infinity^-=C_infinity`.

The finite *positive-scale* cuts `X_{j,p}=lambda_p*x_{jp}` satisfy the all-period proven boxes
\[
|X_{1,p}+u_1|\le15246q_p,\qquad
|X_{j,p}+u_j|\le
 \left(30\cdot15246+\frac{88(4^j-1)}3\right)q_p,\quad j=2,3,5.
\tag{5}
\]
They are **not** bounds on `x_j=f^{j}(0)` for `j=1,2,3,5`: the physical cuts are `x_{jp}=f^{jp}(0)`! In the finite normalized target, `Omega_p=D(0,lambda_p R_p)\setminus[X_{2,p},X_{1,p}]` with `R_p=2^{-p}` for `p>=13`, and `lambda_p R_p>(3/20)2^p\to\infty`. On each fixed `xi`-disk the nonlinear recurrence from the all-period audit, `|E_p(z)|\le t_p^2/128` when `t_p=4^p|z|^2\le1`, gives `lambda_p|E_p(xi/lambda_p)|=O_M(q_p)` for `|xi|<=M`, as `lambda_p q_p\in(3/20,17/100)`. Hence (3) holds locally uniformly on every compact disk, not only on `|w|<=2.1`. The image of each fixed disk is bounded and therefore lies in the expanding target disk for large `p`; since it contains the central critical point, it belongs to the rescaled **central component** `lambda_p V_p`. This proves compact exhaustion of the source slit domain as well. The marked cut endpoints converge by (5) and the corresponding fixed-point estimate from the all-period audit. **We do not infer convergence of suprema from domain exhaustion without a separate stability theorem.**

The maps `iota^*` and `f_*` remain distinct: immersion blocks `I_0 -> (S_18,S_19,S_0,S_1,S_2)`, `I_1 ->(S_3,S_4)`, `I_9 ->(S_16,S_17)` are *not* the covering `f_*(S_j)=I_{j mod 10}`. The upper and lower source bases stated above are independent source A.1 classes. In particular no assertion that every unrestricted parent has **both** restrictions is made.

## 2. Conformal charts and the two explicit admissible foliations

Use the physical-order normalized target midpoint and radius
\[
m=(X_2+X_1)/2,\qquad r=(X_1-X_2)/2>0,
\]
and the Joukowski chart
\[
\mathcal J_P(\zeta)=m+\frac r2(\zeta+\zeta^{-1}),\quad
\zeta=-e^{z},\quad z=s+it,\quad s>0.
\tag{6}
\]
In this chart `z=0` is the **left** target-slit tip. The left-tip homotopy lift has electrode arcs
\[
t\in(-b,-a)\quad\text{and}\quad t\in(a,b),\quad
a=\arccos((m-X_5)/r),\quad b=\arccos((m-X_3)/r),
\quad 0<a<b<\pi.
\tag{7}
\]
These are **opposite accesses** to the same real segment, not two electrodes on the same side.

**General foliation lemma used here (ordinary conformal geometry).**
For a simply connected Jordan quadrilateral `Q` with two disjoint open boundary electrodes `E_-,E_+` and the complementary boundary arcs, a conformal map to a Euclidean rectangle with `E_-,E_+` as the opposite vertical sides pulls back the **open family of horizontal straight segments** to disjoint simple, proper electrode-to-electrode arcs. Its extremal width equals that of *all* electrode-connecting paths in `Q`. Indeed Cauchy–Schwarz along horizontal segments gives the lower area bound `height/width`, and the constant density `1/width` is admissible for every crossing path by horizontal displacement. Corners and isolated exceptional trajectories have zero transversal measure; retaining the open horizontal foliation does not change this width. If the whole quadrilateral injects into the ambient marked slit and every arc is homotopic to the specified crest collar, this foliation is an **A.1 Wave**, not merely an upper all-path comparison.

**Bounded parent competitor, valid for finite `p`.** Inside `Re z>0` take the *right semidisk*
\[
H_R=\{s>0,\ s^2+t^2<R^2\},\qquad R=5/2<\pi.
\tag{8}
\]
Every electrode from (7) is inside its diameter since `b<R`. The elementary conformal bijection
\[
F_R(z)=\frac{2Rz}{R^2-z^2}:H_R\longrightarrow\{\Re \eta>0\}
\]
maps the diameter boundary point `it` to `i B_R(t)`, with
\[
B_R(t)=\frac{2Rt}{R^2+t^2},\quad
A_R=B_R(a),\quad B_R=B_R(b),\quad
k_R=\frac{B_R-A_R}{B_R+A_R}.
\]
The four ordered half-plane electrodes are `-B_R,-A_R,A_R,B_R`. Schwarz–Christoffel gives the **exact width of this explicitly admissible Wave**:
\[
\boxed{W_P^{(R)}=\frac{K(k_R)}{K(\sqrt{1-k_R^2})}},
\qquad K(k)=\int_0^{\pi/2}\frac{d\theta}
 {\sqrt{1-k^2\sin^2\theta}}.
\tag{9}
\]
It is **not** asserted to be the *optimal* marked parent. Its full horizontal rectangle foliation stays in `H_R`, not an arbitrary full half-plane lift. Since `|t|<R<\pi`, the exponential is injective modulo the `2pi i` deck group, and Joukowski is injective outside the unit disk. Thus *all leaves* project as simple disjoint arcs. The simply connected `H_R` gives their homotopy to the `s=0` subarc across `t=0`, hence exactly the left-tip `I_9,I_0,I_1` crest and no forbidden one- or two-atom homotopy class. This establishes
\[
P_p\ge W_{P,p}^{(R)}\quad\text{whenever the entire image }\mathcal J_P(-e^{H_R})
\text{ lies in the target disk.}
\tag{10}
\]
The proof concerns the complete rectangle foliation, not selected semicircles or a sampled curve.

**Even better limiting-domain parent competitor.** For the limiting plane slit, replace (8) by `H_pi={s>0, |t|<pi}`. The conformal map `sinh(z/2)` carries `H_pi` onto the right half-plane and maps the diameter electrodes to `±sin(a/2),±sin(b/2)`. Exactly the same injectivity/crest proof gives
\[
P_\infty\ge P_-:=
\frac{K(k_-)}{K(\sqrt{1-k_-^2})},\quad
k_-={\sin(b/2)-\sin(a/2)\over\sin(b/2)+\sin(a/2)}.
\tag{11}
\]
The half-angle sines are certified **algebraically** via `sin(t/2)=sqrt((1-cos t)/2)`.

**Limiting source children.** The source Joukowski chart is
\[
\mathcal J_C(\zeta)=\frac{X_1}{2}(\zeta+\zeta^{-1}),\quad
\zeta=e^{s+it},\quad s>0,\quad 0<t<\pi.
\tag{12}
\]
The **upper side** electrodes have angles `(pi-d,pi-c)` and `(pi-b_c,pi-a_c)`, where
\[
a_c=\arccos(X_4/X_1),\quad
b_c=\arccos(-X_2/X_1),\quad
c_c=\arccos(-X_5/X_1),\quad
d=\arccos(\alpha_\infty/X_1),
\quad0<a_c<b_c<c_c<d<\pi.
\tag{13}
\]
The map `cosh(z)` sends `s>0,0<t<pi` conformally to the upper half-plane. Put
`A=X_4/X_1, B=-X_2/X_1, C=-X_5/X_1, D=alpha_infinity/X_1`;
then `1>A>B>C>D>0`, and its four ordered electrode values are `-A,-B,-C,-D`. The horizontal rectangle foliation maps to disjoint **source** A.1 Waves of base `(S_1,S_2,S_3)` (the complementary arc is homotopic to the designated intervening `S_2` atom); conjugation supplies `(S_17,S_18,S_19)`. Their equal widths satisfy
\[
C_\infty\ge C_-:=
 \frac{K(\sqrt{\kappa})}{K(\sqrt{1-\kappa})},\qquad
\kappa=\frac{(A-B)(C-D)}{(A-C)(B-D)}.
\tag{14}
\]
No covering pushforward was used to construct these children.

## 3. Certified two-sided limiting widths and strict gain

The earlier full-*lift* arguments give **upper**, not realized, envelopes:
\[
P_\infty\le P_+:={K(k_+)\over K(\sqrt{1-k_+^2})},
\quad k_+=(b-a)/(b+a),
\]
\[
C_\infty\le C_+:={K(\sqrt{\kappa_+})\over K(\sqrt{1-\kappa_+})},
\quad
\kappa_+={(b_c-a_c)(d-c_c)\over(c_c-a_c)(d-b_c)}.
\tag{15}
\]
These include all homotopy-selected lifts, so their use as upper bounds does **not** require foliation injectivity. By contrast, (11),(14) are lower bounds from **actual** embedded Waves. The same rectangle modulus formula is used in both directions for different, explicitly named families.

All entries below are **strict rational outward enclosures** verified with isolated `tau_*`, outward `2^-512` elementary/elliptic series and rational tail remainders (they are not approximate optimizers):

| Limiting quantity | Proven enclosure | Mathematical role |
|---|---:|---|
| parent `P_infinity` | `0.752754 < P_infinity < 0.774925` | (11) embedded lower; (15) all-lift upper |
| either child `C_infinity` | `0.960197 < C_infinity < 0.987650` | (14) embedded lower; (15) all-lift upper |
| independently maximized `D_infinity=2/C_infinity-1/P_infinity` | **`0.696 < D_infinity < 0.793`** | both reciprocal directions certified |

In particular, **the sign of the limiting marked model defect is strictly positive.** These enclosures are tight enough to decide the sign while leaving the exact three optima and their attainment open. No convergence of the physical `P_p,C_p` to `P_infinity,C_infinity` is needed for the stronger separate finite-period theorem below.

## 4. Uniform physical tail with an explicit cutoff `p0=13`

Apply (9) in **each finite target slit** in the positive `xi=lambda_p z` chart. For every `p>=13`, all four normalized cuts in (7) lie in the **widest p=13 rational interval box** (5): increasing the period only shrinks these error boxes. The new verifier evaluates (9) on that whole box and proves the *strict* inequality
\[
\boxed{W_{P,p}^{(5/2)}>2/3\quad\text{for every }p\ge13.}\tag{16}
\]
It separately checks all endpoint orders, `b<5/2<pi`, the cross-ratio interval, and the positive elliptic denominators. This is a certificate for an entire **continuum** of admissible leaves, not finite sampling and not a numerical optimizer.

The full mapped semidisk is inside the **physical** target `U_p`: in normalized coordinates `|m|<2`, `0<r<2` on the `p=13` box. For `s<=5/2`, the elementary Taylor/geometric-tail certificate `e^(5/2)<13` and `e^(-s)<=1` yield
\[
|\mathcal J_P(-e^{s+it})|
 \le |m|+{r\over2}(e^s+e^{-s})<2+{2\over2}(13+1)=16.
\]
But the *entire* normalized target disk has radius
\[
\lambda_p R_p > (3/20)2^p\ge (3/20)2^{13}>16.
\tag{17}
\]
Therefore every projected leaf is contained in the target disk, for all periods at once; no separately unproved source pullback containment is needed for this **parent** competitor. (If the source was required, it would have to be checked as a distinct statement.)

The merged gain audit already proves `C_p\le E_p\le E_p^coarse<63/50` for **all** `p>=13` using the normalized orbit boxes, enlarged child electrodes and the plane-slit full-lift comparison, without requiring a bound on `alpha_p` for the tail. Combining with (10),(16) gives, with the **correct reciprocal reversal**,
\[
\begin{aligned}
D_p&=\frac{2}{C_p}-\frac1{P_p}
>\frac{2}{63/50}-\frac1{2/3}
=\frac{100}{63}-\frac32
=\boxed{\frac{11}{126}>0}\quad(p\ge13).
\end{aligned}\tag{18}
\]
Hence **`p0=13`** works, with no interpolation, optimizer stability assumption, or empirical period trend. This *strict sign theorem* supersedes the earlier sign-indefinite bounds for that tail (without changing the predecessor files). It makes **no assertion for periods 3–12**, for which the older intervals still cross zero.

## 5. Precise interpretation, limitations and hostile review

The two-child **leafwise-pairable parent** still obeys KKL Lemma A.11:
`P_pair <= C_p/2`, hence its defect is **nonpositive**. Our independently optimized unrestricted parent has `P_p>C_p/2` for `p>=13`; therefore **the unrestricted parent supremum cannot equal the pairable parent supremum** in this tail. The gain is exactly the *failure of independent optimization to commute with simultaneous child restriction*, not a violation of KKL's serial inequality. It is a genuine **strict gain for the pre-existing unbuffered maximal marked Wave defect**, conditional on M in the physical interpretation.

For **literal KKL A.2.3 buffered canonical WAD arcs**, the earlier upper full-path envelopes are below the two-square buffer threshold; those particular canonical arc weights are zero. The reciprocal expression here is **not** an inverse of those zero weights. Nor does (18) prove growth across successive KKL pullbacks: the independently maximizing parent and children have **not** been produced simultaneously as one covering/immersion-compatible object. KKL-style Wave amplification therefore cannot be inferred without an additional dynamical compatibility lemma.

**Open analytical debt:** exact values and possible attainment of `P_infinity,C_infinity`; whether `P_p -> P_infinity` and `C_p -> C_infinity` as the marked domains exhaust; corresponding period-3 through period-12 signs; full geometric identification M beyond the cited sources; and any positive buffered canonical WAD statement. The specific optima still missing are the **suprema over simple, embedded, collar-subordinate A.1 laminations** in the two exterior-slit cylinders, not the already computed full-lift Schwarz–Christoffel moduli. These unknowns **do not obstruct** the strict sign statement (18).

**Hostile-review ledger:**

- **No quotient fallacy:** The *upper* plane-slit full-lift families may contain self-intersecting projections. The new *lower* foliation lies inside `|t|<5/2<pi` (or an injective limiting half-strip) and is genuinely embedded after projection.
- **No wrong analytic scaling:** `A_p<0`; `h_p(w)=w^2+tau_p+e_p(w)` and `widehat G_p(xi)=-xi^2-tau_p-e_p(-xi)`. The positive `-A_p` scale preserves physical real order. Normalized cuts refer to `x_{jp}`.
- **No wrong inequalities:** Embedding a rectangle foliation makes a lower bound on a supremum, whereas including all lifts makes an upper bound. Inversion reverses both comparisons, and (18) is an *unrestricted* rather than paired defect.
- **No disguised maximum:** Neither half-strip lower competitor nor full-lift upper envelope is claimed to be optimal. Rectangular horizontal foliations have exactly the stated widths by Cauchy–Schwarz and the constant dual metric.
- **No unwarranted all-period chart extension:** The parent disk cutoff uses the `p=13` common box and `lambda R_p>(3/20)2^p`, not the non-uniform `p=3` radius or a guessed `alpha_p` limit. Periods below 13 are explicitly left open.
- **No false software proof:** The checker re-runs the upstream packets read-only, computes new cross-ratios and elliptic series with outward rational bounds, and fails on changed signs/orders. It does not formalize conformal mapping, prime-end M, A.1, or KKL Lemma A.11 in Lean.

Run from the repository root:

```sh
python -B research/independent_audits/tip_family_limiting_wave_gain_20261116/verify.py
python -B -m unittest discover -s research/independent_audits/tip_family_limiting_wave_gain_20261116 -p 'test_*.py' -v
```

The dedicated workflow also runs the unchanged predecessor, verifies an add-only diff, and dispatches the original research-validation and weighted Lean workflows at the PR's exact head SHA. It is a regression gate for the declared arithmetic results and source boundaries, not a substitute for peer review of the conformal geometry.
