# Buffered canonical WAD on the real primitive-tip family: an exact peripheral exclusion, **not** a support solution

**2026-11-16 — partial independent audit, all selected integers \(p\ge3\).**
**New result:** for \(p=11,12\) and **every** \(p\ge13\), **every**
KKL A.2.3 ideal quadrilateral whose arc is incident on the *outer* boundary
has \(q_\gamma<2\). Therefore all four outer-involving endpoint types
have **zero** canonical buffered weight, without a winding-word cutoff.
The three inner Julia intervals admit uniform exact embedded collars, so
for all \(p\ge11\), \(0\le\|W_{\rm can}\|<619/200=3.095\).
**NOT SOLVED:** the remaining six *inner* endpoint types (infinitely many
isotopy classes within the types), each individual inner \(q_\gamma\), whether
the complete \(W_{\rm can}\) is zero or positive, and whether any positive
norm has an all-period lower bound. No MLC assertion follows. This is
deliberately not a claim to have completed the requested exhaustive support
classification or dual variational certificates.

The primary source is Kahn–Kapiamba–Lyubich (KKL),
[*MLC for parabolically bounded primitive renormalization*,
arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1),
Appendix A.1, A.2.1–A.2.5, A.3.1–A.3.2 and §§5–6.
Read this alongside the **unchanged** earlier
[physical M-discharge](../tip_family_hypothesis_M_discharge_20261116/NOTE.md),
[unbuffered independent gain](../tip_family_canonical_wave_gain_20261116/NOTE.md),
[physical KKL/Wave surface distinction](../canonical_wad_electrode_incidence_20261116/NOTE.md),
[auxiliary capacities](../canonical_wad_conformal_weights_20261116/NOTE.md),
and [four-boundary collar bound at \(p=3\)](../canonical_wad_quadrilateral_moduli_20261116/NOTE.md).
The finite verifier imports those **existing** exact selected-root and
all-period chart checks read-only; no old file is changed.

## 1. Source-faithful surface and the class set

For the *selected* primitive parameter of each integer \(p\ge3\),
write \(f_c(z)=z^2+c\), \(x_j=f_{c_p}^{\,j}(0)\),
\(G_p=f_{c_p}^p\), \(A_p=[z^2]G_p<0\), and
\(R_3=1/4,\ R_p=2^{-p}\ (p\ge4)\). The minimally marked surface on
which KKL §5 places its **canonical** WAD is
\[
Y_{K,p}=D(0,R_p)\setminus(K_{0,p}\cup K_{1,p}\cup K_{2,p}),\quad
\begin{cases}
K_{0,p}=[x_{3p},x_{6p}],\\
K_{1,p}=[x_{4p},x_p],\\
K_{2,p}=[x_{2p},x_{5p}].
\end{cases}                                                   \tag{1}
\]
Its four marked intervals are the **entire** ideal boundary circles
\(I_{\rm out},I_0,I_1,I_2\). The strict certified real order is
\(x_{2p}<x_{5p}<x_{3p}<0<x_{6p}<x_{4p}<x_p\).
This is **not** \(\Omega_p=D(0,R_p)\setminus T_p\) with
\(T_p=[x_{2p},x_p]\) and its ten-atom inner boundary, nor the
source \(\Omega'_p=V_p\setminus T'_p\) with twenty atoms.

For an A.1-*admissible*, simple **unoriented** ideal arc class
\(\gamma\) on (1), let \(\widetilde I,\widetilde J\) be its two
ideal intervals in the **universal cover**, and put
\[
q_\gamma=\overline{\mathcal W}(\widetilde I,\widetilde J),\qquad
w_\gamma=(q_\gamma-2)_+,\qquad
\|W_{\rm can}\|=\sum_\gamma w_\gamma.                             \tag{2}
\]
Since (1) is not a minimally marked annulus, the exceptional
unbuffered annulus clause of A.2.3 does **not** apply. The §5
horizontal-plus-vertical projection \(X\) discards bivertical classes;
the full canonical WAD and \(X\) are separate quantities.

There are **ten unordered endpoint types**, not ten classes:
\[
\begin{gathered}
({\rm out},{\rm out}),({\rm out},K_0),
({\rm out},K_1),({\rm out},K_2),\\
(K_0,K_0),(K_0,K_1),(K_0,K_2),\\
(K_1,K_1),(K_1,K_2),(K_2,K_2).
\end{gathered}                                                  \tag{3}
\]
There are infinitely many simple homotopy classes at some fixed
endpoint types on a four-boundary planar surface. The KKL
\(3|\chi|+|\mathcal I|=10\) *support cardinality* theorem is **not**
a finite enumeration procedure. Classes with both lifted endpoints
on the **same** ideal interval are boundary-subordinate and excluded
by A.1; a valid self-endpoint class in (3) uses **distinct lifts**.

## 2. A general cyclic-cover exclusion theorem (new)

**Theorem (peripheral-length test).** Let \(Y\) be a finite-type
hyperbolic surface with a minimally marked nonsimply-connected
boundary circle \(I\), and not the exceptional minimally marked
annulus. Denote by \(\mathcal W(I)\) KKL A.2.4's width of the
*peripheral cyclic cover*. For **every** admissible ideal arc class
\(\gamma\) incident on \(I\), including all essential self-endpoint
classes, define \(E(s)=K(\sqrt{s})/K(\sqrt{1-s})\). Then
\[
0<q_\gamma
\le E\!\left(1-e^{-\pi\mathcal W(I)}\right).
\tag{4}
\]
In particular, if
\[
\pi\mathcal W(I)<\log(17+12\sqrt2),
\quad\text{then }q_\gamma<2\text{ for *all* such }\gamma.
\tag{5}
\]

**Proof.** Uniformize the universal cover by \(\mathbb H\), taking a
chosen lift of \(I\) to \((0,\infty)\), and its primitive peripheral
stabilizer to \(\tau(z)=\lambda z\) with \(\lambda>1\).
Writing \(\ell=\log\lambda\), the cyclic quotient is the Euclidean
log-strip \(0<\operatorname{Im}\log z<\pi\), periodic of circumference
\(\ell\); the width between its two ideal ends is **\(\ell/\pi\)**,
not its reciprocal. Thus
\[
\ell=\pi\mathcal W(I).                                          \tag{6}
\]
For any other ideal interval lift \(\widetilde J\), normalize its
real endpoints to \((-b,-a)\), \(0<a<b<\infty\).
The intervals \(\widetilde J\) and
\(\tau\widetilde J=(-\lambda b,-\lambda a)\) have disjoint interiors:
distinct ideal boundary lifts do not overlap. If they were equal,
\(\widetilde J\) would be stabilized by the peripheral element of
\(I\), forcing the **same** lift of that component; that is
A.1-boundary-subordinate and excluded. Therefore
\(b/a\le\lambda\). (Coincident peripheral stabilizers in the free
finite-type surface group cannot stabilize distinct boundary intervals.)

For intervals \((0,\infty),(-b,-a)\) in \(\mathbb H\), the
Schwarz–Christoffel/elliptic quadrilateral formula gives
\[
k^2=1-\frac ab\le1-\lambda^{-1},\qquad
q_\gamma=E(k^2).
\]
\(E\) is strictly increasing, proving (4). The descending quadratic
Landen transformation sends \(k_0=1/\sqrt2\), for which
\(K(k_0)=K(k_0')\), to a modulus with
\(k'= (1-k_0)/(1+k_0)=3-2\sqrt2\). Its width is **twice** the old
one, so
\[
E(12\sqrt2-16)=2,\quad
1-(12\sqrt2-16)=17-12\sqrt2=(17+12\sqrt2)^{-1}.                \tag{7}
\]
Consequently (5) follows from strict monotonicity. This proof uses
standard hyperbolic uniformization, the free-surface peripheral
stabilizer fact, the SC elliptic integral formula, and Landen's
identity; the Python verifier checks the **rational** premises and
threshold inequalities, not those continuum theorems. QED.

A particularly convenient **exact sufficient test** is
\[
\ell<7/2
\quad\Longrightarrow\quad
\lambda<e^{7/2}<(33/20)^7<169/5<17+12\sqrt2.
\tag{8}
\]
Here \(e^{1/2}<33/20\) follows by the positive Taylor series with
a geometric remainder; the final comparison uses \(\sqrt2>7/5\).
For \(\ell<3\) there is the simpler \(e^3<27<17+12\sqrt2\).
Notice that (4) is an **unbuffered \(q\) bound**; the prior
\(W_{\rm can}(I)\le\mathcal W(I)\) bounds only *buffered* totals.
This is why (4) genuinely supplies new class exclusions.

## 3. Physical Joukowski annuli, finite charts and the all-\(p\) tail

Work in the positive *conformal* scale \(\xi=(-A_p)z\);
never confuse \(x_{jp}\) with \(x_j\). A segment \([l,r]\) in
these coordinates has center \(m=(l+r)/2\), half-length
\(a=(r-l)/2>0\), and Joukowski chart
\(\xi=m+\frac a2(w+w^{-1})\). The ellipse \(|w|=t\) has
horizontal semiaxis \(a(t+t^{-1})/2\).
For an inner interval \(K_j\), we certify the full ellipse stays
inside the target disk **and misses the other two holes**.
For the outer peripheral class we instead use the **whole carrier**
\([x_{2p},x_p]\) surrounding every hole; the carrier is **not** a fourth
Julia boundary, and its gaps are not removed from (1). The open
Joukowski annulus lies in (1), is essential around all three holes,
and lifts injectively as an essential subannulus of the outer
peripheral cyclic cover. This is a topological annulus comparison,
**not** an identification of the physical carrier condenser with
\(q_\gamma\).

An explicit potential \(u=\log|w|/\log t\), extended by constants to
the two sides of that cyclic-cover subannulus, has exactly
\(2\pi/\log t\) Dirichlet energy. The standard essential-annulus
comparison gives for **each** of the four peripheral components
\[
\mathcal W(I)\le\frac{2\pi}{\log t},
\qquad
\ell_I=\pi\mathcal W(I)\le\frac{2\pi^2}{\log t}.
\tag{9}
\]
No other slit is treated as an insulated electrode, and this
is not a certificate of any *individual* \(q_\gamma\) value.

The new verifier re-isolates the physical \(p=3,\ldots,12\)
selected roots from the existing adjacent \(2^{-256}\) packets,
propagates the **actual** \(x_{jp}\), and checks the following
whole-ellipse annuli by outward interval arithmetic. The last two
finite periods meet the exact (8) length test.

| Selected period | Outer carrier \(t\) | Outer-incident canonical classes |
|---|---:|---|
| 3 | \(23/10\) | not excluded |
| 4 | \(2\) | not excluded |
| 5 | \(4\) | not excluded |
| 6 | \(8\) | not excluded |
| 7 | \(16\) | not excluded |
| 8 | \(32\) | not excluded |
| 9 | \(64\) | not excluded |
| 10 | \(128\) | not excluded |
| 11 | \(300\) | **all \(q_\gamma<2\)** |
| 12 | \(512\) | **all \(q_\gamma<2\)** |
| Every \(p\ge13\) | \(1024\) | **all \(q_\gamma<2\)** |

For all \(p\ge13\), the previously proved **all-period** chart gives
\[
(-A_p)R_p>\frac3{20}2^p,\qquad |m|<2,\quad0<a<2
\]
for the normalized whole carrier, with the p13 box the largest
error box. For \(t=1024\),
\[
|m|+\frac a2(t+t^{-1})
<2+1024+1/1024<\frac3{20}2^{13}
\le(-A_p)R_p.
\]
Thus the entire annulus embeds for **every** \(p\ge13\),
without interpolating sampled periods, and
\[
\ell_{\rm out}
\le \frac{2\pi^2}{\log(1024)}
=\frac{\pi^2}{5\log2}<3.                                 \tag{10}
\]
The last strict inequality uses \(\pi^2<10\) and
\(\log2>2/3\), both certifiable rationally.
For \(p=11,12\), exact Machin-\(\pi\) and atanh-log
outward bounds applied to (9) give
\(\ell_{\rm out}<7/2\), hence the same *classwise* exclusion.
There is no positive outer canonical WAD weight for any \(p\ge11\).

For **each** \(p=3,\ldots,12\), and for the *uniform p13 normalized
orbit box* that contains all \(p\ge13\) boxes, the same verifier also
checks the disjoint embedded three-hole collars
\[
t_{K_0}=11,\qquad t_{K_1}=49,\qquad t_{K_2}=25
\]
with strict rational inequalities
\[
\mathcal W(K_0)<2621/1000,\quad
\mathcal W(K_1)<323/200,\quad
\mathcal W(K_2)<1953/1000.                               \tag{11}
\]
The p13 box uses the known normalized model orbit and the existing
\(4^{-p}\) error propagation through all **six** iterates, not the
\(p=3\) orbit substituted for the tail. This is an *upper*
cyclic-cover width certificate, not a lower one.
Using KKL A.2.3–A.2.5, with returning arcs counted **twice**
in local weights, the absence of outer-incident weight yields
\[
0\le\|W_{\rm can}(Y_{K,p})\|
\le\frac12\sum_{j=0}^2\mathcal W(K_j)
<\frac{6189}{2000}<\boxed{\frac{619}{200}}
\quad (p\ge11).                                           \tag{12}
\]
The same bound holds for the horizontal-plus-vertical projection
\(X\). **Nothing here gives a positive lower bound.**

## 4. Candidate inventory and the exact obstruction to completion

For \(3\le p\le10\), none of the ten types (3) has been excluded
*solely by this audit*. For every \(p\ge11\), **only the following
six endpoint types could have \(q_\gamma>2\)**:
\[
(K_0,K_0),\ (K_0,K_1),\ (K_0,K_2),\
(K_1,K_1),\ (K_1,K_2),\ (K_2,K_2).                         \tag{13}
\]
This is an **exhaustive list of possible endpoint types** once (5)
is applied, **not an enumeration of all classes within them**.
For each candidate \(\gamma\), (4), (11), and the earlier local-weight
bound supply uniform upper controls, but **not** the requested
class-specific two-sided certified \(q_\gamma\) enclosure.
No rigorous universal-cover endpoint cross-ratio interval, dual
separating-family bound, or effective bound on possible deck words is
available for these six types. We therefore do **not** assert either
\(q_\gamma>2\) or \(q_\gamma\le2\) for them. In particular, the KKL
support-size theorem cannot substitute for an exhaustive word search;
the status of *every individual inner* \(q_\gamma\) remains **OPEN**.
The possible all-period norm-lower-bound question is likewise **OPEN**.

A concrete path to finishing the problem is to give interval-validated
uniformizations of (1) for each selected \(p=3,\ldots,12\) plus an
all-\(p\) model perturbation, identify the corresponding Fuchsian
generators, and bound all simple deck words outside an explicit
finite search. For each retained class the **necessary and sufficient**
support test is the exact algebraic inequality
\[
\frac{(b-a)(d-c)}{(c-a)(d-b)}>12\sqrt2-16                 \tag{14}
\]
for the cyclically ordered ideal lift endpoints \(a<b<c<d\),
with the appropriate Möbius normalization.
Proving (14), or its reverse, requires **certified** endpoint intervals;
a finite floating-point sample is not a proof. The new verifier
does not fabricate such endpoints.

## 5. Relationship to the established unbuffered Wave gain

The merged physical M-discharge establishes, relative to its named
published dynamical/prime-end and geometric theorems, the **unbuffered**
A.1 independent-supremum result
\[
D_p=1/C_p^++1/C_p^--1/P_p>1/100\quad(p\ge3),
\qquad D_p>11/126\quad(p\ge13).
\]
Here \(P_p\) is a supremum of parent Waves on the *tree annulus*
\(\Omega_p\) with ten-atom marking, and \(C_p^\pm\) are **independent**
suprema on the source \(\Omega'_p\) with twenty-atom marking.
The parent gain envelope already proves its specified parent/child
lifted quadrilateral widths are **strictly less than 2**; on those
specified unbuffered arcs the A.2.3 two-square buffered coefficient
\((q-2)_+\) is **zero**. Thus the literal canonical buffered coefficient
on *those arcs* **cannot register the positive gain** and has no
positive inverse for a harmonic-sum amplification calculation.

The literal §5 canonical \(W_{\rm can}\), however, lives on
**\(Y_{K,p}\)**, not \(\Omega_p\) or \(\Omega'_p\). The preceding
observation does **not** equate the arcs between these surfaces, and
does **not** prove that all of \(W_{\rm can}\) vanishes. Similarly,
the outer-class exclusion (10) is a **true canonical KKL fact** on
\(Y_{K,p}\), but does not compute any inner coefficient or the
\(\S5\) projection. Do not transfer an unbuffered full-path envelope,
a physical one-slit auxiliary condenser, or a selected A.1 Wave
into a §5 WAD weight.

Finally, \(f_*=(G_p)_*\) is the **unbranched covering pushforward**,
whereas \(\iota^*\) is the **immersion restriction** filtering
proper source pieces; the attachment makes \(\iota\) nonproper.
No leafwise, source-endpoint-preserving WAD-to-Wave identification,
uniform inverse-weight comparison, or nearly-maximal §6 Wave
selection is supplied by the above result. Consequently the
**direct buffered-WAD amplification through the exhibited gain
classes is killed by the buffer**; whether a *different*, positive
inner class permits a broader KKL-style argument is **undecided**.
This is not a counterexample to the KKL theorems or a claim about MLC.

## 6. Reproducibility and hostile-review disposition

From the repository root:

\`\`\`sh
python -B research/independent_audits/tip_family_buffered_wad_20261116/verify.py
python -B -m unittest discover -s research/independent_audits/tip_family_buffered_wad_20261116 -p 'test_*.py' -v
\`\`\`

The checker imports, without changing, the existing exact
p3..12 selected-root and finite-gain chart, all-\(p\) p13 model
interval, and rational Machin/atanh bound generators; it
certifies cut order, disjointness from every foreign slit,
**whole-ellipse** inclusion in the *actual* normalized target disk,
both finite outer \(\ell<7/2\) claims, tail \(\ell<3\),
the algebraic Landen threshold comparisons, the strict rational
inner peripheral bounds, and the upper-norm arithmetic.
Adversarial tests reject a false \(K_0\) collar with \(t=21\),
a grossly oversized outer collar, altered cut order, and an
insufficient length cutoff. The new CI workflow enforces an
add-only diff and runs this checker and its hostile tests, the
unchanged upstream audits, and requires **original Research
validation and weighted Lean on the exact PR head SHA**.

**Written analytic proof, conditional on standard named theorems:**
the cyclic interval-disjointness bound (4), Landen's threshold (7),
annular-cover collar comparison, and all-arc outer exclusion for
\(p\ge11\). **Exact/interval-certified:** selected root chart
replay p3..12, normalized p13 all-\(p\) gate, all four physical
collars, strict length inequalities (8)–(11), and (12).
**Numerical-only:** **none**; no floating optimizers are used.
**Explicitly open / task not fully done:** all inner class enumeration,
their two-sided \(q_\gamma\) bounds, complete zero/positive WAD verdict,
all-period *lower* norm bound, and a WAD amplification transfer
recognizing \(D_p\). No existing file is modified, and none of these
open conclusions is asserted by a passing CI run.
