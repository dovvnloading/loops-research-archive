# Double-crossing charge for actual bank or deep-limb hits

2026-11-25. Written analytic continuation of
[EXCEPTIONAL_WIDTH_REDUCTION.md](EXCEPTIONAL_WIDTH_REDUCTION.md).
The goal is to charge a genuine physical encounter even when all final
punctured restrictions have carrier-only endpoints. This proves a
route-localized conditional estimate, not uniform native calibration,
the stationary hit assertion, or a global research gate.

## 1. Two-crossing lemma without an exit selection

Let U and S be hyperbolic conformal disks, i:S→U a holomorphic
immersion, T a full compact continuum in U, and X=U minus T.
Let H be a nondegenerate full continuum in S, and let E be a
Jordan disk with

\[
 H\subset E,\qquad \overline E\Subset S,\qquad
 i(\overline E)\cap T=\varnothing .
 \tag{1}
\]

The annulus E minus H has modulus μ>0 in the convention
mod A(r,1)=log(1/r)/(2π). Write A_H for the family of simple proper
paths in X whose physical trace meets i(H) at an interior time.
For any such family,

\[
 \boxed{W_X(A_H)\le \frac{1}{4\mu}.}
 \tag{2}
\]

No final ideal-proper restriction, global immersion injectivity,
marking retention, or common compact lift of the whole parent is
required. Neither H nor E needs to be part of the deleted little
Julia cycle.

### Proof

Start a local lift at any preimage in H of a hit by the parent α.
Continue it in the unpunctured S in both directions. In each
direction it must reach the boundary of E at an interior parent
time. Indeed, if a maximal lifetime ends at a finite interior
time while the lift stays in E, compactness of its closure gives
an accumulation point in S. A local inverse chart there extends
the lift across that time by uniqueness, contradicting maximality.
If instead the lift stays in E all the way to an original parent
endpoint, its projection stays in i(closure E), a compact subset
of X by (1). This contradicts properness of the parent in X.
If the lift leaves E earlier, take its first departure from E.

There are thus two disjoint intervals of parent times, one on
each side of the hit, whose lifted paths cross E minus H between
its two ends. For each direction take the last H hit before the
first boundary-E hit; this is an attained time by compactness.
The crossing is inside the annulus in between. The radial
coordinate of a round uniformization tends to the corresponding
boundary circle at these endpoints, even without local
connectivity of H: the nested inner and outer collars in the
annulus separate the two physical boundary components. This
requires no unique angular limit.

Uniformize E minus H by g onto A(r,1). Define the nonnegative
source density

\[
 \sigma(z)=
 {\bf1}_{E\setminus H}(z)\frac{|g'(z)|}{|g(z)|\log(1/r)} .
\]

Each such crossing has σ-length at least 1, by variation of
log|g| on compactly exhausted interior subpaths. This is true
for every locally rectifiable parent: its lifts are locally
rectifiable by inverse charts. The area of σ is exactly

\[
 \int_S \sigma^2\,dA=
 \frac{2\pi}{\log(1/r)}=\frac1\mu.
 \tag{3}
\]

Take disk coordinates on S and U, so these are ordinary
Euclidean densities with the conformal Jacobian included.
Push the metric to the *whole* target by the square sum

\[
 f(w)^2=\sum_{z\in i^{-1}(w)}
             \frac{\sigma(z)^2}{|i'(z)|^2}.
 \tag{4}
\]

This is the same all-sheet change of variables as in Section 1
of the exceptional-width note: a countable Borel partition of
S into injective chart pieces and Tonelli give

\[
 \int_U f^2\,dA=\int_S\sigma^2\,dA=1/\mu.
\]

A locally rectifiable parent has f-length at least the σ-length
of each of its lifted crossings on the respective parameter
interval. The intervals are disjoint, even if other competing
lifts cover the same image. Thus its f-length is at least 2.
The density f/2 is admissible on this core. In finite-area
target disk coordinates a positive constant of arbitrarily
small energy handles every parent of infinite Euclidean length.
For example use f/2+ε, then let ε decrease to zero in L²; this
does not discard any locally nonrectifiable paths. Restrict the
density to X, which only decreases its area. Formula (2)
follows. No Borel choice of one lift is used because (4)
already dominates every lift. QED.

The factor 1/4 is the two-crossing length gain squared, not a
covering-degree correction. This proof does not bound paths
with only one crossing by 1/(4μ).

## 2. Fractional hit-cover extension

Allow finitely many packages (i_j:S_j→U,H_j,E_j) satisfying
(1) with the same T; the source surfaces may differ. Let μ_j be
the annular moduli and f_j the target metrics (4). For each
parent α define J(α)={j: the trace of α meets i_j(H_j)}.

Take nonnegative numbers a_j such that

\[
 \sum_{j\in J(\alpha)}a_j\ge1
 \quad\text{for every parent under consideration.}
 \tag{5}
\]

Then

\[
 \boxed{
 W_X(A)\le\frac14\sum_j\frac{a_j}{\mu_j}.
 }
 \tag{6}
\]

Indeed, form the single target metric
\(f_*=\tfrac12(\sum_j a_j f_j^2)^{1/2}\).
For a finite-length parent the triangle inequality for the
Euclidean norm of the vector integral gives

\[
 \ell_{f_*}(\alpha)
 \ge \frac12
      \left(\sum_j a_j\,\ell_{f_j}(\alpha)^2\right)^{1/2}
 \ge \left(\sum_{j\in J(\alpha)}a_j\right)^{1/2}\ge1.
\]

Apply truncation if an individual integral is infinite; or
ignore a zero coefficient before forming the vector. Add a
vanishing positive constant for the other parents as before.
Tonelli and (3)–(4) give (6). Even if different hit packages use
different competing lifts and their images overlap, the
Euclidean norm inequality is valid. Summing their line lengths
as if the crossings were disjoint would not be valid.

In particular, one hit in a bank gives the sum of the
reciprocal collar moduli divided by four; at least s distinct
hits give the same sum divided by 4s (choose a_j=1/s). This is
a finite fractional cover of actual hit sets, not an inference
of actual hits from symbolic incidence. It differs from the
kernel-checked endpoint graph inequality in
[LEAN_ENDPOINT_ACCOUNTING.md](LEAN_ENDPOINT_ACCOUNTING.md),
which concerns proper exits and local cyclic widths.

## 3. Actual bank collar application

Use the filled-graph identities of
[PQL iterate filled-graph naturality](../../mlc_unified/pql_iterate_filled_graph_naturality.md):
I_m^(-1)(K)=K^m and I_m on K^m is a homeomorphism onto K,
with inverse Γ_m. Thus I_m^(-1)(T)=Γ_m(T).
Suppose the actual selected predecessor bank Qhat_n, b≤n<m,
consists of the degree-two whole pulled components of
[the variable-end theorem, Corollary 5.3](VARIABLE_END_EXIT_TRANSFER.md)
and its physical images Q_n are disjoint from T. The latter
holds for the full-hull carrier in the hypotheses of
[the singleton-cut pruning theorem, Section 6](../maximal_global_closure_20261123/CUTPOINT_PRUNING.md);
its application to the independently named KKL carrier still
requires the carrier identification stated there.

Choose target Jordan disks V_n around K_(m−n), with the
selected full inverse component E_n of V_n under P_m having
compact closure disjoint from Γ_m(T). Such disks exist
qualitatively: the composable degree-two Jordan restrictions
in Corollary 5.3 can be shrunk down to their actual inverse
compactum Qhat_n, which is disjoint from Γ_m(T).
Choose their boundaries avoiding critical values and all
other target little Julia sets. The selected component is a
Jordan disk and the restriction on E_n minus Qhat_n is an
unbranched annular covering of degree two onto V_n minus
K_(m−n). If μ_n=mod(V_n minus K_(m−n)), then

\[
 \operatorname{mod}(E_n\setminus\widehat Q_n)=\mu_n/2 .
\]

Use (6) at the final horizon with weights covering the actual
bank hits. For the family G_hit with at least one bank hit
and D_0 of no-hit parents, subadditivity gives

\[
 W(A_m)\le W(D_0)+\frac12\sum_{n=b}^{m-1}\mu_n^{-1}.
 \tag{7}
\]

This charges all bank-hit parents, including carrier-only
residuals, without assuming an eligible final exit. A
quantitative sufficient calibration is
μ_n^(-1)≤C (R(F)+V(F)+1) uniformly over these specific
selected inverse components, where R(F)=W(RF) and
V(F)=W(U minus T). It would give a charge with coefficient
Cr/2. If the stronger μ_n≥1/(2R(F)) holds, the charge is rR(F).
Neither calibration follows merely from the qualitative
existence of these disks or from the whole-end cyclic-width
estimate. Shrinking can make their reciprocal moduli
arbitrarily large. The old global collar obstruction
[uniform collar charge audit](../../mlc_unified/kkl_stationary_uniform_collar_charge_attack.md)
is not bypassed by asserting unproved quantitative clearance.

## 4. A weaker geometric encounter: the whole selected deep limb

There is a distinct application at intermediate horizons, before
proving any small-Julia predecessor hit. Use the selected physical
terminal inverse sheets Ω_n=φ_0^n(Ω_0), Ω_0 the critical limb,
of [the N2 predecessor theorem](../../mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md)
and the full-hull incidence assumptions of the singleton-cut
pruning theorem. Assume P≥q>b and n satisfies b<n<q.

First T∩Ω_b is empty: if it meets Ω_b, the singleton-cut hull
theorem supplies an original K_i in Ω_b. Since T is forward
invariant, F^b(K_i) lies in T∩Ω_0 and K_i lies in the selected
L_b=φ_0^b(T∩Ω_0), contrary to the proved b+1 distinct-cycle
count. The sheets Ω_n are nested because φ_0(Ω_0)⊂Ω_0 and
the inverse branch is injective on Ω_0. Their closures have
only the extra point α^n, by the cited terminal-sheet theorem.
The selected α^1 belongs to Ω_0; hence
α^n=φ_0^(n−1)(α^1) belongs to Ω_(n−1)⊂Ω_b. Therefore

\[
 C_n:=\overline{\Omega_n}\subset\Omega_b,\qquad
 C_n\cap T=\varnothing .
 \tag{8}
\]

Let H_0=closure Ω_0 be the closed critical limb. The map F^n
on C_n is a homeomorphism onto H_0: it is already a
homeomorphism of the open-in-K limbs and takes their added
boundary point to α_F by continuity. This holds without
local connectivity. H_0 is full by
[the connected-carrier theorem, Lemma 2.1](../maximal_global_closure_20261123/CONNECTED_CARRIER_NONCOLLISION.md).
For n<q all critical values of P_n lie outside H_0 by its
Lemma 2.2 and the limb rotation. Thus there is a Jordan disk
V^0 around H_0 whose selected inverse component E^0 is
univalent and contains Γ_n(C_n). Connectedness of C_n and
the graph identity give this one sheet; its complete inverse
of H_0 is exactly Γ_n(C_n), by the homeomorphism just proved.

The compact continuum Γ_n(C_n) is disjoint from Γ_n(T) by
(8). Let χ:V^0→E^0 be the univalent inverse section, and
choose a Jordan disk V with

\[
 H_0\subset V,\quad
 \overline V\Subset V^0,\quad
 \chi(\overline V)\cap\Gamma_n(T)=\varnothing .
 \tag{9}
\]

This is qualitatively possible by compactness and the Jordan
neighborhood basis of H_0. The source collar
E=χ(V), H=Γ_n(C_n) satisfies (1) for i=I_n.
The modulus is exactly mod(V minus H_0), with degree ONE
rather than the final little-Julia bank degree two.

Consequently every family A_deep of actual proper parents
meeting C_n in U satisfies

\[
 \boxed{
 W(A_{\rm deep})\le
 \frac{1}{4\operatorname{mod}(V\setminus H_0)}.
 }
 \tag{10}
\]

In particular the proof does not require an interior
Q_n hit, two proper retained occurrences, or a final
inner-to-inner exit. The condition (9) is an exact
route-localized target for calibration. Inside the initial
univalent neighborhood V^0 its forbidden set is the relative
closed set χ^(-1)(Γ_n(T)); the compact H_0 avoids it. A
Jordan disk V containing H_0 and compactly separated from
this set is enough. Uniform positive lower control of its
modulus relative to the native widths remains unproved.

One can combine these deep-limb packages and final-bank
packages in (6), even at different horizons. Then the
uncharged family consists only of parents meeting none of
the chosen packages, provided the displayed annular
conductances have a usable uniform bound. Actual physical
encounters, not mere crest labels, are still necessary.

## 5. A stronger exact obstruction to automatic calibration

The rectangle in the preceding exceptional-width note can be
made arbitrarily wide in modulus while the final punctured
surface and the ambient vertical width stay controlled.

Take S=U={|z|<5}, i the identity, K=C={|z|≤4}.
Fix Q={iy:−1≤y≤1} and H={|z−3|≤1/4}; the surface
X_f=S minus (Q union H) is fixed. For rational or real
0<δ≤1/2 take the full carrier T_δ consisting of H and the
polygonal U-shaped arc with vertices (−δ,−2),(−δ,2),
(δ,2),(δ,−2), and a branch from (δ,2) to (3,2) to (3,1/4).
This is a compact full continuum in the fixed disk of radius
4, disjoint from Q (a disk with an embedded finite tree
attached at one point). For every y in [−1/2,1/2] take the
horizontal open segment from −δ+iy to δ+iy. These are
simple, mutually disjoint, Borel proper paths in U minus T_δ.
Every leaf hits Q once, never H, and neither maximal
restriction in X_f is proper at its carrier-only endpoint.

Cauchy–Schwarz across each width-2δ horizontal segment
and integration over the unit height give the exact modulus

\[
 W(A_\delta)=1/(2\delta).
 \tag{11}
\]

The constant density 1/(2δ) on the rectangle proves the
matching upper bound. The bank local cyclic width in X_f
is fixed and finite; X_f itself does not vary. The ambient
vertical width is uniformly bounded because
T_δ⊂closed D(0,4) and ring monotonicity gives

\[
 W(U\setminus T_\delta)
 \le 2\pi/\log(5/4).
\]

For example δ=1/2,1/4,1/8,1/16 gives exact widths 1,2,4,8.
In particular, no bound by a universal multiple of the sum
of the ambient vertical width, the final bank local width
and one follows from the general planar assumptions of the
one-hit reduction alone. Moreover every collar E around Q
whose closure avoids T_δ satisfies μ≤δ/2 by (2) and (11).
This defeats even an optimized qualitative collar choice.

This is an exact conformal countermodel to generic
calibration, not a quadratic dynamical or KKL counterexample;
the fixed local cyclic width is not claimed to be the
renormalization width of a native map. The actual dynamical
hypotheses in Sections 3–4 must be used to establish a
uniform comparison or a different response.

## 6. Remaining target

The double-crossing estimates charge carrier-only residuals
whenever their true hit packages are quantitatively separated
from T. The new whole-limb version accepts weaker physical
encounters and a univalent intermediate-horizon collar.
What remains is (i) prove actual native encounters or handle
the no-hit family, and (ii) calibrate (9) or the selected bank
collars uniformly in the high-type regime, or use an
independent terminal response. No proof of these two
requirements is contained here. The exact countermodel
shows why neither qualitative separation nor local cyclic
width alone supplies (ii).

All arguments in this note are written mathematical proofs;
they are not represented as Lean-checked analysis. The
existing eight finite Lean theorems remain unchanged.
Prepared with ChatGPT assistance; specialist review pending.
