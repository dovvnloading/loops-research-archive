# Native marked Wave versus free-outer annular contact response

**2026-11-15 — independent comparison audit, not an MLC claim.** This tests the
[2026-11-07 annular crossover](../kkl_annular_contact_resistance_crossover_20261107.md)
against the **actual physical KKL-marked wave** of
[PR #68](https://github.com/dovvnloading/loops-research-archive/pull/68),
using its unchanged
[tip manifest](../../../results/tip_KKL_tree_marked_breakage_20261109.json).
The distinction between a **valid marked Wave**, the **maximal canonical WAD
weight**, and a **full Dirichlet condenser** is essential. The original
prime-primitive, large-rotation, proof-selected WAD transfer remains OPEN.

## 1. The two measurements and their conformal normalizations

Write the physical map of PR #68 as
\[
 G=f_{c_*}^{\,3}:V_3\longrightarrow U_3=D(0,1/4),\quad
 T=[x_6,x_3],\quad T'=[-x_3,x_3],\quad
 X=T'\setminus T=[-x_3,x_6).
\]
Here \(x_k=f^k_{c_*}(0)\), with the **exact 128-bit rational parameter
enclosure** from the unchanged source manifest. The map \(G\) is even and is
degree two **on this central quadratic-like component**, not degree eight;
the involution \(z\mapsto-z\) exchanges its fibers. The inclusion
\(V_3\setminus T'\hookrightarrow U_3\setminus T\) is a different map and is
nonproper at the complete new attachment boundary.

**Native target Wave.** PR #68 has a genuine wave of proper, A.1- and
A.3.2-admissible marked paths
\[
 S_{\rm full}:
 \quad z=-9/64+r e^{i\theta},\quad
 3/256<r<1/64,\quad0<\theta<2\pi,
\]
with base \((I_9,I_0,I_1)\), crest \(I_0\), and exactly two surviving
source restrictions, each with a width-preserving holomorphic pushforward.
Its **target-Wave** chart is \(\zeta=\log(z+9/64)\). Thus
\[
 \boxed{\mathcal W(S_{\rm full})=\frac{\log(4/3)}{2\pi}},
 \qquad \mathcal W(S'_\pm)=\frac{\log(4/3)}{\pi},
 \qquad
 \mathcal W(S_{\rm full})
 =\left(\mathcal W(S'_+)^{-1}+\mathcal W(S'_-)^{-1}\right)^{-1}.
 \tag{1}
\]
These are exact extremal widths of the specified curve families, not
values of a Dirichlet model. For every \(0<h\le1/1024\), the nonempty
**actual native sub-Wave**
\[
 S_h:\quad 3/256<r<(3/256)e^h
 \quad\text{satisfies}\quad
 \boxed{\mathcal W(S_h)=h/(2\pi)},\quad
 \mathcal W(S'_{h,\pm})=h/\pi. \tag{2}
\]
Indeed \(e^h\le(1-h)^{-1}<4/3\), so these are actual sublaminations of
PR #68, retaining its original marking and filtered restrictions. In
(2), \(h\) measures **logarithmic radial thickness around \(-9/64\)
in the target**.

**Physical source condenser.** Independently uniformize the entire
slit \(\mathbb C\setminus T'\) by the univalent Joukowski chart
\[
 z=\frac{x_3}{2}(w+w^{-1}),\quad |w|>1,\quad
 (t,\theta)=(\log|w|,\arg w).
 \tag{3}
\]
The actual deck involution of \(G\), \(z\mapsto-z\), is \(w\mapsto-w\);
**we do not assert** that \(G\) becomes the exact map \(w\mapsto w^2\)
in these source/target Joukowski charts. The complete physical excess
segment \(X\), including both of its prime-end sides, has inner source
Carathéodory arc
\[
 A_X=\{\theta:|\theta-\pi|\le\beta\},\quad
 \beta=\arccos(-x_6/x_3),\quad
 \ell_X=2\beta,\qquad
 \boxed{6/5<\ell_X<7/5<\pi}. \tag{4}
\]
Its deck translate \(B_X=A_X+\pi\) is disjoint. The inequalities in
(4) come from the 256-bit outward interval orbit and alternating
**rational** cosine Taylor brackets at \(3/5\) and \(7/10\), not rounded
trigonometry. Strict endpoints versus the open excess segment make
no difference to capacity, but the **complete closed arc** is retained
for KKL attachment typing.

For every \(0<h\le1/1024\), the genuine physical source collar
\(1<|w|<e^h\) lies in \(V_3\setminus T'\). To prove this for **all**
points, put \(z_0=x_3\cos\theta\in T'\). Since
\[
 |z-z_0|\le x_3\sinh h
 <\frac{h}{5(1-h)}\le\frac1{5115}<\frac1{4096},
\]
\(|z|<1/4\), \(|c_*|<2\), and
\[
 |G'(z)|=|8zf(z)f^2(z)|
 <8(1/4)(33/16)(1601/256)<26,
\]
while real monotonicity gives \(G(T')=[x_6,x_3]\subset(-1/5,1/5)\).
Consequently \(|G(z)|<1/5+26/4096<1/4\). Radial paths connect each
collar point to \(T'\) inside \(G^{-1}(U_3)\), so this is the correct
central component \(V_3\). This is a **whole-collar** enclosure and
does not silently replace \(V_3\) by the global degree-eight preimage.

The **different**, source-based response measured here is
\[
 \boxed{D_h(\ell)=
 \inf_{\substack{u\in H^1((0,h)\times S^1)\\
  {\rm Tr}_0u|_{A_\ell}=1,\ {\rm Tr}_0u|_{A_\ell+\pi}=0}}
 \int_0^h\!\!\int_0^{2\pi}
 (|u_t|^2+|u_\theta|^2)\,d\theta\,dt. \tag{5}
\]
All the other inner boundary and **the entire outer boundary** are
free/Neumann. In the full-family width convention,
\(D_h(\ell)=\mathcal W(\Gamma_h(A_\ell,A_\ell+\pi))\).
There is no outer pin, no rescaling of \(t\) to unit height, and
no unexplained \(2\pi\) factor: the height \(h\) is exactly log radius;
the usual annular modulus is \(h/(2\pi)\).
The source deck oddness is forced for the minimizing potential, but
it does **not** force any value for a target Wave.

The two \(h\)'s in (2) and (5) can be chosen to have the **same numerical
value**. That is an explicit *calibration choice*, **not a conformal
identification** of the two collars or their curve families. In
particular PR #68's target leaves have ends in \(I_1,I_9\), and their
source restrictions have ends \((S_3,S_1)\) and \((S_{19},S_{17})\).
They do **not** run from \(A_X\) to \(B_X\).

## 2. The precise provable comparison and its sharp limitation

**Theorem (common-surface, common-electrode comparison).**
Let \(C_h=(0,h)\times S^1\), \(h>0\), and let
\(A,B\subset\{0\}\times S^1\) be two disjoint closed arcs of positive
length and positive separation. Give the outer boundary natural/free
boundary conditions and use the same conformal metric for both
measurements. If **every curve** of an admissible KKL marked Wave
\(\mathcal S\) is a rectifiable curve in \(C_h\) joining \(A\) to \(B\)
(that is, \(\mathcal S\subseteq\Gamma_h(A,B)\), with prime-end endpoints
typed on those very arcs), then
\[
 \boxed{0\le\mathcal W(\mathcal S)
 \le D_h(A,B)=\mathcal W(\Gamma_h(A,B)).} \tag{6}
\]
The multiplicative constant is exactly **1**, independent of \(h\),
marking size, period, and depth **conditional on the stated inclusion
at each stage**; this theorem does not assert the inclusion at
any KKL stage. Constant 1 is optimal for unrestricted curve
subfamilies (take the entire \(\Gamma\)), and the preceding inequality
is not a lower bound on \(\mathcal W(\mathcal S)\).

*Proof.* Use the extremal-width convention
\(\mathcal W(\Gamma)=\inf_{\rho\ge0}
\{\int_{C_h}\rho^2:\int_\gamma\rho\,ds\ge1
\text{ for every }\gamma\in\Gamma\}\).
Every admissible density for the **larger** family \(\Gamma\) is
admissible for \(\mathcal S\). Thus the infimum for \(\mathcal S\)
is no larger. The standard mixed condenser identity (with outer
boundary free) gives the equality in (6). No deck or dynamical
transport is used. \(\square\)

**No positive universal converse, even with true inclusion.**
The archive's actual holomorphic quadratic slit/attachment family
[near-saturation Wave](../kkl_near_saturation_holomorphic_wave_20261107.md)
has, under its explicitly **refined six-atom marking**, an admissible
source marked semicircle packet
\(S_+=\{\gamma_r:d/2<r<h/2\}\subset\Gamma_h(A,B)\) when
\(d=\pi-\ell<h\). Its exact width is
\(\pi^{-1}\log(h/d)\). Restrict further to the valid nonempty
subpacket \(d/2<r<(d/2)e^\delta\) with
\(0<\delta<\log(h/d)\). This remains a genuine marked Wave, and
\[
 \mathcal W(S_{+,\delta})=\delta/\pi\longrightarrow0,
 \quad\text{while}\quad
 D_h(A,B)\ge 2\log(h/d)/\pi>0. \tag{7}
\]
For any proposed \(c>0\), choose
\(\delta<2c\log(h/d)\); then
\(\mathcal W(S_{+,\delta})<cD_h(A,B)\).
Hence **even shared electrode incidence and containment cannot provide
\(cD_h\le \mathcal W(S)\)** without a quantitative wave-family
richness/coverage hypothesis. This holomorphic countercontrol has a
deliberately refined marking and is **not** a prime-primitive KKL
proof-selected canonical WAD stage.

**First documented physical native failure of an *unrestricted*
comparison.** In PR #68's genuine original marking take
\(h=1/1024\), \(S_{\rm full}\), and \(S_h\). The verifier establishes
strictly, in exact rational enclosures,
\[
 \frac1{25}<\mathcal W(S_{\rm full})<\frac1{20},\qquad
 \frac{3h}{5}<D_h(\ell_X)<\frac{6h}{5},\qquad
 \frac h7<\mathcal W(S_h)<\frac h6.
 \tag{8}
\]
Therefore
\[
 \boxed{\mathcal W(S_h)<D_h(\ell_X)
 <\mathcal W(S_{\rm full}).} \tag{9}
\]
The naive claims
\(\mathcal W(\text{every native Wave})\ge D_h\) and
\(\mathcal W(\text{every native Wave})\le D_h\) **both fail**
already at this documented *physical period-three tip*. The failures
are **not** counterexamples to (6), KKL Lemma A.11, or canonical WAD
maximality: **the failed hypotheses are common surface and
deck-opposed electrode incidence**, and the original marked Wave is
not shown to be a proof-selected canonical WAD. This is the first
such **documented witness used here**, not a claim of minimal period
among all possible native examples.

## 3. Certified finite response brackets: fixed tip and thin collars

For the full free-outer condenser (5), the archive proves by a
uniform-charge Neumann response and radial/angular competitors
\[
 \boxed{
 \left[\frac{\pi}{2h}
 +\frac4\pi\bigl(\tfrac32+\log(1+2/\ell)\bigr)
 \right]^{-1}
 \le D_h(\ell)\le\frac{2h}{\pi-\ell}.} \tag{10}
\]
Briefly, the normalized opposite flat electrode charges have response
\(R=(4/\pi)\sum_{n\ge1,\ n\ {\rm odd}}
\coth(nh)\operatorname{sinc}^2(n\ell/2)/n\).
Cauchy–Schwarz gives \(D\ge1/R\). Use
\(\coth x\le1+1/x\), the odd Basel sum
\(\sum_{n\ {\rm odd}}n^{-2}=\pi^2/8\), and
\(\sum_{n\ {\rm odd}}\operatorname{sinc}^2(n\ell/2)/n
\le 3/2+\log(1+2/\ell)\): split at
\(N=\lceil2/\ell\rceil\), bounding the tail by
\(2/(\ell^2N^2)\le1/2\). An angular-linear voltage
on the two gaps gives the upper bound. These steps are a *written
continuum proof*, not a PDE assertion produced by the verifier.

The following rows put **a real native tip benchmark** (2) next
to **independently measured full condenser models**. All inequalities
are rigorous **open rational enclosures**, for each
\(h\in\{1/1024,1/2048,1/4096\}\); no displayed interval is a
floating-point estimate of the true minimizer.

| Electrode model | Native physical benchmark (target) | Dirichlet response (source/model) | Proven limit of \(D_h/h\) |
| --- | --- | --- | --- |
| Physical fixed tip access \(\ell=\ell_X\) | \(\mathcal W(S_h)=h/(2\pi)\) | \(3h/5<D_h<6h/5\) | \(2/(\pi-\ell_X)\) |
| Polynomial control \(\ell=h^2\) | same real \(S_h\) | \(h/2<D_h<2h/3\) | \(2/\pi\) |
| Critical control \(\ell=e^{-1/h}\) | same real \(S_h\) | \(h/4<D_h<2h/3\) | \((\pi/2+2/\pi)^{-1}\) |
| **Literal archive negative control** \(\ell=(h/4)e^{-1/h^2}\) | same real \(S_h\) | \(h^2/2<D_h<4h^2\) | **0** |

**Typing guard:** Only the first row uses the **physical attached
arc** \(A_X\). For the other three rows the source electrodes
\(\ell(h)\) are **formal annular controls**; the archive does not
realize them as KKL attached blocks with their own original marked
Waves. The benchmark \(S_h\) remains the *same actual tip Wave*
throughout, not a fictitious native Wave of the formal cylinder.
The last column uses the *already proved written condenser limits*
in the two 2026-11-07 archive notes; the finite verifier checks
**only the displayed finite strict brackets**, not continuum limits.

For clarity on the last control, the half-disk test potential with
\(\rho=h/2\) gives the stronger exact expression
\[
 D_h((h/4)e^{-1/h^2})
 \le\frac{\pi}{\log2+1/h^2}
 =\frac{\pi h^2}{1+h^2\log2},\qquad
 D_h/h\le\frac{\pi h}{1+h^2\log2}\to0. \tag{11}
\]
The opposite charge bound (10), using
\(\log(1+2/\ell)<\log3+\log(1/\ell)\), gives the
stated lower certificate \(D_h>h^2/2\) at the three
finite heights. The critical and polynomial brackets follow from
(10) and the same exact rational log bounds. In contrast,
\(\mathcal W(S_h)/h=1/(2\pi)\) is constant. **No contact-resistance
crossover law is inherited by this unmatched Wave family.**

The exponentially small-angle crossover
\(h\log(1/\ell)\to C\) belongs solely to (5): its
asymptotic \(D_h/h\to(\pi/2+2C/\pi)^{-1}\) requires
**actual shrinking source electrodes**, and never follows
from the KKL marking length or the existence of a Wave by itself.
For fixed \(\ell_X\), the thin limit is
\(2/(\pi-\ell_X)\), not \(2/\pi\). The angular length
(4) has not been shown to shrink with any iterated period/depth.

## 4. Exact finite checker, scope, and hostile-review guards

Run from the repository root:
\[
\texttt{python research/independent\_audits/wave\_vs\_dirichlet\_contact\_transfer\_20261115/verify.py --check-manifest}.
\]
The new checker **independently recomputes** the physical critical
orbit at outward dyadic precision \(2^{-256}\) from the immutable PR #68
parameter enclosure; tests \(x_3,x_6\), cos-angle bounds, the
certified whole physical collar and the original wave's marking,
width formulas and restriction count. It uses exact
\(\mathbb Q\) operations for Machin's \(\pi\), alternating
Taylor bounds on \(\cos\), and the positive atanh
series with a closed tail bound for \(\log\). It verifies every
strict inequality in (8), (9) and the finite rows of the table,
then checks the deterministic
[results manifest](../../../results/wave_vs_dirichlet_contact_transfer_20261115.json).
No floating point is used in the verifier. The three heights
are certified via one analytic whole-collar bound for every
\(0<h\le1/1024\), not three sampled collars.

**Hostile-review checklist and proof boundaries.**

- **Conformal units:** target \(\log r\) and source \(\log|w|\)
  are different charts; capacity and Width use the same reciprocal
  extremal-length convention; no unjustified modulus swap.
- **Geometry:** verified source \(T'\) and complete \(X\) boundary;
  no assumed exact Chebyshev conjugacy of \(G\); no degree-eight fibers;
  full collar lies inside the central \(V_3\).
- **Functional analysis:** (6), (10), (11), the condenser/width identity,
  and the two rectangle formulas are **written analytic proofs** with
  known classical variational inputs, not machine theorems.
- **Canonicality:** an admissible marked lamination induces a valid
  WAD, **not** automatically the maximal canonical WAD. Even the
  source's maximality estimate \(W_{\rm valid}(\alpha)
  \le W_{\rm can}(\alpha)+2\) does not certify a positive canonical
  weight from the tip packet of width below \(1/20\).
- **Finiteness:** rational interval results are rigorous; there are
  **no numerical-only observations** in the manifest.
- **Uniformity:** (6) has constant 1 whenever inclusion is
  *independently established*. Nothing proves original-marking
  electrode incidence, a uniform reverse constant, bounded
  distortion through the actual immersion, or \(h,\ell\) bounds
  along any large-rotation KKL period/depth sequence.

**Proved:** universal conditional monotonicity (6), absence of a
general positive converse (7), and explicit strict separation
(9) at a genuine original-marked physical tip using the archive's
source-dependent analytic geometry. **Finite-certified:** dyadic
source parameters and whole-collar safety, angular electrodes,
exact rational bounds and harmonic-series equalities. **Numerical
only:** none. **Open:** comparison for the actual *canonical,
proof-used* KKL Wave/WAD at prime-primitive stages; whether those
Waves have two opposed electrode endpoints; source-defined
access/modulus estimates in a parabolic tail; any stage-uniform
two-sided comparison or critical-return conclusion. No claim of
independent specialist review, mathematical priority, or MLC is made.

Primary mathematical source: Kahn–Kapiamba–Lyubich,
*MLC for parabolically bounded primitive renormalization*,
[arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1),
§2.5, §6.1 and Appendix A. Classical ingredients are conformal
extremal width and mixed condenser capacity, Joukowski
uniformization, potential-theoretic charge duality, and
Dirichlet's principle. Synthesis and finite checks were prepared
with assistance from OpenAI GPT-6.
