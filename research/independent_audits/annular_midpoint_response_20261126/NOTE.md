# Annular midpoint response: controlled scalar elimination on a physical neck

**Date:** 2026-11-26. **Target:** H2_RESPONSE_REALIZATION, clause 10 of [network_response_state.md §6](../../mlc_unified/network_response_state.md#6-analytic-response-realization-theorem), and clause 3 (actual itinerary elimination). **Status:** partial written analytic theorem for genuine annular collars and an actual selected-family application. The canonical gate remains OPEN. Base main commit: e894b7af96659859908ddd75d7c8f4d5d4a88d84.

**Claim:** Imposing an unknown constant potential at the middle of an embedded conformal annulus of logarithmic length L, and then eliminating that scalar, increases the actual terminal Dirichlet response by at most the sharp trace-operator factor coth²(L/2). For bounded whole-electrode data the error is also at most 2π csch(L) times squared oscillation. If one end is already a constant electrode, the factor improves to 1+sech(L) and the additive constant to (π/2)csch(L). This is an approximation theorem for the original, unconstrained problem, not an assertion that its true minimizing trace is constant.

The previous [whole-boundary response theorem, §3.5 and clauses 3, 10](../whole-boundary-response_20261126/NOTE.md) controls exact constant-electrode operations, but does not justify imposing that condition on a physical analytic neck. [Research Push IV](../../mlc_research_push_4_bundle/mlc_research_push_4.md) treats full-trace Neumann-wall rectangle operators and their trace-renormalized comparison; the existing scalar-neck no-go correctly precludes exact constant-mode substitution in general. Here the new operation is a variational **constraint on one interior cross-section**, retaining both real half-necks and all modes at their outer ends. No trace energy is deleted. The error is one-sided, sharp on the unrestricted trace space, and survives arbitrary surrounding geometry and terminal minimization. We do not assert priority over classical Fourier/cylinder estimates.

## 1. Precise setup and theorem

Let S be a connected compact bordered Riemann surface, with analytic boundary, and nonempty prescribed labeled constant Dirichlet electrodes on its boundary. One may leave other boundary components free, provided the variational problem is over H¹ and has a minimizer. In the actual application every boundary component is a prescribed electrode. Write x for real terminal potentials, and E_full(x) for the infimum of the conformally invariant Dirichlet energy ∫|∇u|² (no factor 1/2).

Suppose there is a conformally embedded closed annular collar, analytic at its two seams, whose interior contains no electrodes, punctures, side ports, or obstacles; an end circle may itself be an actual boundary electrode. Its coordinate is the flat cylinder [0,L]×(R/2πZ), L>0, with energy ∫₀ᴸ∫₀²π (u_t²+u_θ²)dθdt. For a round annulus r≤|z|≤R the coordinate is t=log(|z|/r), L=log(R/r)=2π mod(A). Only the conformal coordinate is required; it need not be a round annulus in the original plane. Assume that the collar is embedded with the indicated trace identifications, so replacing the function on it without altering its two end traces defines an admissible global H¹ function (standard Sobolev trace gluing across the analytic seams). No assumption on the topology, response or conformal shape of the remaining pieces is made.

Define E_cut by the same global minimization, with the added condition that the trace at t=L/2 is a constant m∈R, *not prescribed*. If the seam separates two pieces, the constrained problem is exactly a scalar-node gluing of the responses of the actual pieces including their half-collars; if not, the two seam copies of the cut piece have the same unknown constant. Nothing is removed from the physical surface. In both cases this is a genuine variational minimization, not a relabeling of an arbitrary trace.

**Theorem 1 (single seam).** For all x,

    E_full(x) ≤ E_cut(x) ≤ coth²(L/2) E_full(x).                  (1)

If one annular end is a prescribed constant electrode, then

    E_full(x) ≤ E_cut(x) ≤ (1+sech L) E_full(x).                  (2)

For whole-electrode potentials x, with osc(x)=max x_i−min x_i,

    0 ≤ E_cut(x)−E_full(x) ≤ 2π csch(L) osc(x)²,                 (3)

and if one end is a constant electrode the right side is (π/2)csch(L) osc(x)². The additive estimates use bounded Dirichlet data and clipping, unlike (1)–(2) which apply already to arbitrary H^(1/2) end traces (one constant for (2)). The inequalities also hold for infima if minimizers are not used, by clipping a minimizing sequence. The constraints are nonempty by the collar construction below. The relative constants in (1)–(2) are sharp for arbitrary end traces (not necessarily for constant-electrode exterior problems).

## 2. Exact Fourier proof, including sharpness

Use the real orthonormal basis 1, √2 cos(nθ), √2 sin(nθ) for the normalized angular measure dθ/(2π). Let a₀,b₀ be the two end means, a,b the real coefficients of a fixed sine or cosine of frequency n≥1. In this normalization the mean-mode energy is 2π(b₀−a₀)²/L. The uncut harmonic interpolant at frequency n solves v''=n²v with endpoints a,b:

    v(t) = [a sinh(n(L−t))+b sinh(nt)]/sinh(nL).

Integrating (v')²+n²v²=[vv']' gives the exact full-mode energy

    Q_n = 2π n [(a²+b²)coth(nL)−2ab csch(nL)].                  (4)

For a constant middle trace the nonzero coefficient there is zero. The two half-collars are independently harmonic, so

    Q_n^cut = 2π n coth(nL/2)(a²+b²).                           (5)

The scalar mean m minimizing the two half-collar mean energies is (a₀+b₀)/2, leaving the original mean energy exactly unchanged. With C=coth(nL), S=csch(nL), H=coth(nL/2), one has H=C+S, C−S=tanh(nL/2)=1/H. In particular

    Q_n^cut−Q_n = 2π n S(a+b)² ≥ 0.                              (6)

The eigenvectors of the full form are (1,1) and (1,−1); the eigenvalues after dividing by 2πn are C−S and C+S. Thus the quotient of (5) by (4) lies between 1 and H²≤coth²(L/2), and equality at the upper bound occurs for n=1, a=b≠0. Opposite signs a=−b give equality at the lower bound, a useful non-scalar countercheck. If b=0, the quotient is H/C=1+sech(nL)≤1+sech L, with equality at n=1. This proves the full-mode comparison by summation over both real modes per frequency. For H^(1/2) end data the sums converge, since for fixed L the coefficients grow at most linearly in n and the means are finite. Equivalently pass to the limit from finite Fourier sums in the trace norm; the explicit solutions converge in H¹ by the same estimates. The constructed middle trace is constant, including in this limit.

Let u be any admissible function on S. Its end traces on the collar are H^(1/2). Leave u unchanged outside and replace its collar restriction by the piecewise harmonic function just constructed. The original collar energy is at least the full harmonic interpolation energy, by Dirichlet minimization, and the replacement is at most the stated factor times the original collar energy. The outside energy is unchanged and nonnegative. Taking the infimum proves the upper estimates (1)–(2); the lower estimates follow by nesting of admissible classes. This argument permits arbitrary coupling between the exterior pieces and the trace variables: it uses the end traces of the original function, not independently chosen traces. It does not require spectral gap or equal kernels of some pre-existing approximate graph.

### 2.1. Uniform additive error

Clip any trial u to the interval [min x_i,max x_i], which does not increase energy or violate the prescribed constant values. Thus it suffices to work with bounded end traces a(θ),b(θ). Let D=osc(x). By Parseval the sum over all nonconstant real coefficients of (a+b)² in (6) is Var(a(θ)+b(θ)), where variance is relative to normalized angular measure. The range of that function has length at most 2D, so its variance is at most D²: subtract the midpoint of its range and use the fact that the mean minimizes squared error. If b(θ) is constant the variance is at most D²/4. For integer n≥1, sinh(nL)≥n sinh(L) (by induction using the addition law, or monotonicity of sinh(t)/t), giving n csch(nL)≤csch L. Consequently the sum of (6) is at most 2π csch L D², or (π/2)csch L D² in the constant-end case. Replacement of the collar costs at most this amount over the original energy. Taking the infimum proves (3). The clipping also works for mixed/free boundary conditions whenever the only prescribed data are the given constant electrodes.

### 2.2. Several disjoint collars and exact scalar operations

For a finite family of collars with disjoint interiors and disjoint middle seams, do all replacements using the original end traces. Shared end circles, if any, retain their original traces. Let k_j be the factor in (1) or (2) applicable to collar j, and C_j the corresponding additive coefficient from (3). With E_many the response imposing a constant on every middle seam, the preceding proof gives simultaneously

    E_full ≤ E_many ≤ (max(1,max_j k_j)) E_full,
    0 ≤ E_many−E_full ≤ (sum_j C_j) osc(x)².                      (7)

The relative factors do not multiply, because the modifications occupy disjoint interiors and the original energy is additive there. All unknown scalar seam values are eliminated by a single constrained Dirichlet minimization. If the pieces are disconnected after cutting, fixed scalar traces on their boundary copies permit independent minimization on the pieces. The response of each actual piece is a finite whole-electrode form when all its remaining boundaries are whole-component constant electrodes (free boundaries may instead be minimized). Without that condition, further trace spaces must still be retained.

For a finite sequence of disjoint-collar constraints and ordinary constant-electrode eliminations with free terminal node values, the same multiplicative bounds survive taking infima of both sides over those same free node values. The additive estimate survives also: clip all free values to the external terminal range, using clipping of admissible physical functions. Parallel sums preserve the sum of additive errors. No claim is made about overlapping necks, welding which changes the trace spaces, endpoints not given by actual collar coordinates, or dynamic successive identifications with nonconstant boundary values. In particular if L_j→∞, additive error summability follows from ∑exp(−L_j)<∞, not merely from L_j→∞; infinite networks/limits require additional compactness and compatible domains.

## 3. Application to the actual selected real primitive tips

Use the actual four-boundary slit surface from the [selected-family canonical exclusion, §1](../canonical_width_attack_20261124/NOTE.md) and [whole-boundary response, §4](../whole-boundary-response_20261126/NOTE.md):

    Y_p = D(0,R_p) \ (K_0 ∪ K_1 ∪ K_2),
    K_0=[X_3,X_6], K_1=[X_4,X_1], K_2=[X_2,X_5],
    X_j=−A_p x_{jp}, R_p=|A_p|2^(−p), p≥13.

Here A_p, x_j and c_p are exactly those in the [all-period actual realization theorem](../real_primitive_tip_family_all_p_20261116/NOTE.md), with its chart, prescribed signed orbit, strict orders (O1),(O2), coefficient bounds (9), and equation (19). The three slits lie inside |z|<2 since |X_1|=|τ|<2 and (O2). The coefficient estimate gives

    (3/20)2^p < R_p < (17/100)2^p.

The normalized surface is the actual geometric surface, with both banks of each slit joined at its tips in the analytic square-root boundary charts as in the preceding proof. Its outer circle is ordinary analytic boundary. The coordinate rescaling is conformal, with no change in energy. Hence A_p^neck={2<|z|<R_p} is an actual free, obstacle-free annulus ending at the constant outer electrode. (The superscript neck distinguishes it from the real coefficient A_p.) No conjectural pullback, component identification, or hypothetical collar is used. Put L_p=log(R_p/2)>(p−4)log 2.

Set s_p=√(2 R_p). Cut at |z|=s_p, and retain the exact whole-component response of the inner slit disk D(0,s_p)\(K_0∪K_1∪K_2), writing it as F_p(y,m) for three slit potentials y and seam value m. The outer annulus between s_p and R_p has constant end values, length L_p/2 and conductance 4π/L_p. For original outer value x_out the exact constrained response is therefore

    E_cut,p(y,x_out) = min_m [F_p(y,m)+(4π/L_p)(m−x_out)²].         (8)

This is a four-terminal inner response with one scalar elimination, not an approximation to the inner response itself. Existence of the minimizer follows from the positive outer conductance and nonnegative finite quadratic F_p. Theorem 1 now gives for every four-electrode potential x,

    E_full,p(x) ≤ E_cut,p(x) ≤ (1+sech L_p) E_full,p(x)
                             < (1+2^(5−p)) E_full,p(x)           (9)

for nonconstant x (the non-strict inequality holds also for constant x). Indeed sech L_p < 2e^(−L_p) = 4/R_p < (80/3)2^(−p)<2^(5−p). The additive error is at most (π/2)csch(L_p) osc(x)². Thus this replacement is uniformly controlled even on degenerating eigen-directions, with no spectral floor assumption. This is an actual-family improvement over merely permitting scalar gluing when a trace is independently constant. It does not turn the canonical WAD into the inner response: the whole-component canonical WAD is zero on Y_p and generally loses information, as proved in the cited earlier work.

### 3.1. Sharp leading outer-electrode energy asymptotic

There is also a two-sided leading asymptotic for the degenerating outer mode, sharpening the earlier upper estimate alone. Write e_out=(0,0,0,1) in slit/slit/slit/outer order and let T_p=E_full,p(e_out). The explicit radial trial function, zero inside radius 2 and log(|z|/2)/log(R_p/2) outside, gives

    T_p ≤ 2π/log(R_p/2).

For the lower estimate, the all-period realization proof directly after (19) encloses the whole real interval [w_4,−w_3] in [−9/5,−1/10], where w_j=A_p x_{jp}=−X_j. Thus w_3≥1/10, and the exact relation w_6=−w_3 implies K_0=[−w_3,w_3] contains J=[−1/10,1/10]. Fill the other grounded slits with value zero. More precisely a function of trace zero on both banks extends by Sobolev gluing across the slit interior; its endpoint singularities are removable for H¹ with finite energy, e.g. by logarithmic cutoffs (a point has zero planar H¹ capacity), after clipping to [0,1]. This produces an admissible trial on D(0,R_p)\J with no extra energy. Grounding more material cannot reduce the condenser energy. Extending by value one outside the radius R_p to any larger enclosing ellipse preserves admissibility and adds zero energy.

The explicit Joukowski map z=(1/20)(w+w^(−1)) conformally identifies |w|>1 with the exterior of J: the two quadratic roots have product one, and off J exactly one has modulus greater than one, while |w|=1 maps onto the slit. On |w|=s>1 its image is an ellipse of semiminor (s−1/s)/20. Taking s=20R_p+1 gives semiminor > R_p, so the ellipse contains the disk. On the ellipse minus J the exact condenser energy is 2π/log(s), by the cylinder mean mode or radial minimization. This yields

    2π/log(20R_p+1) ≤ T_p ≤ 2π/log(R_p/2).                      (10)

Equivalently T_p=2π/log R_p+O((log R_p)^(−2)), with absolute constants for p≥13. From the existing two-sided coefficient estimate, log R_p=p log 2+O(1), so

    T_p = 2π/(p log 2) + O(p^(−2)),
    lim_(p→∞) p T_p = 2π/log 2.                                  (11)

All asymptotic estimates concern a sequence of separate actual polynomials, not a single renormalization tower. The new lower bound uses the physical central slit and exact annular model; it is not inferred from positivity of finite matrices. The statement is for the outer test vector, not an equality for the smallest eigenvalue of the full response. The constants in (10) need not be sharp at the second order.

## 4. Adversarial audit and exact limits

* A scalar seam is not an equipotential identity for the unconstrained harmonic minimizer. Matching nonzero first modes attain the full trace-operator loss, so an exact scalar replacement would be false. Both half-collars retain the nonconstant energy paid by the original ends.
* An abstract annulus modulus without an actual embedded, unobstructed collar does not justify (8). The ordinary collar/no-go results and pulled-equipotential mismatch remain unaffected. The selected physical outer neck satisfies the hypotheses by strict radial containment; no analogous universal existence is established for dynamic internal necks.
* Formula (7) is a simultaneous estimate for pairwise disjoint interiors, not a substitute for the no-bypass and overlap audits in a marked itinerary. No rate for the number of collars, no summability of all physical errors and no future-closed finite port space is proved.
* Whole-boundary energy does not encode returning classes, multiplicities, lift defects or Value. The inner response in (8) is the actual analytic response and is not estimated multiplicatively by the zero WAD. H2 calibration, H3 coercivity, H4 rigidity and MLC remain open. No changes to ledger statuses, source theorem status, or proof dependencies are asserted.
* The Fourier proof uses only ordinary Sobolev trace/gluing, Parseval, harmonic minimization and explicit elementary identities. The Joukowski and radial computations are given explicitly. Prior selected-family geometric and rational interval bounds are consumed as written, not independently reproved here. No disputed KKL §6 step or external source audit is used.

## 5. Reproduction, provenance and attribution

From repository root:

    python -B research/independent_audits/annular_midpoint_response_20261126/check_neck.py
    python -B code/verify_physical_bridges.py

The standard-library checker uses exact rational t=exp(−nL) substitutions, so the hyperbolic ratios are rational functions. It tests the exact mode identity, sharp factors, opposite-mode equality, n csch(nL) bound, finite variance/series regressions, and physical radius and ellipse inequalities. In the local Python run all 2,940 mode cases, 625 variance cases, 225 scalar series cases and 88 radius cases passed. Those are arithmetic regressions, not a formal verification of Sobolev gluing, analytic realization or the universal inequalities, which are proved above. A full local checkout was not available; repository-wide bridge validation is delegated to the proposed read-only workflow, and must be inspected separately. No external PDF or source-byte verification is claimed.

The exact ledger target was checked in ledger.json, and the relevant predecessor notes, all-period realization, canonical exclusion, BC1 and Push IV trace formulas were inspected at the base commit. The repository is large and concurrent, so this is not an exhaustive audit of every dependency or a priority claim. The existing RESPONSE route is registered with this checker; it remains conditional at the global level. No new ledger or bridge-index standing theorem is added.

Credit Matthew Robert Wesney and the archive's prior actual-parameter, physical-surface and response work; credit the classical Dirichlet, Fourier and Sobolev methods and Joukowski transformation used above. OpenAI ChatGPT GPT-6.2 materially assisted repository inspection, proof derivation, adversarial checks, test construction and drafting. No human specialist verification or peer review has been performed. MLC remains open.
