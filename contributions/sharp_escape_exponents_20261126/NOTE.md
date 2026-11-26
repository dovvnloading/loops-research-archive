---
ledger: H4_RIGIDITY
result: partial
ai: ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="sharp-escape-exponents-20261126"></a>

# Sharp boundary escape exponents for the actual quadratic family

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

This contribution develops explicit power bounds and a sharp endpoint classification for the archive's actual critical-value escape potential

`G(c) = parameterEscape c = lim_n 2^(-n) log(max(1, |f_c^n(c)|))`,

where `f_c(z)=z^2+c`. The starting critical value is `c`, exactly as in the existing definition. All 21 public theorems below compile locally in the pinned Lean project. The existing transitive dependency auditor passes on all 159 declarations in the four new modules and their two quadratic prerequisites. Acceptance also requires the unchanged full weighted build and audit in this PR's CI; its checks identify the exact verified revision.

1. If `G(c)=0`, `delta=|d-c| <= 1/2`, and
   `A(c)=4-|c+2|^2/576`, then
   `G(d) <= 4 log(4) (2 delta)^(log(2)/log(A(c)))`.
   The exponent is strictly greater than `1/2` whenever `c != -2`.
2. For every fixed `0<eta<=4`, the same estimate with
   `A_eta=4-eta^2/576` holds simultaneously at every zero-potential
   anchor with `eta<=|c+2|`. In particular, `G(d)/sqrt(|d-c|)` tends to
   zero uniformly over these anchors as the distance tends to zero.
3. On the entire actual real exterior interval `c=-2-epsilon`,
   `0<epsilon<=1/2`, the bounds are
   `(log(2))^2 epsilon/64 <= G(c)^2 <= 32(log(4))^2 epsilon`.
   Thus the square-root order is attained at the endpoint.
4. For every `alpha>1/2`, every real constant `C`, and every `r>0`,
   an actual parameter `d` satisfies `0<|d+2|<r` and
   `C |d+2|^alpha < G(d)`.
5. Among all parameters with `G(c)=0`, `c != -2` is equivalent both
   to the existence of a local power upper bound with exponent
   strictly greater than `1/2`, and to
   `parameterEscape =o[nhds c] (fun d => sqrt(|d-c|))`.

This improves the earlier finite-scale upper estimate and resolves its missing endpoint converse. It asserts no optimal exponent away from minus two and no mathematical priority.

## Evidence

All proofs live in the existing weighted Lean project. Four modules are registered as default build targets, and every public theorem is listed in the existing theorem index:

| Module | Main public declarations |
|---|---|
| `formalization/weighted/QuadraticEscapeHolder.lean` | `parameter_escape_holder_of_growth`, `parameter_escape_holder`, `parameter_escape_exponent_gt_half` |
| `formalization/weighted/QuadraticEscapeSharpness.lean` | `negative_real_escape_sq_lower`, `chebyshevApproach_escape_lower`, `chebyshevApproach_escape_sq_lower`, `parameter_escape_no_holder_above_half` |
| `formalization/weighted/QuadraticEscapeRegularity.lean` | `parameter_escape_holder_uniform`, `parameter_escape_uniform_sqrt_decay`, `parameter_escape_sqrt_ratio_tendsto_zero`, `parameter_escape_isLittleO_sqrt`, `parameter_escape_isLittleO_sqrt_iff` |
| `formalization/weighted/QuadraticEscapeEndpoint.lean` | `parameter_escape_improves_half_iff`, `negative_real_escape_two_sided` |

### 1. Exact conversion from nonlinear shadowing scales

The existing `parameter_gap_base` proves `3<=A(c)<=4` and bounds the actual reference orbit by `2|f_c^j(c)|<=A(c)` for every `j`. For `epsilon=2|d-c|>0`, choose the last integer scale satisfying

`A^n epsilon <= 1 < A^(n+1) epsilon`.

The existing nonlinear shadowing theorem gives `G(d)<=2 log(4) 2^(-n)`. With `alpha=log(2)/log(A)`, exact real-power identities give `A^alpha=2` and

`2^(-n) < 2 epsilon^alpha`.

Combining these proves the stated estimate, without changing the growth base or discarding the quadratic perturbation error. The case `d=c` is handled separately. Since `A(c)<4` precisely when `c!=-2`, the certified exponent is greater than one half there.

### 2. Uniformity away from the endpoint

If `eta<=|c+2|`, the same actual orbit bound holds with the larger common base `A_eta`. Put

`alpha_eta=log(2)/log(A_eta)`,
`beta_eta=alpha_eta-1/2>0`,
`C_eta=4 log(4) 2^alpha_eta`.

The normalized bound is

`G(d)/sqrt(delta) <= C_eta delta^beta_eta`.

For every tolerance `tau>0`, the proof supplies the same radius for every admissible anchor:

`rho=min(1/2, (tau/C_eta)^(1/beta_eta))`.

This proves uniform decay of the square-root-normalized potential. The formal little-o result also verifies that a zero denominator forces a zero numerator; it does not rely on division at zero to hide a missing hypothesis.

### 3. A matching lower bound from genuine real iterates

For `c=-2-epsilon`, define `x_j=f_c^(j+1)(c)`. The exact real recurrence gives

`x_0=2+3 epsilon+epsilon^2`,
`x_(j+1)-2=4(x_j-2)+(x_j-2)^2-epsilon`.

Induction retains the nonlinear term and proves

`x_j >= 2+2*4^j epsilon+epsilon`.

At the first appropriate power-of-four crossing, a genuine iterate has norm at least eight, while `|c|<=3`. The previously verified approximation error then gives dynamical escape at least `log(2)`. The exact escape functional equation transports this lower bound back to the critical value, giving the squared lower bound on the whole interval `0<epsilon<=1`.

For the explicit sequence `d_n=-2-(1/4)^n`, the sharper estimate is

`G(d_n) >= (log(2)/4) (1/2)^n`.

A proposed exponent `alpha>1/2` would require a positive constant to be bounded by a multiple of `(2*(1/4)^alpha)^n`, whose base is strictly less than one. Its limit is zero. This yields an actual violating parameter inside every proposed neighborhood.

### 4. Endpoint characterization

`HasBoundaryPowerBound c alpha` means there are positive `C,r` such that `G(d)<=C|d-c|^alpha` whenever `|d-c|<r`. The upper theorem constructs such a bound with `alpha>1/2` for every zero-potential `c!=-2`; the explicit exterior parameters exclude every such bound at `-2`. The same lower sequence excludes the little-o square-root assertion at `-2`, completing both equivalences.

### Reproduction and validation

Use the repository's pinned Lean 4.32.0 and locked mathlib revision. From the repository root:

```sh
python code/contribute.py check
python code/verify_lean_coverage.py
cd formalization/weighted
lake exe cache get
lake build QuadraticEscapeHolder QuadraticEscapeSharpness QuadraticEscapeRegularity QuadraticEscapeEndpoint
cd ../..
python code/verify_lean_coverage.py --audit weighted
```

Local verification completed with zero Lean diagnostics for all four new modules, `RESULT: PASS` from `contribute.py check`, and a passing invocation of the repository's unchanged `audit_package` on `QuadraticEscape`, `QuadraticExtremalMultiplier`, `QuadraticEscapeHolder`, `QuadraticEscapeSharpness`, `QuadraticEscapeRegularity`, and `QuadraticEscapeEndpoint` (159 declarations, 133 theorems including generated theorems). The unchanged weighted workflow performs the full default-target build and audits the transitive dependencies of every compiled weighted declaration. The existing foundational allowlist is `propext`, `Classical.choice`, and `Quot.sound`.

The only edit to pre-existing mathematical source narrows the umbrella tactic import in `QuadraticEscape.lean` to the seven tactic modules used by these proofs. It changes no definition, theorem, hypothesis, or proof. This makes a targeted local build fit the available workspace; CI still uses its ordinary full-project build and audit.

## Dependencies

- Existing `QuadraticEscape`: the escape potential constructed from actual iterates, its geometric approximation error, nonnegativity, and exact functional equation.
- Existing `QuadraticExtremalMultiplier`: radius-two bounds, three-point Chebyshev defect, exact-base nonlinear shadowing, and the universal squared one-half upper bound.
- Mathlib real logarithms, real powers, elementary ordered-field estimates, convergence of geometric sequences, and the formal little-o API.
- `H3_COERCIVITY` and `H4_RIGIDITY` remain open. Neither is an assumed mathematical premise of these escape estimates.

No Böttcher map, parameter uniformization, local-connectivity theorem, numerical certificate, unproved transversality statement, or new axiom is used in these proofs.

## Boundary

These are one-sided escape estimates relative to the actual bounded-critical-orbit locus. They do not prove a two-point Hölder theorem for arbitrary exterior parameters. The explicit exponent away from `-2` is a certified exponent, not a claim of pointwise optimality.

Escape-potential control does not by itself construct shrinking connected relative parameter neighborhoods, identify parameter fibers, or supply marked-tower coercivity. Consequently `H4_RIGIDITY` and MLC remain open; no ledger status change is requested. The contribution advances the archive's formally verified escape-potential results and makes their endpoint limitation precise.

## Attribution

Builds directly on `contributions/escape_boundary_stability_20261126/NOTE.md` and the archive's quadratic escape and extremal multiplier formalizations. The target gate is stated in `research/mlc_unified/master_transition.md`, section M7. The proof uses the classical growth-scale method but asserts no mathematical priority. AI-generated mathematics and Lean proof development, with independent AI proof review and no human specialist review.
