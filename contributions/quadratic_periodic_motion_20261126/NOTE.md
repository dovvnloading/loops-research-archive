---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-periodic-motion-20261126"></a>

# Constructed periodic motion and critical-relation parameter coordinates

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

This contribution constructs local analytic periodic motion and local analytic parameter coordinates for the **actual quadratic family**. It removes the moving-periodic-point existence premise from the archive's first-collision entrance argument. It also constructs an explicit nonvanishing analytic factor relating that entrance coordinate to the original critical-relation polynomial, and proves exact-period and multiplier-type persistence for each selected cycle.

Write

\[
f_c(z)=z^2+c,\qquad P_n(c)=f_c^n(0).
\]

The four registered Lean modules contain 15 public theorem declarations. The principal result is `LoopsQuadraticCoordinates.first_collision_parameter_coordinate`. For arbitrary natural numbers `a < b`, assume only

\[
P_{a+2}(c_0)=P_{b+2}(c_0),\qquad
P_{a+1}(c_0)\ne P_{b+1}(c_0).
\]

Put `m=a+2`, `p=b-a`, `z0=P_m(c0)`, and

\[
\lambda=(f_{c_0}^p)'(z_0),\qquad
\Delta=P_{b+2}'(c_0)-P_{a+2}'(c_0).
\]

The theorem constructs a single analytic periodic branch `zeta`, its entrance displacement `E(c)=P_m(c)-zeta(c)`, an analytic local inverse `psi`, and the explicit factor `Q` described below. It proves:

1. `zeta(c0)=z0` and `f_c^p(zeta(c))=zeta(c)` near `c0`.
2. `E(c0)=0` and `E'(c0)=Delta/(lambda-1) != 0`.
3. `psi(0)=c0`, `psi'(0)=(lambda-1)/Delta`, with both inverse identities `psi(E(c))=c` and `E(psi(t))=t` on neighborhoods of their base points.
4. `Q` is analytic near `c0`, `Q(c0)=lambda-1`, and `Q(c)!=0` throughout a neighborhood.
5. On a neighborhood of `c0`, the exact identity is

   \[
   P_{b+2}(c)-P_{a+2}(c)=E(c)Q(c).
   \]

6. Locally, `P_(b+2)(c)=P_(a+2)(c)` is equivalent to `E(c)=0`, which is equivalent to `c=c0`.

The inverse and factorization in this principal theorem use the **same** periodic motion. There is no assumed analytic branch, assumed chart, assumed nonzero entrance derivative, or imported unformalized dynamical realization in its hypotheses. This is a local analytic ingredient of the open H4 program, not a proof of H4 or a new MLC parameter class.

## Evidence

### 1. Actual periodic-point motion

[QuadraticPeriodicMotion.lean](../../formalization/weighted/QuadraticPeriodicMotion.lean) first proves joint complex analyticity of the existing actual return iterate `returnOrbit c z p`. It applies Mathlib's analytic implicit-function theorem to

\[
F(c,z)=f_c^p(z)-z.
\]

The partial derivative in the point variable is proved to be multiplication by `returnMultiplier c z p - 1`. When this number is nonzero, `periodic_point_motion` constructs the branch, proves its local uniqueness in **both variables**, and computes its derivative:

\[
\zeta'(c_0)=
-\frac{\partial_c f_c^p(z_0)|_{c=c_0}}{(f_{c_0}^p)'(z_0)-1}.
\]

The numerator is the archive's explicit `returnTangent c0 z0 0 p`, already identified with the actual parameter derivative. The derivative formula follows from the constructed analytic branch and the exact tangent recurrence, rather than being included among the assumptions.

`integral_parameter_periodic_point_motion` removes the multiplier premise for every positive-period point at an algebraic-integer parameter. Its proof uses the existing `QuadraticMultiplierArithmetic` theorems: periodic points at integral parameters are integral, and their positive-iterate multipliers cannot have modulus one. `collision_parameter_periodic_point_motion` applies this to every periodic point at every critical-collision parameter, including cycles outside the critical orbit.

### 2. An explicit analytic factor with no division singularity

[QuadraticCollisionFactorization.lean](../../formalization/weighted/QuadraticCollisionFactorization.lean) defines

\[
S_0(c,x,y)=1,
\]
\[
S_{n+1}(c,x,y)=
\bigl(f_c^n(x)+f_c^n(y)\bigr)S_n(c,x,y).
\]

It proves, for all parameters, points and horizons,

\[
f_c^n(x)-f_c^n(y)=(x-y)S_n(c,x,y),
\qquad S_n(c,z,z)=(f_c^n)'(z).
\]

This is a polynomial construction that remains defined and jointly analytic on the diagonal. It never divides by `x-y`.

For a constructed periodic motion, set

\[
Q(c)=S_p\bigl(c,P_m(c),\zeta(c)\bigr)-1.
\]

The exact iterate-difference identity and periodicity give `P_(m+p)-P_m=E Q`. The diagonal identity gives `Q(c0)=lambda-1`; continuity then proves local nonvanishing. `first_collision_analytic_factorization` constructs this factor directly from the critical-collision hypotheses and proves that the displacement has nonzero derivative.

### 3. Genuine analytic inverse coordinates

[QuadraticCriticalCoordinates.lean](../../formalization/weighted/QuadraticCriticalCoordinates.lean) combines the constructed motion with the existing `landing_motion_identity` and `first_collision_transverse`. The identity gives

\[
\Delta=(\lambda-1)E'(c_0).
\]

The already proved first-collision derivative is nonzero. Hence the entrance derivative is nonzero, and the complex analytic inverse-function theorem constructs `psi`, its analyticity, its reciprocal derivative, and both local inverse identities.

The local uniqueness statement from the implicit-function theorem is pulled back along the actual critical-orbit graph `c -> (c,P_m(c))`. This proves that the original critical relation is exactly the zero-coordinate condition. The inverse identity isolates that zero. The final theorem also applies the explicit factor construction to this same motion.

The companion `center_parameter_coordinate` uses the existing all-period center transversality to construct a local analytic inverse of `P_(n+1)` at every zero. The positive return time need not be the minimal critical period.

### 4. Exact period and multiplier type

[QuadraticPeriodicStability.lean](../../formalization/weighted/QuadraticPeriodicStability.lean) proves joint analyticity of the actual return multiplier. If a selected point has minimal positive period `p` and its specified return multiplier differs from one, its constructed motion retains the actual `Function.minimalPeriod` equal to `p` near the base parameter. This follows by simultaneously preserving the finitely many nonreturn inequalities for `0 < k < p`.

The multiplier along the motion is analytic. Therefore a strict attracting inequality or strict repelling inequality persists. At an algebraic-integer parameter, arithmetic excludes the neutral case; `integral_parameter_periodic_point_stability` proves local equivalence of the attracting/repelling classifications and absence of neutral multipliers on that selected branch. It does not infer repellingness from nonneutrality.

### Reproduction and validation

Use Lean 4.32.0 and the repository's locked Mathlib revision. From the repository root:

```sh
python code/contribute.py check --pr-title '[H4_RIGIDITY] Lean: construct local periodic motion and critical-relation coordinates'
python -B code/verify_lean_coverage.py
cd formalization/weighted
lake exe cache get
lake build QuadraticPeriodicMotion QuadraticCollisionFactorization QuadraticCriticalCoordinates QuadraticPeriodicStability
cd ../..
python -B code/verify_lean_coverage.py --audit weighted
```

All four new modules built locally, and the unchanged transitive auditor accepted all 41 declarations in them, including private helpers and generated declarations. The four modules are default targets, every public theorem is registered, and the existing CI builds the complete weighted project and audits the transitive axiom dependencies of its compiled declarations. The auditor allows only `propext`, `Classical.choice`, and `Quot.sound`; no new axioms or proof holes are introduced. No workflow, proof-trust policy, or status record is changed. The exact-revision acceptance record is the full weighted build and axiom-audit check attached to [PR #222](https://github.com/dovvnloading/loops-research-archive/pull/222); local compilation alone is not substituted for that record.

The earlier three-module checkpoint `d957101480f6d4ab01cddff1a21f60bed4e0e9b2` passed the [full weighted CI build and transitive audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45908113020/job/140209686435): 113 weighted modules and 2,857 declarations. The later explicit-factor module and strengthened coordinate statement require the current PR revision's own CI result; the earlier run is not claimed as verification of later source.

The PR was opened at the initial target-selection checkpoint. Subsequent proof milestones and the integration of the concurrently merged main-branch registration changes are preserved as commits in the same PR.

## Dependencies

- `QuadraticCriticalTransversality.lean`: the actual orbit and derivative recurrences, integrality of critical-collision parameters, center and first-collision transversality, and the exact moving-point tangent identity.
- `QuadraticMultiplierArithmetic.lean`: periodic-point integrality and exclusion of neutral multipliers at integral parameters.
- Mathlib's [analytic implicit-function theorem](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Calculus/ImplicitContDiff.lean), [analytic inverse-function theorem](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Calculus/InverseFunctionTheorem/Analytic.lean), complex calculus, neighborhood filters, and actual iteration/minimal-period API.
- `H4_RIGIDITY` remains open, as does its `H3_COERCIVITY` prerequisite. Neither is a premise of these local theorems.

## Boundary

The theorem gives local analytic coordinates in the ambient complex parameter plane. It does not construct connected relative neighborhoods in the Mandelbrot set, a uniform phase-parameter transfer, protected-tower coercivity or rigidity, or a proof of H4, UPTCR, or MLC. No ledger status change is requested.

The collision theorem's return length `b-a` need not be minimal. Exact-period persistence has its own explicit minimal-period hypotheses. The neighborhood depends on the selected periodic point and return length; no common radius over all cycles or unbounded periods is proved. Nearby parameters need not be algebraic integers: the local type conclusion there is obtained by continuity, not by misapplying the arithmetic theorem.

The affine moving-point coordinate `z-zeta(c)` and its critical entrance are not a Koenigs linearization. The branch and inverse are represented by total Lean functions, but their dynamical and inverse identities are asserted only on the specified neighborhoods. No global continuation, global structural stability, or repellingness of every postcritical landing is claimed.

These results advance the archive's formal analytic interface. The underlying implicit/inverse-function mathematics is classical; no worldwide novelty or mathematical priority claim is made.

## Attribution

Builds directly on the archive's critical-transversality formalization and [arithmetic multiplier contribution](../h4_arithmetic_multiplier_rigidity_20261126/NOTE.md). The broader dynamical context belongs to the classical complex-dynamics literature; the present proofs use the cited Lean developments and Mathlib, not an unverified invocation of a global dynamical theorem. Mathlib's source headers credit the formal implicit- and inverse-function theorem contributors, including Winston Yin, Yury Kudryashov, and David Loeffler.

OpenAI GPT-6 Astra Pro performed proof construction, source integration, compilation, and independent AI source review. No human specialist review has occurred, and CI success is not represented as such review.
