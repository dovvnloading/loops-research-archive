---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical development, Lean proof implementation and adversarial review
human_review: none
---

<a id="uniform-crest-transport-20261128"></a>

# Signed actual-parameter drift and every-index crest transport

## Claim

**Implementation checkpoint: the signed-drift modules await Lean CI.**
The support and physical-transport modules have passed the complete
weighted build; their transitive audit is still running at this checkpoint.
No uncompiled assertion is counted as a validated result.

The principal new target is an intrinsic, signed correction to the
archive's actual normalized return coefficient. Write

- `q = scale p = (1/4)^p`;
- `d = criticalValue c p > 0`;
- `H(z) = normalizedReturn c p z = f_c^[p](d*z)/d`;
- `kappa p c = -quadraticCoefficient c (p-1)*d`;
- `k0` for the unique zero of `relation` in `[17903/10000,17904/10000]`.

`ActualCrestSignedDrift.actual_tip_signed_drift` states, for **every**
`p >= 17` and **every** parameter satisfying the existing `ActualTip p c`,

```text
scale p / 2 < kappa p c - k0
kappa p c - k0 <= 15748 * scale p.
```

The upper bound is inherited and credited below. The positive lower
bound is new: the finite-return coefficient is forced above the limiting
coefficient, and its displacement cannot be smaller in order than
`4^(-p)`. No sign condition is added to `ActualTip`. This does not assert
monotonicity in `p` or compute a limiting first-order constant.

A second result removes the unspecified eventual threshold from the
complete physical crest realization. `UniformCrestSupport` establishes
`StrictSupport c p` for every `p >= 17`. Consequently
`UniformCrestTransport.every_actual_tip_realizes_collar` gives the same
complete proper physical parent and selected descendant families,
including their exact all-density moduli and ratio greater than one
third, at every permitted return index. The convergence result retains
realization at **every** index of the chosen sequence.

## Evidence

Base: main commit `6a10209b3cc51878bc45de7668894757b2575e08`.

### Why the signed result is additional mathematics

`NearTwoTip.actual_tip_coefficient_error` gives only the symmetric bound
`abs (kappa p c - k0) <= 15748 * scale p`. That bound permits either sign
and permits the displacement to vanish faster than the stated scale.
The new proof rules out both possibilities by retaining the sign and
size of the complete nonlinear remainder of the actual iterate.

The proof uses no assumed Taylor remainder or approximate replacement
for the actual polynomial. Put

```text
E(x) = Re(H(x)) - (1 - kappa p c * x^2).
```

The new modules prove the following chain.

1. **Positive physical prefixes and ordered remainder.**
   If `epsilon = c + 2`, the critical deficits satisfy
   `2 - x_(n+2) <= 3*epsilon*4^n`. Since `epsilon <= 20*q`, every
   critical prefix with `2 <= j <= p-1` is at least `17/16`.
   For a physical input `0 <= t <= d`, its displacement from the
   critical prefix is between zero and `4^(j-1)*t^2 <= 9*q`.
   Thus every corresponding physical prefix stays at least one.
   The first even-secant factor is negative and increases with the
   input; all later factors are positive and decrease. The complete
   secant is increasing. Its exact factorization proves
   `0 <= E(x) <= E(1)` for every `abs x <= 1`, and `E(1) > 0`.

2. **A nonvanishing correction at the natural scale.**
   Let `X = x_(p-1)`, `Y = f_c^[p-1](d)`, and `Delta = X-Y`.
   The exact final squaring step gives
   `d*E(1) >= Delta^2`, because the preceding complete remainder
   and critical point are nonnegative. The return identity gives
   `Delta*(X+Y) = d*(kappa p c - E(1))`.
   Since `X+Y <= 4`, `kappa p c >= 7/4`, and the archived error
   implies `E(1) <= 1/100`, this forces `Delta >= 5*d/12`.
   Therefore `E(1) >= 25*d/144`. The coefficient norm bound gives
   `d >= 4*(kappa p c)*q >= 7*q`, hence

   ```text
   q <= E(1) <= 24*q.
   ```

   The lower bound comes from a retained positive square in the exact
   actual recurrence. It is not a consequence of an unsigned error bar.

3. **A forced signed critical-relation deficit.**
   Let `y_j = H^[j](0)`, `u_j = Q_kappa^[j](0)`,
   `delta_j = y_j-u_j`, and `e = E(1)`. The exact recursion is

   ```text
   delta_(j+1) = -kappa*(y_j+u_j)*delta_j + E(y_j).
   ```

   Rational interval bounds on the complete actual orbit give
   `delta_2=e`, `delta_3 >= 2.82*e`,
   `delta_4 >= 0.42*delta_3`,
   `delta_5 <= -3.48*delta_4+e < 0`, and
   `delta_6 <= 2.5*delta_5+e`. Keeping these correlations yields
   `delta_6+delta_3 <= -3.9*e`.
   The exact signed relation in `ActualTip` is `y_6+y_3=0`.
   Consequently the quadratic relation at the actual coefficient
   is at least `3.9*e >= 3.9*q`, strictly positive.

4. **Signed coefficient displacement.**
   The model relation is strictly increasing on the certified
   coefficient interval. Its derivative is less than seven there,
   as follows from the already archived interval certificate.
   Thus the actual coefficient exceeds its unique limiting root,
   and `7*(kappa-k0) > 3.9*q`, which implies the stated `q/2`
   lower bound. The archived symmetric estimate supplies the upper
   bound.

### Complete physical support at every index

The prior `actual_crest_path_width_20261127` contribution explicitly
leaves physical survival for every finite index `p >= 17` open. Its
realization theorem is uniform but eventual, with an unspecified
threshold. The scalar endpoint classification already holds at each
such index. The missing premise is full complex support through four
returns.

The generic `UniformCrestSupport.whole_support_bounds_of_error` proves
that any map within `1/5000` of `Q_kappa(z)=1-kappa*z^2` on `abs z <= 3/2`
has the required support on the entire closed disk centered at `-3/4`
of radius `133/2000`. Four successive disks centered on the quadratic
center orbit have radii

```text
0.0665, 0.187, 0.068, 0.252, 0.83.
```

Every transition pays the full perturbation error anew using
`r_next >= 1/5000 + kappa*r*(r+2*abs a)`. The smallest remaining slack
is the exact positive rational `2093/78125000`.
The actual return satisfies the stronger error bound `10^(-8)` at each
`p >= 17`, so the generic theorem applies and gives

```text
norm (H^[j] z) <= 267/250                (0 <= j <= 4)
931909/1000000 <= Re(H^[2] z)
Re(H^[3] z) <= -537974/1000000.
```

All five phases have gap at least `41/500` from the support cutoff
`23/20`. These are whole-disk statements, including boundaries and
all intermediate points. Existing proper-path and metric theorems
then supply the complete `RealizedCollar` at every index.

### Validation and reproduction

The pinned Lean toolchain is absent locally and disk space is too
limited to install it. The repository's unchanged CI is the compiler
and transitive-axiom judge. All new modules are registered in the
existing weighted build, theorem index and physical-source registry.
The first support build exposed one wrong norm-triangle lemma
application; it was corrected in a subsequent commit. Compilation
and audit status for the stronger modules will be recorded here after
those checks finish. The source-registration and contribution-intake
checks have passed on the earlier support checkpoint.

For reproduction with the repository toolchain installed:

```sh
python code/contribute.py check
cd formalization/weighted
lake exe cache get
lake build ActualCrestSignedDrift UniformCrestTransport
cd ../..
python code/verify_lean_coverage.py --audit weighted
```

## Dependencies

- `NOV26_OPEN_CREST_LIMIT` remains the single claimed open obligation.
- `NearTwoTip` constructs actual parameters at every permitted index
  and supplies the existing symmetric coefficient upper bound.
- `LimitingCrestParameter` supplies the unique model root, strict
  monotonicity, and derivative interval certificate. The small added
  public upper-slope lemma only exposes that existing certificate.
- `LimitingCrestQuadraticReturn` supplies the complete actual return
  remainder upper bound. Its existing coefficient norm bound is made
  public with its statement and proof unchanged.
- `GlobalCrestEstimates` supplies the fixed large-disk error bound.
- `LimitingCrestArcGates` supplies the existing scalar center boxes and
  quadratic disk estimates, reproduced with attribution as private
  helpers in the new support proof.
- `ActualCrestPaths`, `ActualCrestProperFamilies`, and
  `ActualCrestTransportLimit` supply the physical realization conditional
  on strict support; `GlobalCrestClassification` supplies all-index
  scalar gates and the selected endpoint.

## Boundary

Keep `NOV26_OPEN_CREST_LIMIT` open (`result: partial`). The contribution
retains the existing `ActualTip` parameter-selection scope and the
literal real-slit interpretation of the selected smooth families.
It does not identify every actual parameter with a distinguished
primitive-component branch, establish a new least-period claim,
identify native KKL ideal markings or the full immersion-pulled
marking, prove an unrestricted Wave optimum, or prove MLC.

The coefficient result concerns `kappa p c`, not the original parameter
`c`, which is near minus two. It proves a forced side and a sharp order
of displacement, not a limiting first-order constant or monotonicity
across return indices. The exact limiting coefficient, the physical
modulus identities, and their positive limiting ratio are inherited.
Only the selected upper q-side descendants are counted; the denominator
is the entire original chosen circular parent.

No status record, workflow, toolchain, or trusted-axiom policy is changed.
No worldwide-priority claim follows merely from absence in this archive
or from a limited literature search.

## Attribution

The new mathematical content is the signed and scale-sharp nonlinear
correction of the actual return, its forced coefficient displacement,
and the explicit every-index support estimate. Earlier actual-parameter
construction, scalar gates, limiting root, proper-path realization,
metric identities and convergence are credited above. The two small
existing-module API exposures are supporting changes, not new results.
AI mathematical and implementation reviews are not independent human
review. Human review remains `none`. The contribution is released
under the repository's CC0 terms.
