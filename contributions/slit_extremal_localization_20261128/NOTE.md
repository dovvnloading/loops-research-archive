---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation and Lean proof development
human_review: none
---

<a id="slit-extremal-localization-20261128"></a>

# Exact complete parent optima and attaining Waves in finite disks and the plane

## Claim

For the archive's literal four-cut marking `a < b < c < d`, let

```text
h(x) = 1 / (sqrt|x-a| * sqrt|x-b| * sqrt|x-c|),
B = integral_(a,b) h(x) dx,
A = integral_(b,c) h(x) dx.
```

The unconditional Lean theorem
`SlitCubicOptimality.width_eq_period_ratio` proves

```text
SlitWaveLimit.width M Set.univ = ENNReal.ofReal (A / (2*B)).
```

The equality concerns the supremum over every
Borel parent Wave in the existing definitions, including nonsymmetric
families and nonrectifiable continuous simple leaves. The fourth endpoint
`d` does not occur in the exact value. The explicitly constructed reflected
inverse-horizontal family attains this supremum:
`SlitCubicOptimality.family_attains_width`. Its membership in the literal
`ParentWave` class, including endpoint-relative homotopy and Borel support,
is proved. An explicit admissible density has exactly this area, proved by
`SlitCubicUpperBound.density_area_exact`.

`ActualParentOptimality.limitingParentWidth_eq_period_ratio` instantiates
this exact value at the archive's actual limiting critical-orbit cuts, and
`limitingParentWave_attains` supplies their maximizer. For arbitrary ambient
domains the same density gives the upper bound `width M D <= A/(2*B)`.

For a finite disk of radius `R > 0` containing all four cuts, put

```text
Psi_R(x) = -((R-x)/(R+x))^2,
(a_R,b_R,c_R) = (Psi_R(a),Psi_R(b),Psi_R(c)),
B_R = integral_(a_R,b_R) h_(a_R,b_R,c_R)(x) dx,
A_R = integral_(b_R,c_R) h_(a_R,b_R,c_R)(x) dx.
```

`SlitDiskOptimality.width_eq_period_ratio` proves the exact finite value
`width M (ball 0 R) = ENNReal.ofReal (A_R/(2*B_R))`.
`SlitDiskOptimality.family_attains_width` constructs an attaining Wave
inside that original disk. `ActualParentDiskOptimality` proves both the
exact value and explicit attainment for every constructed actual quadratic
tip of period `p >= 17`, in normalized coordinates and in the original
physical disk of radius `2^(-p)`. No optimal chart, maximizing family, or
conformal invariance identity is supplied as an assumption.

`ActualParentExponentialRate.physical_parent_geometric_error` proves,
for every actual tip of period `p >= 30`, the explicit real-width estimate

```text
|physicalParentWidth_p.toReal - limitingParentWidth.toReal|
  <= 3073600 * (1/2)^p * limitingParentWidth.toReal.
```

The sharper split estimate separates critical-orbit motion from disk
geometry as `1600*(4*3906*23646*4^(-p) + 1920*2^(-p))` times the limiting
width. This replaces the previously archived reciprocal-period cutoff
term for the same literal geometric supremum.

The advance claimed relative to the archive is the universal upper bound
together with a matching actual maximizer for the complete parent class.
**The full ledger item is not declared closed.** No worldwide-priority claim
is inferred from an archive search. The underlying analytic and
extremal-length methods are classical.

## Evidence

### Actual density and exact energy

On the closed upper half-plane use the continuous upper-side square roots
and the actual functions

```text
g(z) = 1 / (sqrt_upper(z-a) * sqrt_upper(z-b) * sqrt_upper(z-c)),
F(x+i*y) = integral_(x,infinity) g(t+i*y) dt.
```

The density is

```text
rho(z) = |g(Re z + i*|Im z|)| / (2*B).
```

All parts of its certification are proved:

1. `SlitCubicIntegrability` proves real-axis integrability and positivity
   of `B`; `SlitCubicArea` proves planar integrability of
   `1/(|z-a|*|z-b|*|z-c|)` at the three poles and at infinity.
2. `SlitCubicCalibration.tail_hasDerivAt` proves `F'=-g` from dominated
   differentiation and improper integration. The same module proves
   closed-half-plane continuity, horizontal cancellation, and uniform
   decay of `F` at infinity.
3. `SlitCubicPeriods` proves the opposite boundary period identity by an
   explicit real fractional-linear substitution. `SlitCubicBoundary`
   proves `Re F=0` on the left ray and `Re F=B` on the marked gap.
4. `SlitLeftCrossing.parentLeaf_exists_left_real` uses the actual
   endpoint-fixed slit homotopy to prove every parent hits that left ray.
   `SlitPotentialLength` proves the required two-transition length bound
   using Hausdorff one-measure, without assuming finite length.
   `SlitPotentialReflection` proves the sharp local slope after folding.
5. `SlitCubicAdmissible.density_admissible` assembles these facts for every
   `ParentWave`, with no regular-foliation or uniformizing-chart premise.
6. `SlitCubicEnergy.integral_upper_densitySq` proves the exact integral

   ```text
   integral_upper_half_plane 1/(|z-a|*|z-b|*|z-c|) dArea = B*A.
   ```

   Green's identity is applied to the actual field `Re F * F'` on
   rectangles `[-R,R] x [1/R,R]`. The top and side integrals are proved
   to vanish, the bottom converges to the exact real-axis flux, and
   `SlitEnergyExhaustion` proves convergence of the interior integrals.
   No area identity or conformal chart is assumed.
7. `SlitCubicMetricArea` proves the real axis has zero planar measure,
   uses actual conjugation invariance to double the upper energy, and
   tracks the normalization `1/(4*B^2)` into the archive's ENNReal area.
   The resulting area is exactly `A/(2*B)`.

### Actual conformal rectangle and matching maximizing family

`SlitCubicUnivalence.tail_injOn_upper` independently proves injectivity of
the actual integral. The coordinate `log((z-a)/(z-c))` changes the upper
half-plane to a convex strip. In that coordinate the derivative is
`sqrt_upper(z-a)*sqrt_upper(z-c)/((c-a)*sqrt_upper(z-b))`, whose real part
is proved positive. A real mean-value argument gives injectivity.

`SlitCubicBoundaryRange` and `SlitCubicImaginaryBoundary` prove the four
actual boundary sides, positive height `A`, the second period identity,
and the full real-axis rectangle bounds.

`SlitCubicRectangle` proves that the actual image lies strictly inside
`(0,B) x (-A,0)`, using boundary estimates, uniform decay at infinity,
and a nonvanishing derivative. `SlitCubicSurjective` proves the image is
the entire open rectangle and constructs its actual inverse chart.
`SlitCubicEdges` and `SlitCubicClosedChart` extend that inverse continuously
to the two vertical sides, with the required real-bank locations.

For each horizontal height `-A < y < 0`, the inverse segment is reflected
to form a complete parent leaf. `SlitCubicWaves` proves endpoint locations,
bank orientations, simplicity, the literal left-reference homotopy,
pairwise interior disjointness, and exact Borel geometric support. The
support is the plane with the rightward real ray `[a,infinity)` removed.

`SlitParametricLength` proves the weighted Hausdorff-image estimate for
continuous differentiable parametrizations. `SlitCubicLeafLength` applies
it to both full inverse segments, including their endpoints.
`SlitCubicLowerEnergy` then applies Cauchy--Schwarz on the disjoint sum of
the two horizontal parameter intervals, Fubini, and the actual conformal
Jacobian. Every measurable extended nonnegative density admissible for
this Wave has area at least `A/(2*B)`; no finite-area or bounded-density
restriction is imposed. This lower bound matches the universal certificate.

### Exact finite disks and literal physical maximizers

`SlitDiskCayley` proves that the actual squared Cayley map
`Psi_R(z)=-((R-z)/(R+z))^2` is a biholomorphism from the disk onto the
plane with the nonnegative real ray removed. Its explicit inverse,
complex derivatives, conjugation identities, real order, and bank signs
are proved. `SlitDiskMarking` applies this map to all four actual cuts.

`SlitDiskUpperBound` composes the actual cubic potential with `Psi_R`.
`SlitLocalReflection` proves its folded local slope on every parent trace;
the original homotopy crossing argument applies in the original disk.
The density is exactly the conformal pullback of the cubic density, and
the actual Jacobian gives its area upper bound.

`SlitDiskWaves` pulls the actual inverse-horizontal family into the disk
and proves every `ParentWave` condition there. `SlitDiskLowerChart`
constructs the composed analytic inverse chart, with source exactly the
rectangle and target exactly the upper half-disk. `SlitDiskLeafLength`
controls both complete reflected geometric segments by its explicit
velocity integral. `SlitRectangleLowerEnergy` gives the all-density energy
lower bound from this actual chart. These match in `SlitDiskOptimality`.

`ActualParentDiskMarking` derives disk containment of all actual cuts from
the archived critical-orbit error and target-radius estimates.
`ActualParentDiskOptimality.physicalFamily_attains` specifies an actual
Borel parent Wave in the original quadratic plane whose modulus equals
the entire physical parent supremum.

### Quantitative finite-period consequence

`SlitDiskRate` proves exact affine invariance and normalizes the transformed
cuts to `x_R = R*(Psi_R(x)+1)/4 = x/(1+x/R)^2`. For `|x| <= 2` and `R >= 4`
it proves `|x_R-x| <= 40/R`. The exact disk optimum is the complete plane
optimum at these normalized cuts. The archived two-sided small-mark
transport estimate therefore applies with total four-cut displacement
at most `markError + 160/R`, with no escaping-family cutoff. The actual
radius estimate `R_p >= 2^p/12` yields the stated exponential error.
This estimate is a consequence of the exact geometric optimizer, not a
claim of a new general extremal-length principle.

### Validation and provenance

The starting main commit was `6a10209b3cc51878bc45de7668894757b2575e08`.
This checkpoint incorporates main
`f05f1b9dc8f5fc6eeb68491da2eb44eca6d6cec9`, preserving the independent
depth-gate and uniform-crest work and all registry entries.
All new modules compile locally with the repository-pinned Lean 4.32.0 and
Mathlib. Declaration-level transitive audits permit only `propext`,
`Classical.choice`, and `Quot.sound`. No proof holes, new foundations, or
changes to CI, the ledger, or trust policy are introduced.

The universal-upper-bound checkpoint
`f65e4ca7dbd60de2a03cdd3556fcb46ace2fdd64` passed the complete weighted GitHub
CI build and transitive axiom audit in run `46118469742`, as well as source
and model coverage. The exact plane result was committed at `6cd15700` and
preserved by the mechanical main merge `0be46b59`. This stronger finite-disk
checkpoint is registered for the same checks; its remote CI result is not
assumed from the earlier run.

### Prior archive work and comparison

- `contributions/marked_wave_supremum_limit_20261127/NOTE.md`,
  `SlitWaveLimit`, `SlitWaveFinite`, and `ActualParentRate` already prove
  full-family finiteness, convergence, and quantitative error bounds.
  These are not new claims of this packet.
- `research/tip_family_theorem/THEOREM.md`, Open Problem 2, and
  `research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md`
  already discuss the half-strip competitor and strict separation from
  the pairable optimum. Repeating those lower witnesses is not the claim.
- The present proof controls the entire existing parent class and gives
  an actual matching maximizing Wave. It does not count the classical
  rectangle machinery itself as a new mathematical discovery.

The cubic ratio is the classical Teichmueller-ring modulus for
`C \ ([a,b] union [c,infinity))`. The reflected rectangle foliation is its
classical extremal foliation. Any research novelty must therefore lie in
the precise optimization and identification of the archive's full parent
class, not in the elliptic formula, the conformal map, or their
formalization. The external canonical KKL identification remains a
separate scope question stated below.

A primary classical reference is K. Oikawa, *On the stability of boundary
components*, Pacific Journal of Mathematics **10** (1960), 263-294:
[publisher PDF](https://msp.org/pjm/1960/10-1/pjm-v10-n1-p16-p.pdf), printed
page 267, No. 9 (VIII)-(IX), for reflection doubling and extremal level
curves, and printed page 269, section 5, for the Teichmueller slit ring.
This reference establishes prior classical machinery; it does not certify
the archive-specific KKL identification or any worldwide novelty claim.

For orientation only, the classical elliptic-integral substitution
suggests `A/(2*B)=K(1-m)/(2*K(m))`, with `m=(b-a)/(c-a)` and the parameter
convention `K(m)=integral_0^(pi/2) (1-m*sin(t)^2)^(-1/2) dt`.
At the limiting actual marking, numerical evaluation suggests
`0.7527550636374064`, compared with the archived upper envelope near
`0.7749231261480455`. **Neither this elliptic re-expression nor these decimal
evaluations are a certified Lean result in this checkpoint.** The proved
exact value is the cubic-integral ratio above.

## Dependencies

`NOV26_OPEN_OPTIMAL_LIMIT`; the archive's unchanged `MarkedSlitTransport`,
`SlitWaveModulus`, and `SlitWaveLimit` definitions; the repository-pinned
Mathlib. The proof uses classical complex integration, covering-space
lifting, real changes of variables, and Hausdorff measure theory.

## Boundary

The obligation stays open. Exact value and attainment are proved for the
complete geometric parent class in every ordered four-cut disk and in the
plane, including the literal physical actual-tip problems for `p >= 17`
and their limiting marking. A Lean identification with every aspect of
the external KKL ideal-boundary/minimal-base definition is not supplied.
The periods `3 <= p < 17` are not instantiated from physical tip existence
certificates here. No equality with the separately constrained pairable
problem is claimed; the written archive already states strict separation.
No status change is requested. H1-H4, UPTCR, and MLC remain open. The work
does not establish a historical first-priority claim.

## Attribution

The existing complete-Wave convergence and circular-foliation proofs are
prior archive work. Schwarz-Christoffel, Teichmueller-ring, and classical
extremal-length principles retain their original attribution. AI assistance
has not been reviewed by a human mathematician. Contributions follow the
repository's CC0 license.
