---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation and Lean proof development
human_review: none
---

<a id="slit-extremal-localization-20261128"></a>

# Exact actual pairable optima, attainment, and their limiting maximum

## Claim

### Exact simultaneous two-child optimization in the actual source

`ActualPairableOptimality.pairableWidth_eq_explicit_actual_periods` proves
an exact value for the full physical geometric two-port supremum, for
every actual quadratic tip of period `p >= 17`. Put `G=f_c^p`,
`R=2^(-p)`, `d=G(0)=x_p`, and let `V` be the existing archived source
component. The positive fixed cut `alpha` is selected from its proved
unique interval root. The source slit and ports are exactly

```text
T' = [-d,d],
J0 = (-x_(4p), x_(2p)),
J1 = (x_(5p), -alpha).
```

A pairable parent must have an actual initial proper restriction from
`J1` to `J0` and an actual terminal proper restriction from `J0` to `J1`,
with the designated local lower/upper bank accesses. Their open intervals
lie in `V \ T'`. The intervening parent segment may leave `V`; children
may make arbitrary excursions, and no rectifiability is assumed. The
supremum is over all Borel parent Waves satisfying these conditions, in
the original physical target disk and its existing parent homotopy class.

Define the actual real function

```text
e(y) = -sqrt(((R+d)/(R-d))^2 - ((R+y)/(R-y))^2),
(u,v,w,t) = (e(x_(5p)), e(x_(3p)), e(x_(6p)), e(alpha)),
(a,b,c) = (-1/(v-u), -1/(w-u), -1/(t-u)),
h(x) = 1/(sqrt|x-a| * sqrt|x-b| * sqrt|x-c|),
B = integral_(a,b) h(x) dx,   A = integral_(b,c) h(x) dx.
```

The actual endpoint order `u<v<w<t` and positivity of both periods are
proved. The theorem is

```text
ActualPairableMarking.pairableWidth hp hc = ENNReal.ofReal (A/(2*B)).
```

`ActualPairableOptimality.family_attains_pairableWidth` specifies an
actual Borel Wave attaining that entire supremum. Each member has both
proper restrictions simultaneously; these are not two independently
chosen child optimizers. The existence theorem `NearTwoTip.exists_actual_tip`
already supplies actual tips for every stated period, so this result is
not conditional on an unproved parameter-existence premise.

The archive previously gave selected round competitors and independent
child caps, explicitly without a simultaneous optimizer. The new claim
relative to that archive is the exact identification and attainment for
this complete physical two-restriction problem on the whole actual source.
The period quotient and rectangle machinery are classical. **This geometric
class is a relaxation of the intended native class; no Lean equivalence to
all KKL ideal-boundary, atom, survival, or minimal-base conditions is
asserted.** The exact physical result therefore does not close the entire
canonical ledger item or establish worldwide historical priority.

### Convergence to the attained limiting-domain maximum

Let `Q_k(z)=1-k*z^2`, `q0=0`, `q_(j+1)=Q_k(qj)`, where `k` satisfies the
archive's proved limiting parameter interval and relation `q6+q3=0`.
Let `alpha_infinity` be its unique positive fixed point. The limiting
physical problem has full-plane source and ambient domain, the source
slit `[-1,1]`, the existing limiting parent marking `(q2,q5,q3,1)`, and
ports `(-q4,q2)` and `(q5,-alpha_infinity)`.

`ActualPairableLimitModel.limitingFamily_attains` constructs an actual
Borel pairable Wave attaining the entire limiting-domain supremum. Its
exact value is the same four-port cubic ratio, evaluated at

```text
(u,v,w,t) = (-q4,q2,q5,-alpha_infinity).
```

`ActualPairableLimit.pairable_optimum_converges` proves

```text
pairableWidth_(n+17) --> limitingPairableWidth,
```

for **every** sequence `c_n` with `ActualTip (n+17) c_n`. Both sides are the
complete geometric pairable suprema just defined, and both are attained.
The real-valued version is `pairable_optimum_real_converges`. The proof
does not assume convergence of extremizers or a separately postulated
conformal realization. `ActualPairableDomainLimit.eventually_compact_subset` additionally proves
that every fixed compact subset of the plane eventually lies in the
critical-value-normalized actual source `V_p/d_p`. Thus the full-plane
source is supported by an actual exhaustion theorem, not supplied as a
convergence premise. No convergence of the maximizing foliations is
asserted.

### Complete parent optimization and its finite-disk variation

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

The later theorem `SlitDiskSharpLimit.width_deficit_mul_radius_tendsto`
proves the sharp first-order deficit for each fixed marking:

```text
R * (width M univ - width M (ball 0 R)) --> C(a,b,c) > 0,
C = (A1*B - A*B1)/(2*B^2),
B1 = integral_(a,b) x*h(x) dx,
A1 = integral_(b,c) x*h(x) dx.
```

Widths in this real-valued expression mean `.toReal`. Positivity is proved
from the strict ordering of the weighted means on the disjoint intervals;
the derivative is obtained from an exact change of variables in the cubic
periods. This fixed-mark theorem does not yet assert a sharp moving-tip
asymptotic or a historically new variation formula.

The exact constrained geometric problem uses its actual
source component. `ActualPairableSource.conformalChart` proves that the
actual polynomial return maps the entire upper source component
bijectively onto the target disk cut to its critical value.
`ActualPairablePorts` selects the actual unique positive return fixed point
and proves the four source ports and their membership in that same source.
`SlitPairableWaves` states pairability using two actual proper temporal
subarcs, permitting the parent to leave the source between them.
`SlitPairableCalibration` proves that a single common potential calibrates
both children without a finite-length assumption.
`SlitFourPointChart` constructs the actual four-electrode rectangle inverse
and its closed-side extension. The new matching upper and lower bounds
and the actual attaining Wave are assembled in `ActualPairableOptimality`.

The sharper split estimate separates critical-orbit motion from disk
geometry as `1600*(4*3906*23646*4^(-p) + 1920*2^(-p))` times the limiting
width. This replaces the previously archived reciprocal-period cutoff
term for the same literal geometric supremum.

The main advance claimed relative to the archive is the exact simultaneous
two-restriction geometric optimization and its actual maximizer. The
complete-parent identification and sharp disk variation are also proved.
**The full ledger item is not declared closed.** No worldwide-priority claim
is inferred from an archive search. The underlying analytic and
extremal-length methods are classical.

## Evidence

### Actual full-source coordinate and simultaneous optimizer

`ActualPairableSource` proves that the whole archived upper source maps
bijectively under the actual return `G` to the disk cut from its left
boundary to `d`. It proves full-source containment, exact signed fibers,
criticality, and surjectivity; these are not supplied as chart hypotheses.

To remove the square-root bank discontinuity at the physical ports,
`ActualPairableCoordinate` factors the complete even return as

```text
G(z) = d + z^2*S(z),   Re S(z) < 0,
H(z) = z*sqrt(-S(z)),
J(z) = 2*sqrt(R)*H(z)*sqrt(R^2-d*G(z)) / ((R-d)*(R-G(z))).
```

Both square-root arguments have strictly positive real part on the whole
source. The actual function `J` is holomorphic and injective on `V`, has
nonzero derivative even at the critical point, respects conjugation, and
maps `V`'s upper half onto the complete upper half-plane. Injectivity uses
the exact `+/-` return fibers and oddness; the sign is identified on the
connected upper source. `ActualPairableElectrodes` then proves the four
explicit radical formulas in the claim from `J^2` and the negative-real
branch. No unknown uniformizing map remains in the answer.

`SlitConformalCalibration` transports the sharp local slope through actual
conformal charts. `SlitFourPointMetric` supplies the global map
`z -> -1/(z-u)` on its punctured-plane domain. Their common cubic potential
is zero on `J0` and one on `J1`; each of the two designated temporal
children contributes one transition. Parent simplicity prevents duplicate
positive Hausdorff-one-measure in counting those transitions. Its half
density is therefore admissible for every allowed parent, and the actual
Jacobian gives area at most `A/(2*B)`. This proves the universal bound in
`ActualPairableUpperBound`, including nonsymmetric leaves and source exits
between the children.

`ActualPairableClosedChart` transports the full rectangle inverse through
the regular global inverse of `J`. Ordinary analytic inversion handles
both real port edges. `SlitReflectedRectangles` proves the reflected full
horizontal family is simple, has the literal left-reference homotopy,
has pairwise disjoint interiors and Borel geometric support (by a
countable compact exhaustion of the jointly continuous evaluation map).
`ActualPairableWaves` instantiates this entire construction in the original
physical source and disk. Its designated children meet at the midpoint;
their open temporal intervals are disjoint and properly end on the source
slit. Coincident physical endpoints have the distinct prescribed bank
accesses.

Finally `ActualPairableLeafLength` bounds each complete physical trace's
weighted Hausdorff length by its two actual inverse-horizontal integrals.
Cauchy--Schwarz, Fubini, and the actual chart Jacobian prove area at least
`A/(2*B)` for every measurable extended density admissible for this family.
This matches the universal upper bound and proves actual attainment.

### Exact removed set and convergence of the actual electrodes

`ActualPairableTree.source_inter_preimage_parentSlit` proves the exact set
identity `V intersect G^(-1)(parentSlit) = sourceSlit`; the complete source
slit maps onto the parent slit, and the slit source maps onto the slit
physical target. These are actual polynomial preimage/image statements,
not an assignment of abstract ports to the source. They do not assert a
native ideal-boundary marking or a general Hubbard-tree equivalence.

`ActualPairablePortLimit.normalizedAlpha_error` bounds the actual normalized
positive fixed cut's error by `23646*4^(-p)`. Consequently all four
normalized return-image cuts converge for every sequence of actual tips.
Let `delta=d/R` and `u=y/d`. `ActualPairableElectrodeLimit` proves the exact
normalization

```text
e(y)/(2*sqrt(delta))
  = -sqrt((1-u)*(1-delta^2*u))/((1-delta)*(1-delta*u)).
```

Here `delta -> 0`, so each normalized electrode tends to
`-sqrt(1-u_limit)`. The four limiting values are exactly a common positive
factor `sqrt(k)` times the limiting physical source ports
`(-q4,q2,q5,-alpha_infinity)`, where `q_(j+1)=1-k*q_j^2`, `q0=0`.
`SlitFourPointLimit` proves exact positive-scale invariance and continuity
of the complete four-port period value, using the proved full modulus and
mark transport. `ActualPairableConvergence` applies those theorems to the
actual normalized electrodes and the exact finite pairable optimum.

`SlitReflectedRectangleModulus` supplies the all-density lower estimate for
a general actual analytic rectangle with its continuous edge velocity.
`SlitFourPointPairable` proves exact full-plane two-port optimization and
actual attainment. `ActualPairableLimitModel` instantiates it with the
literal limiting source slit, parent marking, and physical ports.
`ActualPairableLimit` then identifies the preceding finite-value limit with
this attained limiting-domain maximum. `ActualPairableDomainLimit` proves
compact exhaustion using the whole physical-disk estimate
`d*|evenSecant| <= 2`, hence `|G(d*z)| <= d*(1+2*|z|^2)`, and the proved
divergence of the normalized target radii. The limiting supremum is therefore
not replaced by a selected foliation's value or an upper envelope.

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
preserved by the mechanical main merge `0be46b59`; its full weighted CI run
`46120054502` passed. The finite-disk and physical exponential-bound commit
`75f85b82472af2d96d91c3c95e405e3140ea38b9` passed the complete weighted Lean
build and transitive axiom audit in both runs `46120979598` and `46120976219`.
The sharp-limit and actual-source commit
`dc1be854c2ba15ddca9a95bf9789052810e02162` also passed the complete weighted
build and transitive axiom audit in run `46122315623`. The exact pairable commit
`435de833ed0ea8b4423ea568464f41698cf34e97` passed the complete weighted Lean
build and transitive axiom audit in both runs `46123768913` and `46123762245`.
The removed-set, electrode-limit, complete limiting-model optimizer, and
optimum-convergence modules compile locally and are registered for the same
remote checks. A unique local transitive audit of the six final limit/model modules
passes for all 108 declarations, allowing only the repository-standard
`propext`, `Classical.choice`, and `Quot.sound`. Their final CI result is
recorded independently; it is not inferred from the earlier exact finite
checkpoint.

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
certificates here. The full geometric two-port pairable supremum and its attaining Wave are
now also determined exactly, and the actual optima converge to the attained
complete limiting-domain maximum. Native KKL equivalence, designated deck
classes, atom filters, survival semantics, and the ideal minimal-base
conditions remain outside these Lean theorem types. Identification of the
orbit-defined source slit with every external Hubbard-tree convention is
also not asserted here. No equality between unconstrained and constrained
suprema is claimed; the written archive already states strict separation.
No status change is requested. H1-H4, UPTCR, and MLC remain open. The work
does not establish a historical first-priority claim.

## Attribution

The existing complete-Wave convergence and circular-foliation proofs are
prior archive work. Schwarz-Christoffel, Teichmueller-ring, and classical
extremal-length principles retain their original attribution. AI assistance
has not been reviewed by a human mathematician. Contributions follow the
repository's CC0 license.
