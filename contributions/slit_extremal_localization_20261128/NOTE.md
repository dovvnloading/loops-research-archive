---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation and Lean proof development
human_review: none
---

<a id="slit-extremal-localization-20261128"></a>

# Exact cubic-period optimum and attainment for the complete parent problem

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

### Validation and provenance

The starting main commit was `6a10209b3cc51878bc45de7668894757b2575e08`.
This checkpoint incorporates current main
`6964d70bea8a68acae4a627b421086b29f6f63b3`, preserving its depth-gate work.
All new modules compile locally with the repository-pinned Lean 4.32.0 and
Mathlib. Declaration-level transitive audits permit only `propext`,
`Classical.choice`, and `Quot.sound`. No proof holes, new foundations, or
changes to CI, the ledger, or trust policy are introduced.

The universal-upper-bound checkpoint
`f65e4ca7dbd60de2a03cdd3556fcb46ace2fdd64` passed the complete weighted GitHub
CI build and transitive axiom audit in run `46118469742`, as well as source
and model coverage. This exact-optimum checkpoint is registered for those
same checks; its remote CI result is not assumed from the earlier run.

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
complete full-plane parent problem and the actual limiting marking. The
finite-period exact optimizer on the physical target disk and canonical
ideal-boundary identification are not settled in this checkpoint. No
equality with the separately constrained pairable problem is claimed, and
no status change is requested. H1-H4, UPTCR, and MLC remain open. The work
does not establish a historical first-priority claim.

## Attribution

The existing complete-Wave convergence and circular-foliation proofs are
prior archive work. Schwarz-Christoffel, Teichmueller-ring, and classical
extremal-length principles retain their original attribution. AI assistance
has not been reviewed by a human mathematician. Contributions follow the
repository's CC0 license.
