---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="parent-wave-exhaustion-20261128"></a>

# Exact attained limiting parent Wave optimum

## Claim

The complete, unchanged canonical supremum `SlitWaveLimit.width M univ`
has an explicit value and an attained maximum. For every ordered marking
a < b < c < d, put m=(b-a)/(c-a). With the parameter convention

    K(m) = integral from 0 to pi/2 of 1/sqrt(1-m*sin(theta)^2),

the proved value is

    width M univ = ENNReal.ofReal (K(1-m)/(2*K(m))).

A Borel family of pairwise interior-disjoint, simple, correctly oriented
leaves in the original left relative-homotopy class attains that supremum.
The theorem quantifies over the archive's original complete parent-wave
class and its original all-density Hausdorff-trace modulus.

For the literal limiting quadratic marks a=x_2, b=x_5, c=x_3, d=1,
this evaluates `ActualParentSupremum.limitingParentWidth`. The existing
physical-supremum convergence theorem now has this explicit target.
The parameter sequence is also identified with the unique root in F16's
literal signed kneading chart for every p>=17; no arbitrary IVT choice
or assumed invariant interval remains in that identification.

The new research endpoint is the exact canonical maximum and its
attainment, with the physical and parameter links proved. Previously
archived convergence, estimates, elliptic quadrilateral envelopes, and
classical special-function identities are inputs, not claimed discoveries.

## Evidence

The principal Lean declarations are:

- `ParentWaveExact.parent_width_eq_K`: exact value of the complete original supremum.
- `ParentWaveExact.exists_parentWave_attaining_width`: an actual attaining wave.
- `ActualParentExact.limitingParentWidth_eq_coefficient` and
  `limitingParentWidth_attained`: the literal limiting quadratic objects.
- `ActualParentExact.canonical_physical_parent_optimum_converges_to_explicit`:
  explicit limit of the original physical slit-disk suprema.
- `ActualParentExact.exists_canonical_attained_explicit_parent_limit`:
  constructed model root, positive explicit value, canonical physical sequence,
  and actual maximizing limiting wave.
- `ActualParentSelection.signed_chart_root_iff_actual_tip` and
  `exists_unique_signed_chart_root`: equivalence and uniqueness in the
  source's literal equation-free signed chart.

### Why the comparison is sharp for the canonical objects

The original relative-homotopy condition forces every competing parent
leaf to meet the left real ray. Splitting there and folding the two pieces
gives an upper bound by half the modulus of all continuous closed-upper-
half-plane crossings. This step permits arbitrary real-axis contacts and
nonrectifiable traces.

The actual differential is q(z)=1/((z-a)(z-b)(z-c)). In the coordinate
t=sqrt(z-a), its primitive has derivative
2/(sqrt(t^2-(b-a))*sqrt(t^2-(c-a))). A derivative-sign argument proves
injectivity on the quadrant. Finite square-root extensions and a proved
uniform limit at infinity give the full rectangle image, its boundary
sides, and a continuous inverse on every row.

Weighted Hausdorff measure transport is proved by local Lipschitz covers
and disjoint measurable decompositions. It applies to all measurable
extended densities and infinite-length traces. Boundary continuations
and removal of the finite branch-point set calibrate all the upper
crossings. The area equality uses the actual conformal Jacobian.

Pulling back the entire continuum of horizontal rows and reflecting it
constructs a canonical Borel parent wave. Its support, endpoint banks,
simplicity, disjoint interiors, and left homotopy class are proved.
Endpoint deletion and reflection preserve the exact trace modulus with
the required factor 1/2. Thus the upper estimate is attained.

The literal rectangle side lengths are evaluated by trigonometric
substitution and the fundamental theorem of calculus. They are
2*K(m)/sqrt(c-a) and 2*K(1-m)/sqrt(c-a), respectively.

### The selected physical parameter

`SignedKneadingChart` uses the source's strict 14*4^(-p) and 16*4^(-p)
parameter bounds, return-size bound, literal orbit-product coefficient
tau in (-2,1/4), positive critical prefix, and six signs +--+-+.
For every root in this chart, tau=-kappa and kappa<2 imply the full
invariant physical interval: the exact inverse secant product is bounded
by the endpoint derivative product. The archive's global physical
signed-tip uniqueness then applies. This proves equivalence of the named
chart-root condition and `ActualTip`, not just one inclusion.

### Validation

The final equality, attainment, and physical-limit modules compile locally
with pinned Lean 4.32.0. The complete committed checkpoint fb082802 passed
both the full weighted build and transitive dependency audit in GitHub
Actions. The stronger endpoint is being submitted to the same unchanged
CI. Final CI confirmation is still required for this draft.

## Dependencies

- The open ledger row NOV26_OPEN_OPTIMAL_LIMIT and its F16 source statement.
- `marked_wave_supremum_limit_20261127`: the original full geometric supremum,
  exact physical scaling, convergence, and quantitative error estimate.
- The existing global primitive-window and physical signed-tip uniqueness
  modules, used for the explicit parameter identification.
- `maximal_native_wave_20261123/H3_WIDTH.md`: earlier embedded witnesses and
  full-path upper envelopes, distinguished from the equality proved here.
- Mathlib's complex analysis, interval integration, Hausdorff measure,
  Borel image, and Jacobian theorems.

## Boundary

This is partial progress on the composite ledger row. Exact finite-disk
values W_p*, equality with the narrower paired-parent optimum W_p,2*,
and the full parent/child comparison remain outside this theorem.
No ledger or gate status is changed.

The conclusion is exactly the repository's pre-existing ParentWave
supremum and its literal physical quadratic incarnation. The external
KKL A.1 interpretation still requires the archive's written intrinsic
ideal-boundary identification; a complete Lean equivalence with a
separately formalized native A.1 ideal-circle Wave class is not claimed.
We are checking that boundary explicitly rather than substituting a
new proxy definition.

The source signed-chart root is now identified for p>=17. No maximal
primitive-component identification or new least-period theorem is claimed.
The decimal diagnostic in ATTACK.md is not a certified numerical enclosure.
MLC and H1-H4 remain open.

## Attribution

Complete elliptic integrals, conformal rectangle coordinates, extremal
length, and the general quadratic-differential method are classical.
Their formulas alone are not the contribution. The result here proves
the missing sharp variational equality and attained optimizer for the
archive's complete canonical objects, with every geometric hypothesis
discharged in Lean and the selected physical family explicitly linked.
No claim of worldwide priority is inferred from the archive audit.
