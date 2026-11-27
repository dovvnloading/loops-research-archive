---
ledger: KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="stationary-model-ramification-20261126"></a>

# Exact inverse-label loss and local branching in quadratic geometric models

## Claim

This contribution proves an exact comparison between the actual quadratic
inverse-point census and its geometric quotient. It characterizes precisely
when every inverse label survives at a possibly nonsingleton target fiber,
and gives an exponential lower bound when a postcritical point is identified
with a different physical anchor.

It also identifies the topological local-injectivity locus of a nontrivial
geometric model. These are partial results toward
`KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION`, not a closure of that row.

### Objects and hypotheses

Write `f(z)=z^2+c`, let `K` be the actual filled set defined by zero escape,
and let `F=f|K`. Assume:

1. The critical point belongs to `K` and `interior K = empty`.
2. `Y` is Hausdorff, and `p : K -> Y` is continuous and surjective.
3. Every fiber of `p` is preconnected, and `p o F = G o p`.
4. Every point fiber of `G` is totally disconnected.

These are the existing light monotone geometric-model hypotheses. Neither a
two-point model fiber count nor a singleton physical anchor fiber is added
as an assumption. The local branching theorem additionally assumes that
`Y` has more than one point.

For a physical anchor `a in K`, define

```text
P_n(a) = #{ z in C : f^n(z)=a }
M_n(p(a)) = #{ y in Y : G^n(y)=p(a) }

L_n(a) = sum_{0 <= k < n} 2^(n-1-k) *
         1[ p(f^k(c))=p(a) and f^k(c) != a ].
```

The terms use the critical VALUE `c=f(0)`; time `k` here is time
`k+1` from the critical point. Every actual inverse point of `a` lies in
`K` by complete invariance. Repeated critical-orbit contacts are retained
at their distinct times.

### A. Exact loss

For every anchor and every natural depth, including depth zero,

```text
P_n(a) = M_n(p(a)) + L_n(a).
```

Only a postcritical point in the anchor's full geometric fiber that differs
from the anchor itself contributes extra loss. Other points in that
geometric fiber do not create an additional term.

The main Lean declaration is
`quadratic_filled_quotient_loss`, together with
`collapsedCriticalDefect_eq_sum`, which expands the loss into the displayed
weighted sum.

### B. Sharp inverse-label criterion

For every finite horizon `n`, the restriction of `p` to the complete
physical inverse level `f^(-n)(a)` is injective if and only if

```text
for every k<n:
  p(f^k(c))=p(a) implies f^k(c)=a.
```

This is `quadratic_filled_inverse_labels_iff`. The already archived
whole-fiber transport theorem proves that this restriction maps onto the
entire model inverse level. Consequently the criterion characterizes
preservation of all distinct inverse labels.

This is a criterion about complete inverse POINT levels. It must not be
identified with the different carrier equality
`p^(-1)(L_com)=L`: a saturated full lift can contain nontrivial fibers.

### C. Quantitative persistence of a failure

If a false contact occurs at critical-value time `k`, then for every
natural `m`,

```text
M_(k+1+m)(p(a)) + 2^m <= P_(k+1+m)(a).
```

The declarations `collapsedCriticalDefect_growth`,
`collapsedCriticalDefect_of_contact`, and
`quadratic_filled_quotient_loss_lower_bound` establish this. A detected
loss cannot disappear at a later inverse depth.

### D. Topological local branching

For a nontrivial model `Y`, the point `p(0)` is exactly the point at
which `G` has no injective restriction to an open neighborhood:

```text
not (exists open U containing y, G is injective on U)
  iff y=p(0).
```

This is `quadratic_filled_model_local_injectivity_locus`.
The nontriviality hypothesis is material: a one-point quotient satisfies
the counting hypotheses but its map is locally injective everywhere.

The all-depth theorem `quadratic_filled_model_iterate_local_injectivity_iff`
then proves, for every natural `n`,

```text
G^n is injective on an open neighborhood of y
  iff every G^k(y), 0<=k<n, differs from p(0).
```

This is an exact topological branching itinerary for every model iterate.
Continuity and openness of the model map are derived from the physical
quotient and the archived light-model theorem.

## Evidence

### What is reused, and what is new

The initial draft missed a result in a separate existing module. A broader
novelty audit found that `QuadraticEscapeFullness.lean` already proves both
exact critical-fiber recognition and the all-target inverse census.
The duplicate draft development was removed. Neither result is claimed
as a new contribution here.

| Archived input | Existing conclusion | New use |
|---|---|---|
| `QuadraticCriticalFiberCensus.globalFiber_card_exact` | Actual complex inverse count and physical critical-value defect | Physical side of the exact quotient-loss comparison |
| `QuadraticEscapeFullness.quadratic_filled_light_model_all_target_census` | Exact count at every model target | Model side of that comparison |
| `QuadraticEscapeFullness.quadratic_filled_light_model_exact_critical_branch` | Descended reflection and exceptional singleton predecessor fiber | Identification of actual failure of local injectivity, under nontriviality |
| `StationaryLightModel.model_iterate_preimage_projection` | Full model inverse level is the image of any physical anchor's inverse level | Turns equal counts into the sharp inverse-label criterion |
| `StationaryLightModel.quadratic_filled_singleton_anchor_ramification_exact` | Exact count at singleton anchors under its own weaker hypotheses | Comparison point; the new nonsingleton criterion uses additional geometry |

The elementary counting recurrence is not a novelty claim. The added
content is its exact comparison across the supplied geometric quotient,
the necessary-and-sufficient physical label criterion, the quantitative
failure statement, and the local-injectivity characterization.

### Proof route

The archived model defect counts critical-value contacts AFTER projection.
The archived physical defect counts hits at the exact anchor. A projected
contact partitions into a true physical hit or a distinct postcritical
point in the same geometric fiber. Induction proves that the model defect
is the physical defect plus the new collapsed-contact defect. Subtracting
the two archived exact census equations gives the exact loss.

The collapsed-contact recurrence has nonnegative terms, so its vanishing
is equivalent to absence of every false contact through the horizon.
Whole-fiber transport supplies surjectivity of the finite inverse-label
map. Equality of the two finite cardinalities is therefore equivalent to
injectivity. The recurrence also doubles every earlier loss at each
additional inverse step.

For local branching, boundedness of the critical orbit gives connectedness
of the actual filled set by the archived theorem. Its continuous
surjective image is connected. In a nontrivial connected Hausdorff model,
`p(0)` is not isolated. The descended reflection fixes exactly `p(0)`.
Every neighborhood there contains a distinct reflected pair with the
same `G` image, so it cannot be an injectivity neighborhood. Away from
`p(0)`, the archived involution two-sheet theorem constructs an open
injectivity neighborhood.

For iterates, openness pushes an injective neighborhood through earlier
factors, proving that no critical model point can occur in its itinerary.
Conversely, continuity lets the proof intersect the required local
injectivity neighborhoods through the finite orbit. This includes the
zero-depth identity map.

### Lean files and validation

- [StationaryRamificationCensus.lean](../../formalization/weighted/StationaryRamificationCensus.lean):
  new collapsed-contact defect, exact sum, semiconjugacy split, and
  zero-loss criterion; imports the archived census.
- [StationaryModelRamification.lean](../../formalization/weighted/StationaryModelRamification.lean):
  actual quadratic loss identity, inverse-label iff, and exponential
  loss; private helpers only reconcile ambient and subtype counts.
- [StationaryModelBranchLocus.lean](../../formalization/weighted/StationaryModelBranchLocus.lean):
  topological local-injectivity characterization and all-depth branching
  itinerary, using the archived geometric reflection.

The current reduced modules compile locally with the repository's exact
Lean 4.32.0 toolchain and locked Mathlib dependencies. The final compiled
dependency audit and head-specific CI run are still pending at this
checkpoint. No proof result is described as CI-verified until those
checks pass.

Reproduction with the repository toolchain:

```sh
cd formalization/weighted
lake build StationaryRamificationCensus StationaryModelRamification StationaryModelBranchLocus
cd ../..
python -B code/verify_lean_coverage.py
python -B code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

The existing full workflow builds all registered targets and audits every
compiled declaration transitively. It permits only `propext`,
`Classical.choice`, and `Quot.sound`. No workflow, trust policy or ledger
status is modified.

## Dependencies

Ledger context: `KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION`,
with the three imported/proved prerequisites listed in the ledger.
Those documentary statuses are not used as Lean premises.

Mathematical dependencies are the actual Lean modules named above and
their checked dependencies, including actual escape-set complete
invariance, filled-set connectedness, compact quotient transport and
finite-set cardinality.

Earlier work read and distinguished:

- [Quadratic filled fullness contribution](../quadratic_filled_fullness_20261126/NOTE.md).
- [Stationary model degree contribution](../stationary_model_degree_20261126/NOTE.md).
- [Stationary non-LC predecessor-lift audit](../../research/independent_audits/stationary_nonlc_predecessor_lift_20261126/NOTE.md).
- [Stationary fiber-saturation audit](../../research/independent_audits/stationary_fiber_saturation_20261126/NOTE.md).
- [Selected predecessor endpoint obligation](../../research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md).

## Boundary

The ledger row stays OPEN. This does not construct or identify KKL's
named geometric quotient, prove that it is the required dendrite, match
the selected predecessor labels, prove the fixed-alpha singleton fiber,
identify the carrier as the required full inverse image, identify the
selected sheets, or match the physical and geometric small-Julia continua
and marked accesses.

The existing singleton-alpha hypothesis already implies inverse-label
faithfulness there. The new result allows a weaker finite-horizon test
for other, possibly nonsingleton anchors and diagnoses exact failure;
it does not eliminate the native geometric identification work.

The hypotheses do not supply a verified nonconstant quotient with
nonsingleton fibers at a specified parameter. No such example is claimed.
In particular the Chebyshev parameter cannot be advertised as that
example, because the archive already proves its nonconstant monotone
dynamical quotient rigidity.

Local injectivity is a topological property. The result does not assert
a holomorphic local-degree normal form on the model or an analytic
covering of a model Riemann surface. No collar, prime-end, width,
distortion, modulus, or uniform-in-block estimate is derived.
H1-H4, UPTCR and MLC remain open. No ledger status change is requested.

## Attribution

The physical and model censuses, planar fullness, descended reflection,
and full inverse-level projection are existing archive work and are
used directly. The general principles of counting fibers, composing
local inverse maps, and connected-space topology are classical.

The inspected archive contains no earlier exact physical/model
difference formula with the weighted false postcritical contacts, nor
the sharp inverse-label iff. This is a claim about the archive comparison,
not world-first mathematical priority.

AI assistance: OpenAI GPT-6 Astra Pro, including separate novelty and
adversarial-review passes. No independent human mathematical review has
been performed.
