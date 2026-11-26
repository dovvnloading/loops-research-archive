---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="parameter-stable-critical-return-20261126"></a>

# Parameter stability of actual proper one-critical quadratic returns

## Claim

**Proof development; complete Lean CI and axiom audit pending.** This packet
addresses the explicit remaining boundary of the merged parameter-stable
inverse-family contribution: assembling the whole degree-two return while
retaining the moving critical value and trapping the entire middle pullback.
Every result counted by this packet must be a theorem in the repository's
existing Lean project that passes its full compilation and transitive audit.

Write `F_c^n(z)` for `QuadraticEscape.orbit c n z`, the actual finite iterate
of `z ↦ z²+c`. Fix natural times a,b, a compact preconnected target K, and
an anchor x with `F_c^a(x)=0` and `F_c^b(c)∈K`. Define the actual compact
selected components successively:

- D0 is the component of `(F_c^b)⁻¹(K)` through c;
- B0 is the component of `(z²+c)⁻¹(D0)` through zero;
- A0 is the component of `(F_c^a)⁻¹(B0)` through x.

Assume `F_c^a` is injective on A0, `F_c^b` is injective on D0, and neither
compact core encounters zero strictly before its corresponding terminal
time. Give open ambient neighborhoods WA of A0 and WD of D0.
No moving component, parameter neighborhood, open inverse domain,
critical-value retention, or return-degree conclusion is an input.

`quadratic_parameter_one_critical_return` constructs one open parameter
neighborhood P containing c, one fixed open preconnected target V containing
K with compact closure, and an analytic moving anchor ξ with ξ(c)=x. For
every d in P:

1. `F_d^a(ξ(d))=0` and the actual propagated critical value `F_d^b(d)` lies in V.
2. The actual components D_d, B_d, A_d selected successively through d, zero,
   and ξ(d) are open and have compact closures. The source and suffix closures
   remain inside WA and WD.
3. B_d is the **full** preimage `(z²+d)⁻¹(D_d)`. Both signs, including their
   collision at zero, are retained.
4. The prefix and suffix are injective on the closures of A_d and D_d.
5. A_d is the complete global component of `(F_d^(a+1+b))⁻¹(V)` through ξ(d).
   Its return maps onto all of V and is proper in the subspace topologies.
6. At every v in V, the sum of Mathlib's actual analytic multiplicities over
   the complete finite A_d-fiber equals two, including the critical fiber.

`quadratic_parameter_compactly_contained_return` additionally gives
`closure A_d ⊆ V` throughout P when the independently supplied compact
prefix satisfies `A0 ⊆ interior K`. That extra assumption is not inferred
for an empty-interior Julia target. Neither theorem asserts Jordan boundaries.

## Evidence

### 1. Uniform containment of every middle preimage

[QuadraticCriticalTrapping.lean](../../formalization/weighted/QuadraticCriticalTrapping.lean)
contains three public theorems:

- `quadratic_critical_component_eq_preimage` identifies the selected critical
  component with the full preimage of any preconnected target containing the
  critical value. No openness or local connectivity is required.
- `quadratic_full_preimage_parameter_neighborhood` proves that full-preimage
  containment over a compact target persists on common open parameter and
  target neighborhoods. It requires neither connectedness nor the presence
  of the critical value.
- `quadratic_full_preimage_parameter_collar` retains the same conclusion for
  the compact closure of the constructed target neighborhood.

For the second theorem, let W be the prescribed open source neighborhood.
The proper base quadratic maps the closed set `Wᶜ` to a closed set.
Its complement S contains the compact target D. Apply the tube lemma to
`(d,y) ↦ y+c-d` over `{c}×D`. For a nearby root with `z²+d=y`, the exact
identity `y+c-d=z²+c` puts the base quadratic value in S and forces z into
W. This controls every root simultaneously; a selected sign is not substituted
for the full critical inverse image.

### 2. Exact open inverse components

[QuadraticInverseOpen.lean](../../formalization/weighted/QuadraticInverseOpen.lean)
contains:

- `quadratic_compact_component_image`: derives compact-core surjectivity
  onto the connected target from the already formalized univalent collar.
- `connected_precompact_target_neighborhood`: constructs a connected open
  neighborhood whose compact closure lies in a prescribed open set.
- `quadratic_inverse_open_component`: if an inverse exists on a neighborhood
  of a connected open target's compact closure, its image is the entire global
  selected open component. Its closure stays inside the inverse source,
  is compact, and the actual iterate remains injective on that closure.

The compact inverse image of `closure V` is closed and contains the closure
of the open inverse image. Existing compact component recognition, followed
by component monotonicity, prevents the open component from continuing
outside the inverse source. This does not assume a regular or Jordan boundary.

### 3. Construct the complete moving return

[TelescopeParameterReturn.lean](../../formalization/weighted/TelescopeParameterReturn.lean)
contains the two principal theorems named in the claim.

The construction fixes the neighborhoods in a noncircular order:

1. Derive `F_c^a(A0)=B0` and `F_c^b(D0)=K`, and construct the common prefix
   analytic inverse with target Vp containing B0.
2. Use `B0=(z²+c)⁻¹(D0)` and the full-preimage trapping theorem to obtain
   a parameter neighborhood and a suffix ambient neighborhood Vt. Every
   nearby quadratic preimage of Vt lies in Vp.
3. Construct the common suffix inverse with its source closure inside
   `WD ∩ Vt`. Choose V once, with compact closure inside its inverse target.
4. Restrict parameters further so d remains in the suffix source and
   `F_d^b(d)∈V`. Both are open conditions holding at c. Consequently the
   actual critical value d belongs to the selected suffix component.
5. Recognize the entire suffix component by the open inverse theorem.
   Properness gives compact closure of its quadratic pullback, and the
   full-preimage trap puts that whole closure inside Vp. Apply open inverse
   recognition again to construct the compatible prefix component.
6. Apply `selected_saturated_return_full_degree` to these constructed actual
   stages. Its univalent-domain assumptions are discharged from the compact
   data. Exact component saturation, properness, surjectivity, and analytic
   degree two follow for every parameter in the common P.

Transporting only the old compact core over fixed K would not suffice:
`F_d^b(d)` need not stay in K, especially when K has empty interior. The
common **open** V and the explicit continuity restriction solve this issue.

### 4. Analytic symmetry of the complete actual return fiber

[TelescopeDeckInvolution.lean](../../formalization/weighted/TelescopeDeckInvolution.lean)
contains `quadratic_return_analytic_involution`. For an actual one-critical
return with an open injective prefix onto the selected critical component
and an injective suffix, it constructs one analytic map τ on the whole
return source. If g is the conformal prefix inverse, the formula is
`τ(z)=g(-F_c^a(z))`.

The theorem proves that τ preserves the source, satisfies `τ(τ(z))=z`,
reflects the prefix coordinate, and fixes a point exactly when that
prefix coordinate is zero. Every complete return fiber is precisely the
pair `{z,τ(z)}`, with coalescence at the critical point. It also proves
the actual derivative formula

```text
τ'(z) = -(F_c^a)'(z) / (F_c^a)'(τ(z)),
```

encoded as inverse multiplication, and `HasDerivAt τ (-1)` at the critical
fixed point. This is a holomorphic symmetry of the actual finite return,
not an identification with any source-prescribed relative-cover deck phase.
The theorem's proof uses the existing exact full-fiber pairing, while
constructing and differentiating a single analytic involution.

### Validation and development record

[PR #223](https://github.com/dovvnloading/loops-research-archive/pull/223) was
opened as a draft before proof development. Every source checkpoint and
repair is committed there. The first helper checkpoint compiled
`QuadraticCriticalTrapping`; the first open-component build exposed one
implicit-set elaboration mismatch, repaired by specifying the actual
preimage set and anchor explicitly. No unverified full result is claimed.

Local installation of pinned Lean 4.32.0 could not complete because the
workspace had approximately 260 MB free, less than the release archive.
The partial download was removed. The unchanged repository Lean CI is the
compilation and foundational-dependency authority for this contribution.

All modules are registered default Lake targets. The theorem and source
indexes register every public theorem under the existing CONSTRUCT route.
No workflow, validator, dependency pin, toolchain, or canonical status
record is modified. The existing audit permits only `propext`,
`Classical.choice`, and `Quot.sound` and checks every compiled declaration.

Reproduction:

```sh
cd formalization/weighted
lake exe cache get
lake build QuadraticCriticalTrapping QuadraticInverseOpen TelescopeParameterReturn TelescopeDeckInvolution
lake build
cd ../..
python code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

## Dependencies

Research target: MAPPING_TELESCOPE. Its documentary prerequisites
PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER, RELATIVE_COVER_LIFT, and
STAGE_FORWARD_CLOSURE provide context and are not used as Lean assumptions.

The proofs use the actual `QuadraticEscape.orbit`; compact and open selected
component results from `TelescopeCollarRecognition`, `TelescopeUnivalentCollars`,
and `QuadraticParameterInverse`; critical pullback connectedness from
`QuadraticEscapeFullness`; and analytic multiplicity and exact full-return
results from `TelescopeRamification`. Mathlib provides proper and closed maps,
compactness, connected components, the tube lemma, and complex analyticity.
All formal imports are traversed by the existing axiom audit.

## Boundary

This is finite-time and parameter-local progress for actual quadratic maps
under explicitly supplied compact-core assumptions. The neighborhoods depend
on the parameter, stage times, compact cores, and prescribed ambient sets.
No uniform radius over all periods, all native blocks, or infinite towers is
claimed. The times may be zero; the retained middle step is still quadratic.

The construction proves open connected domains and proper returns, with the
additional compact containment only under `A0 ⊆ interior K`. It does not prove
Jordan boundaries or simple connectivity, realize the native relative-cover
lifts or deck-phase itinerary, construct compatible cyclic Jordan cores for
every virtual block, or produce cross-scale compatibility.

Therefore MAPPING_TELESCOPE, H1-H4, UPTCR, and MLC retain their existing open
statuses. No ledger status change is requested. This advances the repository's
formal construction; no priority claim over classical mathematics is made.

## Attribution

Builds on the archive's
[saturated telescope](../saturated_telescope_20261126/NOTE.md),
[ramification and proper-collar](../telescope_ramification_order_20261126/NOTE.md),
[univalent telescope collars](../univalent_telescope_collars_20261126/NOTE.md), and
[parameter-stable inverse families](../parameter_stable_telescope_20261126/NOTE.md),
especially the explicit open boundary of the last contribution.
The source-facing residual is
[critical chronology, section 15.3](../../research/mlc_unified/critical_chronology_and_retimed_telescope.md#153-relative-cover-and-marked-telescope).
The prior written telescope audit's critical-retention counterexample motivates
retaining the actual moving critical value in this construction.

Proof development, integration, and independent source-level review are
AI-assisted. No independent human review has occurred.
