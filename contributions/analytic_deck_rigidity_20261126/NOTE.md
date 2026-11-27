---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="analytic-deck-rigidity-20261126"></a>

# Analytic deck rigidity, two-sheet path lifting, and moving actual returns

## Claim

**Development checkpoint: nine public Lean theorem statements in three
modules.** Compilation and CI evidence are recorded below. A statement is
counted as verified only after the existing full Lean build and transitive
foundational-dependency audit pass on the proof sources.

Let `F_c^n(z) = QuadraticEscape.orbit c n z` be the actual iterate of
`z ↦ z²+c`. The selected one-critical return is `R_c = F_c^(a+1+b)`:
an injective prefix `F_c^a`, one critical quadratic step, and an injective
suffix `F_c^b`. The sources and targets below are actual subsets of ℂ and
actual connected components of polynomial inverse images.

The contribution establishes three interfaces beyond the existing
involution and parameter-stable proper-return construction:

1. **Global deck rigidity.** An analytic self-map of the full return source
   preserving R_c is globally either the identity or the canonical
   involution. Injectivity, surjectivity, and involutivity are conclusions.
   Agreement at one regular source mark determines the map everywhere.
2. **Actual two-sheet covering and path lifting.** Removing the propagated
   critical value gives a covering, with evenly covered neighborhoods
   indexed by `Fin 2`. Every continuous target path avoiding that value
   has a unique continuous lift in the full source after fixing its start.
3. **Joint analytic parameter transport.** Compact one-critical data
   construct one open connected parameter-phase domain of full moving
   return components, and a single jointly analytic involution on it.
   Its fixed point is precisely the analytic moving critical anchor.
   Properness, compact source closures, and total analytic degree two
   persist on the same parameter neighborhood and fixed terminal target.

These are finite-time, parameter-local statements under the explicitly
listed actual-core or actual-component hypotheses. They do not close the
native relative-cover construction gate.

## Evidence

### 1. Global rigidity and intrinsic phase pairing

[TelescopeDeckRigidity.lean](../../formalization/weighted/TelescopeDeckRigidity.lean)
contains four public theorems.

- `quadratic_return_deck_classification` assumes an open prefix source A,
  an injective prefix onto the critical component B, and an injective
  suffix on D, where B is the component of `(z²+c)⁻¹(D)` through zero
  and c belongs to D. It constructs the analytic involution τ and
  classifies every analytic σ with `σ(A) ⊆ A` and `R_c ∘ σ = R_c` on A.
  Neither connectedness of A nor bijectivity of σ is an input: source
  connectedness follows from the conformal prefix inverse, and σ is
  proved bijective and involutive.
- `quadratic_return_deck_marked_unique` proves that two such maps agreeing
  at one x in A with `F_c^a(x) ≠ 0` agree on all of A. The regularity
  condition matters because both deck choices fix the critical point.
- `quadratic_return_pairing_unique` proves that two complete pairings of
  the same actual return fibers coincide, regardless of how their stage
  factorizations or inverse choices were produced.
- `quadratic_return_pairing_conjugacy` proves that a bijection of actual
  return sources preserving and reflecting full fiber equality transports
  the pairings. It includes the singleton critical fiber and does not
  assume the desired intertwining identity.

For rigidity, the existing fiber theorem gives the pointwise equation

```text
(σ(z)-z) (σ(z)-τ(z)) = 0.
```

Mathlib's analytic identity principle on the connected source forces one
factor to vanish throughout the source. Thus independent pointwise branch
choices become one global analytic choice. The exact API is
`AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero` in
`Mathlib/Analysis/Analytic/IsolatedZeros.lean` at the pinned revision.

### 2. Covering neighborhoods and unique physical path transport

[TelescopeUnbranchedCover.lean](../../formalization/weighted/TelescopeUnbranchedCover.lean)
contains four public theorems.

- `quadratic_return_offcritical_deriv` excludes all preterminal critical
  visits at a source point whose return value differs from `F_c^b(c)`.
  It derives nonvanishing of the actual iterate derivative from open
  prefix/suffix injectivity and the chronological critical-visit count.
- `orbit_restriction_cover_of_regular` applies to a proper restriction of
  any actual iterate between open subsets of ℂ. On any target subset
  whose inverse points have nonzero derivative, it constructs
  `IsCoveringMapOn`. Properness is used as a closed-map condition;
  finite polynomial fibers and the analytic inverse theorem construct
  the local covering neighborhoods.
- `quadratic_return_two_sheet_cover` applies to the actual saturated
  components D, B, A selected through c, zero, and x, over an open
  preconnected V containing `F_c^b(c)`. It derives properness and the
  covering, and gives `IsEvenlyCovered ... v (Fin 2)` at every regular
  target v. The two-sheet count comes from the complete physical fiber,
  not from an assumed covering degree.
- `quadratic_return_unique_path_lift` takes any continuous map
  `γ : C(unitInterval, ℂ)` lying in V and avoiding `F_c^b(c)`, and any
  z in A with `R_c(z)=γ(0)`. It proves existence and uniqueness of a
  continuous Γ with Γ(0)=z, Γ(t) in A for every t, and
  `R_c(Γ(t))=γ(t)` for every t. No differentiability or polygonal
  restriction on the path is imposed.

The path theorem uses Mathlib's covering-space lift and its uniqueness
on the actual punctured subspace restriction. It transports the entire
path through the declared global component.

### 3. One jointly analytic involution on the moving total domain

[TelescopeMovingDeck.lean](../../formalization/weighted/TelescopeMovingDeck.lean)
contains `quadratic_parameter_return_deck_family`.

Its hypotheses are the compact actual one-critical data used by the
existing parameter-return theorem: a compact preconnected terminal K,
`F_c^a(x)=0`, `F_c^b(c) ∈ K`, the successive compact selected components
D0, B0, A0, injective prefix and suffix restrictions, and no preterminal
critical encounters on those compact cores. Prescribed open ambient
sets WA and WD contain A0 and D0. No moving domains, inverse families,
parameter neighborhood, or deck transport are inputs.

The theorem constructs an open connected parameter neighborhood P of c,
a fixed open connected target V containing K with compact closure, an
analytic anchor ξ with ξ(c)=x, and one function τ(d,z). Put

```text
A_d = connectedComponentIn ((F_d^(a+1+b))⁻¹(V)) (ξ(d)),
Ω = {(d,z) : d ∈ P and z ∈ A_d}.
```

It proves that Ω is open and preconnected, and τ is jointly complex
analytic on Ω. For every d in P:

- `F_d^a(ξ(d))=0`, and the propagated critical value `F_d^b(d)` lies in V;
- A_d is open, contains ξ(d), has compact closure inside WA, and maps
  properly onto all of V;
- every full A_d-fiber has total Mathlib analytic multiplicity two;
- τ_d maps A_d into itself, squares to the identity, and reflects the
  prefix coordinate: `F_d^a(τ_d(z))=-F_d^a(z)`;
- `τ_d(z)=z` exactly when `z=ξ(d)`;
- `R_d(w)=R_d(z)` exactly when `w=z` or `w=τ_d(z)`;
- the spatial derivative of τ_d at ξ(d) is -1.

The new step retains the common jointly analytic prefix inverse gp from
the compact construction and uses the single formula
`τ(d,z)=gp(d,-F_d^a(z))`. Full critical-preimage trapping ensures that
both signs remain in its common inverse target. The total actual domain
is identified exactly with the open condition

```text
d ∈ P, z ∈ Up, F_d^(a+1)(z) ∈ Us, F_d^(a+1+b)(z) ∈ V,
```

where Up and Us are the common prefix and suffix inverse neighborhoods.
This proves openness of the actual component family, rather than assuming
it. Its connectedness follows by joining each connected vertical fiber
to the connected analytic anchor graph. The fiber identities and critical
derivative agree with the existing fixed-parameter involution by prefix
injectivity.

### Validation and committed progress

[PR #226](https://github.com/dovvnloading/loops-research-archive/pull/226)
was opened as a draft before proof development. The initial code checkpoint
is [d737eb1](https://github.com/dovvnloading/loops-research-archive/commit/d737eb1061e1c9587f2558c4c75b80cb19cc5bf8).
All three modules are registered default Lake targets, every public theorem
is in the theorem index, and each source uses the existing CONSTRUCT route.

The pinned Lean 4.32.0 toolchain and pinned Mathlib dependencies are
installed locally. All three modules pass `lake env lean` locally with exit zero and no
diagnostics. The rigidity file passed on its first run. The covering file
needed one explicit preimage type; the moving-family file needed explicit
component types and analytic projection composition. No theorem statement
was weakened. Full integration and the unchanged CI audits are in progress;
no CI success is asserted before those runs finish.

Reproduction:

```sh
cd formalization/weighted
lake exe cache get
lake build TelescopeDeckRigidity TelescopeUnbranchedCover TelescopeMovingDeck
lake build
cd ../..
python code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

No workflow, validator, dependency pin, toolchain, or status ledger is
changed. The existing transitive audit permits only `propext`,
`Classical.choice`, and `Quot.sound`.

## Dependencies

Research target: MAPPING_TELESCOPE. Its documentary prerequisites
PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER, RELATIVE_COVER_LIFT, and
STAGE_FORWARD_CLOSURE are context, not additional Lean assumptions.

Formal dependencies include QuadraticEscape's actual orbit;
SaturatedTelescope's exact component and complete-fiber identities;
TelescopeRamification's critical chronology and analytic multiplicities;
TelescopeCollarRecognition's proper actual return restrictions;
TelescopeConformalInverse; QuadraticParameterInverse;
QuadraticCriticalTrapping; QuadraticInverseOpen; TelescopeParameterReturn;
and TelescopeDeckInvolution. The pinned Mathlib supplies the analytic
identity principle, inverse theorem, topology of covering spaces, and
continuous path lifting. All formal imports are included in the existing
transitive declaration audit.

## Boundary

This is progress for actual finite quadratic returns under stated compact
core or selected-component hypotheses. It is not a theorem that every
native virtual block supplies those hypotheses. The local parameter
neighborhoods depend on the chosen parameter, times, cores, and ambient
sets; no uniform bound over all periods or infinite towers is proved.

The path theorem avoids the unique critical value. It does not prescribe
which sheet a closed loop returns to, compute fundamental-group monodromy,
or extend regular path lifting through the branch value.

The involution and covering live on the physical return components.
Native relative-cover existence, the required identification of its
source-prescribed marking with these maps, protected ideal-boundary
accesses, compatible cyclic Jordan cores, and cross-scale compatibility
remain open. The general pairing-conjugacy result assumes an actual
bijection preserving and reflecting fiber equality; it does not construct
that bijection for native localization sheets.

MAPPING_TELESCOPE, H1-H4, UPTCR, and MLC keep their existing open statuses.
No ledger promotion or new MLC case is claimed. This advances the archive's
formal development, with no priority claim over classical mathematics.

## Attribution

Builds on the archive's saturated telescope, ramification, univalent collar,
parameter-stable inverse-family, and parameter-stable critical-return
contributions, especially PR #223's full return and analytic involution.
The source-facing residual is
[critical chronology, section 15.3](../../research/mlc_unified/critical_chronology_and_retimed_telescope.md#153-relative-cover-and-marked-telescope).

Proof development, implementation, integration, and independent source-level
review are AI-assisted. No independent human review has occurred.
