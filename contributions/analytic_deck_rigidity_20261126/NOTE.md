---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="analytic-deck-rigidity-20261126"></a>

# Analytic deck rigidity, two-sheet path lifting, and moving actual returns

## Claim

**Verified: ten public Lean theorems in four modules.** The existing full
Lean CI build and transitive foundational-dependency audit passed on the
proof checkpoint linked below. No `sorry`, `admit`, or new axioms are used.

Let `F_c^n(z) = QuadraticEscape.orbit c n z` be the actual iterate of
`z ↦ z²+c`. The selected one-critical return is `R_c = F_c^(a+1+b)`:
an injective prefix `F_c^a`, one critical quadratic step, and an injective
suffix `F_c^b`. The sources and targets below are actual subsets of ℂ and
actual connected components of polynomial inverse images.

The contribution establishes four interfaces beyond the existing
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

4. **Exactly two complete path lifts.** One canonical involution works for
   every regular target path. Its two complete continuous lifts differ at
   every time, are exchanged pointwise by that involution, and exhaust all
   continuous lifts. The actual continuous-lift subtype has cardinality
   exactly two.

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

### 4. Exhaustive deck pairing of entire physical paths

[TelescopePathPairing.lean](../../formalization/weighted/TelescopePathPairing.lean)
contains `quadratic_return_deck_paired_paths`. It constructs one analytic
involution before quantifying over the target path. For every continuous
γ in V avoiding the propagated critical value, it constructs Γ₀ and Γ₁
with all of the following properties:

- both paths lie in the full actual source component and project to γ;
- `Γ₁(t)=τ(Γ₀(t))` for every t;
- `Γ₀(t) ≠ Γ₁(t)` for every t;
- every continuous A-valued lift of γ is globally Γ₀ or globally Γ₁;
- the subtype of **all** such complex-valued continuous lifts has
  `Nat.card = 2`.

The statement assumes neither a lift nor a covering. It constructs the
first lift from full target surjectivity and the unique-path theorem,
then constructs the second by the canonical analytic involution. Equality
at a common time would force a critical fixed point and hence the excluded
critical value.
The exact starting fiber and path uniqueness classify every other lift.
Thus a continuous lift cannot switch between the two phases mid-path.

### Validation and committed progress

[PR #226](https://github.com/dovvnloading/loops-research-archive/pull/226)
was opened as a draft before proof development. The initial code checkpoint
is [d737eb1](https://github.com/dovvnloading/loops-research-archive/commit/d737eb1061e1c9587f2558c4c75b80cb19cc5bf8).
The nine-theorem locally checked checkpoint is
[1e2556a](https://github.com/dovvnloading/loops-research-archive/commit/1e2556a5add8ed77ae4c0ec45c86be70c91fc428).
The main-branch integration
[e817a17](https://github.com/dovvnloading/loops-research-archive/commit/e817a17cedf9a62fc176af05b1efe57850e59577)
preserves both concurrent contributions in the shared registry and Lake
targets. The final proof checkpoint is
[e7adc33](https://github.com/dovvnloading/loops-research-archive/commit/e7adc33165913f080967f7579c7a82cdd70dc44b),
which adds the tenth theorem, exhaustive deck pairing of complete paths.
All four modules are registered default Lake targets, every public theorem
is in the theorem index, and each source uses the existing CONSTRUCT route.

The pinned Lean 4.32.0 toolchain and pinned Mathlib dependencies are
installed locally. All four modules pass `lake env lean` locally with exit
zero and no diagnostics. The rigidity file passed on its first run. The covering file
needed one explicit preimage type; the moving-family file needed explicit
component types and analytic projection composition. No theorem statement
was weakened. The complete path-pairing synthesis compiled on its first run.
The first three targets also passed `lake build` (8,688 jobs), and the
path-pairing target passed its build (8,669 jobs).

At proof checkpoint `e7adc33165913f080967f7579c7a82cdd70dc44b`, all
24 associated CI runs completed successfully (23 distinct workflows,
including a repeated contribution-intake run after the PR body update).
In particular:

- [Weighted spectral mathlib proofs](https://github.com/dovvnloading/loops-research-archive/actions/runs/45914913248/job/140231716782)
  reports `Build completed successfully (8938 jobs)` and
  `AXIOM_AUDIT_PASS weighted: 134 modules, 3098 declarations`.
  All four new modules have explicit audit records reporting allowed
  axioms only, including their private helper declarations.
- [Research validation](https://github.com/dovvnloading/loops-research-archive/actions/runs/45914913437/job/140231702162)
  reports a successful root build (77 jobs),
  `AXIOM_AUDIT_PASS root: 38 modules, 1625 declarations`, and successful
  audits for all five standalone Lean files. The audit's negative-fixture
  check also passes.
- [Contribution intake](https://github.com/dovvnloading/loops-research-archive/actions/runs/45914913275)
  and [model-to-geometry coverage](https://github.com/dovvnloading/loops-research-archive/actions/runs/45914913218)
  pass with the registered ten public theorems. The local contribution
  check and whitespace check pass as well.

The subsequent evidence-recording commit changes only this note. All four
proof sources and their registry/build configuration remain byte-for-byte
identical to the CI-verified proof checkpoint.

Reproduction:

```sh
cd formalization/weighted
lake exe cache get
lake build TelescopeDeckRigidity TelescopeUnbranchedCover TelescopeMovingDeck TelescopePathPairing
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
or extend regular path lifting through the branch value. Joint analyticity
of the family does not assert a conjugacy between different parameter
dynamics or global continuation in parameter space.

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
