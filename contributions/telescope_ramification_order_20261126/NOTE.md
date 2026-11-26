---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="telescope-ramification-order-20261126"></a>

# Actual quadratic return: analytic ramification and weighted degree

Ledger target: construct the actual selected relative-cover telescope, with compatible Jordan cores, complete component/deck-phase route and a single propagated critical value.

## Claim

Verified checkpoint: the actual quadratic spatial orbit has local analytic order exactly 2 raised to the number of visits to zero strictly before the terminal iterate. For the selected return of the existing saturated telescope theorem, injectivity on open prefix and suffix domains excludes all additional critical visits. The full attained fiber has total analytic multiplicity exactly two, including over the propagated critical value (one point of order two) and every other attained value (two points of order one).

## Evidence

Module: [TelescopeRamification.lean](../../formalization/weighted/TelescopeRamification.lean). The theorem index registers all public declarations. The previous QuadraticCriticalWindow module established exact polynomial divisibility; SaturatedTelescope established exact point-set fibers. The new interface uses Mathlib's actual analyticOrderAt and analyticOrderNatAt instead of equating distinct-point cardinality with analytic degree.

1. `orbit_eq_returnOrbit`, `orbit_map_eq_iterate`, `criticalVisits_succ`: reconcile the two existing definitions of the physical quadratic orbit and reuse its chronological critical count.
2. `orbit_analytic`, `orbit_ramification_factor`, `orbit_analytic_order`: translate the existing exact nonvanishing polynomial unit to an entire analytic factor and invoke Mathlib's characterization of finite analytic order. Repeated critical encounters double the exact order; the terminal point is excluded from the count.
3. `criticalVisits_add`, `criticalVisits_zero_iff`, `orbit_injOn_no_critical_visits`: the count is additive along physical concatenation, and injectivity on an open domain rules out every prior zero encounter. Indeed the intermediate image is open and contains a nontrivial reflected pair if it hits zero. Both lifts would then collide at the terminal time.
4. `orbit_unramified_order`, `return_order_one_step`, `selected_return_fiber_order`: the designated critical step determines the analytic multiplicity of every physical return point, after discharging the no-additional-critical-visits hypothesis on both sides using actual univalence on the supplied open domains.
5. `mem_localFiber_orbit`, `selected_return_weighted_degree`: reuse the repository's finite census of actual polynomial roots and exact return fiber theorems. Sum Mathlib analytic order over the complete selected local fiber; the total is two without assuming it as a hypothesis.

Build: `cd formalization/weighted && lake build TelescopeRamification`. Also run the existing weighted full build and transitive foundational-dependency audit. No local Lean toolchain or network-accessible git checkout is available in this environment; GitHub Actions on the exact PR head is the validation authority. No proof is counted as verified while CI is pending.

## Second extension (verified at the corrected proof checkpoint)

[TelescopeCollarRecognition.lean](../../formalization/weighted/TelescopeCollarRecognition.lean) addresses two remaining interface gaps.

- `orbit_component_image`, `orbit_component_compact_preimage`, `orbit_component_proper`: every anchored component of an open pullback by an actual finite quadratic iterate is a proper restriction in the subspace topologies; if the target is preconnected, it covers the whole target.
- `selected_saturated_return_full_degree`: under actual saturated component identifications and injective prefix/suffix, derive the exact full-return component, full target surjectivity, compact preimages, and the analytic multiplicity sum two over **every** target point. No prefix surjectivity premise is required.
- `proper_component_compact`, `proper_component_eventually_subset`, `proper_component_upper_semicontinuous`: compact selected pullback components obey a uniform target-perturbation margin for every prescribed open neighborhood. No local connectivity or finite-component hypothesis is imposed on the compact targets. This supplies a collar-shrinking mechanism, not a construction of cyclic Jordan cores.

Both modules passed the complete weighted build and transitive axiom audit at `db92682a616cc7f0af5c795aad349f1aefa8200e`; the subsequent main synchronization leaves both proof source files byte-identical. See the CI evidence below.

## Dependencies

MAPPING_TELESCOPE, PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER, RELATIVE_COVER_LIFT, STAGE_FORWARD_CLOSURE (research context only). Formal imports are QuadraticCriticalWindow, QuadraticCylinderCensus, SaturatedTelescope and Mathlib, including the pinned analytic order characterization, polynomial analyticity, open quadratic map and exact finite root census.

## Boundary

The weighted fiber conclusion concerns attained target values under actual selected-component and injective open-domain hypotheses. The second extension establishes full target attainment and properness from actual component identities, but does not construct the required cyclic Jordan domains, realize native markings or relative-cover lifts, or prove the general mapping telescope. No ledger status change is requested; MLC remains open. No priority claim over classical complex analysis.

## Attribution

Builds on the archive's QuadraticCriticalWindow exact local factor, the saturated telescope, the quadratic cylinder census, and the November 26 cyclic pullback audit. The first 14 registered declarations were verified at commit `cd14ca55e85af9b292ca60682d3d3b4f813b1d47`: [weighted build and complete axiom audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45881684623/job/140122324403), including the explicit module report `23 declarations, 22 theorems; allowed axioms only`.


## Verified CI evidence

[Corrected proof checkpoint `db92682a616cc7f0af5c795aad349f1aefa8200e`](https://github.com/dovvnloading/loops-research-archive/commit/db92682a616cc7f0af5c795aad349f1aefa8200e) passed both the [weighted push build and complete transitive axiom audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45882995665/job/140126700355) and [weighted PR build and audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45883003725/job/140126707305), plus contribution intake and research validation. The push log reports:

```text
Built TelescopeCollarRecognition (5.5s)
Build completed successfully (8828 jobs).
AXIOM_AUDIT weighted TelescopeCollarRecognition: 10 declarations, 10 theorems; allowed axioms only
AXIOM_AUDIT weighted TelescopeRamification: 23 declarations, 22 theorems; allowed axioms only
AXIOM_AUDIT_PASS weighted: 79 modules, 2143 declarations
```

23 explicitly named public theorems are registered, with the additional kernel theorem constants generated by Lean. Only the repository's three permitted standard axioms are accepted. Local Lean and networked git checkout were unavailable; validation is by repository CI. Main synchronization preserves the two proof blobs unchanged and requires integration CI for the new head. No canonical ledger status is promoted.
