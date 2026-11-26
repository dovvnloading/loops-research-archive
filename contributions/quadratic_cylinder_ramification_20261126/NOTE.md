---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="quadratic-cylinder-ramification-20261126"></a>

# Actual quadratic pullback component ramification and enlargement

Ledger statement: after a target base is typed, exhaust the reached open pullback components by the authorized equal-depth cylinders, with all required metadata and enlargement stability.

## Claim

For f(z)=z²+c, n arbitrary and V open and simply connected, all global components of f^{-n}(V) are univalent sheets exactly when V avoids the finite postcritical set {f^k(c): k<n}. In that case each component is simply connected and maps homeomorphically onto V. A critical orbit encounter obstructs local injectivity on every open neighborhood, without requiring a simply connected target.

For nested open simply connected U⊆V with U postcritical-free, the canonical inclusion of components is onto, and a merger of distinct old components occurs exactly when V contains a postcritical value through the same horizon. A merger can be witnessed over any selected point y in U. The necessity of a merger from a new critical value already holds when V is merely open and connected. These first eleven public Lean theorems passed the build and dependency audit at the checkpoint below. The extension additionally proposes an exact intermediate-component transport identity and an individual-component cardinal-one test over a regular target point, not requiring the entire target to avoid postcritical values.

## Evidence

The registered [QuadraticCylinderRamification.lean](../../formalization/weighted/QuadraticCylinderRamification.lean) module imports the existing actual quadratic census.

1. `quadratic_global_component_image` proves surjectivity of every global pullback component by openness, properness, and relative clopen image. `open_restriction_homeomorph` converts genuine open injective restrictions into homeomorphisms of subspaces.
2. `quadratic_iterate_univalent_component` inducts through actual inverse components. The image of a connected component under the first quadratic step lies in a single component of the tail pullback. The tail is simply connected by induction and excludes c by the postcritical hypothesis. The earlier square-root branch theorem makes the first step injective; composing gives injectivity and the open restriction homeomorphism transports simple connectivity.
3. `quadratic_critical_hit_noninjective` sends an open neighborhood forward to an open set containing zero; a small antipodal pair lifts to two distinct original points with the same final iterate. `quadratic_iterate_surjective` supplies a prefix preimage of zero. `quadratic_postcritical_component_obstruction` and `quadratic_all_components_univalent_iff` yield the converse and exact criterion.
4. `quadratic_component_anchor_bound`: every distinct component consumes at least one distinct point of every target fiber. `quadratic_postcritical_target_merges_regular_fiber`: a regular fiber has cardinal 2^n, whereas any critical-value fiber has strictly smaller cardinal, by the previously proved exact inverse-fiber census. Therefore some pair of distinct regular inverse points lies in the same enlarged component.
5. `quadratic_enlargement_component_surjective` proves that every new component contains a full old component (use the common target point). `quadratic_enlargement_merger_iff` combines the count obstruction with univalence to obtain the exact two-sided criterion for global component mergers.

6. Extension: `quadratic_prefix_component_image` identifies the actual prefix image of a global pullback component with the whole remaining-iterate component, even at a ramified step. `quadratic_component_univalent_from_regular_fiber` inducts using this equality. A unique regular inverse point forces the tail component to have one such point; if the tail contains c then reflection in the component containing zero pairs distinct regular inverse points, a contradiction. `quadratic_component_single_regular_fiber_iff` and `quadratic_localized_single_regular_fiber_iff` express the test as exact cardinal one, also for any proper open localization. These four added theorems are pending verification.

Verified baseline: [bc1c6143ab23f7d90b3bd38c5acc95f7c48e8931](https://github.com/dovvnloading/loops-research-archive/commit/bc1c6143ab23f7d90b3bd38c5acc95f7c48e8931), [push weighted CI 45876638914](https://github.com/dovvnloading/loops-research-archive/actions/runs/45876638914) and [PR weighted CI 45876647870](https://github.com/dovvnloading/loops-research-archive/actions/runs/45876647870) succeeded. The push audit reported 20 module declarations, 19 kernel theorems including generated auxiliaries, and `AXIOM_AUDIT_PASS weighted: 75 modules, 2060 declarations`. The earlier weighted run 45876388477 rejected path-connectedness projection and dependent membership casts; corrected without changing statements. This is a verified eleven-theorem baseline, not a green claim for the later extension.

Local Lean/lake and networked git are unavailable; all validation must come from GitHub Actions. Reproduction: `cd formalization/weighted && lake build QuadraticCylinderRamification`, then from the repository root run `python3 -B code/verify_lean_coverage.py --audit weighted`. The extension must pass the same full build and transitive audit.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING; the existing QuadraticCylinderCensus, QuadraticCriticalFiberCensus and StationarySeparatorTransport modules; Mathlib's continuous root and homeomorphism theory. See [finite-cylinder commuting lift](../../research/mlc_unified/finite_cylinder_commuting_lift.md), sections 4–5; [single-fiber census](../cylinder_fiber_exhaustion_20261126/NOTE.md); [ramification-aware census](../critical_fiber_census_20261126/NOTE.md).

## Boundary

These statements concern the actual global inverse components, not a declared symbolic family. An actual virtual stage must still supply the simply connected typed target, proper localization or global component identification, declared cylinders and their metadata, and a certificate that its enlargement satisfies the critical-value exclusion. No claim that every source stage is postcritical-free. A target with holes may have monodromy even without critical values; the converse in the merger criterion requires simple connectivity. No cross-base ownership, access or sheet metadata, boundary contact control, universal marked realization, H1–H4, UPTCR, or MLC is established. No literature priority is claimed.

## Attribution

Builds on Kahn–Lyubich's decoration construction (arXiv:math/0609046), the archive's finite-cylinder commuting lift and earlier exact quadratic component and inverse-fiber censuses, and Mathlib. The intended contribution is an explicit Lean formalization of the global component and critical-value enlargement criterion, not a claim that the underlying complex-dynamics principle is new.
