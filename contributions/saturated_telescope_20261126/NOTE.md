---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="saturated-telescope-20261126"></a>

# Exact connected-component and critical-fiber recognition for saturated telescope stages

Ledger statement: Every actual finite virtual stage cycle admits compatible selected relative-cover lifts embedded on relatively compact Jordan cores, preserving the component/deck-phase route and the propagated critical value to obtain a closed degree-two selected return.

## Claim

Candidate Lean result: for continuous stages on actual topological spaces, any finite locally saturated anchored chain is globally saturated at every consecutive subsegment, without local connectivity. For the actual complex map z ↦ z²+c, with a selected critical pullback component through 0 and an injective prefix onto it and injective suffix on its target, the attained return fibers have exactly two points except at the propagated critical value, which has a unique preimage. The second preimage is constructed, not assumed.

## Evidence

The registered Mathlib module `formalization/weighted/SaturatedTelescope.lean` contains:

1. `component_pullback_comp`: the image of the entire connected component of the composite preimage is preconnected and contains the intermediate anchor. Maximality therefore yields equality with the iterated selected component, not just inclusion.
2. `saturated_route_component`, `routeMap_image`, `quadratic_segment_saturation`: induction through any consecutive segment, using the actual physical iterate and summed stage time. This applies to cyclic return recognition and intermediate subsegments alike.
3. `quadratic_critical_component_symmetric`: negation preserves the full quadratic preimage, fixes the anchor 0, and is continuous. Hence negation preserves the selected connected component even if it is not locally connected.
4. `quadratic_segment_fiber_pair`, `quadratic_return_critical_value`, `quadratic_return_noncritical_fiber`: construct the opposite-sign partner using prefix surjectivity; exclude additional partners by the actual quadratic collision factorization and injectivity of the prefix and suffix. This yields an exact complex-point fiber set and locates the unique critical fiber, without assuming the desired return multiplicity.

Reproduction from the repository root:

```sh
python code/verify_lean_coverage.py
python code/verify_physical_bridge_contracts.py
cd formalization/weighted
lake exe cache get
lake build SaturatedTelescope
lake build
cd ../..
python code/verify_lean_coverage.py --audit weighted
```

The local chat environment has no Lean or network-accessible git checkout. Registration follows the repository's lean-add procedure via the GitHub connector, and the existing weighted workflow is the authoritative compilation and transitive dependency check. Until that workflow passes on this source, these are candidate formal results only.

## Dependencies

Research context: MAPPING_TELESCOPE, PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER, RELATIVE_COVER_LIFT, STAGE_FORWARD_CLOSURE; see research/independent_audits/h1_mapping_telescope_20261126/NOTE.md, §2. The Lean proof does not import these ledger assertions as assumptions. It uses Mathlib connected components, continuity, image/preimage and elementary complex field algebra, and the archive's existing QuadraticEscape.orbit definition.

## Boundary

The theorem assumes actual connected-component saturation and anchor consistency at each stage; it does not construct the virtual carriers. The fiber result assumes an actual selected component through the critical point, prefix bijectivity onto it and suffix injectivity on the target. It proves point-set cardinality, not holomorphic degree counted with multiplicity, properness, a polynomial-like restriction, a deck-phase lift, or relative-cover/Jordan-core realization. The actual source-facing existence and marking problems and MLC remain open. No ledger promotion is requested. No claim of priority over classical topology or complex dynamics.

## Attribution

Builds on the archive's saturated cyclic pullback argument (2026-11-26) and the existing QuadraticEscape module. The composition and fiber lemmas are explicit formal extensions of the recognition interface to all subsegments and the exact critical-value fiber. No human review.
