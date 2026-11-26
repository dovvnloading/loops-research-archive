---
ledger: DIRECT_DECORATION_END_PRIME_END_COFINALITY
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="decoration-critical-cycle-exclusion-20261126"></a>

# Direct-decoration critical-cycle exclusion and exact external footprint transport

## Claim

Candidate Lean theorems strengthen Lemma 1 of the November 26 direct-decoration audit: noninjectivity of the actual return on one phase propagates around a cycle using only the two surjective orbit-image equalities, without a degree-one tail assumption. An injective closed cylinder of time at least the cycle period then excludes any preconnected phase avoiding its frontier. Independently the actual quadratic iterate commutes with exterior restriction, and an injective angular map on the initial footprint that maps each deeper footprint onto its target induces a bijection on the limiting footprints; a two-angle target obstruction transports back to every source center.

## Evidence

Registered module `formalization/weighted/DecorationCriticalCycle.lean`: `quadratic_phase_return_noninjective`, `quadratic_noninjective_persists`, `preconnected_avoids_frontier`, `quadratic_cycle_phase_exclusion`, `quadratic_exterior_image`, `nested_angular_bijOn`, `nested_angular_obstruction_transfer`.

The phase proof uses surjectivity of the backward arc to lift a hypothetical collision of the forward arc into the injective phase return. The injective phase return also implies injectivity of the backward arc. Together they contradict the original noninjective phase return. Persistence of a collision under later iterates is algebraic. The frontier lemma separates the interior and complement of a closed set; a preconnected phase meeting the cylinder must lie in its interior. This transfers a collision into the purported injective cylinder. The exterior image identity follows from the escape-potential scaling law. For angular transport, a target angle in every depth has a lift at every depth, and injectivity in the initial footprint makes all these lifts identical. Two distinct target angles therefore lift to distinct source angles.

Local Lean and network git are unavailable. These are candidates pending the existing CI compiler and full dependency audit; no theorem is counted as validated before that. Reproduce:

```sh
python code/verify_lean_coverage.py
python code/verify_physical_bridge_contracts.py
cd formalization/weighted
lake build DecorationCriticalCycle
cd ../..
python code/verify_lean_coverage.py --audit weighted
```

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION; research/independent_audits/decoration_end_cofinality_20261126/NOTE.md, sections 2–3; existing PrimeEndSectorImpressions, PrimeEndSectorFilters, SaturatedTelescope and QuadraticEscape Lean modules and Mathlib.

## Boundary

The exact closed physical cylinders, cycle image equalities, initial return noninjectivity, frontier avoidance, and injectivity of the deep actual restriction remain explicit hypotheses; this does not construct the native puzzle or degree-two return. Angular transport assumes the stage image equalities and initial branch injectivity; it does not construct the Böttcher coordinate or establish its sector incidence. No uniform shrinking, prime-end landing, global local connectivity or ledger promotion is claimed. No mathematical priority claim.

## Attribution

The archive's November 26 direct-decoration audit, the classical Böttcher/prime-end framework, and existing kernel formalization of quadratic iterates and escape profiles.
