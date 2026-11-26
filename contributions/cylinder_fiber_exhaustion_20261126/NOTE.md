---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="cylinder-fiber-exhaustion-20261126"></a>

# Single-fiber exhaustion of localized quadratic pullback components

## Claim

Lean-verified reduction: for an actual complex quadratic iterate restricted properly to an open localized domain over a connected open target, each connected component surjects onto that target. Thus it suffices to check a single target fiber against the declared component family to establish component exhaustion, with unique ownership if the declared components are distinct. This replaces a whole-domain coverage verification by a finite single-fiber verification under the stated hypotheses. Separately, a finite census of distinct actual inverse points is bounded by the degree, and attaining the degree certifies the entire global fiber without assuming a regular value.

## Evidence

[`QuadraticCylinderCensus.lean`](../../formalization/weighted/QuadraticCylinderCensus.lean) is registered in the weighted Lean project. The formal proof consists of 19 explicitly named theorems:

1. `open_component_relative_closed` proves the ambient relative-closure identity for components of open sets, using local connectedness of the ambient space, not local connectivity of a Julia set.
2. `localized_component_image` uses the open and closed map properties and relative closedness of the localized domain to show that the image of each component is relatively clopen in its connected target; the image is nonempty.
3. `proper_localization_relative_closed` derives the relative closedness premise from properness of the actual restriction, even if its domain is disconnected. It reuses the compact inverse-image lemma in `StationarySeparatorTransport`.
4. `quadratic_open`, `quadratic_proper`, `quadratic_iterate_open`, and `quadratic_iterate_proper` prove the ambient open/proper map properties for the actual polynomial and every iterate, including critical points. Properness follows from the bound on the norm of inverse images of compact sets.
5. `one_fiber_component_exhaustion` and `quadratic_localized_census` reduce coverage to a single target fiber and return equality of actual connected subsets, with unique declared index under distinctness.
6. `iteratePolynomial_eval`, `iteratePolynomial_degree`, `quadratic_fiber_card_bound`, and `quadratic_full_degree_census` identify the actual iterate polynomial of degree 2^n and prove the sharp global census criterion by root counting.

7. `mem_localFiber`, `localFiber_card_bound`, and `quadratic_localized_count_census` turn the localized census into an exact finite root-set test; a finite index family with distinct components and common-fiber anchors exhausts the localization as soon as its cardinality reaches the actual filtered fiber size. This handles q-return localizations without using the incorrect global degree as a local count.
8. `no_new_component_of_same_fiber` proves that an open proper enlargement with unchanged filtered fiber has no new component missing every old declared component. It allows mergers; the no-merger condition and full metadata compatibility remain separate.

9. `proper_localization_component_global` identifies each component of a proper open localization with its full ambient pullback component. This removes the need to assume that identification separately, once properness and openness are certified.
10. `proper_localization_eq_of_same_fiber` strengthens the enlargement result: if both domains are proper and open over the same connected target, unchanged local fiber implies equality of the domains. In that fixed-target setting there can be neither mergers nor new components.

CI development history: the first weighted build (run 45867844853, commit 4f2b19c) rejected a closure-lemma application and the polynomial recurrence/degree proofs. The corrections passed the full build and transitive dependency audit at the checkpoint below.

Validation: [commit c12a8aac](https://github.com/dovvnloading/loops-research-archive/commit/c12a8aac47843ede66611e749b0eb0bc3a41a831) passed [weighted Lean CI run 45868510235](https://github.com/dovvnloading/loops-research-archive/actions/runs/45868510235) (Lean 4.32.0, source coverage and trust-escape scan, full build and transitive kernel axiom audit). The complete observed workflow set on that head was 23/23 successful. The audit printed:

```text
AXIOM_AUDIT weighted QuadraticCylinderCensus: 35 declarations, 29 theorems; allowed axioms only
AXIOM_AUDIT_PASS weighted: 69 modules, 1903 declarations
```

The 29 kernel theorem constants include generated auxiliaries; 19 theorems are explicitly named in the source and registered in the theorem index. Only the repository's permitted standard Lean axioms are used. Local Lean and networked git were unavailable, so validation is from repository CI. Reproduction from the repository root: `cd formalization/weighted && lake build QuadraticCylinderCensus`, then return to the root and run `python3 -B code/verify_lean_coverage.py --audit weighted`. This note records the verified proof checkpoint without changing its Lean source.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING. Earlier work: [finite-cylinder commuting lift](../../research/mlc_unified/finite_cylinder_commuting_lift.md), sections 4–5; [direct-decoration compactification](../../research/mlc_unified/virtual_cantor_pullback_compactification.md), sections 3 and 5; [root-pullback carrier](../../research/mlc_unified/root_pullback_virtual_carrier.md), section 5; `StationarySeparatorTransport.proper_restriction_compact_preimage`. Mathlib's complex open quotient map for positive powers, compact-preimage characterization of proper maps, and polynomial root count are used directly.

## Boundary

This does not assert that the source's actual localized domain is proper over the typed target, that its declared cylinders are full connected components of that localization, or that a one-fiber census has been supplied. In particular the two univalent branches of a q-return yield 2^m depth-m words, not the global degree 2^(qm) for q>1. The global full-degree criterion must not be substituted for a localized census. Critical chronology, access/obstacle metadata, cross-base ownership and enlargement across changing targets still require geometric certificates. No ledger or global gate is closed. No literature priority is claimed.

## Attribution

Builds on Kahn–Lyubich's decoration construction (arXiv:math/0609046), the archive's direct-decoration compactification and finite-cylinder commuting lift, and Mathlib's established topology and polynomial results.
