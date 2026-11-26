---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-local-ramification-20261126"></a>

# Actual quadratic local ramification and multiplicity conservation

## Claim

Work in progress. The intended theorem connects the already formalized local critical order of the actual quadratic iterate with the intrinsic degree of an actual connected pullback component. For f(z)=z²+c, an open connected target V, n ≥ 0, a point x whose n-th iterate belongs to V, and any y in V, the goal is to prove that the sum over actual inverse points z in the selected component of 2 raised to the number of critical encounters before time n is exactly 2 raised to that component's reflection rank. Critical target values are included. No result is claimed until Lean compilation and the transitive axiom audit succeed.

## Evidence

Draft opened before proof implementation to claim the obligation. The first proof checkpoint adds [QuadraticLocalRamification.lean](../../formalization/weighted/QuadraticLocalRamification.lean) and [QuadraticRamificationCensus.lean](../../formalization/weighted/QuadraticRamificationCensus.lean). Existing QuadraticCriticalWindow proves exact local factorization; QuadraticComponentFiberDegree and QuadraticEnlargementDegree prove distinct-point fiber accounting. The new candidate bridge is a sum of the actual local ramification orders over the actual inverse fiber, followed by componentwise critical ramification accounting.

The first module supplies the critical-count shift, the exact local-order bridge, signed inverse-fiber transport, weighted degree conservation including critical targets, and equality of the recursive target defect with the sum of actual local multiplicity excesses. The second constructs the finite set of actual critical points, identifies it with the ramified part of the postcritical inverse census, and derives the exact component critical budget and its distinct-critical-point bound. Repeated critical orbit hits contribute multiplicity rather than duplicated points.

Lean and Mathlib cannot fit in the local workspace, so compilation is delegated to the repository's unchanged weighted CI. The initial local source-registration and trust-escape scan and ten adversarial coverage regressions pass. The first contribution check caught an accidental Markdown link in the prose; it is corrected in this checkpoint. The first proof checkpoint is commit `2513020d7eed9406770c8d5c2706d06d41cc48af`. Main advanced during development and caused shared-registry conflicts; merge commit `6c581daf4f3df10a03abfe384bd52bf1f54d4b4d` preserves both the new telescope registrations and this contribution. Contribution intake and model-to-geometry coverage pass on that merge. The first weighted build at [workflow 45899701683](https://github.com/dovvnloading/loops-research-archive/actions/runs/45899701683) failed at the finite-image summand elaboration described below.

The first weighted build rejected one under-specified summand in the finite-image reindexing lemma. The second checkpoint supplies that function explicitly; no theorem statement or assumption is weakened. All first-checkpoint proof errors are recorded in the linked run. The extended statements still require a successful build and transitive audit.

Validation uses the pinned Lean 4.32.0 project, default-target registration via code/contribute.py lean-add, repository contribution checks, and the weighted CI build with its transitive axiom audit. Proof placeholders, new axioms, and trust escapes are forbidden.

### Second proof checkpoint

The extension adds exact local-multiplicity composition, equality of the original pullback component with the pullback of its actual intermediate component, intermediate weighted-fiber conservation, and additivity of the intrinsic reflection rank. The census is identified with the literal zero set of the complex derivative. On the whole plane the reflection rank is n and the missing-charge correction is zero, yielding the exact global ramification sum 2^n-1.

[QuadraticCriticalPortrait.lean](../../formalization/weighted/QuadraticCriticalPortrait.lean) derives the recurrence of the distinct critical locus from the actual two signed inverse branches. If 0 has no positive return before n, there are exactly 2^n-1 distinct critical points. If p is its first positive return, then at horizon n at least p the number is (2^p-2) times 2^(n-p), plus one. These are proposed Lean proofs pending the same CI, not numerical certificates.

### Third proof checkpoint and validation

The second proof commit `4046a0037c33c20c6ccd42c3ec7465d41227a119` compiled all eighteen then-present theorems of QuadraticLocalRamification in [weighted workflow 45900067531](https://github.com/dovvnloading/loops-research-archive/actions/runs/45900067531). Research validation, contribution intake, and model-to-geometry coverage passed. The weighted build stopped at four Census proof-script sites: rewriting under inequality, a propositional simplification, and exposing the local component abbreviation to arithmetic. Those scripts are corrected without changing the statements; the aggregate audit is still required.

The final substantive extension is `mergerCensus_complete_iff_weighted_degree`: for a declared subfamily of the actual old components inside a selected enlarged component, completeness is equivalent to summed local multiplicity equal to the enlarged intrinsic degree. The anchor can be any point of the old target, including a critical value. This removes the regular-anchor hypothesis from the previous degree-based exhaustion test. Its partition lemma counts each actual inverse point in its unique old component. Concrete critical-count corollaries cover every horizon for c=0, c=-1 and c=-2.

## Dependencies

Ledger prerequisites: DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING. Lean dependencies under review: QuadraticCriticalWindow, QuadraticComponentFiberDegree, QuadraticEnlargementDegree, and their Mathlib imports.

## Boundary

This contribution targets an actual polynomial component theorem, not the native virtual-cylinder realization. Identification of the authorized virtual demand family, target bases, localization, marked accesses, chronology, sheet metadata, and root-enlargement certificates remains open. The ledger row stays open. H1–H4, UPTCR and MLC are not proved. No literature priority claim.

## Attribution

Builds on the archive's quadratic critical-window, component-fiber-degree, and enlargement-degree contributions and Mathlib. Exact theorem dependencies and verified statements will be recorded as the proof develops.
