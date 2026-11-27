---
ledger: DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-merger-balance-20261126"></a>

# Exact component merger accounting for actual quadratic root enlargements

Ledger statement being addressed:

> Under every certified final-root enlargement, prove the required subgroup reflection and exhaustion equalities and a Cartesian bijection of compactified geometric trace components, proper-path multiplicities, source and target endpoint frames, accesses, obstacles, nonproper bridges, and cyclic order. The first born, lost, or merged sheet, component, proper path, endpoint, access, obstacle, or bridge is the obstruction certificate. This geometric theorem is independent of the relation width-response estimate.

## Claim

Draft proof development; no compiled result is claimed at this checkpoint.

For the actual quadratic iterate f_c^n, an open connected target U inside an open connected target V, and one actual V-pullback component B, the proposed exact balance is

    number of old U-components in B + sum of their reflection debts
      = 1 + reflection debt of B + newly admitted critical charge.

The charge counts the actual fiber deficits over the distinct postcritical target values in V minus U. Repeated postcritical target values are counted once; repeated critical encounters are retained in the local multiplicities. Reflection debt is the independently recursive invariant already defined by QuadraticEnlargementDegree, not an asserted count of topological holes.

The proposed sharp selected-component consequence says that the retained inverse-source square is Cartesian exactly when

    old selected debt = enlarged debt + new critical charge.

A failed equality should produce a missing inverse point over every retained target value, including a critical target, and the equality should preserve the complete geometric inverse trace of every subset of U.

A simultaneous all-parameter sharpness construction is being formalized: remove all postcritical values through depth n from the complex plane and enlarge a small regular disk to the resulting target. All 2^n old univalent components merge into one actual enlarged component although both targets have empty postcritical inventories.

## Evidence

Proof development is in the pinned Lean 4 project. The intended modules are QuadraticMergerBalance, QuadraticMergerNaturality, and QuadraticSilentMerger, registered through the existing contributor command. They must pass the existing Lean CI build and its transitive dependency audit before the claims above are marked verified.

The balance uses the archive's already established degree conservation, target-wise defect conservation, and aggregate critical-defect/debt identity. It then partitions the postcritical inventory into old and newly admitted values and cancels the old charge. This run does not reprove those existing degree or census theorems.

The selected-component certificate uses the positivity of one plus each competing component's debt. The geometric trace statement concerns arbitrary target subsets and therefore includes geometric inverse traces with loops or backtracking; it is not based on enumerating only parametrized lifts.

The sharpness construction uses the connectedness of the complex plane minus a finite set, the existing full regular-fiber count, and the existing univalence theorem over a simply connected postcritical-free target. Those are imported ingredients; the new purpose is to realize the full possible defect in the merger balance for every parameter and depth.

## Dependencies

Target: DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH. Its source-facing native realization prerequisites remain open.

Existing formal inputs: QuadraticEnlargementDegree, QuadraticComponentFiberDegree, QuadraticCylinderRamification, QuadraticLocalRamification, and QuadraticRamificationCensus. In particular, the archive already has a reflection-rank equality criterion for no merger. The present proposed advance is the exact decomposition of mergers into new critical charge and reflection-debt transfer, and its sharp all-parameter realization.

Source-facing specification: research/mlc_unified/canonical_kl_geometric_trace_proper_end_response.md, PE-5. Earlier algebraic no-birth/source-boundary analyses are used only to identify the residual, not as extra Lean assumptions. Mathlib supplies finite sums and connectedness of finite-set complements.

## Boundary

This is a proposed partial result for actual polynomial inverse components, not a complete proof of the native ledger obligation. The native final-root certificate, canonical/KL relation alignment, compactified endpoints, proper-path status, protected accesses, obstacles, subgroup reflection/exhaustion, and cyclic order are not supplied by the component identity.

The sharp enlargement example is an actual quadratic construction, but it is not asserted to be an authorized native KL final-root enlargement. It refutes critical-inventory-only certification for arbitrary connected open polynomial targets, not the full native theorem.

No ledger status change is requested at this draft checkpoint. H1-H4, UPTCR, and MLC remain open. No priority claim over the mathematical literature is made.

## Attribution

Builds on the archive's actual quadratic component degree, enlargement conservation, local multiplicity, and critical census contributions. The native source motivation is Kahn-Lyubich decoration theory and the repository's canonical/KL geometric-trace specification. Proof development and review are AI-assisted; there has been no independent human review.
