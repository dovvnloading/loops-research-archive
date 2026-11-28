---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

# Connected-fiber detection by finite sampling energy

<a id="fiber-sampling-energy-20261127"></a>

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

Early draft research claim; no new theorem is claimed proved at this checkpoint. The proposed independent route uses quantitative statistical observability of a connected fiber by finite weighted parameter samples. Connectedness should amplify one detectable pair into many disjoint detectable neighborhoods. The intended theorem compares sampling energy, the mass detecting each neighborhood, and observation radius. All final claims must be Lean theorems compiled and audited by the unchanged CI.

## Evidence

The archive's proved reduction is `UPTCR_IMPLIES_MLC`, conditional on the still-open `UNIVERSAL_PROTECTED_TOWER_CLOSURE`. The latter is the entire jointly realized six-clause proposition in `research/mlc_unified/mlc_closure_proposition.md`, not a missing finite lemma. Its constants are chosen before the quadratic polynomial. Its sixth clause already requires singleton parameter fibers and connected relative neighborhoods. `ResearchGates.lean` checks abstract predicate composition and explicitly retains the geometric terminal bridge; it does not instantiate that bridge with quadratic parameters.

This investigation deliberately leaves the marked-width construction. The proposed pattern comes from small-ball probabilities, packing, and quantitative identifiability: a connected set of positive diameter must supply many separated observation sites, so uniformly detecting it has an energy cost. Global equidistribution alone does not provide the needed local detection bound.

## Dependencies

Research target: `H4_RIGIDITY`; its prerequisite `H3_COERCIVITY` remains open. Planned Lean proofs use the repository-pinned Mathlib. No new analytic input is assumed proved.

## Boundary

No claim of H4, UPTCR, MLC, a new MLC case, or worldwide priority. The application must still construct the actual finite quadratic sample families, prove local mass detection of every candidate fiber point, prove the required energy rate, and supply the connected parameter-neighborhood interface. Existing generic fiber and finite-cut criteria in the literature are not claimed new.

The local Lean installer exceeded available scratch storage before installation. Local compilation is unavailable; the existing CI is the proof authority.

## Attribution

Archive bottleneck audit: `research/mlc_unified/mlc_closure_proposition.md`, `research/mlc_unified/novelty_and_value_audit_20260725.md`, and `ResearchGates.lean`. Earlier archive quotient, common-cut and nested-compact criteria will be compared explicitly in the final note. All work is AI-assisted and awaits independent human review.
