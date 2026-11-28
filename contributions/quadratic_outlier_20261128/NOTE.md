---
ledger: H4_RIGIDITY
result: no_retained_result
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Quadratic outlier investigation — no retained theorem

**Outcome: the requested new, CI-compiled Lean theorem was not obtained.**
This is the record of an unsuccessful draft investigation. The result field
intentionally names no accepted contribution category: no partial theorem,
obstruction, or closure of a ledger gate is being submitted for acceptance.

## Claim

No new mathematical claim is retained. The investigation identified the
archive's exact open terminal hypothesis and rejected five candidate
directions before formalization. Statements, calculations, primary-source
comparisons, and individual decisions are in [CANDIDATES.md](./CANDIDATES.md).
Those rejections are a research record, not the new theorem requested.

## Evidence

### Exact open hypothesis

The inspected starting main commit was
6964d70bea8a68acae4a627b421086b29f6f63b3.

The ledger records the written conditional theorem
**UPTCR_IMPLIES_MLC** with dependencies **YOCCOZ** and **BACKWARD_RECORD** and
the explicit open hypothesis **UNIVERSAL_PROTECTED_TOWER_CLOSURE** (UPTCR).

The statements are in:

- [UPTCR, §§4–5](../../research/mlc_unified/mlc_closure_proposition.md):
  the universal quantifiers and six clauses.
- [Theorem 4.1](../../research/mlc_unified/uptcr_cross_validation.md):
  the terminal conditional implication.
- [Novelty/value audit, §9](../../research/mlc_unified/novelty_and_value_audit_20260725.md):
  the existing warning that the implication does not eliminate the hard
  rigidity content.

UPTCR requires universal constants chosen before the parameter, and all of
the following on the same actual tower for every infinitely renormalizable
quadratic:

1. Canonical protected carriers.
2. Exact analytic realization.
3. A uniformly finite response state.
4. A universal backward transition.
5. Coercive marked compactness.
6. Tower rigidity, a singleton full marked parameter fiber, and nested compact
   connected relative parameter neighborhoods forming a shrinking basis.

The final clause includes the analytic pullback/rigidity and the
fiber-to-neighborhood conclusion. Merely proving another formal implication
to it does not supply it.

[ResearchGates.lean](../../ResearchGates.lean) is a specification/composition
layer. Its conditional_local_connectivity additionally assumes a
ComplementTheorem and an actual TerminalBridge; its abstract slots are not
a formal realization of the analytic UPTCR package.

### Novelty gate

The five recorded candidates were:

- A cross-parameter critical-orbit cancellation criterion: direct subtraction
  and variation of constants.
- A center derivative/Thurston determinant identity: classical.
- Separation inside a nonhyperbolic combinatorial class using its existing
  angled internal address: the missing rigidity assertion remains.
- Parameter equality from infinitely intersecting critical orbits: a direct
  classical consequence.
- Finite projective matching of consecutive critical-orbit points: the
  rational-function identity principle and normalization.

The candidate record gives precise hypotheses and distinguishes a false
novelty claim from an unproved stronger statement. No global novelty
impossibility theorem is asserted.

### Existing archive work checked

Existing formalizations already cover
[critical transversality](../../formalization/weighted/QuadraticCriticalTransversality.lean),
[periodic motion](../../formalization/weighted/QuadraticPeriodicMotion.lean),
[collision factorizations](../../formalization/weighted/QuadraticCollisionFactorization.lean),
[local multiplier coordinates](../../formalization/weighted/QuadraticMultiplierCoordinate.lean),
and [phase secant univalence](../../formalization/weighted/QuadraticParameterUnivalence.lean).
None is relabeled as a new contribution here.

### Formalization and validation status

Lean 4.32.0 was made available locally and a compiler smoke check passed.
No candidate survived the pre-formalization novelty gate, so no new Lean
module was written, registered, or compiled. No new theorem has CI or
transitive-axiom validation. Documentation/intake checks cannot substitute
for that validation.

The local draft-intake check can be reproduced with:

~~~sh
python code/contribute.py check --draft \
  --pr-title '[H4_RIGIDITY] No retained theorem after outlier novelty checks'
~~~

The unclassified result is permitted only for a draft. This packet is not
eligible for ready-for-review acceptance.

## Dependencies

UPTCR and H4 are the target context, not hypotheses used to assert a new
conclusion. Primary references and the exact classical consequences used to
reject candidates are linked in [CANDIDATES.md](./CANDIDATES.md).

## Boundary

Nothing here closes H4, UPTCR, or MLC. No new fiber criterion, actual-family
obstruction, or reduction is claimed. The failed search does not prove that
such a result is impossible.

The missing research step is a genuinely new argument coupling an invariant
or operator to two actual parameters in one combinatorial fiber. None of the
checked finite identities provides that step. No ready-for-review
contribution is being claimed, and the archive's status records are unchanged.

Under AGENTS.md's instruction to close an unsuccessful draft with no retained
result, PR #266 is to be closed after preserving this record. Its commits
remain available as the investigation history.

## Attribution

Classical results remain attributed to their authors in the candidate record.
The archive's mathematics and formalizations remain credited to its authors
and contributors. OpenAI ChatGPT GPT-6 Astra Pro assisted with source audits,
candidate generation, adversarial checks, and local environment preparation.
No human specialist reviewed this investigation.
