---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Quadratic outlier investigation — draft research record

This draft was opened before formalization. No new theorem or progress toward MLC is claimed at this checkpoint. The result field is provisional while the draft is in progress.

## Claim

The aim is a precise obstruction, criterion, or reduction for the actual quadratic family outside the archive's marked-width machinery. A candidate will be stated here and compared with the closest classical results before any formalization. A specialization or direct classical consequence will be discarded as a research claim.

## Evidence

### Starting snapshot and exact open hypothesis

The starting `main` commit is `6964d70bea8a68acae4a627b421086b29f6f63b3`. `UPTCR_IMPLIES_MLC` is a proved **written conditional implication** whose explicit open hypothesis is `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, the Universal Protected-Tower Compactness and Rigidity proposition (UPTCR). See [`mlc_closure_proposition.md`, §§4–7](../../research/mlc_unified/mlc_closure_proposition.md) and [`uptcr_cross_validation.md`, Theorem 4.1](../../research/mlc_unified/uptcr_cross_validation.md).

It requires one set of universal constants, chosen before the parameter, and all six clauses on the same actual tower for every infinitely renormalizable quadratic polynomial: protected carriers, exact analytic realization, finite response state, backward transition, coercive marked compactness, and tower rigidity. The last clause includes singleton full marked parameter fibers and compact connected relative parameter neighborhoods forming a shrinking neighborhood basis. Neither that clause nor the universal package is established.

The existing Lean logical composition theorem is not a formal proof of this analytic package or an unconditional theorem about MLC: `ResearchGates.lean` also assumes the terminal bridge interpreting its abstract package.

### Research constraints

This investigation sets aside Waves, marked widths, collars, protected carriers, mapping telescopes, tip families, abstract metric/sampling criteria, arithmetic denominators of centers, encounter-charge/geometric-limit obstructions, and Green-potential density criteria.

### Checkpoint 0

The exact archive gap and relevant prior quadratic formalizations are being audited. Candidate selection and primary-source novelty checks are underway. There is no Lean result at this checkpoint.

## Dependencies

The UPTCR statement and `H4_RIGIDITY` are context, not assumptions to be used to manufacture a conclusion. Any retained theorem will state its own actual quadratic-family hypotheses and list every mathematical input explicitly.

## Boundary

This is an early draft, not a contribution ready for acceptance. It does not close H4, UPTCR, or MLC. It does not claim mathematical novelty or a compiled Lean theorem yet. An unsuccessful investigation will be recorded honestly and the draft closed rather than a known theorem relabeled as new research.

## Attribution

Classical inputs remain credited to their authors. The archive's existing research and formalizations are due to its credited authors and contributors. This investigation uses OpenAI ChatGPT GPT-6 Astra Pro for proof search, source comparison, formalization, and adversarial review; no human specialist review has occurred.
