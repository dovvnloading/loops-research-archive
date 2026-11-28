---
ledger: UNIVERSAL_PROTECTED_TOWER_CLOSURE
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Quadratic Thurston outlier: investigation in progress

This draft records an authorized independent investigation. No new mathematical
result, novelty claim, or successful Lean compilation is asserted at this stage.

## Claim

The precise remaining hypothesis of the archive's terminal written reduction
is `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, abbreviated UPTCR. The proved ledger
row `UPTCR_IMPLIES_MLC` is a conditional implication. UPTCR requires all six
clauses for every infinitely renormalizable quadratic, with universal constants:
canonical construction, analytic realization, finite response, backward
transition, coercive compactness, and rigidity with singleton parameter fiber
and connected relative neighborhoods. The last clause is not supplied by the
conditional implication. The archive's actual-family reduction is written;
its Lean ledger and specification checks do not formalize that analytic proof.

The requested new theorem is not yet selected. Before formalization this packet
will state each candidate and compare it with the closest primary literature;
candidates that specialize known theorems will be rejected.

## Evidence

Starting main commit: `f05f1b9dc8f5fc6eeb68491da2eb44eca6d6cec9`.

Archive pointers: `ledger.json`, rows `UPTCR_IMPLIES_MLC` and
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`;
`research/mlc_unified/manuscript.md`, Proposition D and Theorem E;
`research/mlc_unified/mlc_closure_proposition.md`, Sections 5--7.

The investigation deliberately excludes the established Wave, width, collar,
carrier, telescope, and tip-family machinery. It also excludes abstract metric
or sampling criteria, arithmetic center denominators, encounter-charge and
geometric-limit obstructions, Green-potential density criteria, and projective
critical-orbit cross-ratio jets.

An initial literature screen rejects a bare rederivation of the unicritical
Thurston-operator characteristic polynomial or its elementary spectral bounds:
these are already treated by X. Buff, A. Epstein, and S. Koch, *Eigenvalues of
the Thurston operator*, arXiv:1707.01990. Precise candidate comparisons will be
recorded before any candidate is formalized.

## Dependencies

The named ledger row is the research target, not an assumption of any new
theorem. No archive status files or workflows are to be changed.

## Boundary

This is an unfinished draft. It does not close UPTCR, any of H1--H4, or MLC.
No theorem is counted until it compiles in the existing Lean CI and passes the
transitive dependency audit without proof placeholders or new axioms.
If the investigation produces no qualifying new result, that fact will be
reported and the draft closed rather than submitted as a theorem.

## Attribution

The archive's reduction and obligation names belong to the existing project.
The investigation and subsequent formalization are AI generated; no human
specialist has reviewed either correctness or originality.
