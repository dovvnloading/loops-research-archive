---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation and Lean proof development
human_review: none
---

# Actual crest transport on the complete original parent

## Claim

This is an early research claim, not a proved result. The target is to rule out
late re-entry of the actual terminal gate on the full original circular
parent, and to prove the geometric properties needed to interpret the
selected transported curves. No new theorem is claimed at this checkpoint.

## Evidence

The starting revision is 665e5f9. The existing
`ActualCrestTheorem.exists_actual_complete_collars_and_limit` constructs an
actual unique terminal collar on `[1/16,133/2000]`, and proves convergence of
its full radial coefficient. Its contribution packet explicitly leaves
possible admissible components elsewhere in the larger original parent.
The present attempt addresses that remaining quantifier and the actual
transported curve family. Existing results will be used and attributed,
not counted as new progress.

The intended evidence is Lean 4 in the existing weighted project, compiled
by the repository's unchanged CI and subject to the existing transitive
dependency audit. Draft investigations will be committed as they develop;
only completed, checked theorems can become the final claim.

## Dependencies

`NOV26_CREST_16`, `NOV26_OPEN_CREST_LIMIT`; the previous
`actual_crest_foliation_20261126` and `actual_maximal_crest_20261127`
contributions; `NearTwoTip`, `ActualCrestSupport`,
`QuadraticCrestDividedDifference`, and the actual proper-return modules.

## Boundary

The ledger obligation remains open. There is no completed new theorem at
this checkpoint, and no assertion of global mathematical priority. The
previous radial coefficient alone does not establish physical extremal
width or the complete KKL marking. This attempt must prove any such
identification it uses; no missing geometric conclusion will be assumed
in a theorem premise and then reported as established.

## Attribution

The source object is the selected circular parent in
`research/independent_audits/crest_transport_asymptotics_20261116/NOTE.md`.
The preceding Lean contributions supply actual parameter construction,
local endpoint geometry, and radial-integral convergence. Classical
complex analysis and Mathlib results will be cited where used. Original
contributions are released under the repository's CC0 terms.
