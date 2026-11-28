---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation and Lean proof development
human_review: none
---

<a id="actual-crest-global-20261127"></a>

# Actual crest transport on the complete original parent

## Claim

This is an unvalidated proof-development checkpoint. The draft Lean proofs
exclude every later actual terminal crossing on the full original circular
parent, identify the entire two-cut gate with one interval, and classify
all real intersections of the first four images of each actual semicircle.
The selected closed fourth-image arcs are also proved jointly injective in
radius and angle in the draft source. These statements are not claimed as
checked results until the unchanged Lean CI accepts them.

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

The first CI attempt isolated one failed positivity tactic in the enlarged
disk estimate; the next checkpoint corrects it and adds the principal
proofs. `ActualCrestGlobalModel.eventually_all_actual_tips_no_reentry`
quantifies over every actual signed-tip parameter and every angular crossing
in `[133/2000,1/8]`. Its proof obtains a uniform separation on the full
radius-angle rectangle, proves actual intermediate-domain control, and
compares three literal normalized returns with the model. It does not assume
a selected crossing family or the absence of later components.

`ActualCrestGlobal.actual_original_parent_collars` combines that new
exclusion with the archived short-window endpoint theorem: the entire
original-parent gate is exactly `(1/16,r_p)`, and the archived convergence
theorem now applies to that entire gate. `ActualCrestArcCensus` separately
checks real intersections, closed-arc collisions, and rectifiability.

## Dependencies

`NOV26_CREST_16`, `NOV26_OPEN_CREST_LIMIT`; the previous
`actual_crest_foliation_20261126` and `actual_maximal_crest_20261127`
contributions; `NearTwoTip`, `ActualCrestSupport`,
`QuadraticCrestDividedDifference`, and the actual proper-return modules.

## Boundary

The ledger obligation remains open. The source is not yet compiler-validated
at this checkpoint, and there is no assertion of global mathematical priority. The
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
