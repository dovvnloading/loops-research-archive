---
ledger: VIRTUAL_RETURN_BASE_ATLAS
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-local-deck-20261126"></a>

# Local cyclic sheet symmetries of actual quadratic iterates

Ledger statement being addressed:

> Every actual virtual-Molecule block and finite provisional root package has source-defined open nice return localizations and actual atomic branch components with integer iterates, complete critical and degree words, exact component, parent, obstacle, localization, sheet, and protected-access phase data, together with exact enlargement morphisms and demand-bijective no-birth maps wherever complete language stability is claimed.

## Claim

Draft research claim, pending Lean implementation and CI: for every complex quadratic
parameter, every anchor, and every finite iterate, construct a physical open disk chart
whose analytic cyclic sheet action has order exactly two to the number of preterminal
critical encounters, and classify its fiber-preserving continuous self-maps.
No result in this draft is counted as proved until its Lean theorem compiles and passes
the repository's compiled proof-dependency audit.

## Evidence

This PR was opened before implementation to claim the obligation. Proofs, theorem
registration, and exact CI evidence will be committed here as work proceeds.

The first implementation checkpoint adds four registered modules:
`PowerMapRigidity.lean`, `QuadraticLocalDeckAction.lean`,
`QuadraticLocalDeckRigidity.lean`, and `QuadraticLocalInverseObstruction.lean`.
They contain the complete proposed proof terms, with local compilation and CI
validation still in progress at this checkpoint. The proposed obstruction concerns
continuous inverse choices over full punctured target disks, not merely analytic
inverse choices.

Local checkpoint: `lake build PowerMapRigidity` completed successfully with no warnings.
The module proves punctured-disk preconnectedness, constant-phase rigidity for every
positive complex power, and the absence of a continuous right inverse for every power
of degree greater than one (with an even-degree specialization). The physical transfer
and complete CI audit remain pending at this checkpoint.

The starting point is the existing actual-iterate analytic normal form in
`formalization/weighted/QuadraticPowerNormalForm.lean` and local census in
`formalization/weighted/QuadraticLocalFiberCensus.lean`. The new target is an entire
analytic symmetry action and its rigidity, including repeated critical encounters.

## Dependencies

The addressed row is `VIRTUAL_RETURN_BASE_ATLAS`. The existing source discussion is
`research/mlc_unified/virtual_return_base_atlas.md`, especially the branch record in
Section 3.3 and the open selector in Sections 8 and 11. Analytic inputs will come from
the repository's pinned Lean 4.32.0 / Mathlib v4.32.0 dependency chain.

## Boundary

The intended result is local and concerns the actual polynomial iterate. It does not
select a nice return base at a virtual scale, identify a prescribed global relative-cover
marking, construct protected prime-end accesses, or prove enlargement naturality.
`VIRTUAL_RETURN_BASE_ATLAS` remains open, as do H1--H4 and MLC. No ledger status change
is proposed. No worldwide originality claim is made for classical local branched-cover
mathematics or its formalization.

## Attribution

The local power-map description is classical complex analysis. This contribution builds
on the archive's exact critical-visit factorization, analytic power coordinates, and
local fiber census. The global one-critical involution in `TelescopeDeckInvolution.lean`
is a related prior result. Concurrent PRs #226 and #228 concern global degree-two
return symmetries and regular inverse atlases, respectively; this PR targets arbitrary
local critical multiplicities and their full cyclic symmetry group.
