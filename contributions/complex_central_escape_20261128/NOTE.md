---
ledger: NOV26_OPEN_SUBSECTOR
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Investigation: uniform complex escape for the actual central return

Ledger statement being addressed:

> Fine-subsector edge escape: Old-edge spectral data do not imply iterated fine-subsector domination or zero-edge escape (F12).

## Claim

Research in progress. No new theorem or closure is claimed at this initial revision.

The target is a quantitative off-real escape theorem for the actual normalized three-return, together with identification of its full complex filled set with its orbit-defined real interval. The physical quadratic iterate, its complete selected component, and the actual critical orbit must be retained throughout.

## Evidence

The main branch already proves uniform real angular expansion and a physical precritical mesh in contributions/physical_cylinder_expansion_20261128/NOTE.md. Its boundary explicitly leaves identification of the real orbit interval with the full complex filled set open.

The proposed attack is to factor the actual return at its critical value and two endpoints, obtain a uniform complex angular derivative estimate, and use that estimate to exclude every non-real nonescaping point. An absolute approximation to the limiting quadratic is insufficient near the real interval; the proof must control the relative escape defect. These are research targets, not established lemmas.

Every proposed mathematical advance will be recorded in this PR and must become a compiled Lean theorem in formalization/weighted, registered in the existing build and theorem index, before it is reported as proved.

## Dependencies

- NOV26_OPEN_SUBSECTOR: open ledger target.
- Existing ActualThreeReturnExpansion, ActualThreeReturnNormalization, PhysicalCentralCarrier, and the selected ThreeReturn component construction.
- All exact imported declarations and any external results will be recorded if used.

## Boundary

No new mathematical result is established at this revision. No ledger status change is proposed. Real expansion alone does not identify the complex filled set, give a complete KKL prime-end marking, or prove general Wave amplification, H1-H4, or MLC.

The execution workspace was full before cloning, and no local Lean executable was available. Source work currently uses the GitHub connector; the unchanged repository CI must validate any submitted Lean proof. No local compilation is claimed.

## Attribution

This attempt builds on the archive's physical cylinder expansion and all-period selected three-return construction. Those existing results are not claimed as new. Research and adversarial scope review are by OpenAI ChatGPT GPT-6 Astra Pro; no human review has occurred.
