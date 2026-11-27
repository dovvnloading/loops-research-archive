---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="actual-crest-foliation-20261126"></a>

# Actual quadratic-return crest foliation

## Claim

Work in progress. This packet targets the missing passage from the
archive's pointwise perturbed crossing to a unique, continuously selected
crest curve for literal quadratic return maps. A second target is a sharp
all-period coefficient window for the designated near-minus-two family.
No new mathematical result is claimed before its Lean proof compiles.

## Evidence

The starting point is `LimitingCrestQuadraticReturn.lean`, merged in PR
#233. It proves a complete complex remainder bound and one crossing at
each radius, conditional on explicit real return-scale and coefficient
inequalities. It does not prove crossing uniqueness, a continuous angular
selection, or an embedded transported arc family for the actual return.

The intended new proof will control the complete derivative or divided
difference of the actual return, retain every higher-degree term, and
derive injectivity and angular order on a fixed complex domain. It will
then construct the crossing family and state its exact relationship to
the original polynomial iterates. Every completed theorem and validation
checkpoint will be committed to this packet and its registered Lean
modules.

## Dependencies

NOV26_CREST_16 and the merged `limiting_crest_gate_20261126` packet supply
the existing frontier and source context. The proof will build on the
repository's actual quadratic-return definitions and Mathlib. The older
all-period coarse real chart is archived; reproducing it alone will not
be counted as the new contribution.

## Boundary

NOV26_OPEN_CREST_LIMIT remains open during development. Uniqueness and
continuity of a crossing family do not by themselves identify physical
KKL markings, prove an extremal-width formula, or settle convergence of
canonical widths. Each remaining hypothesis will be stated explicitly.
No ledger status change is requested at this stage.

## Attribution

This work builds on the November crest audits and PR #233's exact
limiting-model and literal-return estimates. Proof development and
review are AI-assisted; no independent human review has occurred. CC0.
