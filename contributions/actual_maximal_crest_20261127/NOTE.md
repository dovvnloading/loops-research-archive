---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="actual-maximal-crest-20261127"></a>

# Actual maximal connected crest endpoints and their limit

## Claim

Draft research claim; no new theorem is certified at this initial commit.
The target is the still-open `NOV26_OPEN_CREST_LIMIT` entry in `ledger.json`.
This work aims to construct the maximal connected terminal-gate collar
for the actual normalized quadratic returns, including its moving endpoint,
and prove convergence to the limiting quadratic endpoint.

## Evidence

Baseline: main commit `7b179434fdbf12070485ba4a91c6dc3c9f55fa24`.
The earlier `actual_crest_foliation_20261126` contribution constructs actual
crossing curves only on `[63/1000,33/500]`. Its Boundary items 2 and 4 leave
the actual maximal collar endpoint and full circular-collar coefficient
unproved. The earlier `limiting_crest_gate_20261126` contribution proves
the unique endpoint of the limiting model, not that of an actual return.

Planned proof route: extend the actual crossing family to
`[1/16,133/2000]`, construct its first terminal-gate exit, and use uniform
convergence plus the strict limiting radial order to control the moving
endpoint. A first-exit construction must not assume that the actual
perturbed terminal function is monotone or has only one root.

The pinned Lean 4.32.0 and Mathlib environment is available locally.
Compilation, theorem registration, and the existing CI transitive axiom
audit are mandatory before any result is claimed.

### First compiled checkpoint

`formalization/weighted/CrestFirstExit.lean` now proves first-exit
existence, uniqueness of the first exit, the exact surviving connected
component, uniform outer sign margins, and convergence of every selected
root under uniform convergence to a strictly decreasing limiting
coordinate. The actual perturbed coordinate need not be monotone.
All nine public declarations compile locally with the pinned toolchain;
their transitive dependencies use only `propext`, `Classical.choice`, and
`Quot.sound`. These are supporting lemmas, not a claim that the actual
crest endpoint has already been constructed. The actual-polynomial
specialization and moving-endpoint integral are in progress.

## Dependencies

`NOV26_CREST_16`, `NOV26_OPEN_CREST_LIMIT`; the existing
`LimitingCrestEndpoint`, `ActualCrestLimit`, `NearTwoTip`, and
`QuadraticCrestCrossing` Lean modules; the two contribution packets named
above; the source crest-asymptotics audit under
`research/independent_audits/crest_transport_asymptotics_20261116/`.

## Boundary

This draft does not close the ledger entry. The parameter identity with
the designated primitive component, full marked proper-path survival,
and the identification of an integral with physical extremal width must
be proved or explicitly retained as remaining gaps. No ledger status
change is requested at this stage. No MLC or H1-H4 conclusion is claimed.

## Attribution

Builds on the archive's November crest-asymptotics program and the merged
limiting-model and actual-crossing formalizations. The initial audit has
ruled out re-submitting their fixed-radius crossing or model-endpoint
results as new progress. AI-assisted proof development and independent
AI scope review; no independent human review. Released under CC0.
