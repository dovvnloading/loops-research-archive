---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Rigorous limiting quadratic crest gate

## Claim

Work in progress. The target is the positive limiting circular collar in the
quadratic model Q_k(z) = 1 - k z^2 named in the existing crest asymptotics note.
The first objective is a uniform, exact polynomial certificate for a nonempty
radial interval and its angular and terminal gates, followed by quantitative
persistence under explicitly bounded perturbations. No result is yet claimed.

## Evidence

The source is research/independent_audits/crest_transport_asymptotics_20261116/NOTE.md,
section "Quantitative near--2 evidence and the open limit". Its finite p <= 16
certificates do not establish its numerical limiting-model conjecture.
New mathematical results will be Lean theorems compiled and dependency-audited
by the repository's existing CI. Local Lean is unavailable and the workspace
does not have disk capacity for the toolchain and Mathlib cache.

## Dependencies

NOV26_CREST_16 supplies the existing finite provenance. The planned proof will
use exact rational polynomial inequalities, actual complex quadratic maps,
and Mathlib's elementary analysis; it will not assume the desired positive
collar or interpret a numerical approximation as a theorem.

## Boundary

NOV26_OPEN_CREST_LIMIT remains open. A limiting quadratic-model gate alone
does not identify actual all-period KKL prime-end markings or prove the
uniform convergence of the physical maps and widths. Those implications
must be proved separately before proposing closure. No status record changes.

## Attribution

Builds on the archive's November 16 crest transport asymptotics and its
explicit limiting quadratic, circle center, angular branch, and terminal
gate. AI assistance covers proof search, Lean implementation, and review;
no independent human review has occurred.
