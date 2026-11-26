---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="analytic-deck-rigidity-20261126"></a>

# Analytic deck rigidity for actual one-critical quadratic returns

## Claim

Work in progress. This packet targets global uniqueness and compatibility of
analytic deck choices on the actual connected one-critical return domains
constructed in the existing Lean project. No new theorem is counted as a
result until it compiles in the repository's CI and passes its transitive
foundational-dependency audit.

The first intended theorem classifies every analytic fiber-preserving map
from a connected return domain to itself as the identity or the canonical
analytic involution. The next targets are uniqueness from a noncritical
marked point and compatibility under restriction and parameter variation.
Statements and scope will be updated to match the compiled proofs.

## Evidence

The draft PR is opened before proof development. Lean source, registration,
proof repairs, and validation evidence will be committed incrementally.
All proofs will use the existing Lean 4.32.0 Mathlib project and unchanged CI.

## Dependencies

Research target: MAPPING_TELESCOPE. Existing formal inputs include
TelescopeDeckInvolution, TelescopeParameterReturn, TelescopeConformalInverse,
and the actual quadratic orbit defined in QuadraticEscape. Mathlib supplies
analytic and topological results; no research conjecture is a new premise.

## Boundary

No global mapping telescope, native relative-cover marking, Jordan-core
existence, infinite-scale compatibility, H1-H4, UPTCR, or MLC conclusion is
claimed. The result will remain partial and no ledger status change is
requested. This is a formal extension of the archive, with no assertion of
priority over classical complex analysis.

## Attribution

Builds on the saturated telescope, ramification, univalent collars,
parameter-stable inverse families, and parameter-stable critical-return
contributions, in particular the analytic involution constructed in
PR #223. The source-facing residual is the archive's critical chronology
and retimed telescope, section 15.3. Proof development and review are
AI-assisted; no human review has occurred.
