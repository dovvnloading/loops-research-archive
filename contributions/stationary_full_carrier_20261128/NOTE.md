---
ledger: KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation and independent AI review
human_review: none
---

# Investigation of full-carrier stationary separation

Ledger statement being addressed:

> For the canonical Q_0-selected chain through H=b+2, prove in the full physical carrier that Q_0 separates alpha^0 from L_0^1 and, for every 1<=n<H, Q_n separates alpha^n from L_0^(n+1). Construct the proof-used collars and marked accesses and prove that competing carrier routes outside the selected inverse sheet do not bypass Q_n. Applying phi_0 inside one sheet is insufficient because a separating path in the full carrier may leave that sheet.

## Claim

**Draft investigation. No new theorem is claimed.** The target is the remaining
noncompact connected-bypass case for the actual physical selected carrier, without
assuming the native quotient identification, saturation, finite-component
exhaustion, or critical clearance that earlier reductions leave open.

A result will count here only after a new Lean theorem is registered and passes
the repository's unchanged build and transitive axiom audit. Re-formalizing an
archived lemma, assuming the desired geometric identification, or proving a
classical substitute will not be presented as progress.

## Evidence

Baseline: `main` at `f05f1b9dc8f5fc6eeb68491da2eb44eca6d6cec9`.

The existing `StationaryCompactContact.lean` already proves compact-witness
injectivity and three conditional full-separation routes. It forces a surviving
antipodal connected bypass to accumulate on the deleted critical set (at zero
under the full empty-interior hypothesis). It does not exclude that accumulation.

The investigation will test whether actual primitive-return dynamics excludes
this residual, or whether a genuine example refutes the proposed implication.
Every proposed argument will be checked against the existing compact-contact,
separator-transport, multi-interface, and geometric-fiber results before any
formalization is described as new.

Lean and Lake are not installed in this local environment. Any proof submitted
will therefore require a successful build in the existing repository CI before
it is counted as a theorem. No Lean file has been added at this checkpoint.

## Dependencies

- `KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION` (target, still open).
- `KKL_NATIVE_TERMINAL_HUBBARD_TREE`.
- `KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN`.
- `KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN`.
- `KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS`.
- Earlier work: `contributions/stationary_compact_contact_separator_20261126/NOTE.md`,
  `contributions/stationary_separator_no_bypass_20261126/NOTE.md`, and
  `contributions/stationary_multi_interface_separator_20261126/NOTE.md`.

## Boundary

No obligation is closed and no mathematical advance is claimed at this initial
checkpoint. All native carrier, collar, marked-access, and full-horizon clauses
remain open. No status-record change is proposed. The draft will be closed if
the investigation produces no qualifying result.

## Attribution

The source problem belongs to the Kahn-Kapiamba-Lyubich program and the archive's
stationary separator analyses. The prior Lean modules are dependencies and prior
work, not discoveries of this investigation. No worldwide priority claim is made.
