Research Push VI - nested-separator contact closure
Date: 2026-07-25

Principal result
----------------
For the binary direct-decoration f^q pullback package, all historical physical
contacts with future nested shells are exactly represented on the current
separator.  The accumulated prefix response, current root-shared contact mask,
and current trace-coordinate map form an exact Markov state.  Nonconsecutive
bypasses are glued when they appear on the current separator; no all-pairs
historical contact graph and no no-bypass hypothesis are needed.

Conservative status
-------------------
Proved split node:
  PHYSICAL_END_SEPARATOR_CONTACT_REALIZATION

Still open:
  DIRECT_DECORATION_TRACE_COLLAR_REALIZATION in its global source-complete scope
  END_PLUMBING_TRACE_RESPONSE_CONTROL in the H2/Value topology
  VAAPC-I, H2, MBTT, H3 coercivity, rigidity, UPTCR, MLC

Next largest gate
-----------------
  CONTACT_AWARE_RESPONSE_COCYCLE_COMPACTNESS_AND_VALUE_OBSERVABILITY

Audit
-----
separator_contact_audit.py uses exact SymPy rational Schur complements.
250 randomized trials gave zero one-shot-versus-recursive discrepancy and zero
mask failures.  Shapely is used only to check the alternating-rectangle bypass
geometry.

Files
-----
mlc_research_push_6.md                 full theorem/proof memo
mlc_manuscript_insertions_push_6.tex  proposed manuscript insertion source
mlc_manuscript_insertions_push_6.pdf  render-verified five-page insertion
mlc_ledger_patch_push_6.json          conservative split-node patch proposal
separator_contact_audit.py            exact recursive response audit
separator_contact_report.json         audit output
contact_mask_compiler.py              finite contact-mask compiler
contact_mask_example.json              sample input
contact_mask_example_output.json       sample compiled state
pdf_preflight_push6.txt                PDF preflight report
