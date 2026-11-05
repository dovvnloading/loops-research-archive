# Proof-evidence traceability audit — 2026-11-04

**Baseline:** the original main-branch snapshot of dovvnloading/loops-research-archive, before the independent-audit branch was created. Inputs were the 465-entry root ledger.json and GitHub's recursive tree (541 blobs).

**Scope:** names of Markdown files directly referenced as evidence. A permissive basename match was used, so this is a *lower bound* on traceability problems. This test does not inspect document anchors, verify that a stated theorem occurs inside a cited file, or certify a proof.

## Baseline findings

| Structural check | Result |
|---|---:|
| Ledger entries | 465 |
| Imported / marked proved / open | 34 / 316 / 115 |
| Duplicate IDs | 0 |
| Dependencies to missing IDs | 0 |
| Dependency cycles | 0 |
| Marked proved with a direct open dependency | 0 |
| Evidence references to absent Markdown files | **36** |
| Distinct missing Markdown files | **8** |

Missing files and affected statuses:

| Referenced filename (not found anywhere in tree) | Entries | Statuses |
|---|---:|---|
| unbounded_satellite_modulus_source_reaudit_20260726.md | 1 | 1 imported |
| virtual_wave_horizon_certificate.md | 3 | 2 proved, 1 open |
| virtual_return_branch_language.md | 5 | 3 proved, 2 open |
| virtual_cantor_package_interface.md | 5 | 3 proved, 2 open |
| research_push_4_assessment_and_integration.md | 9 | 9 proved |
| research_push_5_assessment_and_integration.md | 8 | 6 proved, 2 open |
| push5_independent_reverification_and_extrapolation.md | 1 | 1 proved |
| direct_decoration_bigraded_kl_stage_grid.md | 4 | 3 proved, 1 open |
| **Total** | **36** | **27 proved, 8 open, 1 imported** |

The missing filenames are also mentioned in surviving source_ledger.md or research_log.md. The repository contains related research-push bundles, but similarity of subject matter does **not** establish that the missing proof is reproduced by any particular surviving file.

A limited history query at the expected paths returned no commits; this does not rule out a source file formerly existing outside Git, on another branch, or at another path.

## What the test does and does not establish

A broken pointer is a *reproducibility defect*, not a mathematical disproof. The 27 marked-proved entries lack directly retrievable evidence at their declared Markdown targets. Their proof status has **not** been silently changed, and their evidence pointers should **not** be redirected without checking the precise proof and hypotheses.

The companion script verifies plain Markdown targets as follows:

- Read ledger.json and count statuses independently of the declared counts.
- Check dependency IDs, cycles, and whether any marked-proved entry directly requires an open entry.
- Recognize plain filename.md#section and path/filename.md#section evidence strings.
- Mark a target absent only if its basename is missing from *everywhere* in the checkout.

This is intentionally conservative: links that pass may still have broken anchors, wrong proof sections, or a mismatched hypothesis.

## Repair sequence

1. Search original research workspace, local backups and earlier branches for the eight **exact files**, preserve hashes and attribution, and restore the originals if located.
2. Where the content survives under another name, match each cited theorem/claim to **specific** surviving lines and confirm all hypotheses before editing the evidence pointer.
3. Add a separate anchor/content audit. Keep traceability tests distinct from semantic proof validation.
4. Rerun the strict diagnostic. Do not add blank placeholders or promote any MLC gate simply to make CI green.

## Additional release-provenance gap

[Paper 3's existing QA_REPORT.md](../../papers/paper3_protected_carriers/QA_REPORT.md) and qa_release.py explicitly target Draft II, whereas [the root README](../../README.md) promotes a Draft III Visual Edition. A new Draft III integrity/visual and mathematical QA record is needed if that edition is intended as the canonical release. Draft II's deterministic QA does not automatically certify Draft III.

**Source entry points:** [ledger.json](../../ledger.json), [research log](../mlc_unified/research_log.md), [source ledger](../mlc_unified/source_ledger.md). The independent audit was added without modifying any existing proof-obligation status.
