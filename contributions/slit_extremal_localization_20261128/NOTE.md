---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation and Lean proof development
human_review: none
---

# The complete marked-slit extremal problem: research record

## Claim

This is an initial research checkpoint, not a claimed mathematical result.
The target is the exact optimum or attainment of the complete parent-Wave
supremum in the limiting four-cut slit geometry. A result will be counted only
after compilation in the repository's Lean project and its transitive axiom
audit. No worldwide-priority claim is made from an archive search alone.

## Evidence

The starting main commit is `6a10209b3cc51878bc45de7668894757b2575e08`.
The obligation is open in `ledger.json` under `research_updates`.
`code/contribute.py start` currently reads only the main `obligations` array;
the existing contribution validator accepts both arrays, so this packet is
created directly without changing the contribution tooling or ledger.

Prior work inspected before choosing the target:

1. `contributions/marked_wave_supremum_limit_20261127/NOTE.md` and the
   `SlitWaveModulus`, `MarkedSlitTransport`, `SlitWaveFinite`,
   `ActualParentSupremum`, and `ActualParentRate` modules already prove
   finiteness, complete-family convergence, and an explicit period estimate.
2. `research/tip_family_theorem/THEOREM.md`, Open Problem 2, and
   `research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md`
   already give written strict separation from the pairable optimum.
3. The circular-parent and circular-crest modules already compute their
   chosen families' all-density moduli. Repeating those lower witnesses,
   positivity, qualitative convergence, or paired serial inequalities is
   outside this packet's intended research claim.

The remaining candidate is an explicit extremal foliation or an exact
obstruction in the full marked homotopy class. The first investigation is
whether the slit problem can be identified with a two-conductor ring without
losing the selected left class at the puncture at infinity. This identification
is a question, not a theorem or a premise smuggled into a theorem.

The pinned Lean 4.32.0 toolchain is being installed locally in scratch.
The existing CI and trust policy are unchanged.

## Dependencies

`NOV26_OPEN_OPTIMAL_LIMIT`, its archived slit-family definitions and preceding
actual-tip convergence results; the repository-pinned Mathlib. Exact external
mathematical dependencies will be recorded if a proof is obtained.

## Boundary

No new theorem has been proved at this checkpoint. Exact value, attainment,
and canonical ideal-boundary identification remain open. No status change is
requested. H1-H4, UPTCR, and MLC remain open. An unsuccessful attack will be
reported as unsuccessful rather than submitted as a research advance.

## Attribution

The existing whole-Wave convergence and circular-foliation proofs are prior
archive work. Classical conformal mapping and extremal-length principles
retain their original attribution. AI assistance has not been reviewed by a
human mathematician. Contributions follow the repository's CC0 license.
