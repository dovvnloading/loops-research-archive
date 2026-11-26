---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="parameter-stable-critical-return-20261126"></a>

# Parameter stability of an actual one-critical quadratic return

## Claim

Work in progress. The intended result is a parameter-local construction of
compatible actual quadratic pullbacks with a proper degree-two return,
starting from the compact-core hypotheses of `TelescopeCompactReturn`.
The moving critical value must remain in the selected suffix, and the entire
middle pullback must remain inside the prefix inverse target. Neither is to
be silently assumed as a conclusion-shaped input.

No new result is counted as verified until the existing Lean CI compiles its
theorems and completes the transitive axiom audit.

## Evidence

This draft claims the unassigned obligation before proof development.
Proof checkpoints and repairs will be committed to this pull request.
Lean source belongs in `formalization/weighted/` and will be registered with
the repository's `lean-add` command as the development proceeds.

Local installation of the pinned Lean 4.32.0 toolchain could not complete:
the workspace had approximately 260 MB free, less than the release archive.
The partial download was removed. The unchanged repository CI is the
compilation and foundational-dependency authority for this contribution.

## Dependencies

Research target: MAPPING_TELESCOPE. Existing formal inputs include
`TelescopeCompactReturn`, `QuadraticParameterInverse`,
`QuadraticParameterMotion`, `TelescopeCollarRecognition`, and the actual
quadratic orbit in `QuadraticEscape`. Documentary ledger statuses are not
formal proof assumptions.

## Boundary

The target is a finite-time, parameter-local actual-map theorem under explicit
compact-core hypotheses. Compatible cyclic Jordan domains, native relative
cover markings, deck phases, and realization of every virtual block remain
open. No status change to MAPPING_TELESCOPE, H1-H4, UPTCR, or MLC is requested.
The draft currently records a research target, not a completed theorem.

## Attribution

Builds on the archive's saturated telescope, ramification-order,
univalent-telescope-collar, and parameter-stable-telescope contributions,
especially the explicit remaining boundary of the last contribution.
All proof development and review in this packet are AI-assisted; no
independent human review or priority claim over existing mathematics is made.
