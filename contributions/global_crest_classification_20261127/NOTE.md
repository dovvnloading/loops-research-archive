---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="global-crest-classification-20261127"></a>

# Global actual crest classification on the full parent radius range

## Claim

Research in progress. No new theorem is claimed at this initial checkpoint.
The target is a classification of the complete actual terminal gate throughout
the original parent radius interval, not only the short window covered by the
archived actual-crest theorem.

## Evidence

Baseline: main commit `665e5f9`. The archived
`actual_maximal_crest_20261127` contribution proves eventual actual radial
order, a unique terminal endpoint, and the full moving-integral limit on
`[1/16,133/2000]`. Its Boundary leaves possible further admissible components
elsewhere in the original parent interval unresolved.

The proposed attack extends the actual crossing family to `[1/16,1/8]`,
which contains the source parent interval `[1/16,(p-1)/(8*p)]`, controls the
larger intermediate images, and uses the complete actual divided differences
to classify the terminal condition globally. Source real cut inequalities
are to be checked for the same actual parameters and circles. All proposed
mathematical conclusions require compiled Lean proofs in this project.

### Development checkpoint: global collision argument

The larger parent requires a real change of estimates: its second image
can have norm greater than `23/20`, the old approximation radius. New
complete remainder and divided-difference bounds are being checked on
the disk of radius `3/2`.

The proposed global proof has three successive exact fiber exclusions.
The first image of a crossing has positive imaginary part and norm below
`2/5`; the second image is real and lies between `99/100` and `13/10`.
Equality of third images then forces equality of second images (the
positive real sign excludes the opposite point), equality of first images
(the positive imaginary sign excludes it), and equality of original
points (their real parts are negative). Equality of radii follows.
Continuity plus two explicitly certified endpoint signs should orient
this global injectivity as strict decrease.

The source endpoint inequalities are checked only on the retained small
collar. Some fail near radius `1/8`; the terminal exclusion, rather than
a false extension of those inequalities, must remove that region.
The Lean development in this checkpoint is in progress and is not yet a
verified theorem claim.

## Dependencies

`NOV26_OPEN_CREST_LIMIT`, `NOV26_CREST_16`; the existing actual-tip,
crossing, divided-difference, limiting-model, and proper-return modules;
the repository's pinned Lean 4.32.0 and Mathlib revision.

## Boundary

This is an initial draft claim of a research task, not a completed result.
The ledger status stays open. No new KKL Wave width, arbitrary-path marking,
parameter-branch identification, primitive-period classification, or MLC
conclusion is asserted. The exact completed statement and residual gaps will
replace this checkpoint only after proof and validation.

## Attribution

The current short-window endpoint and radial-integral results belong to the
archived contributions and are inputs. They will not be presented as new
results. Original work is released under the repository's CC0 terms.
