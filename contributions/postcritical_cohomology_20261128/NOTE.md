---
ledger: UNIVERSAL_PROTECTED_TOWER_CLOSURE
result: partial
status: working-draft
ai: OpenAI ChatGPT GPT-6
human_review: none
---

# Outlier research: postcritical cohomology and parameter-fiber rigidity

**Active draft, not a theorem claim.** The precise archive gate is
`UNIVERSAL_PROTECTED_TOWER_CLOSURE` (UPTCR), the still-open six-clause universal
construction/compactness/rigidity proposition. The archive proves only
`UPTCR_IMPLIES_MLC` conditionally. H1–H4 and MLC remain open.

This fresh investigation tests a genuinely different *single-orbit cohomology /
invariant postcritical statistic* mechanism in the actual quadratic family
`f_c(z)=z²+c`. We reject the earlier metric cohomology criterion; we do not
reuse mixed two-parameter susceptibility or two-generator intertwining maps.
No KKL waves, marked widths, collars, protected carriers, telescopes, tip
families, arithmetic denominators, geometric-limit charge, Green-density
criteria or projective cross-ratio jets are imported.

Before Lean formalization, this branch will record an exact candidate,
classical nearest-neighbor comparison, and a non-circular reason that its
dynamical hypothesis is meaningfully distinct from parameter equality.
The Lean acceptance target is **a proved implication to a singleton fiber
and pointwise local connectivity of the actual quadratic bounded-orbit locus**,
not merely an algebraic identity. The fiber map will be stated as an explicit
continuous monotone surjection; the canonical pinched-disk identification will
not be silently assumed.

## Claim

Under development; no theorem accepted yet. The active pattern is to extract
rigidity from the quadratic additive parameter in a cohomological obstruction
of a single bounded postcritical orbit rather than from metric orbit closeness.

## Evidence

No new Lean source or successful validation claimed in this first commit.

## Dependencies

Actual orbit and compactness infrastructure:
`QuadraticEscape.lean`,
`QuadraticMixedSusceptibilityMLC.lean` (compactness only),
`QuadraticMonotoneFiberTopology.lean` (classical topological implication).
No susceptibility theorem will be imported.

## Boundary

No new MLC case, theorem or satisfaction of a novel criterion is claimed yet;
the exact missing actual-family mechanism remains to be demonstrated. Any
eventual Lean theorem must compile in the repository's pinned Lean 4.32.0
project with only the permitted foundational axioms.

## Attribution

OpenAI ChatGPT GPT-6. Human specialist review: none. Classical sources and
prior archive work will be credited in the pre-formalization record.
