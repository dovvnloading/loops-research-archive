---
ledger: H3_COERCIVITY
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="h3-planar-fill-limit-20261126"></a>

# Order-continuity of the actual planar filled hull

Ledger statement being addressed: bounded calibrated potentials and uniform normalized incidence and congestion must prevent analytic marked-carrier degeneration.

## Claim

For any decreasing sequence of compact subsets S_n of the complex plane, the genuine filled hull satisfies Fill(intersection S_n) = intersection Fill(S_n). The seeds need not be connected or nonempty. Fullness persists under this decreasing limit, and for every open neighborhood V of the filled limit there is a single finite N after which every filled carrier lies in V.

## Evidence

The candidate Lean proofs are in `formalization/weighted/PlanarFillLimit.lean`. The exact-head CI verdict is required before these are counted as results.

1. `connectedComponentIn_iUnion_monotone_open`: the connected component of an increasing union of open plane sets is the union of the stage components. A path between two points in the open component has compact range; the directed open cover contains that entire range at one stage.
2. `planarFill_iInter_antitone_compact`: choose a point in the unbounded component of the initial complement. It remains outside all filled stages and the filled limit. Apply the preceding component theorem to the increasing complements. Thus any point exterior to the limit is exterior already at some stage; monotonicity gives the other inclusion.
3. `planarFill_iInter_fixed`: fullness survives a nested compact limit.
4. `planarFill_eventually_subset_open`: the closed bad region of the initial compact filled carrier cannot meet every later filled carrier, by the directed-family compactness lemma.

Reproduce: from `formalization/weighted`, run `lake build PlanarFillLimit`, then from repository root run `python3 -B code/verify_lean_coverage.py --audit weighted`. This session has no local Lean executable or GitHub network access from the shell; GitHub Actions is the validation authority.

## Dependencies

The actual `planarFill` construction, compactness and unique unbounded component in `PlanarFullification.lean` (Paper 3 A-fill / E-fill-absorption); Mathlib's open connected/path-connected equivalence, compact directed open cover, and compact directed closed family lemmas. The existing NESTED_FULL_PACKET_NONSEPARATION ledger row treats a narrower application to full packets; this packet concerns the actual fill operation on arbitrary decreasing compact seeds.

## Boundary

H3_COERCIVITY remains open. The result requires nested compact carriers, not arbitrary Hausdorff-convergent carriers. It does not construct nesting for any source-defined tower, preserve distinguished accesses or relative covers, prevent diameter collapse, control response forms, or prove analytic nondegeneracy. No gate or status is promoted. This is not a claim of worldwide mathematical novelty.

## Attribution

Matthew Robert Wesney's archive and Paper 3; prior planar fullifier formalization; Mathlib's general topology. OpenAI GPT-6.2 authored the proposed proof development.
