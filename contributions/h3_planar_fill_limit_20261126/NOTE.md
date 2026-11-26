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

The Lean proofs are in `formalization/weighted/PlanarFillLimit.lean`. The first four theorems compiled and passed the transitive dependency audit on commit `a9c9d79f77069af9bb7de2975b46656e640d6c55` ([weighted build and audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45850809697), which reports four declarations and four theorems with allowed axioms only). The extension below is a new proof candidate until its own CI completes.

1. `connectedComponentIn_iUnion_monotone_open`: the connected component of an increasing union of open plane sets is the union of the stage components. A path between two points in the open component has compact range; the directed open cover contains that entire range at one stage.
2. `planarFill_iInter_antitone_compact`: choose a point in the unbounded component of the initial complement. It remains outside all filled stages and the filled limit. Apply the preceding component theorem to the increasing complements. Thus any point exterior to the limit is exterior already at some stage; monotonicity gives the other inclusion.
3. `planarFill_iInter_fixed`: fullness survives a nested compact limit.
4. `planarFill_eventually_subset_open`: the closed bad region of the initial compact filled carrier cannot meet every later filled carrier, by the directed-family compactness lemma.

Reproduce: from `formalization/weighted`, run `lake build PlanarFillLimit`, then from repository root run `python3 -B code/verify_lean_coverage.py --audit weighted`. This session has no local Lean executable or GitHub network access from the shell; GitHub Actions is the validation authority.

### Extension: upper semicontinuity and an actual connected-carrier obstruction

The positive nested theorem gives a stronger one-sided Hausdorff statement: for a compact seed K and any open V containing its filled hull, a positive closed-thickening radius controls the hull of every subset of that thickening. This is `planarFill_upper_semicontinuous`.

The converse stability is false even with compact connected planar carriers and fixed antipodal markers. The new declarations `planarFill_of_proper_subset_unitSphere` and `planarFill_unitSphere` distinguish the proper circle subset (a radial exit makes its complement nonseparating) from the whole unit circle (its fill is the closed disk).

`full_connected_approx_nonfull_unitSphere` constructs compact connected circular arcs arbitrarily close in both Hausdorff directions to the circle, all retaining I and -I. Every arc is full, and its fill misses the entire open unit disk; the circle fills that whole disk. The approximation proof uses uniform continuity on the closed angle interval, not numerical discretization. Thus uniform macroscopic size, connectedness, fullness and fixed marks alone do not make fullness closed in Hausdorff topology. This is a candidate Lean formalization of a classical geometric obstruction, not a claim that it violates the additional specific hypotheses of H3.

## Dependencies

The actual `planarFill` construction, compactness and unique unbounded component in `PlanarFullification.lean` (Paper 3 A-fill / E-fill-absorption); Mathlib's open connected/path-connected equivalence, compact directed open cover, and compact directed closed family lemmas. The existing NESTED_FULL_PACKET_NONSEPARATION ledger row treats a narrower application to full packets; this packet concerns the actual fill operation on arbitrary decreasing compact seeds.

## Boundary

H3_COERCIVITY remains open. The initial exact identity requires nested compact carriers. The extension supplies one-sided stability for nonnested Hausdorff perturbations, but also exhibits a failure of two-sided stability for actual compact connected full carriers. It does not construct nesting for any source-defined tower, preserve distinguished accesses or relative covers, prevent diameter collapse, control response forms, or prove analytic nondegeneracy. No gate or status is promoted. This is not a claim of worldwide mathematical novelty.

## Attribution

Matthew Robert Wesney's archive and Paper 3; prior planar fullifier formalization; Mathlib's general topology. OpenAI GPT-6.2 authored the proposed proof development.
