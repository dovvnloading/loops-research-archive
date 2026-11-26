---
ledger: DIRECT_DECORATION_END_PRIME_END_COFINALITY
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="prime-end-sector-filters-20261126"></a>

# Exact multisector cofinality and finite-iterate endpoint recognition

## Claim

Candidate Lean formalization of the November 26 direct-decoration audit, with the angular-height filter criterion generalized to arbitrary compact metric angular footprints. The whole exterior trace is cofinal with ordinary neighborhoods exactly when the nested angular footprint is a singleton and that angle is interior at every finite stage. Two surviving angles obstruct every possible ordinary prime-end center, independently of any planar impression equality. A finite endpoint of a real angular lift obstructs reverse cofinality. For the actual complex quadratic map, a connected fiber of any finite iterate is a singleton if nonempty; in particular two connected side impressions containing a common landing point and mapping to singleton impressions are exactly that point.

## Evidence

Registered module `formalization/weighted/PrimeEndSectorFilters.lean`. The two rectangle inclusions explicitly encode the ordinary punctured angular-height neighborhood filter. Compactness supplies a uniform finite-stage inclusion in every open neighborhood of the limiting footprint, while positive height permits testing each surviving angle at every depth. The reverse direction tests a positive-height point over every angle in a small ball. The endpoint theorem tests both sides of a real angular interval. The physical endpoint recognition proof inducts on the actual quadratic iterate: its intermediate image is preconnected and lies in two opposite square roots, so separation by the complements of the two singletons forces one root; iterate the argument.

Local Lean and network git are unavailable. The existing weighted CI is the compiler of record; none of these candidate theorems count as validated before exact-source compilation and the transitive dependency audit. Reproduce from the repository root:

```sh
python code/verify_lean_coverage.py
python code/verify_physical_bridge_contracts.py
cd formalization/weighted
lake build PrimeEndSectorFilters
cd ../..
python code/verify_lean_coverage.py --audit weighted
```

### Extension: finite sector capacity, uniform address shrinking and endpoint covariance

Candidate module `formalization/weighted/PrimeEndSectorImpressions.lean` proves the finite-sector cardinal bound without any coherent labeling or disjointness assumption. It turns pointwise singleton physical cylinders into uniform shrinking over all infinite words by a compact directed cover of the product address space, using finite-prefix dependence rather than a normal-family convergence rate. It proves the exact right-sided cofinal filter of a nondegenerate endpoint track. The physical impression result proves both connectedness of compact nested wedge limits and exact covariance under the actual quadratic iterate whenever polynomial images of the source wedges and target wedges are mutually cofinal. This handles height rescaling without requiring matching indices. The singleton target conclusion then forces a singleton source side impression, with no assumed preimage inverse branch. The native wedge, chart, boundedness and landing hypotheses are still explicit. The extension must independently pass the existing weighted kernel and dependency audit before it counts as validated.

## Dependencies

DIRECT_DECORATION_PULLBACK_COMPACTIFICATION; research/independent_audits/decoration_end_cofinality_20261126/NOTE.md, sections 3–4; research/mlc_unified/critical_chronology_and_retimed_telescope.md, section 15.2. Imports Mathlib and SaturatedTelescope (actual QuadraticEscape.orbit and its continuity). No ledger assertion is imported as a proof constant.

## Boundary

The angular sets and positive decreasing heights must come from the actual Böttcher chart and native ray/equipotential pieces. The theorem does not construct that chart, establish actual angular sector formulas, prove the two retained rays in the source decoration, or prove planar shrinking. The endpoint recognition theorem assumes connected side impressions and their finite-iterate image identities; it does not prove those source identifications or landing. No prime-end or MLC gate promotion; no claim of mathematical priority. This is partial formal progress, not a new proof of MLC or a completed ledger obligation.

## Attribution

Builds on the archive's November 26 written direct-decoration audit, the classical Böttcher/prime-end framework, and the archive's existing actual quadratic orbit formalization. No human review.
