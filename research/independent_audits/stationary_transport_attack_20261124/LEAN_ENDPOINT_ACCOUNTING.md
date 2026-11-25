# Finite stationary endpoint accounting: proposed Lean layer

Source: [Variable-end stationary exit transfer](VARIABLE_END_EXIT_TRANSFER.md), especially equations (4.2)–(4.4), Corollary 4.2 and the degree-budget applications in Section 5. Base revision: `411fd90a48c9eb6af162d23184ba51ab23ae73ae`.

The new [StationaryEndpointCover.lean](../../../formalization/weighted/StationaryEndpointCover.lean) module represents occurring endpoint pairs by a finite edge type and ideal ends by a finite vertex type. Its orientation has no geometric meaning. Distinct endpoints are an explicit premise, and the incidence load counts each edge once at each of its two ends.

## Theorem interface

* `incidentLoad_eq_split` and `weighted_load`: exact double counting of distinct-end incidence.
* `fractional_cover`: finite real-valued weak duality for arbitrary finite endpoint graphs. A local capacity bound is required only at a strictly positively charged vertex.
* `one_end_bank` and `two_end_bank`: variable-end incidence gives the bank sum; both-end incidence gives half the bank sum.
* `bank_charge_le_degree`, `one_end_degree_budget`, and `two_end_degree_budget`: composition with pointwise degree bounds and a supplied total degree budget.

For the geometric application, the source must first provide disjoint-support width additivity, parent-to-selected-lift comparison, actual distinct ideal ends, and the local incidence inequalities. For a cover with finite positively charged capacities, each edge has at least one positively charged endpoint and hence finite width (by nonnegativity and that endpoint's incidence bound). The real-valued model then applies. Uncharged capacities are arbitrary real placeholders and are not estimates of possibly infinite geometric widths. A cover of infinite cost gives only a trivial extended-real upper bound; this module does not formalize extended-real infima or geometric modulus.

The total degree budget is a premise, not a proved native covering census. The module does not establish that actual proper stationary exits exist, nor does it prove KKL Lemma 6.31 independently, close MARK, H1–H4, UPTCR, or MLC.

## Reproduction

From the repository root:

```sh
python -B research/independent_audits/stationary_transport_attack_20261124/verify.py
python -B research/independent_audits/stationary_transport_attack_20261124/check_endpoint_cover_lean_model.py
cd formalization/weighted
lake build StationaryEndpointCover
```

An independent local exact-arithmetic experiment checked 2,376 assignments including uncharged endpoints, and reproduced the source's fixed-end, variable-bank, inner-bank, and triangle costs 2, 8, 4, and 3/2. The committed regression reproduces that experiment. Lean compilation was not available in the authoring runtime; the module has been registered in the existing weighted mathlib CI and requires successful kernel checking before being described as Lean-verified. No source ledger status is changed.

Prepared with ChatGPT assistance; no human specialist review or novelty claim.
