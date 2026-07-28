# Draft II changes — 2026-07-27

## Paper-level decision

Draft I was not ready to stand as an independent paper. Its final
direct-decoration section substantially overlapped the stronger 20-page
companion paper, and its prime-end conventions lagged the corrections already
made there. Draft II keeps the project as a separate paper only after changing
its center of gravity to the general planar theory.

The direct-decoration application is no longer assembled into Draft II.
The companion manuscript contains the rooted-end compactification, shift
dynamics, gap cells, arbitrary packet replacement, and decoration-carrier
theorem. Draft II contains protected certificate realization, the exact free-component criterion,
packet audits, the separation ledger, and the finite-to-infinite compactness
gate.

## Correctness repairs

- Replaced weak nested-side language by null prime-end chains.
- Replaced closed collar avoidance by relative collar tails
  `closure(D) \ A`, allowing distinct prime ends to have overlapping
  impressions inside an atom.
- Made the port/tree incidence conditions explicit.
- Repaired the single-atom (`s=1`) sufficiency construction in the
  free-component criterion.
- Corrected the claim about Carathéodory extension: one landing access is not
  equivalent to local connectivity; a blanket continuous boundary extension
  is.
- Replaced the compacta-duality source lock by Spanier, while retaining
  Hatcher as an accessible secondary account.
- Made the ribbon-order conclusion precise as a regular-neighborhood boundary
  word, without asserting an undeclared prime end for every tree edge.
- Corrected protected-impression language from “is not the impression” to
  “belongs to no protected impression.”
- Strengthened the naturality hypothesis of the packet audit to transport the
  entire typed assignment.

## New mathematics

The new section `extracted/G_separation/separation_budget.tex` proves:

1. **Attachment exact sequence.** For
   `B_i = C union A_1 union ... union A_i` and `T_i = C intersection A_i`,
   the restriction `H^1(B_{i-1}) -> H^1(T_i)` is surjective and

   ```text
   0 -> reduced H^0(T_i) -> H^1(B_i) -> kernel(restriction) -> 0
   ```

   in Čech cohomology.

2. **Separation ledger.** Under finite-rank hypotheses,

   ```text
   sigma(C union all A_i)
     = sigma(C) + sum_i(components(T_i) - 1 - sigma(T_i)).
   ```

   Disconnected traces create complementary components; separating traces
   cancel separations already carried by the connector.

3. **Exact full-connector criterion.** If the connector and atoms are full,
   the final union is full exactly when every attachment trace is connected,
   with no local-connectivity or finite-component hypothesis.

4. **Continuum-connector realization.** The certificate tree can be replaced
   by any full continuum connector with connected traces and the same
   relative-collar clearance.

5. **Arbitrary Hausdorff-limit defect.** Full arc carriers with singleton
   traces can converge to a carrier with any prescribed finite number of
   bounded complementary components.

6. **Nested-limit stability.** Decreasing full connector envelopes with
   connected nonempty traces have a full limiting connector with connected
   traces; common obstacle and protected-collar conditions pass to the limit.

The full/full criterion is explicitly positioned in the
Janiszewski–Mullikin tradition. The general homomorphism-level ledger is
presented as a Mayer–Vietoris/Alexander-duality consequence tailored to the
carrier problem, not as a new foundation for plane topology.

## Architecture

Draft II uses:

```text
introduction
preliminaries
obstructions
comparison with standard hull constructions
certificate realization
attachment cohomology and separation ledger
exact free-component criterion
packet criterion
fixed-packet audit
scope and next gates
provenance appendix
```

`assemble.py` now accepts `--skeleton` and `--output` and recognizes the new
`G_separation` cluster, so frozen and revised architectures can coexist.
