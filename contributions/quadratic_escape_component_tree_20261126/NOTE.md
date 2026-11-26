---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI GPT-6 Astra Pro; proof design, Lean formalization, source review, and CI repair
human_review: none
---

<a id="quadratic-escape-component-tree-20261126"></a>

# Exact quadratic escape components and full binary coding

Ledger statement being addressed:

> Every virtual-molecule block admits a monotone finite cell-tree quotient of its dynamically relevant Cantor carrier with universal atomic and gate incidence and compatible partial cellular dynamics.

## Claim

This packet constructs finite component hierarchies from actual quadratic dynamics and proves the exact component cardinality of the actual filled set in the escaping-critical regime. It is a partial structural contribution toward `H1_CELL_TREE_EXTRACTION`; the source-defined virtual-molecule carrier is not identified with these sets.

Write

\[
f_c(z)=z^2+c,\qquad G_c(z)=\lim_{m\to\infty}2^{-m}\log\max(1,|f_c^m(z)|),
\]

using the already constructed `QuadraticEscape.escape`, and put

\[
S_c(t)=\{z:G_c(z)\le t\},\qquad a_c=G_c(0),\qquad K_c=S_c(0).
\]

The existing `quadratic_filled_iff_bounded` identifies `K_c` with the genuine bounded-orbit filled set. No symbolic replacement for the polynomial, its iterates, or its escape potential is used.

The principal statements are:

1. **Two actual sheets.** For every complex `c` and `0 <= t < a_c`, there is a homeomorphism

   \[
   e_t:S_c(t)\cong\{0,1\}\times S_c(2t),\qquad
   \operatorname{pr}_2(e_t(z))=f_c(z).
   \]

   Neither connectedness of the upper target, local connectivity, a Jordan boundary, nor a supplied inverse branch is assumed.
2. **Exact finite component census.** For every `t > 0`, let `n` be the first integer with `a_c <= 2^n*t`. Then

   \[
   \#\pi_0(S_c(t))=2^n.
   \]

   The constructed labels are the actual connected components. The actual iterate `f_c^n` maps each component homeomorphically onto `S_c(2^n*t)`. Equality at the final critical height is included. At each subcritical step, every parent component has exactly two child components, and the actual quadratic map maps each child homeomorphically onto its parent.
3. **All positive scales.** If `a_c > 0`, the component count at height `a_c/2^n` is exactly `2^n`. Thus these counts have no finite upper bound as the positive height varies.
4. **All infinite addresses.** If `a_c > 0`, there is a continuous surjective map

   \[
   \iota:K_c\longrightarrow\{0,1\}^{\mathbb N},\qquad
   \iota\circ f_c=\sigma\circ\iota,
   \]

   where `sigma` is the one-sided shift. The coding factors continuously and surjectively through the actual connected-component quotient.
5. **Exact zero-height component cardinality.** For every `a_c > 0`,

   \[
   |\pi_0(K_c)|=2^{\aleph_0}.
   \]

   This statement concerns components, not just points of the filled set, and it does not assume that the components are singletons.

These are formalizations of classical polynomial escape-set topology. No priority claim for new mathematics is made.

## Evidence

### Lean declarations

Every module below is registered as a default weighted build target, in the public theorem index, and in the source inventory. The complete source contains the proof terms; this note is an explanation rather than an additional proof premise.

| Module | Principal declarations and purpose |
|---|---|
| [QuadraticEscapeBranches.lean](../../formalization/weighted/QuadraticEscapeBranches.lean) | `sublevel_split`: constructs both actual inverse sheets and identifies their projection with the quadratic map. |
| [FiniteComponentTree.lean](../../formalization/weighted/FiniteComponentTree.lean) | `component_eq_label_fiber`, `component_count`, `componentHomeomorph`, `component_isClopen`, `component_isCompact`: turns a finite discrete product into exact component topology. |
| [ComponentDoubling.lean](../../formalization/weighted/ComponentDoubling.lean) | `productComponentEquiv`, `productComponentHomeomorph`, `self_double_components_infinite`: retains actual parent components even when the target is disconnected. |
| [QuadraticEscapeComponents.lean](../../formalization/weighted/QuadraticEscapeComponents.lean) | `sublevel_iterated_split`, `sublevel_component_census`, `sublevel_component_iterate_homeomorph`, `positive_sublevel_exact_components`, `critical_dyadic_component_count`, `sublevel_component_counts_unbounded`, `sublevel_component_parent_census`, `sublevel_component_parent_homeomorph`, `escaping_filled_components_infinite`. |
| [CompactBinaryCoding.lean](../../formalization/weighted/CompactBinaryCoding.lean) | `address_surjective`, `address_semiconj`, `componentAddress_surjective`, `componentAddress_section`, `componentAddress_semiconj`, `component_uncountable`: realizes infinite addresses by compactness and descends the coding to actual components. |
| [QuadraticEscapeCoding.lean](../../formalization/weighted/QuadraticEscapeCoding.lean) | `filled_two_sheet`, `filled_binary_coding`, `filled_component_cardinality`, `filled_component_uncountable`: specializes the coding and exact cardinality to the actual filled quadratic set. |

### Why the construction works

1. **Exclude the critical value at exactly the needed height.** The established functional equation gives `G_c(c)=2*G_c(0)`. If `t<a_c`, the full compact upper target `S_c(2t)` therefore excludes `c`. Its translation by `-c` is compact, full, and avoids zero. The earlier continuous-logarithm theorem supplies a logarithm on this actual compact set, including when it is disconnected.
2. **Construct and exhaust both sheets.** Exponentiating half the logarithm gives a continuous nonzero square root. Its positive and negative choices are disjoint. Factorization of the quadratic equation proves that they exhaust the full inverse image, and the escape functional equation identifies that inverse image with `S_c(t)`. A continuous bijection from the compact two-sheet product to the Hausdorff lower sublevel is a homeomorphism. Its projection is proved to be `f_c`, not merely conjugate to an unspecified map.
3. **Iterate without losing the physical map.** Compose the sheet homeomorphisms through every subcritical stage. Reassociate their finite labels with `Fin (2^n)` and retain the actual `n`-th iterate as the last coordinate. At the first height reaching `a_c`, the archive's exact connectivity theorem makes the common factor connected. Connected components of a finite discrete product with a connected factor are precisely the label fibers. The same product argument on component quotients proves the adjacent parent census and component homeomorphisms.
4. **Handle both endpoint regimes.** Powers of two eventually cross every finite critical height when `t>0`, so a least crossing exists. At height zero with escaping critical point, the same construction gives `K_c` homeomorphic to two copies of itself. A quadratic fixed point, constructed by an algebraic square root, proves nonemptiness without a bounded critical-orbit hypothesis. Compactness was already proved for the actual filled set.
5. **Realize every infinite word.** For the zero-height splitting, label an orbit by its first coordinate at every iterate. Continuity of every coordinate proves continuity into the product space of binary sequences. Repeated inverse sections realize every finite prefix. Each prefix cylinder is closed, nonempty, and nested; compactness supplies a point realizing the entire infinite sequence. No diameter estimate or unique-point assertion is used.
6. **Count actual components.** The binary sequence space is totally disconnected, so the continuous itinerary is constant on each connected component and descends continuously to the component quotient. Surjectivity gives the lower bound `2^aleph_0`. The quotient map from `K_c` onto its components gives an upper bound by `|K_c|`, and the genuine subtype injection into the complex plane gives the upper bound `|C|=2^aleph_0`. The two bounds establish equality.

### Reproduction and validation

The projects pin Lean `v4.32.0`; the weighted project pins Mathlib `v4.32.0` at commit `81a5d257c8e410db227a6665ed08f64fea08e997`.

From the repository root:

```sh
python -B code/contribute.py check
python -B code/verify_lean_coverage.py
cd formalization/weighted
lake exe cache get
lake build QuadraticEscapeBranches FiniteComponentTree ComponentDoubling QuadraticEscapeComponents CompactBinaryCoding QuadraticEscapeCoding
cd ../..
python -B code/verify_lean_coverage.py --audit weighted
```

The first complete package build and transitive axiom audit both passed on PR #217 at commit `9bc220773ce3d318d5483475b03cd3fe7cc2e0dc`, including the merge of current `main`: [weighted Lean build and audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45899026746). The audit reported `AXIOM_AUDIT_PASS weighted: 99 modules, 2587 declarations`; each of the six new modules reported allowed axioms only. The existing [Research validation](https://github.com/dovvnloading/loops-research-archive/actions/runs/45899026827) and [Contribution intake](https://github.com/dovvnloading/loops-research-archive/actions/runs/45899026518) workflows also passed at that checkpoint. Subsequent documentation changes remain subject to the final PR checks. Local intake, source registration, and forbidden-proof-escape checks pass. Local Lean compilation was unavailable because the toolchain and Mathlib exceed the available scratch storage; CI is the compiler of record.

The permitted transitive logical foundations are only `propext`, `Classical.choice`, and `Quot.sound`. No new axioms, proof holes, native proof bypass, or new workflow is introduced. CI checks these conditions on the compiled declarations, not only on the text of the source.

The draft PR was opened before implementation, and the inverse-sheet construction, finite census, CI repairs, and infinite coding were committed incrementally. Earlier checkpoints remain visible in the PR history.

## Dependencies

The target is `H1_CELL_TREE_EXTRACTION`. Its ledger prerequisites `TREE_NERVE_FULLNESS` and `TOPOLOGY_REPLICATION_NO_GO` remain unchanged; this packet does not treat either as a premise that identifies the virtual-molecule carrier.

The mathematical inputs are the repository's compiled `QuadraticEscape`, `QuadraticEscapeFullness`, `StationaryFiberDynamics`, and planar-fullification results. In particular, the proof uses `escape_step`, `orbit_shift`, `quadratic_escape_sublevel_compact`, `escape_pair_sublevel_full`, `compact_connected_complement_log`, `quadratic_escape_sublevel_connected_of_critical`, and `quadratic_filled_compact`.

Pinned Mathlib supplies the compact-to-Hausdorff homeomorphism criterion, connected-component quotients, compact directed intersection, the algebraic-closure square-root theorem, and cardinal arithmetic. Relevant primary source files are `Mathlib/Topology/Homeomorph/Defs.lean`, `Mathlib/Topology/Connected/TotallyDisconnected.lean`, `Mathlib/Topology/Compactness/Compact.lean`, `Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, and `Mathlib/Analysis/Complex/Cardinality.lean`. All are consumed as compiled proofs rather than imported research assumptions.

The source rows use `METADATA`: no existing model-to-physical bridge or canonical ledger status is promoted by registration.

## Boundary

The results apply to genuine quadratic positive escape sublevels and, for `G_c(0)>0`, to the zero-height filled set and its component dynamics. They do not identify these sets or their finite labels with the source-defined virtual-molecule Cantor carrier, its small-Julia atoms, gates, access marking, or protected partial returns. Those identifications and the required universal incidence estimates remain open.

The binary coding has a chosen continuous-log sheet labeling. It is a surjective semiconjugacy; its fibers have not been proved connected or singleton. The packet does not identify the filled set with the Cantor set and does not prove that every filled-set component is a point. Individual component fullness and regularity of equipotential boundaries are not part of the delivered theorem statements.

`H1_CELL_TREE_EXTRACTION`, H1–H4, UPTCR, and MLC retain their existing open status. No new MLC case, global marked construction, calibration estimate, rigidity theorem, or status promotion is claimed. The formalization is new to this archive's current Lean modules; classical mathematical priority remains with the literature.

## Attribution

This packet builds on the classical polynomial-dynamics setting developed by Fatou, Julia, Douady, Hubbard, and their successors; on Matthew Robert Wesney's archive and its preceding Lean escape-potential, fullness, and physical filled-set work; and on Mathlib's topology, complex analysis, algebraic closure, and cardinality proofs.

OpenAI GPT-6 Astra Pro assisted with proof design, implementation, independent review of hypotheses and boundaries, and repair using CI compiler diagnostics. No human specialist review has been performed for this packet. The contribution follows the repository's CC0 terms; cited researchers and tool providers are not represented as reviewers or endorsers.
