---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI GPT-6 Astra Pro; proof design, Lean formalization, and review
human_review: none
---

<a id="quadratic-escape-component-tree-20261126"></a>

# Binary component trees of actual quadratic escape sublevels

Ledger statement being addressed:

> Every virtual-molecule block admits a monotone finite cell-tree quotient of its dynamically relevant Cantor carrier with universal atomic and gate incidence and compatible partial cellular dynamics.

## Claim

Work in progress. The target is an exact binary decomposition of genuine quadratic
escape sublevels below the critical escape height, followed by the exact finite
component count at every positive height. Only declarations compiled and audited
by the existing Lean CI will be counted as results.

## Evidence

The intended proof uses the actual escape potential from `QuadraticEscape.lean`,
the compactness, fullness, logarithm construction, and exact connectedness threshold
from `QuadraticEscapeFullness.lean`, and the identity `G_c(z^2+c)=2G_c(z)`.
A logarithm on the translated upper sublevel should produce two disjoint continuous
inverse branches, allowing a finite component tree to be constructed from actual
dynamics. The exact statements and validation record will be added as they compile.

The pinned Lean toolchain is not installed locally. The available scratch space
cannot fit the toolchain and Mathlib, so the existing Lean workflows on this PR
are the compilation and transitive axiom-audit authority.

### Checkpoint 1: inverse sheets and component topology

The first implementation adds `QuadraticEscapeBranches.lean` and
`FiniteComponentTree.lean`. The former constructs both inverse sheets from
a continuous logarithm on the translated full compact target, then proves
that their disjoint union is homeomorphic to the actual lower sublevel, with
the actual polynomial as the projection. The latter identifies components
of a finite product decomposition with its label fibers and proves the exact
component count, compactness, and a homeomorphism of each component to the
common factor. These declarations await CI validation at this checkpoint.

### Checkpoint 2: all finite horizons and the zero-height boundary

`QuadraticEscapeComponents.lean` now iterates the constructed splitting,
retaining the actual iterate as its final coordinate. At the first height
`2^n*t >= G_c(0)`, the top factor is connected, so the exact component count
is `2^n`. At the dyadic heights `G_c(0)/2^n`, this gives unbounded component
complexity for each escaping-critical parameter. `ComponentDoubling.lean`
provides the quotient census and homeomorphism from each child component
onto its actual parent, including when the upper target is disconnected.
At height zero, the same two-copy decomposition and a constructed fixed
point rule out a finite component count of the genuine filled set.

The first weighted CI run rejected several elaboration steps (sublevel
unfolding, a dependent membership rewrite, and pointwise negation). This
checkpoint repairs those steps. The new declarations still count only
after successful compilation and the transitive axiom audit.

## Dependencies

`H1_CELL_TREE_EXTRACTION` is the target. Its existing prerequisites
`TREE_NERVE_FULLNESS` and `TOPOLOGY_REPLICATION_NO_GO` retain their ledger status.
The new proofs build on the archive's `QuadraticEscape`, `QuadraticEscapeFullness`,
and `PlanarFullification` modules and their pinned Mathlib dependencies.

## Boundary

This is a positive-height escape-sublevel construction, not a construction of the
virtual-molecule carrier or its marked accesses and gates. The connection to those
objects, uniform incidence, compatible marked partial dynamics, and the full
`H1_CELL_TREE_EXTRACTION` obligation remain open. H1–H4 and MLC remain open.
No ledger promotion or new workflow is proposed. No mathematical novelty or
priority claim is made for classical polynomial escape-set topology.

## Attribution

The geometric setting is classical complex polynomial dynamics, including the
work of Fatou, Julia, Douady, and Hubbard. This packet builds specifically on
the archive's previously compiled escape-potential and fullness formalizations,
and on Mathlib's topology and exponential covering proofs. Human specialist
review has not yet occurred.
