---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-component-conjugacy-20261126"></a>

# Exact binary dynamics on escaping quadratic components

Ledger statement being addressed:

> Every virtual-molecule block admits a monotone finite cell-tree quotient of its dynamically relevant Cantor carrier with universal atomic and gate incidence and compatible partial cellular dynamics.

## Claim

Draft claim: for every complex quadratic parameter whose critical point escapes,
construct a continuous binary itinerary whose fibers are exactly the actual
connected components of the filled set, and obtain a topological conjugacy from
the component quotient to the one-sided full binary shift. This strengthens the
existing surjective binary factor by proving connectedness of every address
fiber. The claim remains a development target until the Lean project and its
transitive dependency audit pass CI.

## Evidence

Work in progress. Fix one positive-height two-sheet splitting above the filled
set. Its actual inverse branches generate nested compact connected cylinders.
Their escape heights tend to zero. Identify their intersections with the fibers
of the zero-height itinerary induced by the same splitting, then descend to the
actual connected-component quotient. All mathematical claims will be implemented
and registered in the existing weighted Lean project; this note is not proof.

## Dependencies

Target: H1_CELL_TREE_EXTRACTION. Build on QuadraticEscapeBranches,
QuadraticEscapeComponents, CompactBinaryCoding, and QuadraticEscapeCoding,
especially the existing packet contributions/quadratic_escape_component_tree_20261126.
The pinned Mathlib compactness and connectedness theorems are the intended
topological inputs. Exact declaration references will accompany the implementation.

## Boundary

The actual escape sets are not identified with the virtual-molecule carrier,
its atoms, gates, accesses, or protected return system. No singleton-component
or shrinking-diameter theorem is assumed or claimed. The component quotient,
rather than the filled set itself, is the intended conjugate of the full shift.
H1_CELL_TREE_EXTRACTION, H1-H4, UPTCR, and MLC remain open. No ledger status change
or mathematical priority beyond the archive's formalization is proposed.

## Attribution

This extends Matthew Robert Wesney's archive and its existing Lean escape-set
and binary-coding proofs, formalizing classical polynomial-dynamics topology.
Proof development and review are AI-assisted; no human specialist review has
been performed. The contribution follows the repository's CC0 terms.
