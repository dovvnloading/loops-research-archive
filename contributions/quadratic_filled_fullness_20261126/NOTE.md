---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

# Actual quadratic filled-set fullness and compact subcarrier topology

## Claim

Draft investigation: prove fullness of the actual bounded-orbit quadratic filled set, not of a finite model or an assumed full carrier. No new theorem is claimed until the exact Lean commit passes CI.

## Evidence

Target: a bounded complementary component of the filled set has boundary in the filled set. The uniform bound on all polynomial iterates on that boundary should propagate through the component by the maximum modulus principle, contradicting escape. The existing planar fill and quadratic escape modules are the intended interfaces.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE, KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN. Existing StationaryFiberDynamics, StationaryMonotoneGeometry and PlanarFullification modules.

## Boundary

Draft only. The actual named KKL quotient, hereditary unicoherence, the selected geometric continuum correspondence, and MLC remain unproved. No local Lean installation or network git access is available; repository CI is the compiler of record.

## Attribution

Builds on the archive's earlier quadratic escape and monotone geometric predecessor formalizations, the classical maximum modulus principle, and the geometric setting of Douady–Hubbard and Kahn–Kapiamba–Lyubich.
