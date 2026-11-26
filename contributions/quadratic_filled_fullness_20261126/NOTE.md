---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="quadratic-filled-fullness-20261126"></a>

# Actual quadratic escape sublevel fullness and compact subcarrier topology

## Claim

Candidate formalization (exact-head CI not yet verified): every escape-potential sublevel of an entire pair of parameter and initial-point functions is full. In particular this implies fullness of every dynamical quadratic escape sublevel and every quadratic parameter-potential sublevel, fullness and connected complement of the genuine bounded-orbit quadratic filled set, and fullness of its arbitrary compact subcarriers when the filled set has empty interior.

## Evidence

Lean module: [QuadraticEscapeFullness.lean](../../formalization/weighted/QuadraticEscapeFullness.lean). Public declarations: `orbit_pair_differentiable`, `escape_pair_frontier_bound`, `frontier_complement_component_subset`, `escape_pair_sublevel_full`, `quadratic_escape_sublevel_full`, `quadratic_parameter_sublevel_full`, `quadratic_filled_full`, `quadratic_filled_connected_complement`, `quadratic_filled_compact_subcarrier_full`.

1. Inductively differentiate actual iterates of the entire pair. For a bounded domain, continuity of the parameter on its compact closure supplies a uniform parameter bound.
2. At each finite iterate the complex maximum modulus principle provides a frontier point with norm at least the norm at the chosen interior point. The monotone logarithm and positive normalization transfer that inequality to the finite escape approximants.
3. The archive's uniform escape convergence on bounded parameter ranges applies even to the changing frontier maximizers. If the escape potential at the point exceeded the frontier bound, take one third of the positive difference as the convergence tolerance. The two approximation errors and the finite maximum inequality give a contradiction.
4. The frontier of a complementary component of a closed set is contained in the closed set: a component containing an exterior frontier point is open and would meet the original component, hence coincide with it. This contradicts frontier membership.
5. A bounded complementary component of a closed escape sublevel therefore inherits the same escape bound, a contradiction. The potential is the actual limiting orbit potential, not a supplied harmonic or subharmonic model.
6. Specialize to the constant-parameter and identity initial-point pair and to the identity parameter/initial-point pair. Nonnegativity identifies the zero dynamical sublevel with the actual filled set. The planar-fill exterior theorem gives connected complement. The existing compact-subcarrier theorem then applies without postulating ambient fullness.

Reproduction: `cd formalization/weighted && lake build QuadraticEscapeFullness`. The module is registered as METADATA in the default targets, public theorem index and source inventory. The existing weighted Lean CI and transitive dependency audit are the compiler of record; local Lean and network git access are unavailable. No proof is counted before the exact head passes those checks.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE, KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN. Existing StationaryFiberDynamics, StationaryMonotoneGeometry, PlanarFullification and QuadraticEscape. Mathlib's pinned `Complex.exists_mem_frontier_isMaxOn_norm` in `Mathlib/Analysis/Complex/AbsMax.lean` supplies the classical maximum modulus principle.

## Boundary

The named KKL/Kiwi quotient, empty interior of the named physical set, hereditary unicoherence (in particular the Janiszewski step), singleton anchors, and exact geometric selected-continuum correspondence remain separate obligations. This result does not establish connectedness of the filled set itself, nor local connectivity of its boundary, H1–H4, or MLC. No ledger promotion or new workflow. No priority claim for the classical fullness theorem.

## Attribution

Builds on the archive's earlier quadratic escape and monotone geometric predecessor formalizations, Mathlib's maximum modulus proof and the classical geometric setting of Douady–Hubbard and Kahn–Kapiamba–Lyubich.
