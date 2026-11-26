---
ledger: DIRECT_DECORATION_END_PRIME_END_COFINALITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-quantitative-coding-20261126"></a>

# Quantitative point coding and repelling periodic census for large quadratic parameters

## Claim

For every complex parameter `c` with `8 ≤ ‖c‖`, let `f_c(z)=z²+c` and
let `K_c` be the set of points whose actual forward orbits are bounded.
The new Lean development constructs a homeomorphism

`h : K_c ≃ₜ (ℕ → Fin 2)`

with `h(f_c(z)) = shift(h(z))`. For every pair of points whose first
`n` address entries agree,

`dist(z,w) ≤ ‖c‖ / 2^n`.

Thus every infinite address has exactly one physical point, every nested
filled-set prefix cylinder has singleton intersection, and `K_c` is
totally disconnected. In the ambient complex plane it is perfect, has empty
interior, and equals its own frontier; the positive-escape locus is dense.
The cylinder estimate is proved from the actual
quadratic formula; neither contraction nor singleton fibers are supplied
as hypotheses of the physical theorem.

For every positive integer `n`, there are exactly `2^n` distinct complex
solutions of `f_c^n(z)=z`. This counts periods **dividing** `n`.
A separate theorem constructs a point of **least** period `n` for every
positive `n`. Periodic points are dense in `K_c`, and every `z∈K_c`
has a point `w` fixed by the `n`-th iterate with
`dist(z,w) ≤ ‖c‖/2^n`.

The derivative is the calculus derivative of the actual recursive iterate.
For every `z∈K_c` and every `n≥0`,

`(2*‖c‖)^n ≤ ‖(f_c^[n])'(z)‖²`, and `4^n ≤ ‖(f_c^[n])'(z)‖`.

Consequently every positive-period complex point is repelling. Periodicity
itself is proved to imply boundedness, so neither the census nor the
repelling theorem omits periodic points outside a supplied carrier.

This is a reusable physical contraction and coding result associated with
the open obligation, **not a native direct-decoration subcase**. The
parameter-domain mismatch and the remaining native obligations are stated
under Boundary.

## Evidence

### Registered Lean modules and principal declarations

| Module | Principal conclusions |
|---|---|
| `QuadraticCantorGeometry.lean` | `norm_bound`, `filled_disk_cover`, `branchDisks_disjoint`, `same_disk_expansion` |
| `QuadraticCantorSplitting.lean` | `filled_nonempty`, `filled_compact`, `expanding_two_sheet` |
| `ExpandingBinaryCoding.lean` | `prefix_dist_bound`, `expanding_address_injective`, `expanding_binary_conjugacy`, `prefix_intersection_singleton` |
| `BinaryShiftCensus.lean` | `fixed_point_card`, `periodic_extension`, `periodic_points_dense`, `exact_period_exists` |
| `QuadraticCantorExpansion.lean` | `orbit_hasDerivAt`, `deriv_norm_sq_lower_double_parameter`, `deriv_norm_lower_four`, `periodic_mem_filled`, `periodic_repelling` |
| `QuadraticCantorCoding.lean` | `filled_conjugacy_exists`, `physical_cylinder_intersection`, `filled_totally_disconnected`, `complex_periodic_point_count`, `complex_exact_period_repelling`, `periodic_approximation`, `filled_periodic_points_dense` |
| `QuadraticCantorBoundary.lean` | `filled_no_isolated`, `filled_perfect`, `filled_interior_empty`, `filled_frontier`, `positive_escape_dense` |

All seven files are in `formalization/weighted/`, are default Lake targets,
and are registered in the theorem and source indexes. The existing
`CompactBinaryCoding.lean` now uses four precise imports instead of the
whole Mathlib umbrella; its definitions, statements and proof bodies are
unchanged.

### Proof construction

1. **Actual bounded-orbit semantics and radius.** The domain `filled c`
   is defined by the existing escape potential's zero locus.
   `filled_iff_bounded_orbit` identifies it with bounded actual orbits.
   The previously proved bound `‖f_c^j(z)‖≤1+‖c‖` gives
   `‖z‖²≤2‖c‖+1`, hence `‖z‖≤‖c‖−1` when `‖c‖≥4`.
   Applying that improved bound at the successor gives
   `‖z‖²≤2‖c‖−1`, hence `‖z‖≤‖c‖/2` when `‖c‖≥8`.
   Compactness follows from continuity and boundedness. An explicit
   quadratic fixed point proves nonemptiness.

2. **Constructed physical partition.** Choose `a²=−c`.
   The identity
   `‖z−a‖*‖z+a‖=‖z²+c‖≤‖c‖/2`, together with
   `‖z−a‖+‖z+a‖≥2‖a‖`, places every filled-set point in one of the
   two closed disks centered at `±a` with radius `‖a‖/2`.
   These disks are disjoint. Reflection exchanges the disks and preserves
   the filled set. Square roots supply the inverse points.
   The disk label and actual forward image therefore form a continuous
   bijection `K_c → Fin 2 × K_c`; compactness supplies the homeomorphism.

3. **Metric expansion and generating property.** Points `z,w` in one
   disk satisfy `‖z+w‖≥‖a‖≥2`. Factoring the difference of squares
   proves `2‖z−w‖≤‖f_c(z)−f_c(w)‖`.
   A common prefix of length `n` permits this estimate at every step.
   The final points lie in the radius-`‖c‖/2` disk, so
   `2^n dist(z,w)≤‖c‖`. Unboundedness of `2^n` proves injectivity
   for infinite addresses. The existing nested-compact-cylinder proof
   supplies surjectivity. No arbitrary preexisting splitting is presumed
   to generate points.

4. **Exact symbolic census and physical transfer.** Repetition and
   restriction give an explicit equivalence between the fixed points of
   the `n`-fold shift and the binary words on `Fin n`.
   A word with one marked entry gives least period `n`.
   Repeating progressively longer prefixes converges coordinatewise,
   and the physical estimate makes the approximation quantitative.
   The proved conjugacy transports these conclusions to the actual
   dynamics. `filledMap_iterate` identifies its subtype iterates with
   the existing complex recurrence. The escape identity
   `G_c(f_c^n(z))=2^n G_c(z)` forces every positive-period complex
   point into `K_c`, completing the census in all of `ℂ`.

5. **Actual analytic expansion.** The successor radius bound implies
   `‖c‖≤‖z‖²+‖f_c(z)‖≤‖z‖²+‖c‖/2`.
   Hence `‖z‖²≥‖c‖/2≥4` along every bounded orbit.
   A `HasDerivAt` induction proves the actual derivative product.
   Each squared factor has size at least `2‖c‖`, yielding the stated
   all-horizon inequalities and repelling periodic orbits.

6. **Physical boundary and exterior density.** Flip a sufficiently late
   address entry and use the prefix estimate to construct a distinct
   bounded-orbit point at any prescribed positive Euclidean accuracy.
   This proves perfectness in the actual plane. A connected open complex
   ball cannot lie in a totally disconnected set, so the filled set has
   empty interior. Closedness then identifies it with its frontier, and
   nonnegativity of the escape potential identifies the dense complement
   with the positive-escape locus. No Julia-set or prime-end identification
   is inserted as an assumption.

### Validation and reproducibility

Local Lean 4.32.0 compilation succeeds for all seven new modules and the
existing coding dependency using the repository's pinned Mathlib revision.
The unchanged CI performs the full weighted Lake build and audits the
transitive axioms of **every declaration**, not just a selected theorem.
The exact commit and workflow conclusions are recorded in the pull request
checks and description; a local source scan alone is not a proof result.

From `formalization/weighted/`:

```sh
lake build QuadraticCantorGeometry QuadraticCantorSplitting \
  ExpandingBinaryCoding BinaryShiftCensus \
  QuadraticCantorExpansion QuadraticCantorCoding QuadraticCantorBoundary
```

From the repository root:

```sh
python code/contribute.py check
python code/verify_lean_coverage.py --audit weighted
```

The sources contain no proof holes, custom axioms, unsafe reductions, or
native decision shortcuts. Only the project's permitted standard axioms
`propext`, `Classical.choice`, and `Quot.sound` are accepted by the
transitive audit.

## Dependencies

- The actual escape-potential construction, functional equation, continuity,
  and bounded-orbit equivalence in `QuadraticEscape.lean`.
- The already proved finite-prefix realization and nested compactness
  argument in `CompactBinaryCoding.lean`.
- Mathlib's complex square-root existence, norm arithmetic, compactness,
  homeomorphisms, countable products, finite cardinality, and derivative
  calculus. These are imported as Lean theorems, not new assumptions.
- Ledger context: `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION` is the
  closed prerequisite of the selected open obligation. The present theorem
  does not import its written geometric claim as an axiom.
- Earlier work reviewed: the direct-decoration cofinality, exponential
  shrinking and analytic-history end-blowup audit notes under
  `research/independent_audits/*_20261126/`; the contribution packets for
  prime-end sector filters, sector rank, impression decomposition, and
  decoration critical-cycle exclusion; and the existing
  `QuadraticEscapeCoding.lean` factor theorem.

## Boundary

- The range `‖c‖≥8` is **outside** the connected-filled-set native KL
  decoration regime. This is a reusable, rigorously realized analytic
  toolkit, not a proof about the native decoration objects. The obligation
  stays **open**, and no status change is requested.
- The contracting cylinders consist of bounded-orbit points with a common
  geometric disk itinerary. No contraction of the full native puzzle
  neighborhoods, exterior portions, or prime-end traces is established.
- No Böttcher chart, external ray, angular footprint, prime-end
  identification, access protection, collar charge, or analytic end blowup
  is constructed. The written native hyperbolic/Koebe argument remains
  unformalized. Singleton physical fibers do not identify distinct accesses.
- The derivative estimate `4^n` and the cylinder estimate `2^{-n}` are
  separate proved results. A stronger cylinder estimate is not inferred
  from derivative growth on a disconnected set.
- No theorem here proves the same conclusions for every escaping parameter.
  The explicit norm hypothesis is retained in all physical statements.
- No MLC, H1–H4, parameter rigidity, or universal protected-tower closure
  is claimed. No novelty beyond this repository's formal development and
  no independent human mathematical review are claimed.

## Attribution

The classical large-parameter Cantor-set and symbolic-dynamics argument is
formalized here using the archive's existing escape potential and compact
coding construction. The earlier written decoration audits distinguish
singleton physical fibers from multiple angular accesses and supply the
scope warning retained here. Mathlib supplies the general analytic,
topological and arithmetic library. OpenAI GPT-6 Astra Pro developed the
proofs with parallel proof construction and an independent AI statement
review. All results remain subject to the repository's unchanged compiler,
axiom-audit and contribution checks; human review is `none`.
