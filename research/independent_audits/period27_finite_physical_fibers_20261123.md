# Every finite inverse fiber inside the period-27 real partition

**Date:** 2026-11-23. **Base source:** `79dc6c6e9d2f370b505ff47cfaed3feba46d4899`.
**Target:** the previously written finite-path extension of the
[physical period-27 Markov-row bridge](period27_real_markov_bridge_20261123.md).

## Exact result and boundary

Let $f_c(x)=x^2+c$, where $c$ belongs to the certified dyadic parameter
bracket and satisfies $f_c^{27}(0)=0$. The existing real-period theorem
supplies an actual parameter with these properties. Let
$v_0<\cdots<v_{26}$ be the actual critical-orbit points in increasing
order, let $E_i^\circ=(v_i,v_{i+1})$, and let $I=[v_0,v_{26}]$.
The source-row, target-column matrix is

$$
A_{ij}=\begin{cases}1&\text{if the checked row predicate contains }j
\text{ in row }i,\\0&\text{otherwise.}\end{cases}
$$

For **every** $n\in\mathbb N$, $i,j\in\{0,\ldots,25\}$, and
$y\in E_j^\circ$, the new Lean theorem proves finiteness and the exact count

$$
\boxed{\#\{x\in E_i^\circ:f_c^n(x)=y\}=(A^n)_{ij}.}
$$

The proof supplies an actual equivalence between the finite admissible-path
type and this real-point subtype. It does not assume a coding correspondence,
assume that the physical fiber is finite, or identify physical points merely
by numerical proximity.

The source-interior fibers also form a proved disjoint partition of the
entire inverse fiber **inside the closed physical core**:

$$
\coprod_{i=0}^{25}\{x\in E_i^\circ:f_c^n(x)=y\}
\ \cong\ \{x\in I:f_c^n(x)=y\}.
$$

Consequently this complete core fiber is finite and

$$
\boxed{\#\{x\in I:f_c^n(x)=y\}
=\sum_{i=0}^{25}(A^n)_{ij}.}
$$

The restriction to $I$ is part of the theorem. Real preimages outside $I$
are not counted. The result gives no bijection with all real preimages on
$\mathbb R$, no infinite coding theorem, no periodic-point count, no entropy
identity, and no identification with the delayed clone graph or a complex
Hubbard-tree operator.

## Independently proved transitions

The generic source
[FiniteMarkovFibers.lean](../../formalization/weighted/FiniteMarkovFibers.lean)
uses only the following one-step realization data: strictly ordered real
vertices; a specified real function; a forward transition on vertices;
images of each closed source edge lying in the core; injectivity on each
closed source edge; and equivalence of the row predicate with actual
one-step preimage existence for each target-interior point.

The specialization
[Period27FiniteFibers.lean](../../formalization/weighted/Period27FiniteFibers.lean)
constructs `realizedSystem` by proving every field for the actual quadratic.

| Generic premise | Actual physical proof |
|---|---|
| Strict order of vertices | `LoopsRealPeriod27.Markov.vertex_strictMono`, using the certified real orbit order |
| Correct vertex successor | `LoopsRealPeriod27.Markov.vertex_step`, using the actual orbit equation $f_c^{27}(0)=0$ |
| Every closed edge maps into $I$ | `physical_edge_image` and monotonicity of the ordered vertex list |
| One-step injectivity on each edge | `quadratic_injOn_edge` |
| Row membership iff physical preimage existence | `row_iff_physical_preimage`, for every target-interior point |
| An actual parameter satisfies the premises | `exists_physical_center_with_markov_rows`, inherited from the exact real period-27 center theorem |

These are explicit mathematical premises of the generic theorem, rather
than new axioms. The specialization discharges them from existing proofs.

### 1. Complete and unique interval location

`interior_index_unique` proves that different open edges are disjoint.
`interior_ne_vertex` proves that no vertex lies in any open edge.
`exists_interior_index` locates every nonvertex point of $I$ in an open
edge by taking the largest vertex strictly below it. This proves coverage
as well as uniqueness; it does not infer coverage from a diagram.

### 2. Endpoint exclusion at every finite horizon

`iterate_vertex` proves by induction that every iterate of a vertex is
again a vertex. Therefore a point whose $n$th image is in $E_j^\circ$
cannot itself be a vertex, and none of its intermediate iterates can be
a vertex. A one-step preimage in a closed source edge is therefore in
that edge's interior (`preimage_interior`). Branch injectivity then yields
`unique_interior_preimage`.

This is why the complete-core fiber can be partitioned by open source
edges without discarding any of its points. Target endpoints are excluded
by hypothesis; no multiplicity statement for those endpoints is asserted.

### 3. Actual backward lifting and its converse

The finite path type has the recursion

$$
\operatorname{Paths}_0(i,j)=\{\text{proof that }i=j\},\qquad
\operatorname{Paths}_{n+1}(i,j)
=\coprod_{k:A_{ik}=1}\operatorname{Paths}_{n}(k,j).
$$

`pathFiberEquiv` lifts the terminal point backward along this path using
the unique physical inverse on each indicated branch. Different paths
yield different physical points: their first images must agree if the
points agree, the first-image interiors uniquely determine the next edge,
and the shorter paths are recovered inductively.

For surjectivity, `fiber_successor_decomposition` starts from an arbitrary
actual preimage. Its first image lies in $I$ by the proved image inclusion.
It is not a vertex by Step 2, so Step 1 assigns it a unique open edge.
The converse one-step row theorem proves that this is an allowed edge.
The remaining iterate equation gives the shorter physical fiber. Thus
the construction loses no actual preimage in the specified source edge.

### 4. Cardinality and the matrix orientation

`paths_card_eq_matrix_power` proves the count by induction. At the
successor step the dependent-sum cardinality is

$$
\sum_{k:A_{ik}=1}\#\operatorname{Paths}_n(k,j)
=\sum_k A_{ik}(A^n)_{kj}=(A^{n+1})_{ij}.
$$

`physical_fiber_finite` transports finiteness across the equivalence;
`physical_fiber_card_eq_matrix_power` transports its cardinality.
This matters because Lean's `Nat.card` is also defined for infinite
types: the separate finiteness theorem rules out a misleading use of
that totalized definition.

`coreFiberPartition` proves the complete core decomposition directly.
`corePathFiberEquiv` composes it with the path equivalences, proving both
core-fiber finiteness and the column-sum formula.

## Zero horizon and negative cases

The horizon is a natural number, including zero; negative iterates are
not part of the statement. For $n=0$, the fiber is exactly $\{y\}$ when
$i=j$, and it is empty when $i\ne j$, by disjointness of open edges.
This agrees with $A^0=\mathrm{Id}$. The complete-core fiber is then
exactly $\{y\}$, whose column sum is one.

For any horizon, a zero matrix-power entry means that the corresponding
source-interior fiber is empty, not that several preimages cancel.
The matrix and the proved counts take values in $\mathbb N$. In
particular the existing omitted-row example is retained at horizon one.

The theorem cannot be extended to a target vertex by removing the
interior hypothesis. For example, take $n=0$, $i=j$, and $y=v_j$ in the
closed target edge. The source-interior fiber is empty because
$v_j\notin E_j^\circ$, but $(A^0)_{jj}=1$. Thus the claimed formula would
already fail at horizon zero. The endpoint-exclusion argument uses the
interior hypothesis at its essential step, and closed source edges share
vertices.

## Public physical declarations and verification

The physical declarations are in namespace `LoopsRealPeriod27.Markov`:

| Declaration | Formal conclusion |
|---|---|
| `physicalPathFiberEquiv` | Finite paths and actual source-interior preimages are equivalent for every $n$ |
| `physical_preimage_finite` | The actual source-interior fiber is finite |
| `physical_preimage_count` | Its cardinality equals $(A^n)_{ij}$ |
| `physicalCoreFiberPartition` | All source-interior fibers partition the complete closed-core fiber |
| `physical_core_preimage_finite` | The complete core fiber is finite |
| `physical_core_preimage_count` | Its cardinality is the corresponding column sum |
| `exists_physical_center_with_all_fiber_counts` | The analytic premises are inhabited by an actual center, uniformly in all horizons, edges, and interior targets |

Reproduce the kernel checks from `formalization/weighted` with the pinned
toolchain and Mathlib dependency:

```sh
lake build FiniteMarkovFibers Period27FiniteFibers
```

The modules include `#print axioms` checks of the bridge declarations.
The only reported logical axioms are Mathlib's standard `propext`,
`Classical.choice`, and `Quot.sound`; the proofs use no `sorry`, custom
axiom, or `native_decide`. Mathematical status changes should follow the
successful build of the exact source revision.

## Attribution and research role

This is an elementary finite Markov-partition argument and a formalization
of the archive's existing written proof. It is not presented as a new
general theorem in dynamics or a worldwide-first correlation. Its concrete
advance is a reusable, kernel-checked transition from verified finite rows
to actual distinct real inverse points, with complete endpoint and core
coverage arguments. Any later spectral or renewal interpretation can now
consume this specific physical count theorem instead of assuming it.

AI assistance was used for proof design, Lean implementation, and exposition.
Verification here means Lean kernel acceptance and the stated dependency
audit; independent human review is not represented as completed.
