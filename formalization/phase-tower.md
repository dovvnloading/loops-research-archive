# Multiscale phase towers: exact quotient information and the 3/9/27 carry model

**Formalization:** [`PhaseTower.lean`](../PhaseTower.lean), [`PhaseTower27.lean`](../PhaseTower27.lean)  
**Lean version:** root `lean-toolchain`, Lean 4.32.0 (no mathlib dependency for these modules)  
**Scope:** universal finite clock facts and conditional transport of *actual* physical iterates.  
**Claim status:** strictly finite/conditional. **No MLC ledger status is changed.**

## Research question

The recent exact real quadratic model has a critical period-27 orbit and
nested physical return times 3 and 9. Its canonical phase projections are

```text
27 physical phases --mod 9--> 9 inner-return phases --mod 3--> 3 outer-return phases.
```

The central *marking* question is different from simply checking arithmetic
congruences: when is a label of a finer orbit determined by the coarser clock?
If it is not, exactly which retained phase information can repair the loss?

Paper 1 warns against discarding sheet information, Paper 2 explicitly
distinguishes a one-scale symbolic compactification from a cross-scale
geometric theorem, and the November 2026 symbolic atlas distinguishes
candidate angles from analytically realized access/sheet transport.
The Lean result here gives a sharply typed **finite phase-only model** for
one part of that interface. It does not equate these finite clock labels
with sheet cosets, prime ends, or KL marked state data.

## 1. Universal loss and factorization of phase markings

For `p > 0`, let

```text
Phase p := Fin p
project p q : Phase q -> Phase p,       i |-> (i mod p).
```

For an arbitrary target type `A` and marking `L : Phase q -> A`, define

```text
FactorsThrough p q L
   := exists g : Phase p -> A, forall i, L i = g (project p q i).

ConstantOnFibers p q L
   := forall i j, project p q i = project p q j -> L i = L j.
```

**Exact quotient criterion.** For `0 < p <= q`, Lean proves

```text
FactorsThrough p q L  <->  ConstantOnFibers p q L.
```

The forward direction is immediate from equality of projected phases.
The reverse direction is constructive: choose the canonical fine
representative `i=a` of each coarse phase `a` and define
`g(a)=L(a)`. Fiber constancy makes this independent of the representative.
Surjectivity proves **uniqueness** of the recovered coarse marking.

**Sharp obstruction.** For `0 < p < q`, there are distinct fine
phases `0` and `p` with equal coarse residues. Consequently, **any
injective marking of all `q` phases fails to factor through the
`p`-clock**. This is stronger than exhibiting a failure of a particular
coding or a particular putative inverse: *no* relabeling
`g : Phase p -> A` can recover the distinct marks.

The proof is polymorphic in `A`, so this impossibility does not depend
on real numbers, choice of alphabet, or a numerical example.

### Why the iff matters

The obstruction is not a blanket prohibition on collapsing clock phases.
Some labels really are constant on fibers and can be transferred
losslessly. The iff characterizes exactly when this is allowed, and the
uniqueness theorem shows there is then only one coherent coarse label.

For example, a property determined entirely by the residue modulo 3
factors through the 9-to-3 projection. A label distinguishing phase 0
from phase 3 provably does not.

## 2. Composable refinement and a physical versus symbolic distinction

If `p | q`, Lean derives

```text
(j mod q) mod p = j mod p
project p q (project q r i) = project p r i.
```

It also proves that if an `r`-marking factors through `q`, and its
induced `q`-marking factors through `p`, then the original marking
factors through `p`. This gives a precise test for whether an
intermediate refinement is genuinely retaining indispensable information.

Arithmetic phase projection alone does **not** prove that a physical
dynamical set exists or that its phase labels are correct. Accordingly,
the module separately takes a self-map `f`, nested predicates
`inner ⊆ middle ⊆ outer`, and return-invariance hypotheses
`f^p(outer) ⊆ outer` and `f^q(middle) ⊆ middle`. It proves that for every
physical starting point `x ∈ inner` and every time `j`, there exist
*physical* witnesses `y ∈ outer`, `z ∈ middle` with

```text
f^j(x) = f^(j mod p)(y)
f^j(x) = f^(j mod q)(z).
```

These witnesses come from the actual iterate-addition law and the
forward-invariance assumptions, not a symbolic routing postulate.

A separate conditional alignment theorem says that if nonzero outer
phases are disjoint from a proposed first-return base, then a return
to that base requires `j mod p = 0`. Both statements expose their
dynamical assumptions rather than deriving them from the combinatorics.

## 3. Exact reversible 27-phase address

A phase `0 <= j < 27` has the **unique** representation

```text
j = a + 3 b + 9 c,      0 <= a,b,c < 3,
a = j mod 3,
b = (j / 3) mod 3,
c = j / 9.
```

The Lean types enforce all range restrictions:

```lean
abbrev Address27 := Phase 3 × Phase 3 × Phase 3
def encode27 : Phase 27 -> Address27 := ...
def decode27 : Address27 -> Phase 27 := ...
```

Both inverses are proved, not merely tested on example inputs:

```text
decode27 (encode27 j) = j,
encode27 (decode27 a) = a.
```

Hence `encode27` is injective and surjective. By construction:

- `a` is the exact **3-phase**.
- `a+3b` is the exact **9-phase**.
- `a+3b+9c` is the exact **27-phase**.

The two phase projections commute; dropping `c`, then `b`, has
the same 3-phase result as forgetting both directly. The retained digit
pair or triple is a *finite complete clock address*, not a claim of a
complete geometric or sheet marking.

## 4. A verified clock automaton, not just a static encoding

The physical phase update is

```text
next27(j) = (j+1) mod 27.
```

For the address `(a,b,c)`, the exact carry update is

```text
a' = (a+1) mod 3,
b' = (b + 1_{a=2}) mod 3,
c' = (c + 1_{a=2 and b=2}) mod 3.
```

The 27-case transition identity is checked by kernel reduction:

```text
carry27(a) = encode27(next27(decode27(a))).
```

A general **induction on time** then proves the all-time conjugacy

```text
iterate carry27 t (encode27 j)
    = encode27 (iterate next27 t j)
```

for every `t : Nat`, not just for 27 sampled transitions.
Finally, the module proves that every phase/address returns exactly at
period 27: the 27th iterate is the identity, while no time
`0 < t < 27` fixes any phase.

This proves that the retained three digits support the full physical
27-clock without phase aliasing, and gives a concrete model of the
kind of extra *combinatorial* memory needed when passing between
the nested clocks.

## Formal theorem index

| File | Core declarations | Role |
|---|---|---|
| `PhaseTower.lean` | `project_surjective`, `project_injective_of_le`, `project_has_collision` | Precise quotient size/injectivity boundary |
| `PhaseTower.lean` | `factorsThrough_iff_constantOnFibers`, `coarse_marking_unique` | Necessary and sufficient lossless-marking condition |
| `PhaseTower.lean` | `injective_marking_never_factors`, `two_marks_obstruct_factorization` | Universal phase information-loss obstruction |
| `PhaseTower.lean` | `mod_mod_of_divisor`, `project_compose`, `factorization_transitive` | Functorial compatibility down a tower |
| `PhaseTower.lean` | `physical_outer_phase_route`, `physical_three_level_routes`, `actual_return_requires_outer_alignment` | Conditionally transport actual iterates |
| `PhaseTower27.lean` | `decode_encode27`, `encode_decode27` | Reversible 27-state address |
| `PhaseTower27.lean` | `carry_is_physical_successor`, `carry_conjugacy_all_times` | Conjugacy between physical successor and carry automaton |
| `PhaseTower27.lean` | `next27_no_early_return`, `address_exact_period27` | Exact minimal period |
| `PhaseTower27.lean` | `nine_to_three_cannot_preserve_distinct_marks`, `twentyseven_to_nine_cannot_preserve_distinct_marks` | Specific strict refinement obstructions |

## Proof boundary and remaining work

The source certificate establishes certain real restrictive intervals
and exact combinatorial orbit/angle data, while the independent complex
certificate establishes a separate *attracting* quadratic-like
two-scale model under stated hypotheses. This formalization **does not
import those analytic certificates into Lean**: it formalizes the
general logical transport conditional on containment/invariance, and
it checks the independent finite phase automaton.

In particular:

1. No proof here identifies real or complex dynamical accesses, parameter
   rays, tuned component roots, sheets, or prime ends.
2. The `3/9/27` digit model is *not* an encoding of Paper 1's infinite
   coset-valued sheet fiber.
3. No theorem proves the protected KL marked construction (`H1`), width
   calibration (`H2`), coercivity (`H3`), rigidity (`H4`), universal
   protected-tower closure, or Mandelbrot local connectivity.
4. The proof status of the 465-entry source-locked ledger is unchanged.
5. Further work must establish the source-correct physical labeling and
   prove which additional access/sheet observable remains future-faithful
   across scales. No amount of clock arithmetic supplies that by itself.

## Reproduction

From the repository root, with the pinned Lean version:

```sh
lake build PhaseTower PhaseTower27
lake build
```

The research validation workflow checks these modules and rejects
proof placeholders. The exact version-specific GitHub Actions run for
the branch should be checked before merging.

**AI assistance:** OpenAI GPT-6 assisted with theorem architecture,
Lean proof generation, and mathematical boundary documentation.
The GitHub Actions Lean kernel check is an independent mechanical check
of the encoded formal theorems; expert verification that those theorems
match the research program's intended observables remains necessary.
