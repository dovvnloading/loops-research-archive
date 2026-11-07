# General finite-clock memory theorem (Lean 4.32.0)

**Scope:** This note records a generalization of the repository's 3/9/27
phase memory formalization. It is a theorem about *finite cyclic clocks*.
It does not construct physical rays, prime ends, localization sheets,
holomorphic renormalizations, or a Mandelbrot local-connectivity proof.

## Precise construction

For any positive integers p and k, let the physical clock be
`Fin (p*k)`. The coarse observable is reduction modulo p, and the
auxiliary memory digit is the integer quotient:

```
address(i) = (i mod p, i / p)
decode(r,s) = r + p*s
```

The new [PhaseMemoryGeneral.lean](../PhaseMemoryGeneral.lean) proves, for
**all** p>0 and k>0 and without finite enumeration:

- `decode_address` and `address_decode`: these maps are inverse.
  Accordingly, `address_injective` and `address_surjective` give a
  lossless mixed-radix representation.
- `zeroFiber_projects_zero` and `zeroFiber_injective`: the k distinct
  fine phases `i=p*s` lie over the same coarse phase zero.
- `memory_injective_on_zeroFiber`: if any code
  `i ↦ (i mod p, mem(i))` is injective, its memory values on that
  zero fiber are already pairwise distinct, for an **arbitrary memory
  type** `M`.
- `zeroSensor_future_requires_memory`: *even without assuming a
  transition on the augmented state*, merely preserving all future
  readings of the single Boolean sensor `(i == 0)` forces the same
  injection `Fin k → M`, using the pre-existing general clock
  observability theorem.
- `address_step_semiconjugate` and `addressNext_coarse`: the
  deterministic update induced by the physical successor advances the
  coarse phase correctly, including carries and wraparound.
- `address_factors_all_future_streams`: the explicit k-state
  memory has a deterministic transition and reconstructs the entire
  future stream of **every** observable.

Thus the number of auxiliary states required for a lossless
future-faithful augmentation is **exactly k**, in the precise sense that
every candidate memory type must admit an injection from `Fin k`,
and the concrete type `Fin k` suffices. No entropic or asymptotic
approximation is used.

## Relation to the 3/9/27 example

The previous [PhaseFuture27.lean](../PhaseFuture27.lean) constructs and
checks a concrete triple-ternary carry automaton and proves memory
requirements of 9 states for a 27→3 quotient and 3 states for a 27→9
quotient. These are now also instances of the all-p,k theorem, with
`(p,k)=(3,9)` and `(9,3)`. The old theorem statements and concrete
`decide +kernel` examples are retained as separate regressions.

## Reproduction and trust

In the repository root, run:

```bash
lake build PhaseMemoryGeneral
lake build
```

The [research-validation workflow](../.github/workflows/lean-proofs.yml)
includes the module in its default kernel build and scans for
`sorry`/`admit`. The module includes explicit `#print axioms`
commands for its key theorems.

**Critical boundary:** preservation of the Boolean clock sensor is an
encoded symbolic hypothesis. No result here shows that the actual
source-defined KKL prime-end or edge-incidence map admits such an
address, or that the synthetic finite memory is an actual analytic
sheet marking. In particular, no H1–H4, UPTCR, or MLC gate is promoted.
