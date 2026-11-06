# Future-observable phase quotients and sharp 3/9/27 memory requirements

**Modules:** [`PhaseFuture.lean`](../PhaseFuture.lean), [`PhaseFuture27.lean`](../PhaseFuture27.lean).  
**Build target:** root `lake build` using pinned Lean 4.32.0; no mathlib required.  
**Scope:** deterministic dynamics and finite cyclic phase clocks only. The existing MLC ledger, H1–H4 gates, and source-locked analytic status remain unchanged.

## The next gap after PR #24

The previous phase-tower formalization proved that a static fine-phase marking
factors through a coarse clock exactly when it is constant on fibers of the
projection. This resolves **one observation at one time**.

The dynamical research program needs a stricter interface: a quotient that
retains the information needed by **future iterations**. A symbolic quotient
can look harmless at one instant but erase a distinction visible later.

We formalize this as a property of deterministic transition systems. The
result is an exact, source-independent logical tool; the research program
must still prove that its particular accesses, sheet states, or observables
fit these types.

## 1. The general future-sound quotient theorem

Let `S` be a state space, `T` a coarse state space, `f : S -> S` a
physical transition, `g : T -> T` a proposed coarse transition,
`pi : S -> T` a quotient, and `obs : S -> O` a named observable.

Define **future equality** by

```text
FutureEqual f obs x y :=
  forall t : Nat, obs (f^[t] x) = obs (f^[t] y).
```

This is an equivalence relation and is **forward invariant**. Define
future soundness on quotient fibers by

```text
PreservesFuture pi f obs :=
  forall x y, pi x = pi y -> FutureEqual f obs x y.
```

There are two separate properties whose conflation would be unsound:

- **Transition compatibility / semiconjugacy:** `pi (f x) = g (pi x)`.
- **Current observation factorization:** `obs x = read (pi x)` for
  some coarse readout `read : T -> O`.

The Lean proof has two substantive stages. First, transition
compatibility is propagated to **all** times by an induction:

```text
pi (f^[t] x) = g^[t] (pi x).
```

Second, readout factorization and that conjugacy give

```text
obs (f^[t] x) = read (g^[t] (pi x))
```

for every physical state and time. Conversely, future soundness implies
that `obs` is constant on each quotient fiber, and surjectivity of
`pi` permits selecting one state per fiber to define a coarse readout.
Thus, for a **surjective, transition-compatible** quotient,

```text
PreservesFuture pi f obs
    <-> FactorsObservation pi obs
    <-> FactorsFutureStream pi f g obs.
```

The theorem does **not** require `S` or `T` to be finite, nor does
it require a decidable or numeric observable type. It proves
future-*observation* soundness, not injectivity of the quotient or
preservation of every conceivable future observable.

### The necessary hypothesis, with a Lean-checked countermodel

It would be incorrect to say static factorization always implies future
soundness for any quotient. If a quotient is not transition compatible,
two states with equal coarse state can evolve to states with different
coarse states and different readings. The semiconjugacy hypothesis
prevents precisely this failure.

The `bad_static_does_not_preserve_future` theorem gives an explicit
four-state countermodel. Take the quotient `pi : Fin 4 -> Fin 2`
given by parity, and observe `obs(i)=(i mod 2 == 0)`. Then the current
observable factors through the quotient exactly. But a deterministic
transition that fixes phase 0 and sends phase 2 to phase 1 has no
compatible quotient transition: phases 0 and 2 have the same parity
at time zero, yet their observations differ at time one. Lean proves
all three claims (`bad_static_observation_factors`,
`bad_quotient_has_no_compatible_transition`, and
`bad_static_does_not_preserve_future`) by kernel-checked proofs.

## 2. Concrete cyclic clock semiconjugacy

For any positive period `p`:

```text
clockNext p : Fin p -> Fin p,
clockNext p i = (i+1) mod p.
```

Lean proves:

- `clockNext p` is injective for all `p>0`;
- for all times, `iterate (clockNext p) t i = (i+t) mod p`;
- if `p` divides `q`, the reduction `Fin q -> Fin p`
  commutes with successor, hence all future iterates;
- for such a projection, future soundness is equivalent to static
  factorization of the named observation through the mod-`p` residue.

The last fact is an exact dynamic strengthening of PR #24's theorem,
not a new assumption about a source quadratic polynomial.

## 3. One bit can distinguish every clock state across time

Consider an extremely weak sensor:

```text
zeroSensor p i := (i == 0)   -- only one Boolean output per time
```

At any single time, this sensor distinguishes just phase zero from all
the others. Yet its **complete future stream** distinguishes every phase.

Lean proves the stronger *bounded* theorem: for all `p>0`, if the
sensor readings of two phases agree at times

```text
t = 0, 1, ..., p-1,
```

then those two phases are equal.

The proof is not an exhaustive enumeration. For an initial phase `i`,
choose `t = (p-i) mod p`; then `0<=t<p` and the first trajectory
reaches phase zero. Equal sensor readings force the other trajectory
to reach phase zero at the same time. Since successor and its iterates
are injective, the initial phases coincide.

Formally, the whole length-`p` Boolean trace defines an **injective
map**

```text
Fin p -> (Fin p -> Bool).
```

It follows that *any* code retaining this named sensor at all future
times must be injective, even though the instantaneous sensor is not.

This should not be confused with a claim that one-bit sensors suffice
to reconstruct Kahn–Lyubich geometric states. The underlying cyclic
clock is known and finite, and the sensor is precisely specified.

## 4. Sharp finite memory requirements for 27 -> 9 -> 3

The prior Lean model certifies a complete 27-phase clock with a
three-digit ternary address `(a,b,c)`:

```text
j = a + 3b + 9c,   a,b,c in {0,1,2}.
```

The new module proves **both constructive upper bounds and universal
necessary lower bounds** for the following augmented clocks:

| Coarse phase retained | Memory alphabet necessary | Explicit sufficient memory | Total encoded states |
|---|---|---|---|
| `j mod 9` | At least **3** distinct values in a single fiber | `floor(j / 9)` in `Fin 3` | 9×3 = 27 |
| `j mod 3` | At least **9** distinct values in a single fiber | `floor(j / 3)` in `Fin 9` | 3×9 = 27 |

**Proof of the lower bound.** Fix coarse phase zero. In the 3-phase
case, the nine phases `0,3,...,24` all have the same coarse projection.
If `i -> (i mod 3, memory(i))` preserves every future zero-sensor
reading, the general observability theorem makes that combined code
injective. Hence its memory restriction to those nine phases is an
injection `Fin 9 -> M` for any proposed memory type `M`, proving
nine distinguishable values are necessary. The 9-phase case similarly
has three phases `0,9,18` and forces an injection `Fin 3 -> M`.

**Proof of sufficiency.** Lean checks exact inverse identities for

```text
Fin 27 <-> Fin 3 × Fin 9,
Fin 27 <-> Fin 9 × Fin 3,
```

constructs their induced deterministic transitions, and proves
that **every observable** can be read at every future time from the
augmented address. The memory requirement is therefore sharp for
retaining the full 27-state phase clock; this is a statement about
the finite model, not the infinite marking space of the paper.

The two constructions agree with the old three-digit address:
`floor(j/3)=b+3c` and `floor(j/9)=c`.

## 5. Negative control: a snapshot does not suffice

Two phases in the same `mod 3` fiber, `j=1` and `j=10`, both
initially produce `false` on the zero sensor. But after 26 transitions,
the first phase is zero while the second is nine, so their readings
disagree. Lean checks this concrete witness from the actual
successor recurrence.

This is a **local witness**, not by itself a counterexample to
universal static factorization (which the mod-3 zero sensor already
fails). Its role is to show how testing one pair at time zero misses
a later observable distinction.

## 6. Formal proof inventory

| File | Theorems | What the Lean kernel establishes |
|---|---|---|
| `PhaseFuture.lean` | `futureEqual_next`, `semiconjugate_iterate` | Forward-invariant future equality, all-time semiconjugacy |
| `PhaseFuture.lean` | `futureSound_iff_observationFactor`, `factorsFutureStream_iff_factorsObservation` | Exact abstract quotient criteria |
| `PhaseFuture.lean` | `clock_project_semiconjugate`, `clock_future_iff_static_factor` | Dynamic phase projection criterion for arbitrary divisible periods |
| `PhaseFuture.lean` | `bad_static_observation_factors`, `bad_static_does_not_preserve_future` | Four-state countermodel showing why semiconjugacy is essential |
| `PhaseFuture.lean` | `clock_reaches_zero`, `zeroSensor_bounded_future_separates`, `zeroTrace_injective` | One-bit sensor separates all states over one full clock period |
| `PhaseFuture.lean` | `strict_phase_quotient_loses_zero_future` | Strict phase reduction without memory fails for named sensor |
| `PhaseFuture27.lean` | `outerDecode_encode`, `outerEncode_decode`, `middleDecode_encode`, `middleEncode_decode` | Two exact reversible 27-phase representations |
| `PhaseFuture27.lean` | `outer_future_memory_lower_bound`, `middle_future_memory_lower_bound` | Universal injection lower bounds for arbitrary memory alphabets |
| `PhaseFuture27.lean` | `outerAddress_future_stream`, `middleAddress_future_stream` | Concrete induced transitions and all-time readout for every observable |
| `PhaseFuture27.lean` | `same_snapshot_but_different_future` | Explicit delayed distinction in the 27-phase clock |

The modules print axiom dependencies for the main theorems. The
workflow rejects proof holes and builds all declared root Lean libraries.

## 7. What remains genuinely open

These proofs do not establish or assume the existence of the required
geometric Kahn–Lyubich marked carrier, its transport, or an analytic
observational state. The zero-phase Boolean sensor is a *chosen finite
observable* of a phase clock and is not identified with an external
ray, a prime-end access, a sheet coset, or extremal width.

The next mathematical interface is source-correct: one must name the
actual geometric observation functions consumed by the reduction,
verify that the dynamical transition respects the proposed quotient,
and prove that the selected readouts remain sufficient for all future
analytic steps. A quotient may be lossless for the chosen finite sensor
and still lose other necessary geometric information. Paper 1's
infinite sheet-kernel warning therefore remains in force.

In particular: **no MLC conjecture claim is promoted; no H1–H4
or universal protected-tower closure is proved by this extension.**

## Reproduce and review

From the repository root:

```sh
lake build PhaseFuture PhaseFuture27
lake build
```

The GitHub Research validation workflow builds these modules on every
matching branch push and pull request, runs the Python research audits,
and rejects placeholders. The branch's latest complete run should be
inspected before merging.

**AI assistance disclosure:** GPT-6 produced the theorem architecture,
Lean implementations, proof scripts, documentation, and any revisions
from CI diagnostics. Machine checking by the Lean kernel verifies the
encoded mathematical statements; external review remains necessary to
validate their applicability to complex-dynamical marked states.
