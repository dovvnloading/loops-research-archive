---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="critical-return-monodromy-20261126"></a>

# Exact monodromy and analytic branch selection for actual one-critical returns

## Claim

This packet determines the sheet reached by every regular closed path under
the archive's actual selected one-critical quadratic return. It also proves
an exact criterion for an analytic inverse branch on a retained target:
every based loop must have even winding in the constructed critical
coordinate. The prescribed starting sheet extends uniquely whenever that
condition holds. Every integer winding occurs in every neighborhood of
the propagated critical value, and no continuous inverse section exists
on any punctured neighborhood of that value.

There are **40 public Lean theorems in six modules**. The four physical
modules contain 15 of those theorems; the other 25 provide the required
continuous-loop and square-root infrastructure. The progress relative to
the archive is the actual return's closed-loop phase calculation, exact
branch-selection criterion, and local realization of all phases. No
novelty or priority claim is made for classical covering theory or the
square-root monodromy calculation itself.

The ledger obligation is broader:

> Every actual finite virtual stage cycle admits compatible selected relative-cover lifts that are embedded on relatively compact Jordan cores, preserve the full component and deck-phase route, and retain the propagated critical value after the unique quadratic stage, so that the planar critical-spine compiler produces a closed degree-two selected return.

The result is **partial**. It settles the previously uncomputed closed-loop
phase for the specified physical return and identifies the precise
obstruction to a consistent inverse branch. It does not construct the
entire native relative-cover telescope required by that statement.

### Actual objects and hypotheses

Write `f_c(z) = z^2+c`, `P = f_c^a`, `S = f_c^b`,
`R = f_c^(a+1+b)`, and `v = S(c)`. The Lean iterate is
`QuadraticEscape.orbit`. Let V be open and preconnected, with v in V,
and take the actual connected components

```text
D = connectedComponentIn (S⁻¹(V)) c,
B = connectedComponentIn ((z ↦ z²+c)⁻¹(D)) 0,
A = connectedComponentIn (P⁻¹(B)) x,     P(x) = 0.
```

Assume P is injective on A and S is injective on D. These are the existing
saturated-return hypotheses. The components, maps, loops and sections
below are actual subsets and functions in the complex plane.

## Evidence

### 1. One intrinsic coordinate and every lifted endpoint

[TelescopeReturnMonodromy.lean](../../formalization/weighted/TelescopeReturnMonodromy.lean)
contains nine public theorems. `quadratic_return_square_coordinate`
constructs one analytic injective coordinate s on the whole target V,
using the actual conformal suffix inverse:

```text
s(y) = (S|D)⁻¹(y) - c,
s(R(z)) = P(z)²        for every z in A,
s(y) = 0  iff  y = v  for every y in V.
```

The coordinate is constructed using surjectivity of the actual selected
suffix component onto V and the existing conformal-inverse theorem.
Complete return surjectivity also proves that any two coordinates
satisfying the square identity agree on all of V
(`ReturnCoordinate.eqOn_of_onto`). Consequently each actual loop's winding
is independent of the inverse construction
(`ReturnCoordinate.winding_eq_of_onto`).

`quadratic_return_monodromy` constructs this coordinate and one analytic
deck involution tau. For every continuous closed path gamma in V avoiding
v, and every complete actual lift Gamma in A, it proves

```text
Gamma(1) = Gamma(0)       iff  winding(s ∘ gamma) is even,
Gamma(1) = tau(Gamma(0))  iff  winding(s ∘ gamma) is odd.
```

No smoothness, polygonal-path assumption, simply connected target, or
preassigned winding label is needed.
`quadratic_return_unique_lift_with_monodromy` also constructs the unique
lift from every prescribed regular source point z, with its endpoint
explicitly equal to z or tau(z) according to that parity. Existence and
the endpoint computation occur in one theorem.

### 2. Exact analytic inverse-branch criterion

[TelescopeBranchSelection.lean](../../formalization/weighted/TelescopeBranchSelection.lean)
contains three public theorems. Let U be an open preconnected subset of
V avoiding v. Choose a basepoint y in U and a physical starting point
z in A with R(z)=y. Then
`quadratic_return_unique_analytic_section_iff_even_loops` proves the
equivalence of:

1. Every actual based loop in U has even winding after applying s.
2. There is an analytic sigma on U with sigma(U) contained in A,
   R(sigma(w))=w throughout U, and sigma(y)=z. Moreover every continuous
   physical inverse section with the same prescribed value equals sigma
   on U.

Even continuous section existence has exactly the same criterion
(`quadratic_return_continuous_section_iff_even_loops`). The necessary
direction, `continuous_section_forces_even_loops`, does not require
connectedness or analyticity of the proposed section. The domain need
not be simply connected, and the prescribed value chooses the initial
sheet. Uniqueness is equality on U; arbitrary extensions outside U are
not compared.

The sufficiency proof includes the required physical identification.
The loop condition constructs a root xi of s with xi(y)=P(z). For w in U,
actual return surjectivity gives q in A with R(q)=w. Then xi(w)^2=P(q)^2,
so xi(w) is P(q) or -P(q). The actual critical component B is sign
invariant, hence xi(w) belongs to B in both cases. Composing xi with the
actual conformal inverse of P gives a section into A. The square identity
and injectivity of s prove the right-inverse equation. Uniqueness of the
anchored square root, followed by injectivity of P on A, proves uniqueness
of the physical section. Membership in the chosen component is derived
rather than assumed.

### 3. All integer windings at one local basepoint

[TelescopeMonodromyRealization.lean](../../formalization/weighted/TelescopeMonodromyRealization.lean)
contains `quadratic_return_all_local_windings`. It constructs one s and
one tau for the return. For every open neighborhood W of v, it chooses
one positive radius r and one source point z **before** quantifying over
all integers n. For every n, it constructs a loop gamma_n in
`(V ∩ W) \ {v}` and a lift Gamma_n from that same z such that

```text
P(Gamma_n(t)) = r exp(pi i n t),
s(gamma_n(t)) = r² exp(2 pi i n t),
winding(s ∘ gamma_n) = n.
```

Every complete lift of gamma_n closes exactly when n is even and ends
at its deck partner exactly when n is odd. Negative integers and zero
are included. The radius is in the critical-stage coordinate; it may
depend on W and the selected return.

[TelescopeMonodromyObstruction.lean](../../formalization/weighted/TelescopeMonodromyObstruction.lean)
contains two theorems. `quadratic_return_small_switching_loop` explicitly
constructs a switching loop in every W without assuming a loop or
monodromy action as input. `quadratic_return_no_punctured_section` then
rules out a continuous physical right inverse even on
`(V ∩ W) \ {v}`. Composing any supposed section with the constructed loop
would give a closed lift, contradicting the proved switching. This is a
local obstruction to a single inverse branch, not a counterexample to
the two-sheet telescope obligation.

### 4. Continuous-loop infrastructure and verification

[SquarePathMonodromy.lean](../../formalization/weighted/SquarePathMonodromy.lean)
contains 19 public theorems. A continuous logarithm along a nonzero path
is constructed using Mathlib's exponential covering. For a closed path
its endpoint increment is a unique integer multiple of `2*pi*i`; that
integer defines `windingNumber`. The proofs establish independence from
the starting logarithm, homotopy invariance, additivity under pointwise
multiplication, the integer-power law, and exact values on exponential
loops. The square-lift endpoint identity is proved from the lifted
logarithm and then converted into the even/odd alternatives.

[SquareRootSelection.lean](../../formalization/weighted/SquareRootSelection.lean)
contains six public theorems. On a path-connected, locally path-connected
space, the even-loop condition constructs a unique continuous square root
with prescribed initial value. The proof derives independence of the
chosen path using actual covering lifts and a path followed by a reversed
path. A continuous square root of a nonzero analytic function on an open
complex domain is proved analytic by the local analytic inverse theorem.
These results supply the preceding physical criterion.

The repository pins Lean 4.32.0 and Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. All six targets build locally:

```sh
lake -d formalization/weighted build SquarePathMonodromy SquareRootSelection \
  TelescopeReturnMonodromy TelescopeMonodromyObstruction \
  TelescopeMonodromyRealization TelescopeBranchSelection
python -B code/contribute.py check
```

The local build completed successfully, and the contribution check returned
`RESULT: PASS`. A separate declaration-wide audit checked all 99 declarations
introduced by the six modules, including 74 theorem constants (generated and
private constants included). It found only the three permitted foundational
dependencies. Source hashes matched the compiled Lake traces before this
audit and were unchanged afterward.

The files are registered as default Lake targets, every public theorem is
in `physical_bridge_index.json`, and the physical modules are assigned to
the existing open CONSTRUCT route. A source registration is not a route
status promotion. The final PR records the exact checked commit and its
CI links. Required CI includes the full weighted Lean build, source
coverage and transitive dependency audit; permitted foundational
dependencies are only `propext`, `Classical.choice` and `Quot.sound`.
The proofs use no `sorry`, `admit`, new axioms or executable proof bypass.

## Dependencies

The direct archive dependencies are
[TelescopePathPairing](../../formalization/weighted/TelescopePathPairing.lean),
[TelescopeUnbranchedCover](../../formalization/weighted/TelescopeUnbranchedCover.lean),
[TelescopeDeckInvolution](../../formalization/weighted/TelescopeDeckInvolution.lean),
[TelescopeConformalInverse](../../formalization/weighted/TelescopeConformalInverse.lean),
and their saturated-return and ramification prerequisites. The proof uses
Mathlib's exponential and power coverings, path lifting and uniqueness,
locally path-connected spaces, and analytic inverse theorem at the pinned
revision. Every dependency is a Lean proof term; no paper theorem is
introduced as a new axiom.

## Boundary

MAPPING_TELESCOPE remains open. The specified saturated component
identities, injective prefix and suffix, critical anchor, and inclusion
of the propagated critical value are hypotheses. This packet does not
prove that every native virtual stage cycle supplies those hypotheses.
It does not construct the source-defined relative-cover identification,
the protected ideal-boundary accesses, compatible relatively compact
Jordan cores, the complete marked cyclic route, or an infinite tower
with uniform geometric control.

The computed winding is that of `s ∘ gamma`. Equality with the ordinary
ambient winding of `gamma-v` on an arbitrary multiply connected V is not
proved here. Pointwise multiplication of loops is not path concatenation;
the packet does not claim a new complete calculation of the native
fundamental group or its marked peripheral subgroups. The branch criterion
quantifies over every based loop and is not a finite decision procedure.
Regular path lifting still excludes the branch value. Local winding
realization provides no period-uniform or cross-scale radius bound.

No ledger status change, new MLC case, or closure of H1-H4 is requested.

## Attribution

The immediate predecessor is
[analytic deck rigidity](../analytic_deck_rigidity_20261126/NOTE.md), whose
Boundary explicitly leaves the sheet reached by a lifted closed loop
uncomputed. This packet builds on its existing lift existence and pairing
instead of presenting those results again as new progress. It also uses
the earlier saturated-telescope, conformal-inverse, and parameter-stable
critical-return work. The source-facing residual remains
[critical chronology, section 15.3](../../research/mlc_unified/critical_chronology_and_retimed_telescope.md#153-relative-cover-and-marked-telescope).

Proof development, implementation, integration, and independent
source-level review are AI-assisted. No independent human review has
occurred. The contribution is released under the repository's CC0 terms.
