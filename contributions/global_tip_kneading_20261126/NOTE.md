---
ledger: NOV26_OPEN_WINDOW
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean development and independent AI mathematical review
human_review: none
---

<a id="global-tip-kneading-20261126"></a>

# Global real kneading isolation for the ten finite primitive tips

## Claim

For each return index `p = 3,...,12`, there is exactly one real parameter
`c` satisfying the actual critical relation

```text
x_0(c) = 0,        x_(n+1)(c) = x_n(c)^2 + c,
x_(6p)(c) + x_(3p)(c) = 0,
```

and the complete selected critical itinerary through time `6p`:

- At return times `p,2p,3p,4p,5p,6p`, the signs are `+--+-+`.
- At every intermediate time congruent to `1 mod p`, the sign is negative.
- At every other intermediate time, the sign is positive.

The parameter quantifier is over **all of the real line**. There is no
seed interval, signed parameter chart, or assumed parameter bound in the
hypotheses of `exists_unique_global_signed_tip`. The resulting zero is
simple: the derivative with respect to `c` of `x_(6p)+x_(3p)` is nonzero.

A second theorem, `exists_unique_restrictive_tip`, proves existence and
uniqueness on an explicitly defined actual real interval domain using
only the six return signs. Put `d=x_p(c)` and `J=[-d,d]`. The domain is

```text
d > 0,
f_c(J) is strictly negative,
f_c^j(J) is strictly positive for 2 <= j < p,
f_c^p(J) is contained in J.
```

These conditions concern every point of the genuine interval and contain
neither a collision equation nor a parameter locator. The theorem proves
that the constructed root supplies this interval geometry. It also proves
that any parameter with this geometry, the six return signs, and the
collision equation equals that root.

This is **partial progress on NOV26_OPEN_WINDOW**, whose ledger statement is:

> Global primitive-component uniqueness: Local p=3..12 seed intervals and signed p>=13 chart do not prove full maximal-real-component uniqueness (F02).

The new result removes the microscopic parameter-chart hypothesis for
all ten finite complete itineraries, and establishes uniqueness throughout
the explicit real interval domain. It does not identify that domain with
a canonical maximal primitive component or settle the all-period row.

## Evidence

### 1. New exclusion, rather than another local root test

The archive's [F02 audit](../../research/tip_family_theorem/AUDIT.md)
explicitly limits finite-period uniqueness to intervals of width
`2*10^(-75)`. The [all-period note](../../research/independent_audits/real_primitive_tip_family_all_p_20261116/NOTE.md)
provides its separate signed-chart argument only for `p >= 13`.
Neither establishes the finite global statement above.

The new proof first shows that a negative critical iterate at any time
`n >= 2` forces `-2 < c < 0`. For `c >= 0` all critical iterates are
nonnegative. For `c <= -2`, the second iterate is at least `-c`, and that
lower bound propagates. The selected negative third return therefore
reduces the whole real parameter line to one closed interval, `[-2,0]`,
without presupposing a near-`-2` chart.

### 2. An exhaustive cover checked by the Lean kernel

Five certificate modules encode binary trees covering **the entire closed
interval `[-2,0]`**, for all ten periods. A node's interval is inherited
from its ancestors. A split at an integer-scaled endpoint covers both
closed children, so shared endpoints are retained and no gap can occur.
All computations use exact signed integers at scale `2^128`.

| Return index | Leaves in the complete cover |
|---:|---:|
| 3 | 120 |
| 4 | 134 |
| 5 | 145 |
| 6 | 161 |
| 7 | 169 |
| 8 | 187 |
| 9 | 203 |
| 10 | 215 |
| 11 | 229 |
| 12 | 243 |
| **Total** | **1,806** |

The leaves comprise 1,301 wrong-sign exclusions, 91 direct nonzero-relation
exclusions, 404 deflated-relation exclusions, and exactly ten retained root
intervals. `decide +kernel` verifies every split and every exclusion.
`coverCheck_sound` then proves soundness for **every real parameter** in
these intervals, including all irrational values between grid endpoints.

A wrong-sign leaf combines a non-strict opposing interval bound with the
required strict orbit sign. A direct leaf encloses the actual collision
polynomial away from zero. A retained leaf checks that its entire interval
is contained in the designated root box. Python only generates the
certificate; it is not in the theorem's trust base.

### 3. Exact deflation removes center roots safely

Direct interval exclusion near centers is obstructed by the zero factor
`x_(3p)`. The proof establishes the exact identity

```text
x_(6p) + x_(3p)
  = x_(3p) * (2 + product(j=0,...,3p-1) (x_(3p+j) + x_j)).
```

The product is the complete difference-of-iterates factor, including its
`j=0` term. The strict third-return sign proves `x_(3p) < 0` before the
factor is canceled. Consequently a nonzero enclosure of the parenthesized
factor genuinely excludes every selected root in the leaf, while centers
are rejected by the required strict signs. There is no numerical zero
tolerance or division by an unproved nonzero quantity.

### 4. Existence, simplicity, and actual interval geometry

For each retained box Lean checks opposite endpoint signs, a uniform
nonzero derivative interval, the complete strict critical itinerary, and
the strict endpoint margin `x_p+x_(2p)>0`. The existing `DepthThreeReal`
soundness theorem supplies a unique actual real root in the strict
interior. Its closed-box injectivity combines with the global exclusion
cover to prove global uniqueness.

The decimal seeds from the archive are only locators used by the generator.
The new boxes are much wider, with intended radius `16^(-p)/32`, rounded
outward onto the exact `2^-128` grid. Their endpoints, derivative bounds,
and sign predicates are all proved inside Lean independently of the
locator's correctness.

`GlobalTipWindow.lean` proves an exact finite endpoint characterization of
the whole-interval domain. For `p>=2`, it is equivalent to

```text
x_p > 0,       x_(p+1) < 0,
x_(p+j) > 0 for 2 <= j < p,
-x_p <= x_(2p).
```

The argument bounds every first image between `c` and `x_(p+1)`, uses
antitonicity of squaring on the negative first phase, then uses monotonicity
on each positive phase. Invariance implies that every complete return of
zero stays in `J`. Thus the domain and the six return signs imply the
complete word used in global exclusion. Conversely, the root-box
certificates construct this actual domain for the selected root.

### 5. Lean modules and verification

The primary theorem module is
[GlobalTipFamily.lean](../../formalization/weighted/GlobalTipFamily.lean).
Its main statements are:

- `exists_unique_global_signed_tip`: global existence and uniqueness for
  the complete critical word, for every `3 <= p <= 12`.
- `global_tip_enclosed`: every eligible real parameter belongs to the
  exact retained interval, with no prior parameter bound.
- `global_tip_simple`: the genuine parameter derivative is nonzero.
- `global_tip_restrictive`: the selected root supplies the actual invariant
  central interval and all its strict intermediate phase signs.
- `exists_unique_restrictive_tip`: global existence and uniqueness on that
  actual interval domain with the six return signs.

[GlobalTipIsolation.lean](../../formalization/weighted/GlobalTipIsolation.lean)
contains the general exact-cover proof and deflation.
[GlobalTipWindow.lean](../../formalization/weighted/GlobalTipWindow.lean)
contains the genuine interval dynamics and the global parameter bound.
The five `GlobalTipCertificates*` modules contain all finite tree, root,
word, and invariant-endpoint checks. They are registered as default targets
and every public theorem is listed in the repository's theorem index.

The project pins Lean 4.32.0 and Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. Reproduce the data and build with:

```sh
python -B contributions/global_tip_kneading_20261126/verify_certificates.py
lake -d formalization/weighted build GlobalTipFamily
python -B code/contribute.py check
```

The verifier is read-only unless `generate_certificates.py --write` is
explicitly requested. Normal CI compiles the registered project targets
and audits every declaration transitively. The only permitted foundational
dependencies are `propext`, `Classical.choice`, and `Quot.sound`; no proof
placeholder, new logical assumption, or executable proof bypass is used.
Exact checked commits and CI links are recorded in the PR description.

## Dependencies

The mathematical proof reuses `DepthThreeCert`, `DepthThreeReal`,
`Period27RealCenter`, their signed-integer interval soundness dependencies,
and Mathlib's real calculus and intermediate value theorem. It does not
import an unformalized dynamics theorem as an assumption.

The [earlier finite audit](../../research/independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py)
provides only decimal root locators. The existing complex secant-product
calculation in `QuadraticCollisionFactorization` motivates the real
factorization used by the checker; the elementary factorization itself is
supporting infrastructure, not the claimed new global exclusion result.

## Boundary

**NOV26_OPEN_WINDOW remains open.** This packet proves the finite
`p=3,...,12` global full-itinerary theorem and its exact invariant-real-
interval formulation. It does not extend global exclusion to all `p>=13`
or prove equality between the formal real interval domain and a canonical
maximal primitive component. No ledger status change is requested.

The complete critical word is stronger than the six return signs alone.
Global uniqueness from only those six signs is asserted only with the
explicit actual interval-domain hypothesis, whose full-word consequence
is proved. The interval domain does not itself assert pairwise disjointness
of all phase intervals, a complex polynomial-like restriction, or the
complete KKL marking.

The index `p` is the return index. This packet does not claim a separately
proved exact eventual dynamical period or preperiod. Simplicity is a
parameter-derivative conclusion, not a claim about a repelling multiplier.
No canonical complex-copy identification, Wave width, marked transport,
MLC case, H1-H4 closure, or worldwide mathematical priority is asserted.

## Attribution

The new contribution is the exhaustive finite global parameter exclusion
and its exact connection to the actual invariant interval domain. It
builds on the archive's finite-tip audits and the depth-three certificate
soundness engine, preserving their explicit distinctions between finite
arithmetic, genuine dynamics, and unproved canonical identifications.

Proof development, exact certificate generation, integration, and an
independent source-level mathematical review were AI-assisted. No
independent human review has occurred. The contribution is released under
the repository's CC0 terms.
