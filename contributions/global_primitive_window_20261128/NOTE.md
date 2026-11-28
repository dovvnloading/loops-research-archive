---
ledger: NOV26_OPEN_WINDOW
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation, Lean proof development, and independent AI review
human_review: none
---

<a id="global-primitive-window-20261128"></a>

# Global primitive-window investigation

Ledger statement being addressed:

> Global primitive-component uniqueness: Local p=3..12 seed intervals and signed p>=13 chart do not prove full maximal-real-component uniqueness (F02).

## Claim

Work in progress; the following Lean statements await compilation of their
complete dependency chain. No closure or mathematical-priority claim is made
at this checkpoint.

The final candidate theorem is
`GlobalPrimitiveTipUniqueness.exists_unique_physical_signed_tip`: for every
integer `p>=17`, there is exactly one real parameter with an actual symmetric
invariant interval whose first image is negative and whose intermediate
images at times `2,...,p-1` are positive, whose critical returns at multiples
`p,...,5p` have signs `+--+-`, and for which
`f_c^(6p)(0)+f_c^(3p)(0)=0`. The predicate quantifies over every real parameter
and an arbitrary positive interval radius. It assumes no parameter chart,
return scale, or coefficient isolator. Its equivalence to the archive's
`ActualTip` predicate is also stated and proved in the candidate source.

For the literal real quadratic map `f_c(x)=x^2+c`, set `d=f_c^p(0)`.
Suppose `c` lies in `[-2,-1]`, `d>0`, the entire interval `[-d,d]` has a
negative first image and positive images at times `2,...,p-1`, and its
`p`-th image lies in itself. For every integer `p>=17`, the candidate argument
gives

\[
 14\,4^{-p}<c+2<16\,4^{-p},\qquad 0<d<14\,4^{-p}.
\]

These two small-scale bounds are conclusions from global physical interval
hypotheses. They are not assumptions. This is the proposed global-to-local
step toward the window obligation. The full class has parameter diameter
less than `160*16^(-p)`. Additional candidate theorems derive pairwise
disjointness of all physical phase images and show that every archived
`ActualTip` belongs to this class. These statements do not yet prove
uniqueness of the signed critical relation by themselves; the additional
global signed-root argument below supplies that step.

## Evidence

The initial source inspection distinguishes the following existing results:

1. The November 16 all-period note proves unique simple roots in an explicit
   signed near-minus-two chart, with a parameter asymptotic and a derivative
   lower bound. Reproducing that argument is not the proposed contribution.
2. `NearTwoShooting.lean` constructs a positive-inverse shooting chart and
   proves uniqueness of the parameter for each prescribed terminal value.
3. `NearTwoTip.lean` constructs actual signed tips in a broader parameter
   enclosure, but does not identify the whole maximal primitive window or
   prove uniqueness there.

The investigation will first determine the exact hypotheses that distinguish
the intended window from other roots of the same polynomial relation. A
candidate result counts only after its Lean theorem compiles in the unchanged
repository CI and passes the existing transitive dependency audit. No
unproved result is presented as mathematical progress.

### First proof checkpoint

The four new registered modules are `GlobalPositiveWindow`,
`GlobalRestrictiveWindow`, `GlobalInverseWindow`, and
`GlobalWindowLocalization`. Their proposed argument is:

1. Extend the positive inverse branch `B_c(x)=sqrt(x-c)` to the entire
   parameter interval `[-2,-1]`. Its iterates have parameter Lipschitz
   constant at most one, so `c^2+c-B_c^(p-2)(0)` is strictly decreasing.
   The actual positive critical itinerary forces this shooting function
   to be nonnegative. The previously certified negative right endpoint
   then gives `c+2<20*4^(-p)` globally.
2. Reverse the entire physical interval itinerary. For its endpoint image
   `e=f_c^p(d)` one obtains the exact identity
   `d^2=B_c^(p-1)(d)-B_c^(p-1)(e)`, with `e` in `[-d,d]`. This is an
   equality of actual iterates, not a symbolic replacement for them.
3. The first inverse step on the entire possible endpoint range has secant
   constant at most `3/4`, and every subsequent step has constant at most
   `1/3`. The endpoint identity first forces
   `d <= (27/2)*3^(-p)`; no small terminal scale is assumed.
4. Compare the complete normalized inverse product at `-d` with that at
   zero. The derived coarse scale makes the total product loss less than
   `1/400`. The archived `241/400` lower bound at zero consequently gives
   a strict `3/5` lower bound at the actual negative endpoint. The exact
   inverse secant product then gives `d*4^p<40/3<14`.

The full source, not this outline, is the candidate proof. The first weighted
CI run compiled `GlobalPositiveWindow` but rejected proof elaboration in
`GlobalInverseWindow` and `GlobalRestrictiveWindow`. Those errors have been
corrected in the next checkpoint; no successful whole-build claim is made.
Source coverage has passed. The local installation runs
core Lean 4.32.0 but lacks sufficient space for the weighted dependencies,
so weighted compilation is delegated to the unchanged repository CI.

### Complete-window boundary equation

The next candidate argument goes beyond an enclosure. Let `c(d)` be the
unique positive-inverse shooting parameter for `0<=d<=14*4^(-p)`, and set

\[
 P(d)=\prod_{j=1}^{p-1}
 \frac{B_{c(d)}^j(d)+B_{c(d)}^j(-d)}4,
 \qquad L(d)=\frac{8\,4^{-p}}{P(d)}.
\]

The complete inverse secant identity converts endpoint invariance exactly
to `d<=L(d)`. The product is between `3/5` and `1` on the whole shooting
domain, and the parameter comparison and product telescoping estimate make
`L` a contraction with Lipschitz constant at most `1/2`. This gives one
boundary scale `D`, with `8*4^(-p)<=D<=(40/3)*4^(-p)`. The target conclusion
is that the entire positive restrictive class equals the single parameter
interval `[c(D),c(0))`, excluding disconnected hidden pieces. The full
physical converse, including all intermediate interval phases, is part of
this argument; it cannot be replaced by a terminal scalar condition alone.

This classification is being developed in the PR and remains unvalidated
until the unchanged weighted CI accepts the complete dependency chain.

### Signed-root comparison checkpoint

The physical fourth-return sign gives `kappa<2` throughout the global class;
the negative second return gives `kappa>0`. Thus the signed coefficient
chart is also a conclusion. The whole-disk remainder bound used here is
`22*4^(-p)`, derived from the complete archived iterate remainder with the
new global return bound `d<14*4^(-p)`.

For comparison between two physical parameters, the exact inverse product
is retained as a function of its normalized target. This yields an implicit
identity for the complete normalized return, and parameter and spatial
Lipschitz bounds for its quadratic error of `200*p*4^(-p)` and
`300*p*4^(-p)`, respectively. Propagating these differences through six
actual returns gives a signed-error Lipschitz constant at most
`110000000*p*4^(-p)<1`. Combined with the archived model slope greater than
six, the proposed actual signed relation has secants greater than five
on the narrow coefficient isolator. This support theorem is not itself
advertised as new local root mathematics.

To extend that order to all globally admissible signed roots, the current
argument factors out the nonzero third return from the exact threefold
even-secant identity. The resulting root equation is a product equal to
two. This avoids dividing an approximation error by an arbitrarily small
third return. The candidate rational model comparison first confines every
such root to `[1.785,1.795]`, then uses a positive model-factor slope and
endpoint gaps to derive the narrow isolator `[1.7903,1.7904]`. The factor
error is at most `50000*4^(-p)`, uniformly over the complete physical class.

### Recognition from an arbitrary physical interval

`GlobalPrimitiveIntervalRecognition` starts with an arbitrary positive
radius `r`, an invariant interval `[-r,r]`, and the full physical branch
itinerary. These assumptions force `c` into `[-2,-1]`. The positive critical
return and positive fourth return then force the canonical interval
`[-f_c^p(0),f_c^p(0)]` to be invariant as well. Combining this recognition
with the global root exclusion and signed secant theorem removes every
quantitative chart assumption from the final uniqueness statement.

The existing `ActualTip` existence theorem supplies a parameter for each
`p>=17`; new estimates verify that it satisfies the physical predicate.
The final existence-and-uniqueness theorem and all new supporting modules
are committed for validation, not reported as kernel-accepted before CI.

### Rejected first route

Requiring only the first positive critical prefix and six signs at multiples
of `p` is too weak: it leaves the intervening orbit branches uncontrolled.
Exploratory numerical root scans found many unintended candidates. Those
scans are diagnostics, not a submitted theorem. The replacement hypotheses
refer to every point of an actual restrictive interval at every intermediate
time. A sign table is never substituted for that physical condition.

## Dependencies

- `NOV26_OPEN_WINDOW` and `NOV26_TIP_THEOREM` in `ledger.json`.
- `research/tip_family_theorem/AUDIT.md`, finding F02.
- `research/tip_family_theorem/THEOREM.md`, parameter-chart convention.
- `research/independent_audits/real_primitive_tip_family_all_p_20261116/NOTE.md`.
- `formalization/weighted/NearTwoInverse.lean`, `NearTwoProduct.lean`,
  `NearTwoShooting.lean`, and `NearTwoTip.lean`.

## Boundary

This draft has not yet received kernel validation. The ledger remains
unchanged. No local
certificate is to be promoted to global window uniqueness, and no classical
kneading-uniqueness theorem is to be relabeled as new mathematics. Any final
result must state its actual dynamical objects, hypotheses, and remaining
gap. If the attempt produces no substantive new theorem, this draft will be
closed rather than submitted as a successful contribution.

The exponential scales themselves belong to classical real quadratic window
theory. The candidate new scope is the effective classification of the entire
physical interval class, quantitative secants across its actual return
maps, and the resulting globally quantified physical signed-tip theorem.
Periods `3` through `16` remain outside this global argument. Identification
with a separately defined maximal renormalization component is also outside
the formal statement. Qualitative kneading uniqueness has classical
precedents; a literature-wide novelty claim would require further evidence
and is not made.

## Attribution

The selected family, signed relation, prior local uniqueness, and quantitative
near-minus-two chart belong to the existing archive. The classical quadratic
dynamics literature will be checked before making any novelty claim.
