---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro; proof development and independent AI scope review
human_review: none
---

<a id="actual-crest-foliation-20261126"></a>

# All-period actual crossing curves and uniform limits

## Claim

For every integer p >= 17, this packet constructs an actual real quadratic
parameter and a coherent continuous curve of imaginary-axis crossings of
its p-th return. The crossing is unique on each entire upper semicircle,
the curve is injective, and the normalized curves converge uniformly to
one explicitly specified limiting quadratic curve. Every assertion below
is a theorem in the repository's pinned Lean 4.32.0 project.

This is a **partial** contribution to NOV26_OPEN_CREST_LIMIT. It removes
the raw real-parameter hypotheses from the archived conditional crossing
theorem and replaces separate existential crossing points with actual
unique, continuously selected curves and quantitative limits. It does
not establish the full marked circular-leaf transport or width limit
required to close the ledger row.

Write

```text
f_c(z) = z^2 + c,       q_p = 4^(-p),
d_p = f_c^p(0),         a_p = the coefficient of z^2 in f_c^p,
kappa_p = -a_p*d_p,     H_p(z) = f_c^p(d_p*z)/d_p,
Q_k(z) = 1-k*z^2,       S = [63/1000, 33/500].
```

### Actual parameters and one common limit

For every p >= 17 the construction supplies c_p satisfying

```text
-2 <= c_p <= -2 + 20*q_p,
0 < d_p <= 12*q_p,
1.7903 <= kappa_p <= 1.7904,
f_c_p^(6*p)(0) + f_c_p^(3*p)(0) = 0,
f_c_p^(3*p)(0) < 0.
```

There is one kappa_infinity in [1.7903,1.7904], the unique root in that
interval of Q_k^6(0)+Q_k^3(0)=0. The actual parameters satisfy

```text
|kappa_p-kappa_infinity| <= 15748*q_p,
|H_p(z)-Q_kappa_infinity(z)| <= 23646*q_p   for every |z| <= 23/20.
```

The internal name `ActualTip` abbreviates exactly the signed-return,
parameter, scale, and coefficient conditions in its definition. It is
not an additional assertion of component identification or minimal period.

### Unique crossings and actual curves

Let

```text
circlePoint(s,u) = -3/4 + s*(u + i*sqrt(1-u^2)).
```

For every s in S, there is exactly one u in [-1,1] for which
Re H_p(circlePoint(s,u))=0. This unique crossing satisfies
-1/100 < u < 1/100. The selected function u_p:S -> R is Lipschitz with
constant 100. The normalized curve

```text
gamma_p(s) = circlePoint(s,u_p(s))
```

is continuous, injective, and Lipschitz with constant 15. The proof
retains the positive imaginary first image, real second and third images,
and the strict third-image corridor along the entire curve.

The end-to-end theorem
`ActualCrestTransport.exists_actual_unscaled_crest_curve` assumes only
p >= 17. It constructs the same actual parameter and a single continuous,
injective curve Gamma_p in the original dynamical plane, with

```text
|Gamma_p(s) + 3*d_p/4| = d_p*s,
Re f_c_p^p(Gamma_p(s)) = 0,
Im f_c_p^p(Gamma_p(s)) > 0,
Im f_c_p^(2*p)(Gamma_p(s)) = 0,
Im f_c_p^(3*p)(Gamma_p(s)) = 0,
-d_p < Re f_c_p^(3*p)(Gamma_p(s)) < -f_c_p^(4*p)(0).
```

It also proves
|Gamma_p(s)-Gamma_p(t)| <= 15*d_p*|s-t|.
These are literal polynomial iterates, not a surrogate map or a
postulated geometric realization.

### Quantitative and formal uniform convergence

Let u_infinity(s) be the archived limiting-model angular formula at the
single constructed kappa_infinity, and set
gamma_infinity(s)=circlePoint(s,u_infinity(s)). Uniformly for every s in S,

```text
|u_p(s)-u_infinity(s)| <= 236460*q_p,
|gamma_p(s)-gamma_infinity(s)| <= 32000*q_p.
```

`ActualCrestLimit.exists_uniformly_converging_actual_crests` chooses actual
sequences with p=n+17 and proves, using Lean's filter and uniform-convergence
predicates:

- c_n tends to -2;
- kappa_n tends to kappa_infinity;
- the normalized returns converge uniformly on the whole disk |z|<=23/20;
- the angular selections converge uniformly on S;
- the normalized selected circle-point curves converge uniformly on S.

## Evidence

### The new two-point estimate

The analytic step missing from a pointwise approximation is control of
differences at two arbitrary complex points. The exact recursively defined
even divided difference D_p satisfies

```text
H_p(z)-H_p(w) = (z^2-w^2)*D_p(z,w),
|D_p(z,w)-a_p*d_p| <= 36*q_p
```

on the entire disk |z|,|w|<=23/20. Every higher-degree term of the actual
iterate is retained. Under the sharp coefficient bounds, this gives

```text
1 < |D_p(z,w)| < 2,
H_p(z)=H_p(w)  iff  z=w or z=-w,
|H_p(z)-H_p(w)| <= 5*|z-w|.
```

If additionally Re z, Re w <= -5/8, then
|z-w| <= |H_p(z)-H_p(w)|. Thus the return has a controlled inverse
on the negative half disk containing the parent circles. This is an
exact collision statement on a complete complex domain.

For the crossing coordinate, the residual divided difference is at most
one thousandth times |z^2-w^2|. Combining it with the limiting quadratic's
angular growth yields actual angular growth at least (v-u)/20 on
[-1/100,1/100]. The model's signed wall margins and the actual uniform map
error exclude all roots outside that interval on the upper semicircle.
Radial Lipschitz control then gives the constants 100 and 15.

### Construction of the parameters

The positive inverse branch B_c(x)=sqrt(x-c) turns parameter selection into

```text
c^2+c = B_c^(p-2)(d).
```

Rational all-depth deficit estimates at c=-2, parameter Lipschitz bounds,
and strict monotonicity of this shooting expression supply an actual
nonempty parameter interval for d between 0 and 12*q_p. A telescoping
inverse-product estimate gives normalized product at least 241/400 and
the needed coefficient lower bound. The sharp kappa corridor is then
constructed by the intermediate value theorem.

For the six-plus-three normalized critical relation, the complete
iteration error is at most 94488*q_p. The two limiting endpoint margins
are strictly greater than 1/10000 in magnitude, with opposite signs.
For p>=17 the actual error preserves these signs, so a second
intermediate-value argument supplies the exact signed critical relation.
The limiting relation has derivative greater than six throughout the
parameter interval, giving the inverse estimate 15748*q_p for kappa.
The map and curve limits follow from this estimate and the two-point
crossing control.

### Lean modules

| Module | Principal role |
|---|---|
| `NearTwoInverse.lean` | Actual positive inverse orbit, rational deficit bounds, parameter dependence |
| `NearTwoProduct.lean` | Uniform inverse-product and coefficient lower bounds |
| `NearTwoShooting.lean` | Constructed real shooting interval and sharp coefficient chart |
| `CriticalReturnRelationStability.lean` | Six-plus-three error, exact scaling, endpoint signs |
| `NearTwoTip.lean` | Actual signed-return parameters and coefficient convergence |
| `QuadraticCrestDividedDifference.lean` | Complete two-point bounds, exact collisions, distance estimates |
| `QuadraticCrestCrossing.lean` | Full-upper-semicircle uniqueness and Lipschitz selected curves |
| `ActualCrestLimit.lean` | Explicit rates and actual uniform-convergence theorems |
| `ActualCrestTransport.lean` | One coherent curve for literal original-plane polynomial iterates |

All nine files are under `formalization/weighted/`. Every public theorem
is registered through `code/contribute.py lean-add` in the existing
default build and theorem/source index.

### Validation

Every new module compiled locally with the pinned Lean 4.32.0 and Mathlib,
without warnings. Local transitive axiom checks of the main construction,
collision, crossing, and convergence theorems use only
`propext`, `Classical.choice`, and `Quot.sound`.

The repository's unmodified CI builds the complete weighted project and
audits the transitive axioms of **every declaration**, including private
helpers. The final head-specific CI record belongs in the pull request
description. Reproduction:

```sh
cd formalization/weighted
lake exe cache get
lake build ActualCrestTransport ActualCrestLimit
cd ../..
python -B code/verify_lean_coverage.py --audit weighted
python -B code/contribute.py check
```

There are no proof holes, custom axioms, native evaluation shortcuts, or
changes weakening the validation rules.

## Dependencies

This contribution addresses NOV26_OPEN_CREST_LIMIT and builds on
NOV26_CREST_16, the November crest asymptotics audit, and the merged
`limiting_crest_gate_20261126` packet from PR #233. Its formal dependencies
are the existing LimitingCrest modules, the elementary interval-crossing
lemma in `ParabolicShooting.lean`, core Lean, and the pinned Mathlib.

No imported Douady-Hubbard, KKL, prime-end, or extremal-width statement is
introduced as a new axiom or as an assumption of the final actual-curve
existence and uniform-convergence theorems.

## Boundary

**NOV26_OPEN_CREST_LIMIT remains open. No ledger status change is requested.**

The precise remaining issues are:

1. Identification with the archive's designated primitive-component
   parameter, and its exact minimal critical preperiod/renormalization
   period, are not proved here. The actual signed relation and all
   quantitative conditions used in this packet are proved.
2. The radius interval S=[.063,.066] is a fixed interior interval. The full
   parent begins at 1/16=.0625, and its limiting maximal terminal endpoint
   is near .0663789. This packet does not construct the actual maximal
   collar endpoint or prove its convergence.
3. A radius-indexed curve of crossing points is not the complete family
   of circular leaves. This packet does not prove full four-stage marked
   proper-path survival, KKL membership, prime-end identification, or
   properness onto an identified marked target.
4. No candidate integral is identified with physical extremal width here.
   Neither the full circular-collar width ratio nor its proposed limit
   near .347005 is proved.

The actual all-period analytic curves and their uniform limits are the
new result. They are not a proof of H1-H4, a universal Wave-transport
theorem, or MLC.

## Attribution

The November all-period tip note already contains written/coarsely
certified all-period parameter existence, coefficient bounds, a complete
complex remainder, and a Rouche construction. Reproducing those results
alone would not advance this research. The inverse shooting and product
lemmas here are supporting formal infrastructure.

The new contribution relative to the archived frontier is the complete
actual two-point control, unique coherent actual crossing curves for
every p>=17, and their quantitative/formal uniform limits to one fixed
model. It extends PR #233's conditional pointwise crossing theorem.
No priority claim is made beyond this archive.

Proof development and scope review are AI-assisted. Independent AI review
checked constants, period indices, nonvacuity, parameter construction,
and the distinction between crossings and marked width. No independent
human review has occurred. Released under the repository's CC0 terms.
