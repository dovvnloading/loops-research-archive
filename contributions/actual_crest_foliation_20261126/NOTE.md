---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="actual-crest-foliation-20261126"></a>

# Actual quadratic-return crest foliation

## Claim

Work in progress. This packet targets the missing passage from the
archive's pointwise perturbed crossing to a unique, continuously selected
crest curve for literal quadratic return maps. A second target is a sharp
all-period coefficient window for the designated near-minus-two family.
No new mathematical result is claimed before its Lean proof compiles.

## Evidence

### Locally verified checkpoint: inverse-orbit estimates

`formalization/weighted/NearTwoInverse.lean` compiles with the repository's
pinned Lean 4.32.0 and Mathlib. Its 14 public theorems establish the exact
positive-square-root inverse orbit, interval preservation, a uniform
parameter Lipschitz estimate, monotonicity, continuity, and rational
all-depth bounds for the inverse-orbit deficit at c=-2. This is supporting
infrastructure for the new actual-parameter construction, not a claim that
the crest obligation is closed. The source is registered in the default
weighted build and declaration index; CI will recheck it modularly and
audit every declaration's transitive foundational dependencies.

Local command (the runner selects the pinned compiler and existing cache):

```sh
lean-check NearTwoInverse.lean
```

The source SHA-256 at this checkpoint is
`288f279c6a091d9a8b8dbdb654a04c5d95347ac43ee76fe6a57f2fd0fd4bffcd`.

### Locally verified checkpoint: all complex two-point differences

`QuadraticCrestDividedDifference.lean` adds ten public theorems and
compiles locally without warnings. Write d=f_c^p(0), let a be the
quadratic coefficient of f_c^p, and set H(z)=f_c^p(dz)/d. For p>=13,
c in [-2,0], and 0<d<=12*4^(-p), the exact even divided difference D
satisfies, for every z,w in |z|,|w|<=23/20,

    H(z)-H(w) = (z^2-w^2) D(z,w),
    |D(z,w)-a*d| <= 36*4^(-p).

When -a*d lies in [1.7903,1.7904], this proves all of the following
for the actual polynomial return on the whole disk:

1. H(z)=H(w) if and only if z=w or z=-w.
2. |H(z)-H(w)|<=5|z-w|.
3. If Re(z),Re(w)<=-5/8, then |z-w|<=|H(z)-H(w)|.

The third estimate gives injectivity with a controlled inverse on the
entire negative half disk containing the parent crest circles. These
are two-point conclusions; the previous C0 remainder estimate alone
did not prove them. The proof uses a polynomial recurrence for the
complete divided difference and retains every higher-degree term.
The stated real parameter and coefficient hypotheses remain explicit
until the parameter-selection module is completed.

### Locally verified checkpoint: actual parameter charts and crossing curves

The following additional modules now compile locally without warnings:

- `NearTwoProduct.lean` proves a period-independent lower bound on the
  inverse-orbit product. The normalized product is at least 241/400.
- `NearTwoShooting.lean` constructs the actual near-minus-two parameter
  chart for every p>=17. It proves the positive return-scale bounds and
  a complete parameter interval whose normalized coefficient crosses
  both walls 1.7903 and 1.7904. These are conclusions about actual
  polynomial iterates, not assumed input data.
- `CriticalReturnRelationStability.lean` controls the six-plus-three
  normalized critical relation by 94488*4^(-p) and proves opposite
  signs at those two sharp coefficient walls. It also excludes the
  zero third-return factor.
- `QuadraticCrestCrossing.lean` proves strict angular growth for the
  actual return, uniqueness of the crossing on the entire upper
  semicircle, a Lipschitz-100 angular function, and a Lipschitz-15,
  injective continuous complex crossing curve. Every point on this
  curve satisfies the previous positive-imaginary and real terminal
  corridor gates. Its radius ranges over the whole interval [.063,.066].

- `NearTwoTip.lean` now constructs, for every p>=17, an actual parameter
  c in [-2,-2+20*4^(-p)] satisfying the signed relation
  f_c^(6p)(0)+f_c^(3p)(0)=0, with f_c^(3p)(0)<0, positive small p-return,
  and the sharp coefficient band. It also proves
  |kappa_p-kappa_infinity|<=15748*4^(-p), where kappa_infinity is the
  unique constructed limiting-model root. The all-period unscaled
  corridor theorem consequently has no assumed real-chart premises.

The internal predicate `ActualTip` means precisely these signed-return
and quantitative conditions. It does not encode a primitive-component
classification or an exact minimal-period theorem. The final curve-limit
and original-plane curve assembly are still being checked.

### Development target

The starting point is `LimitingCrestQuadraticReturn.lean`, merged in PR
#233. It proves a complete complex remainder bound and one crossing at
each radius, conditional on explicit real return-scale and coefficient
inequalities. It does not prove crossing uniqueness, a continuous angular
selection, or an embedded transported arc family for the actual return.

The intended new proof will control the complete derivative or divided
difference of the actual return, retain every higher-degree term, and
derive injectivity and angular order on a fixed complex domain. It will
then construct the crossing family and state its exact relationship to
the original polynomial iterates. Every completed theorem and validation
checkpoint will be committed to this packet and its registered Lean
modules.

## Dependencies

NOV26_CREST_16 and the merged `limiting_crest_gate_20261126` packet supply
the existing frontier and source context. The proof will build on the
repository's actual quadratic-return definitions and Mathlib. The older
all-period coarse real chart is archived; reproducing it alone will not
be counted as the new contribution.

## Boundary

NOV26_OPEN_CREST_LIMIT remains open during development. Uniqueness and
continuity of a crossing family do not by themselves identify physical
KKL markings, prove an extremal-width formula, or settle convergence of
canonical widths. Each remaining hypothesis will be stated explicitly.
No ledger status change is requested at this stage.

## Attribution

This work builds on the November crest audits and PR #233's exact
limiting-model and literal-return estimates. Proof development and
review are AI-assisted; no independent human review has occurred. CC0.
