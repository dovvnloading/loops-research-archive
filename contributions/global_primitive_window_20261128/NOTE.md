---
ledger: NOV26_OPEN_WINDOW
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation, Lean proof development, and independent AI review
human_review: none
---

<a id="global-primitive-window-20261128"></a>

# Effective control of the complete positive restrictive window

Ledger statement being addressed:

> Global primitive-component uniqueness: Local p=3..12 seed intervals and signed p>=13 chart do not prove full maximal-real-component uniqueness (F02).

## Claim

**Kernel-validated partial result.** The complete weighted build and
transitive axiom audit passed on proof revision
`dd9edd968987f483b1c46e51a589449742a444e9` in
[the unchanged repository CI](https://github.com/dovvnloading/loops-research-archive/actions/runs/46124729184).
The final theorem and every supporting module compile without proof gaps
or new axioms.

Write `f_c(x)=x^2+c`, `x_j(c)=f_c^j(0)`, `d_c=x_p(c)`, and `q=4^(-p)`.
All statements below concern these literal quadratic iterates.

### Effective classification of the full physical class

For `p>=17`, let `C_p` be the class `PositiveRestrictiveReturn c p`:
`c` lies in `[-2,-1]`, `d_c>0`, the entire canonical interval `[-d_c,d_c]`
has a negative first image, all its images at times `2,...,p-1` are positive,
and its `p`-th image lies in itself. The new argument derives

```text
14*q < c+2 < 16*q,
0 < d_c < 14*q,
|c-a| < 160*q^2                 for c,a in C_p.
```

The parameter and return-scale cutoffs are conclusions. Moreover, the
whole class is exactly one half-open interval

```text
C_p = [c(D),c(0)),
8*q <= D <= (40/3)*q,
```

where `c(d)` is the unique positive-inverse shooting parameter and `D` is
the unique solution of an exact contracting endpoint equation. This
identifies every member of the physical class, including any hypothetical
disconnected pieces. The literal phase images are pairwise disjoint.

### Uniform comparison of actual return maps

Let `A_p(c)` be the coefficient of `z^2` in `f_c^p(z)`, set
`kappa_c=-A_p(c)*d_c`, and define

```text
F_c(z) = f_c^p(d_c*z)/d_c,
E_c(z) = F_c(z) - (1-kappa_c*z^2).
```

For every `c,a` in the full class and every `z,w` in `[-1,1]`,

```text
|E_c(z)-E_a(z)| <= 200*p*q*|kappa_c-kappa_a|,
|E_c(z)-E_c(w)| <= 300*p*q*|z-w|.
```

The proof also gives

```text
|c-a| <= 12*q*|d_c-d_a|,
(1/2)*4^(p-1)*|d_c-d_a| <= |kappa_c-kappa_a|.
```

These are comparisons across the entire actual physical family, with no
assumed narrow coefficient isolator and no assumed parameter derivative
bound. They are the effective estimate underlying the signed-root result.
Local parameter-error estimates are already present in the archive; the
additional scope here is the full physical class with its chart and scale
hypotheses derived from the dynamics.

### Global physical signed-tip uniqueness

`PhysicalSignedTip p c` quantifies over **every real parameter `c`** and
the existence of **an arbitrary positive radius `r`**. Its conditions are:

1. `f_c([-r,r])` is negative; every whole image at times `2,...,p-1` is
   positive; and `f_c^p([-r,r])` lies in `[-r,r]`.
2. The critical returns at multiples `p,2p,3p,4p,5p` have signs `+--+-`.
3. `x_(6p)(c)+x_(3p)(c)=0`.

There is no parameter chart, canonical-radius requirement, or coefficient
isolator in this predicate. The final Lean statement is

```lean
theorem exists_unique_physical_signed_tip (p : ℕ) (hp : 17 ≤ p) :
    ∃! c : ℝ, PhysicalSignedTip p c
```

The same module proves equivalence between this global physical predicate
and the archived `ActualTip p c`. Existing local existence is a dependency;
it is not presented as a new existence construction.

## Evidence

### Registered Lean statements

All 24 new modules and their 126 public theorems are registered in the
weighted Lean project and the physical bridge index. The principal entries
are:

| Source | Principal statement |
|---|---|
| `GlobalWindowBoundary.lean` | `complete_restrictive_window` |
| `GlobalWindowInverseShape.lean` | `kappa_strong_secant`, `inverseRatio_lipschitz` |
| `GlobalWindowParameterSecant.lean` | `parameter_error_lipschitz`, `spatial_error_lipschitz` |
| `GlobalWindowRootFactor.lean` | `actualFactor_eq_two`, `signed_root_model_error` |
| `GlobalWindowRootLocalization.lean` | `signed_root_coarse_interval` |
| `GlobalPrimitiveIntervalRecognition.lean` | `recognize_canonical_return` |
| `GlobalPrimitiveTipUniqueness.lean` | `exists_unique_physical_signed_tip`, `physical_signed_tip_iff_actual_tip` |

Validation is through the repository's unchanged weighted workflow,
including its successful full build (9,260 build jobs) and transitive audit
of all 7,695 declarations across 292 weighted modules. The audit permits
only `propext`, `Classical.choice`, and `Quot.sound`. The source-coverage and
proof-escape checks pass for all 341 registered Lean files. Research
validation, the core Lean audit, and the standalone Lean audits also passed.
The local installation has
the pinned Lean 4.32.0 core but not the complete weighted dependency cache;
weighted compilation is performed in CI.

### Mathematical argument

**1. Recognize the physical interval before choosing a chart.**
Starting with any positive-radius symmetric invariant interval and the full
branch itinerary, the first two critical images force `c<-1`. If `c<-2`,
the critical orbit escapes the range compatible with the negative first
image of the invariant interval. Thus `c` lies in `[-2,-1]`. The return map
reverses order in the square of the input. If its positive critical endpoint
were sent below the negative critical endpoint, the following returns would
remain negative. The positive fourth return rules this out and forces
invariance of the canonical interval `[-d_c,d_c]`.

**2. Derive the small scales globally.**
The positive inverse branch `B_c(x)=sqrt(x-c)` gives a globally decreasing
shooting function on `[-2,-1]`; its certified right endpoint forces
`c+2<20*q`. For the actual endpoint image `e=f_c^p(d_c)`, reversing every
physical phase gives the exact identity

```text
d_c^2 = B_c^(p-1)(d_c) - B_c^(p-1)(e),    e in [-d_c,d_c].
```

A first inverse-step contraction of `3/4` and subsequent contractions of
`1/3` give the preliminary bound `d_c <= (27/2)*3^(-p)`. This makes the
loss in the complete normalized inverse product less than `1/400`.
Combining it with the archived zero-target bound `241/400` leaves a strict
`3/5` lower bound at the actual negative endpoint. The exact inverse
secant product then forces `d_c*4^p<40/3<14`. Shooting comparison gives
the sharper parameter enclosure `14*q<c+2<16*q`.

**3. Classify the whole positive-return class.**
For `0<=d<=14*q`, let `c(d)` be the unique shooting parameter and define

```text
P(d) = product_(j=1,...,p-1) (B_{c(d)}^j(d)+B_{c(d)}^j(-d))/4,
L(d) = 8*q/P(d).
```

Here `B_{c(d)}` denotes the inverse branch at parameter `c(d)`.
The entire endpoint invariance condition is exactly `d<=L(d)`.
The product lies in `[3/5,1]`, and a telescoping product estimate together
with `|c(d)-c(e)|<=12*q*|d-e|` gives Lipschitz constant at most `1/2` for
`L`. Its unique fixed point `D` separates all admissible terminal values:
the complete domain is `(0,D]`. Continuity and strict antitonicity of
`c(d)` give precisely `[c(D),c(0))`. The converse reconstructs all physical
intermediate interval images; the scalar endpoint condition is not used
without that converse.

**4. Control variation of the complete return error.**
Retain the inverse product as a function of its normalized target:

```text
P_c(y) = product_(j=1,...,p-1) (B_c^j(d_c)+B_c^j(d_c*y))/4.
```

Exact inverse identities yield

```text
kappa_c = d_c*4^(p-1)*P_c(1),
F_c(z) = 1-kappa_c*z^2*P_c(F_c(z))/P_c(1).
```

Comparing this product in the parameter, terminal value, and target gives
the strong coefficient secant and the two `200*p*q` and `300*p*q` error
bounds. A small multiple of the unknown return-map difference is absorbed
using the explicit horizon estimate for `p>=17`. Propagating these
differences through six actual returns bounds the signed-error variation
by `110000000*p*q*|Delta kappa|`, with `110000000*p*q<1`.

**5. Exclude every signed root outside the isolator.**
The second and fourth return signs first give `0<kappa_c<2`.
The complete normalized return error is at most `22*q`; the corresponding
even-secant error is at most `43*q`. At a signed root, the exact
threefold even-secant identity permits cancellation of the nonzero third
return and gives `actualFactor=2`. The proof does not divide an
approximation error by a potentially tiny third return.

The model factor is

```text
M(k) = k^3*(-Q_k^3(0))*(1+Q_k^4(0))*(-(Q_k^2(0)+Q_k^5(0))),
Q_k(z) = 1-k*z^2.
```

The error in this factor is at most `50000*q` on the full signed physical
class. Exact rational inequalities and the return signs first exclude
the complement of `[1.785,1.795]`. A certified positive slope for `M`
and endpoint gaps then force every root into `(1.7903,1.7904)`.
All finite rational estimates are proved inside Lean.

**6. Conclude actual uniqueness and existence.**
On the derived narrow interval, the archived model signed relation has
secants greater than six. The new parameter-error bound therefore gives
actual signed-relation secants greater than five. Two physical roots
must have the same coefficient; the strong coefficient comparison and
shooting comparison force the parameters to coincide. The archived
`ActualTip` existence theorem supplies a parameter, and separate new
physical-geometry and return-sign estimates verify the unrestricted
physical predicate. This dependence is acyclic.

## Dependencies

- `NOV26_OPEN_WINDOW` and `NOV26_TIP_THEOREM` in `ledger.json`.
- `research/tip_family_theorem/AUDIT.md`, finding F02, and
  `research/tip_family_theorem/THEOREM.md`, parameter-chart convention.
- `research/independent_audits/real_primitive_tip_family_all_p_20261116/NOTE.md`:
  the already archived local signed-tip result and local parameter-error
  estimates. Its section II gives `|e_tau|<88*q`, a spatial derivative bound
  `256*q`, and a parameter derivative bound `30000*q^2` in its assumed
  chart. The present contribution is not a claim to have first obtained
  small local parameter-error estimates.
- `NearTwoInverse.lean`, `NearTwoProduct.lean`, `NearTwoShooting.lean`,
  `NearTwoTip.lean`, `LimitingCrestQuadraticReturn.lean`, and
  `LimitingCrestParameter.lean` in the weighted Lean project.

## Boundary

This is a **partial** contribution to `NOV26_OPEN_WINDOW`. The ledger is
unchanged. Periods `3` through `16` remain outside the global argument.

The classified half-open interval is the positive-critical-return
physical class. It excludes its period-`p` center and includes its
endpoint-invariance boundary. It is not identified here with an entire
customary primitive window or a hyperbolic component.

The remaining component-level obligation is precise: define the source's
intended maximal primitive parameter set independently, then prove that
every signed candidate in that set admits the symmetric invariant interval
with the full branch itinerary used here. That containment would allow the
global physical uniqueness theorem to apply. Identifying the whole
positive part of the component additionally requires the converse and
maximality. Renaming the present physical class as that component would
not prove the missing identification. No MLC conclusion follows.

Qualitative postcritical kneading uniqueness is classical. The contribution
claimed here is the effective control across the complete physical family,
including the derived cutoffs, contracting boundary equation, parameter
error secants with globally verified hypotheses, and uniform factored-root
exclusion. The order of small local return-map errors and their parameter
derivatives is not claimed as new. A Lean proof certifies
these statements, not their worldwide priority; no literature-wide first
claim is made.

## Attribution

The selected family, signed relation, local existence, local model slope,
and near-minus-two chart belong to the existing archive. The following
primary references delimit the novelty claim; they are not imported as
unproved Lean assumptions:

- John Milnor and Charles Tresser, *On Entropy and Monotonicity for Real
  Cubic Maps*, revised 1999, section 8, p. 42, and Appendix B, Theorem B.3,
  [arXiv:math/9809096](https://arxiv.org/abs/math/9809096): qualitative
  uniqueness of postcritically finite real polynomials from kneading data,
  up to positive affine conjugacy.
- Genadi Levin, Weixiao Shen, and Sebastian van Strien, *Positive
  Transversality via transfer operators and holomorphic motions with
  applications to monotonicity for interval maps*, Nonlinearity 33 (2020),
  3970-4012, [arXiv:1902.06732](https://arxiv.org/abs/1902.06732): positive
  transversality, including applications to the real quadratic family.
- Brian R. Hunt, Jason A. C. Gallas, Celso Grebogi, James A. Yorke, and
  Huseyin Kocak, *Bifurcation rigidity*, Physica D 129 (1999), 35-56,
  section 3, Lemma 1,
  [author's page](https://user.eng.umd.edu/~bhunt/papers/bifr/): quantitative
  local approximation by quadratic return families, including control in
  both spatial and parameter variables. Such local approximation and the
  classical window-scaling exponents are not claimed as discoveries here.

Mathematical investigation, proof development, and independent internal
reviews were performed by AI agents. No human review has occurred.
