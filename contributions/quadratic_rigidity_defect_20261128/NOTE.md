---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-rigidity-defect-20261128"></a>

# Critical-orbit projective curvature at matched multipliers

## Claim

For every fixed return clock $k\geq3$, the ordered critical-return
quadruples of the fixed-point and period-two quadratic charts are
projectively inequivalent in a punctured neighborhood of their centers
when their true multipliers agree: the difference of their cross-ratios
has exact quadratic multiplier coefficient $1/128$.

The main result is an algebraic separation factorization. It compares two
actual quadratic critical-orbit configurations, removes their identical
multiplier poles and first two finite terms, and leaves the square of the
multiplier times a rational expression whose value at the center is
exactly $1/128$. The identities hold for every $k\geq3$, with explicit
nonvanishing hypotheses on their displayed denominators. The polynomial
remainders are supplied by Lean, rather than inferred from numerical fits.

**Source-completion validation: locally compiled and dependency-audited.**
All eleven modules described below have compiled in the repository's
Lean project with its pinned Lean 4.32.0 toolchain and pinned Mathlib. Their
dependency audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The authoritative remote gate is **Weighted spectral mathlib
proofs / mathlib-kernel-check** on this PR; its build and exhaustive
dependency audit determine CI acceptance.

## The archive's exact remaining hypothesis

The terminal written reduction is `UPTCR_IMPLIES_MLC`, Theorem 7.2 of
[mlc_closure_proposition.md](../../research/mlc_unified/mlc_closure_proposition.md#theorem-72--uptcr-implies-mlc).
Its open hypothesis is **`UNIVERSAL_PROTECTED_TOWER_CLOSURE`**, the
Universal Protected-Tower Compactness and Rigidity proposition, abbreviated
UPTCR. Section 5 requires one set of universal constants and all six clauses
for every infinitely renormalizable quadratic: canonical construction,
exact analytic realization, a uniform finite response state, a backward
transition, coercive compactness, and tower rigidity with the parameter
fiber conclusion.

In particular, UPTCR-6 requires uniformly quasiconformal finite-depth
pullbacks, an appropriate limiting conjugacy and no invariant line field,
and compact connected relative parameter neighborhoods whose intersection
is the full marked combinatorial fiber. It requires that fiber to be a
singleton. The reduction then derives shrinking neighborhoods and local
connectivity; it does not independently prove those UPTCR-6 premises.
The distinction is explicit in
[the proposition's status and six clauses](../../research/mlc_unified/mlc_closure_proposition.md#5-universal-protected-tower-compactness-and-rigidity-proposition)
and its [clause-to-ledger crosswalk](../../research/mlc_unified/mlc_closure_proposition.md#6-clause-to-ledger-crosswalk).

The theorems in this packet assume none of those tower hypotheses. They
study finite critical-orbit configurations directly. No UPTCR clause or
ledger status is promoted by this contribution.

## Actual quadratic objects and the exact statements

Let

\[
f_c(z)=z^2+c,\qquad P_0(c)=0,\qquad P_{n+1}(c)=P_n(c)^2+c.
\]

The observable is the ordered cross-ratio

\[
R_n(c)=
\frac{P_{3n}(c)\bigl(P_n(c)-P_{2n}(c)\bigr)}
     {P_n(c)\bigl(P_{3n}(c)-P_{2n}(c)\bigr)}.
\tag{1}
\]

Its four marks are $0,P_n(c),P_{2n}(c),P_{3n}(c)$. In Lean they are
`criticalOrbit`, `crossRatio`, and `criticalClock`; the actual iterate
identity is `criticalOrbit_eq_iterate`. The equations below are stated on
the displayed nondegenerate domain, rather than relying on Lean's
totalized division at a zero denominator.

Use the two exact parameter charts

\[
c_1(q)=\frac q2-\frac{q^2}{4},\qquad
c_2(t)=-1-t-t^2,\qquad \mu(t)=-4t(1+t).
\tag{2}
\]

The first map fixes $q/2$, with multiplier $q$. The second has the
two-cycle $t\mapsto-1-t\mapsto t$, with multiplier $\mu(t)$. The points
of this cycle are distinct when $t\ne-1/2$. These facts are proved by
`main_fixed_point`, `main_multiplier`, `periodTwo_first_step`,
`periodTwo_second_step`, `periodTwo_cycle_distinct`, and
`periodTwo_multiplier_product` in
[QuadraticProjectiveActual.lean](../../formalization/weighted/QuadraticProjectiveActual.lean).

Put

\[
e(t)=-\frac1{8(1+t)^3},\qquad
D_{e,k}(q)=\operatorname{eval}_q(\texttt{denPoly}\ e\ k).
\]

The denominator polynomial is defined explicitly in the proof below. Its
constant term is always $-1/4$ for $k\geq1$.

### The fixed-point chart

For every integer $k\geq3$, there is a polynomial $U_k\in\mathbb C[q]$
such that, for every $q\ne0$ with $D_{0,k}(q)\ne0$,

\[
R_k(c_1(q))+q^{-k}+\frac34+\frac q{16}
=q^3\frac{U_k(q)}{D_{0,k}(q)},
\qquad D_{0,k}(0)=-\frac14.
\tag{3}
\]

This is exactly `criticalClock_main_cubic_remainder` in
[QuadraticProjectiveRigidity.lean](../../formalization/weighted/QuadraticProjectiveRigidity.lean).
In particular, the coefficient of $q^2$ in the regular part is zero.
The stronger exact identity (3), including its polynomial remainder and
denominator value, is what the algebraic theorem proves.

### The period-two chart

For every integer $k\geq3$, there is one polynomial

\[
Q_k\in(\mathbb C[e])[q]
\]

such that, for every $t\ne0,-1$ with

\[
D_2(t):=D_{e(t),k}(\mu(t))\ne0,
\]

one has

\[
\begin{aligned}
R_{2k}(c_2(t))+\mu(t)^{-k}+\frac34+\frac{\mu(t)}{16}
  -\frac{\mu(t)^2}{128}
={}&\mu(t)^3\left(
  \frac{Q_k(e(t),\mu(t))}{D_2(t)}
  +\frac{3+3t+t^2}{512(1+t)^4}\right),\\
D_2(0)={}&-\frac14.
\end{aligned}
\tag{4}
\]

This is `criticalClock_periodTwo_center_jet` in
[QuadraticProjectiveRigidity.lean](../../formalization/weighted/QuadraticProjectiveRigidity.lean).
The intermediate theorem `criticalClock_periodTwo_cubic_remainder` keeps
the exact varying coefficient $1/(128(1+t)^3)$ instead of its center value
$1/128$. The explicit identity

\[
\frac{\mu(t)^2}{128(1+t)^3}-\frac{\mu(t)^2}{128}
=\mu(t)^3\frac{3+3t+t^2}{512(1+t)^4}
\tag{5}
\]

is `periodTwo_curvature_center_correction`. It explains exactly why
replacing the varying coefficient by its center value changes only the
cubic remainder.

### Algebraic separation at matched multipliers

Evaluate the first chart at $q=\mu(t)$. Equations (3) and (4) give

\[
R_{2k}(c_2(t))-R_k(c_1(\mu(t)))
=\mu(t)^2 S_k(t),
\tag{6}
\]

where

\[
\begin{aligned}
S_k(t)=\frac1{128}+\mu(t)\biggl(&
 \frac{Q_k(e(t),\mu(t))}{D_2(t)}
 +\frac{3+3t+t^2}{512(1+t)^4}\\
 &-\frac{U_k(\mu(t))}{D_{0,k}(\mu(t))}\biggr).
\end{aligned}
\tag{7}
\]

The domain of (6) is $t\ne0,-1$ together with nonvanishing of both
displayed $D$ denominators. The theorem
`criticalClock_separation_factor` supplies the two polynomials and this
exact equation. `criticalClock_separation_unit` uses the named expression
`separationUnit`, and `separationUnit_zero` proves

\[
S_k(0)=\frac1{128}.
\tag{8}
\]

All three are locally compiled in
[QuadraticProjectiveSeparation.lean](../../formalization/weighted/QuadraticProjectiveSeparation.lean).
Equations (6)–(8) are the principal algebraic separation statement. They
exhibit the first surviving projective difference after matching the true
multiplier and canceling the common singular and finite terms.

### The formal local obstruction

The rational function $S_k$ in (7) is continuous at the center, and all
denominator conditions in (6) hold in a neighborhood of the center. The
locally compiled theorem `criticalClock_separation_coefficient` in
[QuadraticProjectiveLimits.lean](../../formalization/weighted/QuadraticProjectiveLimits.lean)
proves the exact coefficient extraction

\[
\lim_{\substack{t\to0\\t\ne0}}
\frac{R_{2k}(c_2(t))-R_k(c_1(\mu(t)))}{\mu(t)^2}
=\frac1{128}.
\tag{8a}
\]

The theorem `criticalClock_eventually_separated` proves that there is a
neighborhood of zero in which every nonzero $t$ gives unequal cross-ratios.
The neighborhood is allowed to depend on $k$.

The final theorem
`criticalClock_eventually_not_projectiveEquivalent` in
[QuadraticProjectiveEquivalence.lean](../../formalization/weighted/QuadraticProjectiveEquivalence.lean)
states that, in such a punctured neighborhood, no nondegenerate fractional
linear map identifies the two actual ordered quadruples:

\[
\begin{aligned}
&(0,P_k(c_1(\mu(t))),P_{2k}(c_1(\mu(t))),P_{3k}(c_1(\mu(t))))\\
&\hspace{3em}\longmapsto
(0,P_{2k}(c_2(t)),P_{4k}(c_2(t)),P_{6k}(c_2(t))).
\end{aligned}
\tag{8b}
\]

Here `NondegenerateProjectiveEquivalent c n d m` is an explicit predicate:
there are complex coefficients $A,B,C,D$ with $AD-BC\ne0$, the four source
denominators of $T(z)=(Az+B)/(Cz+D)$ are nonzero, and $T$ sends all four
source marks to the four target marks in the displayed order. The theorem
requires no additional source-distinctness hypothesis. Its Lean statement
is

```lean
theorem criticalClock_eventually_not_projectiveEquivalent
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ t : ℂ in 𝓝 0, t ≠ 0 →
      ¬ NondegenerateProjectiveEquivalent
        (mainParameter (periodTwoMultiplier t)) k
        (periodTwoParameter t) (2 * k)
```

This consequence uses classical cross-ratio invariance, proved explicitly
in the companion algebra. The coefficient limit reads the finite
factorization (6); it invokes no limiting dynamical space or compactness
hypothesis.

## Evidence

The proof is a finite polynomial calculation, followed by actual-family
specialization and the continuity of the displayed rational remainder.

### Normalization retains the critical anchor

The normalized recurrence is

\[
y_0=-\frac12,\qquad
y_{n+1}=q(y_n+y_n^2)+e q^3(y_n+y_n^2)^2.
\tag{9}
\]

The critical point $y_0=-1/2$ remains a marked entry. The actual-family
identifications, proved for every iterate, are

\[
\begin{aligned}
P_n(c_1(q))&=q\left(\frac12+y_n\right)\quad(e=0),\\
P_{2n}(c_2(t))&=t(1+2y_n)
  \quad(q=\mu(t),\ e=e(t),\ t\ne-1).
\end{aligned}
\tag{10}
\]

They are `criticalOrbit_main` and `criticalOrbit_periodTwo`. The second
uses the complete quartic return polynomial, through
`periodTwo_normalized_return`; it is not a quadratic approximation to that
return.

Write $y_n=q^n a_n(e,q)$. The polynomial recurrence is

\[
\begin{aligned}
a_0&=-\frac12,\\
a_{n+1}&=a_n+q^n I_n,\\
I_n&=a_n^2\left(1+e q^2(1+q^na_n)^2\right).
\end{aligned}
\tag{11}
\]

For the divided tail

\[
H_{m,k}=\sum_{j=0}^{k-1}q^j I_{m+j},
\]

the exact identity is $a_{m+k}=a_m+q^mH_{m,k}$. This is the finite
telescoping identity `a_add`; it uses no mapping-telescope construction.

### Stabilized polynomial jets

In [QuadraticProjectiveTail.lean](../../formalization/weighted/QuadraticProjectiveTail.lean),
`JetEq p r` means the exact divisibility $q^3\mid p-r$. For every
$k\geq3$, `a_jet` and `H_jet` prove

\[
\begin{aligned}
a_k&\equiv-\frac14+\frac q{16}+\frac{1+e}{16}q^2\pmod{q^3},\\
H_{k,k}&\equiv\frac1{16}+\frac q{32}
                 +\frac{1+8e}{256}q^2\pmod{q^3}.
\end{aligned}
\tag{12}
\]

The first few iterates determine these coefficients. Subsequent increments
contain the already-extracted factor $q^n$, so the coefficients through
degree two stabilize. The divided tail still contributes nonzero terms;
discarding it would give the wrong projective residue.

### Removing the pole without discarding the nonlinear term

Set $s=q^k$, $A=a_k$, $B=a_{2k}$, $C=a_{3k}$, $H=H_{k,k}$, and
$J=H_{2k,k}$. The regular denominator and numerator are

\[
\begin{aligned}
D&=(1+2sA)(B-sC),\\
E&=H+2AB-2sAC-s^2J-2s^2AC+2s^3BC.
\end{aligned}
\tag{13}
\]

The exact cross-ratio calculation gives

\[
R+q^{-k}=E/D.
\tag{14}
\]

The source-level identities are `clock_difference_factor`,
`crossRatio_scaled_regular_part`, and `normalizedClock_regular_part` in
[QuadraticProjectiveAlgebra.lean](../../formalization/weighted/QuadraticProjectiveAlgebra.lean)
and [QuadraticProjectiveResidue.lean](../../formalization/weighted/QuadraticProjectiveResidue.lean).
In particular $D(0)=-1/4$, $E(0)=3/16$, and their quotient has the
finite residue $-3/4$.

Substituting (12) into (13) gives the proved jets

\[
\begin{aligned}
D&\equiv-\frac14+\frac q{16}+\frac{1+e}{16}q^2,\\
E&\equiv\frac3{16}-\frac q{32}-\frac{13+8e}{256}q^2
\qquad\pmod{q^3}.
\end{aligned}
\tag{15}
\]

Consequently

\[
q^3\ \bigm|\ E+\left(\frac34+\frac q{16}+\frac e{16}q^2\right)D.
\tag{16}
\]

This is `residue_cubic_dvd`, derived from `denPoly_jet` and `remPoly_jet`.
It proves the full retained finite jet, rather than just the multiplicity
of its pole.

### Why one universal quotient is necessary

A separate existence statement for a quotient polynomial at each fixed
$e$ does not supply continuous dependence when $e=e(t)$ varies. The
proof therefore lifts the recurrence, both numerator and denominator, and
the correction into $(\mathbb C[e])[q]$. Specialization in $e$ recovers
all the original polynomials exactly.

The coefficients of $q^0,q^1,q^2$ in the corrected universal numerator
evaluate to zero at every complex $e$, by (16). They are polynomials in
$e$; polynomial extensionality over the infinite field $\mathbb C$
forces them to vanish identically. Thus there is one quotient
$Q_k(e,q)$, valid simultaneously for all $e,q$.

These statements are `X_pow_dvd_of_forall_specialize`,
`exists_universal_residue_factor`, and
`normalizedClock_universal_cubic_remainder` in
[QuadraticProjectiveUniversal.lean](../../formalization/weighted/QuadraticProjectiveUniversal.lean).
Substitution of the genuine varying error $e(t)$ now gives (4) without
making an unjustified regularity assumption about a pointwise choice.

## The pattern and its relation to prior results

The calculation preserves the critical point as an anchor in a projective
configuration. After the true multiplier pole and the common finite terms
are removed, the quadratic finite coefficient records the normalized
quartic coefficient of the center return. The two actual return maps are

\[
f_0(z)=z^2,\qquad f_{-1}^{\,2}(z)=-2z^2+z^4.
\]

Writing them as $bz^2+dz^4+\cdots$, the values of $d/b^3$ are $0$ and
$-1/8$. The recovered projective coefficients are respectively $0$
and $1/128=-(-1/8)/16$. These exact center identities are also proved as
`actual_center_return_curvatures`.

The candidate was stated and compared with primary sources before its
formalization. [NOVELTY.md](NOVELTY.md) records the precise comparison:

- The earlier pole/multiplicity census was rejected because
  Mihalache–Vigneron, Theorem 2, equation (14), already gives it.
- Koenigs linearization supplies an orbit scale for a fixed nonzero
  multiplier; its holomorphic coordinates do not preserve raw
  cross-ratios.
- Teplinsky's Schwarzian distortion formula concerns a map with
  nonvanishing derivative on its domain. The critical anchor and the
  multiplier-zero degeneration require the extra calculation here.
- Buff–Epstein–Koch's spectral formula and degeneration results do not
  state the retained anchored four-point jet.

The new statement submitted for review is the specific all-clock
coefficient identity and actual-family factorization (3)–(8). The general
ideas of linearization, cross-ratio distortion, and polynomial Taylor
calculation are classical. The checked statements do not yield the
retained formula by direct specialization, but this bounded comparison is
not a guarantee of priority or of absence from the literature. No human
specialist has reviewed the novelty assessment.

## Validation and reproducibility

Starting main snapshot:
`f05f1b9dc8f5fc6eeb68491da2eb44eca6d6cec9`.
The earlier unsuccessful investigation is preserved in
[PR #266](https://github.com/dovvnloading/loops-research-archive/pull/266).
The candidate, revisions, source checks, and formal proofs are recorded as
successive commits in this contribution's PR.

The locally compiled dependency chain is:

| Module | Main obligation discharged |
|---|---|
| `QuadraticProjectiveAlgebra` | Exact cross-ratio algebra and cancellation |
| `QuadraticProjectiveTail` | Polynomial orbit and divided-tail jets for every $k\geq3$ |
| `QuadraticProjectiveActual` | Identification with actual quadratic iterates and multipliers |
| `QuadraticProjectiveResidue` | Cubic divisibility and the fixed-error remainder |
| `QuadraticProjectiveUniversal` | One polynomial quotient for all correction parameters |
| `QuadraticProjectiveRigidity` | Actual-family equations (3) and (4) |
| `QuadraticProjectiveSeparation` | Matched-multiplier factorization (6) and center value (8) |
| `QuadraticProjectiveContinuity` | Continuity of the universal polynomial evaluations and denominator units |
| `QuadraticProjectiveLimits` | Coefficient limit (8a) and eventual inequality of the actual observables |
| `QuadraticProjectiveAffine` | Supporting fractional-linear algebra and cross-ratio invariance |
| `QuadraticProjectiveEquivalence` | Eventual nonexistence of an ordered projective identification (8b) |

Local compilation used the repository's pinned Lean 4.32.0 executable and
the Mathlib revision in its manifest. No `sorry`, `admit`, `native_decide`,
or new axiom is used. The final local audit covers all eleven modules and
113 public named theorems, including their generated declarations and
transitive dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` appear in their axiom dependencies. Independent rational-series
calculations were used as diagnostics during proof discovery, and are not
part of the proof certificate.

The complete module chain can be built from `formalization/weighted` with
`lake build QuadraticProjectiveEquivalence`. The authoritative remote
acceptance check is **Weighted spectral mathlib proofs /
mathlib-kernel-check** on this PR. Its build and exhaustive axiom audit
must pass for the submitted revision; a prior checkpoint's green run does
not certify a later revision. The PR records the applicable remote run.

## Dependencies

The proofs depend on the elementary quadratic recurrence, exact algebra of
complex polynomials, coefficient divisibility, and polynomial
extensionality. The actual orbit identifications are proved, not assumed.
The primary references in [NOVELTY.md](NOVELTY.md) serve to delimit the
novelty claim and reject redundant candidates; their analytic conclusions
are not imported as unproved Lean assumptions.

## Boundary

This is a local result about the two explicit quadratic center charts and
their finite return configurations. Every theorem quantifies over each
fixed $k\geq3$. The coefficients stabilize for all such $k$, but the
proof gives no remainder bound uniform as $k\to\infty$.

No statement for all hyperbolic centers, no arbitrary-period curvature
reconstruction theorem, and no extension to an infinitely renormalizable
parameter is proved here. The proof does not separate two arbitrary
parameters in a common Mandelbrot fiber, show that a combinatorial model
is injective, prove the absence of invariant line fields, or establish a
new MLC case. UPTCR, H1–H4, and MLC retain their existing statuses. The
ledger classification is `partial`; no status promotion is proposed.

The result uses no KKL Wave construction, marked-width estimate, protected
carrier, collar, mapping telescope, or tip family. It is not a metric or
sampling criterion, an arithmetic statement about center denominators,
an encounter-charge argument, a geometric-limit obstruction, or a
Green-potential density criterion. The finite algebraic identity (6) is
the object being proved.

## Attribution

OpenAI ChatGPT GPT-6 Astra Pro assisted with candidate generation,
primary-source comparison, mathematical proof search, Lean formalization,
and adversarial review. No human specialist review has occurred. A Lean
check certifies the submitted formal statements and their dependencies;
it does not certify a claim of research priority.
