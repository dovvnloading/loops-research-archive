---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; research, proof development, and adversarial review
human_review: none
---

<a id="quadratic-geometric-limits-20261128"></a>

# Actual quadratic flights: reciprocal transport and invisible encounters

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

**Development checkpoint.** The statements below are the precise targets of
new Lean modules in this pull request. Compilation and the transitive axiom
audit are pending. No theorem below counts as validated before those checks
pass. This contribution does not close H4 or prove MLC.

The proposed contribution is an obstruction to a specific kind of loss of
geometry in affinely normalized **actual quadratic returns**. The mechanism
retains each nonlinear encounter as an exact quadratic map in transported
critical-value coordinates. Reciprocal coordinates separate the cumulative
complex displacement from its quadratic error. Finite-jet algebra then tests
whether a small number of persistent encounters can disappear in a quadratic
limit.

This is not a claim that geometric limits, parabolic implosion, the Schwarzian
cocycle, or Euler approximation are new ideas. The new proposed statements are
the explicit quantitative actual-orbit criterion and the sharp finite-encounter
obstructions in the normalization fixed below. The literature comparison is
part of the boundary of this claim.

## Evidence

### 1. The exact archive frontier

The base is main commit `6a10209b3cc51878bc45de7668894757b2575e08`.
The exact unresolved global hypothesis is
**`UNIVERSAL_PROTECTED_TOWER_CLOSURE`**, the Universal Protected-Tower
Compactness and Rigidity Proposition (UPTCR), quantified over **every
infinitely renormalizable quadratic polynomial** with universal constants.
The ledger marks `UPTCR_IMPLIES_MLC` as proved with this explicit hypothesis.

Its six clauses require one compatible actual construction with canonical
protected carriers, exact analytic realization, uniformly finite response
state, a universal backward transition, coercive marked compactness, and
rigidity with singleton parameter fibers and connected relative neighborhoods.
All of H1--H4 remain open. The exact sources are
[`mlc_closure_proposition.md`, section 5](../../research/mlc_unified/mlc_closure_proposition.md)
and [`uptcr_cross_validation.md`, Theorem 4.1](../../research/mlc_unified/uptcr_cross_validation.md).
The first failure of the existing construction is at UPTCR-1; that first
failure must not be confused with the whole missing six-clause hypothesis.

There is a separate formalization distinction:
[`ResearchGates.lean`](../../ResearchGates.lean) is an abstract specification.
Its `conditional_local_connectivity` theorem consumes a separate
`TerminalBridge` and complementary-parameter theorem. It does not instantiate
the written analytic reduction with the actual Mandelbrot set.

Having identified that frontier, this contribution uses none of the archive's
Wave, marked-width, collar, protected-carrier, mapping-telescope, or tip-family
methods. It also uses no fiber metric/sampling criterion and no arithmetic
of center denominators. Each new foundation module imports only Mathlib;
subsequent modules import these new foundations.

### 2. Exact physical coordinates, at every return time

Let `f_c(z)=z^2+c`. Start at the critical value and choose a nonzero affine
critical scale `s`. Set

\[
x_j=f_c^j(c),\qquad \lambda_0=s^2,\qquad
\lambda_{j+1}=2x_j\lambda_j,\qquad
 a_j=\frac{\lambda_j}{2x_j}.
\]

Assume `x_j != 0` through the indicated finite flight. In particular these
quantities are defined along every finite segment of a critical orbit which
never returns to zero. The theorem does not require a critical center.

For every consecutive actual orbit block define the entire polynomial

\[
T_{r,n}(u)=
\frac{f_c^n(x_r+\lambda_r u)-x_{r+n}}{\lambda_{r+n}}.
\tag{1}
\]

It fixes zero with derivative one. Direct expansion of the actual quadratic
map gives the exact one-step map

\[
h_{a_j}(u)=u+a_j u^2,\qquad
T_{r,n}=h_{a_{r+n-1}}\circ\cdots\circ h_{a_r}.
\tag{2}
\]

No term has been truncated in (1)--(2). The critical return itself is

\[
\frac{f_c^{N+1}(sz)-f_c^{N+1}(0)}{\lambda_N}=T_{0,N}(z^2).
\tag{3}
\]

Thus degree four in `u` is degree eight in the original critical coordinate.
No square root or nonlinear coordinate choice occurs in the definitions.

`QuadraticFlightJet.lean` proves (1)--(3) as identities of entire polynomials.
Its `HasJet` statement retains an exact polynomial remainder `X^5*R`.
The coefficient laws are derived from these identities, not assumed.
The public bridges include `flight_actual_identity`,
`normalizedActualFlight_eq_flight`, `actualBlock_eq_flight`, and
`critical_return_identity`.

### 3. Reciprocal transport without a bound on total absolute variation

For a finite actual charge sequence put

\[
S_n=\sum_{j<n}a_j,\qquad E_n=\sum_{j<n}|a_j|^2.
\]

The reciprocal coordinate `v=1/u` obeys the **exact** identity

\[
v_{j+1}=v_j-a_j+\frac{a_j^2}{v_j+a_j}.
\tag{4}
\]

Fix `delta>0`. Suppose

\[
|v-S_n|\ge\delta\quad(0\le n\le N),\qquad
E_N\le\delta^2/16.
\tag{5}
\]

The proposed finite theorem proves, simultaneously for every `n<=N`,

\[
\left|v_n-(v-S_n)\right|\le\frac{2E_n}{\delta},\qquad
|v_n|\ge\delta/2,
\tag{6}
\]

and

\[
\boxed{\quad
\left|T_{0,n}(v^{-1})-(v-S_n)^{-1}\right|
\le\frac{4E_n}{\delta^3}.
\quad}
\tag{7}
\]

The estimate has no dependence on the number of steps and assumes no bound
on `sum |a_j|`. The entire partial-sum path in (5) matters; a separated final
sum alone is insufficient.

Proof: each `|a_j|<=delta/4` follows from the square-sum bound. If (6) holds
through time `n`, its error is at most `delta/8`; the denominator in (4) is
therefore at least `delta/2`. The next error is at most
`2|a_n|^2/delta`. Induction proves (6), and the exact identity for differences
of inverses gives (7). The proof verifies nonvanishing rather than silently
using division across a pole.

For a sequence with a common separation `delta`, `E_N -> 0`, and `S_N -> t`,
(7) yields the Möbius limit

\[
T_{0,N}(u)\longrightarrow \frac{u}{1-tu}
\]

uniformly over any set of initial reciprocal points satisfying the common
separation. The uniform target error is at most
`4 E_N/delta^3 + |S_N-t|/delta^2`. This is a
specific controlled flight regime. It is not the construction of a Lavaurs
map or a general parabolic-implosion theorem.

Lean files: `QuadraticReciprocalFlight.lean` proves the quantitative estimate
and nonvanishing; `QuadraticActualShadow.lean` connects it to the literal
quadratic maps and proves the corresponding limit statement.

### 4. Three encounters cannot disappear through the eighth critical jet

Consider actual critical returns split into four consecutive actual flights,
with three selected one-step encounters between them. Their lengths may vary
and tend to infinity. Suppose:

1. The selected actual charges converge to `a,b,d`.
2. The coefficients of degrees two, three and four of each of the four
   normalized actual flights tend to zero.
3. The same three coefficients of the complete normalized actual flight tend
   to zero.

Then the proposed theorem concludes

\[
\boxed{a=b=d=0.}
\tag{8}
\]

In other words, a quadratic limit cannot hide three persistent encounters
when all intervening flights disappear through this jet order. This is a
conditional obstruction on explicit orbit-derived maps, not a new assertion
that all infinitely renormalizable maps have this profile.

The proof is sensitive to the **order** of the encounters. The first three
nonidentity coefficients of `h_d o h_b o h_a` are

\[
A=a+b+d,\qquad B=2ab+2d(a+b),\qquad
C=a^2b+d((a+b)^2+4ab).
\]

If `A=B=C=0`, then `d=-a-b` and `a^2+ab+b^2=0`. The last coefficient reduces
to `-ab(4a+5b)`. If either `a` or `b` is zero, both are zero. Otherwise
`b=-4a/5`, and the preceding quadratic identity becomes
`21a^2/25=0`. This proves (8) over the complex numbers with no phase or
reality assumption.

The order eight is meaningful for this three-encounter assertion. Taking
`a=1`, `b=w`, `d=-1-w`, where `w^2+w+1=0`, cancels `A` and `B`, but not `C`.
A single Schwarzian or two moment conditions would miss this profile.

The stronger orbit-energy version proves the intervening jet convergence
instead of assuming it. Write a block's partial charge sums as `S_j`, its
signed square sum as `Q`, and its absolute square sum as `E`. If
`|S_j|<=M` through the block, its coefficients `A,B,C` obey

\[
A=S_N,\qquad |B-S_N^2|\le E,\qquad |C-S_N^3|\le5ME.
\]

Consequently bounded partial sums, `S_N -> 0`, and `E -> 0` force all three
coefficients to vanish. These conditions allow unbounded absolute variation.
`QuadraticFlightEnergy.lean` derives these bounds from exact summation
identities. The main actual-family result
`actual_critical_three_encounter_energy_obstruction` uses these concrete
conditions on the four shifted actual charge sequences and concludes (8).
Only the full return's flat critical jet remains a hypothesis.

`QuadraticThreeEncounterAlgebra.lean` proves the exact expansion, obstruction,
sharpness test and limiting algebra. `QuadraticThreeEncounterLimit.lean`
proves the statement with all four blocks defined by (1), and with all
coefficients taken from those actual polynomials. In particular no assumed
model-to-physical identification is used.

### 5. Two encounters amid genuine Möbius flights

A complementary exact rational theorem allows nonzero parabolic flight times.
Put `m_t(u)=u/(1-tu)` and consider

\[
G=m_r\circ h_b\circ m_t\circ h_a\circ m_s.
\]

If `G` agrees with the identity through degree five, then
`a=b=0` and `s+t+r=0`. Its denominator is one at zero, and its complete cleared
identity defect is a polynomial of degree at most five. After removing the
quadratic term, the next three coefficients satisfy

\[
C_3=-(a^2+b^2),\quad C_4=a^2(t-b)-2ab^2,\quad
C_5=a^2(a(t-b)-b^2).
\]

The identity `C_5-a C_4=a^2 b^2` proves the assertion without division.
The nonzero example `(a,b,s,t,r)=(1,i,0,i-2,1-2i)` has cleared defect exactly
`-u^5`. Thus degree four is insufficient. In the original critical
coordinate this is a tenth-order obstruction, not the eighth-order statement
of section 4.

`QuadraticMobiusEncounter.lean` proves the rational composition formula,
the sharp bound, and the corresponding germ theorem. The latter says an
identity on a neighborhood of zero forces the same vanishing; it uses the
exact polynomial's finite-root property. This rational theorem is reported
separately from the actual-family theorem until its complete actual block
limit bridge has compiled. An actual sparse-two-encounter conclusion is not
silently inferred from two unrelated modules.

### 6. Literature and novelty comparison

The following are background and boundary checks, not unformalized premises
in the new Lean proofs:

- Hexi Ye, *The Schwarzian derivative and polynomial iteration*,
  [arXiv:1105.5598v2](https://arxiv.org/abs/1105.5598), section 2.1,
  equations (2.1)--(2.2), gives the classical Schwarzian cocycle and iterate
  sum. Its Theorem 1.1 concerns a different normalization away from the
  precritical closure. The scalar six-jet cocycle was rejected as a novelty
  claim by itself.
- Curtis McMullen, *Complex Dynamics and Renormalization*,
  [author's text](https://people.math.harvard.edu/~ctm/home/text/papers/renorm/renorm.pdf),
  already develops geometric renormalization limits. The broad geometric
  direction is not claimed as unprecedented.
- Matthieu Astorg and Fabrizio Bianchi, *Non-autonomous parabolic implosion*,
  [arXiv:2603.27686](https://arxiv.org/abs/2603.27686), studies nonautonomous
  additive perturbations and Lavaurs phases. Our exact orbit-derived
  `u+a_j*u^2` decomposition and finite separated-driver estimate have a
  different statement; this does not establish that no comparable lemma
  exists anywhere in the literature.

The novelty claim is limited to the explicit actual-return obstruction and
quantitative criterion formulated here. Neither a search with no matching
result nor Lean compilation certifies global bibliographic originality.
No broad new MLC theorem is claimed.

### 7. Progress and validation

- Early draft PR opened from the stated main commit before proof development.
- `09bc48a`: first algebraic obstruction and exact expansion submitted to CI.
- `0b36045`: exact actual-orbit factorization and reciprocal shadowing submitted.
- `6f6b976`: the actual polynomial identification, reciprocal estimate, and
  three-encounter algebra compiled. Limit modules exposed ordinary proof-script
  errors, repaired in the following checkpoint.
- Further actual-return and limiting theorems are being integrated.
- Local Lean is not installed; the workspace has insufficient disk space for
  the pinned toolchain. The unchanged weighted Lean workflow is the compiler
  and transitive-axiom judge.
- All new files must be registered with `code/contribute.py lean-add`; the
  existing coverage and contribution checks remain unchanged.

## Dependencies

- `H4_RIGIDITY` is the addressed open obligation, not a mathematical premise.
- The archive frontier is identified from the source files in section 1.
- Formal dependencies: Mathlib and the new modules listed above only.
- The exact quadratic recurrence, field identities, polynomial coefficients,
  finite sums, norm inequalities, and elementary limits constitute the proof.
- No imported dynamical theorem, no new axiom, and no trust escape is used.
  The CI axiom audit must verify this at the final commit.

## Boundary

The obligation stays **open**. The theorem does not prove UPTCR, H4, MLC,
triviality of a parameter fiber, or a new local-connectivity case.

The Lean quantifiers cover arbitrary actual quadratic parameters and finite
orbit segments with the stated nonvanishing hypotheses, and arbitrary
sequences of those segments. An infinitely renormalizable parameter with
nonperiodic critical orbit is within this scope at every finite return time.
No Lean definition or construction of infinite renormalization, polynomial-like
restriction, Lavaurs map, horn map, harmonic measure, or parameter fiber is
introduced. No theorem establishing the hypotheses for every such parameter
is hidden in the wording.

The key unresolved bridge is dynamical: a hypothetical nontrivial parameter
fiber has not been shown to force a sequence in which a finite persistent
encounter profile is hidden by these controlled flights. Driver separation
may fail; quadratic variation need not vanish; there may be infinitely many
persistent encounters; surviving flight maps need not be the identity or
Möbius maps in the fixed affine normalization; degeneration may occur outside
every fixed germ neighborhood. These alternatives are not ruled out here.

Output and input coordinates are fixed affine physical normalizations.
Arbitrary nonlinear coordinate changes would alter the jets and are outside
the theorem. Coefficient convergence is an explicit hypothesis where stated;
it is not silently upgraded to locally uniform convergence or to parameter
local connectivity.

The harmonic-measure seed was not used: harmonic-measure nullity alone does
not show that a connected fiber is a point. No theorem about harmonic measure
is being promoted to fiber rigidity.

## Attribution

The archive and cited original authors retain credit for prior mathematics.
The user's geometric-limit question motivates this investigation. Classical
Schwarzian, parabolic-coordinate and composition ideas are explicitly credited
above. The contribution's proposed novelty lies in its stated finite
actual-return criteria, not in those classical ingredients. AI assistance and
the absence of human mathematical review are disclosed in the front matter.
