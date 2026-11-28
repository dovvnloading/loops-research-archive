---
ledger: MLC
result: obstruction
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-limit-obstruction-20261127"></a>

# Exact arithmetic cost of a quadratic critical return coordinate

Ledger statement being addressed:

> The Mandelbrot set is locally connected.

**Scope:** an all-period arithmetic obstruction for actual quadratic centers. This does
not prove MLC or a new local-connectivity case. The theorems compile in the repository's
pinned Lean project, and the complete build and unchanged transitive axiom audit have
passed. Exact validation evidence is recorded in section 7.

## Claim

Let

$$
f_c(z)=z^2+c,\qquad P_j(c)=f_c^j(0).
$$

Suppose that zero has **exact period** $N\ge2$:

$$
P_N(c)=0,\qquad P_j(c)\ne0\quad(0<j<N).
\tag{1}
$$

Write the genuine polynomial return and its critical linear normalization as

$$
f_c^N(z)=A_Nz^2+B_Nz^4+z^6E_N(z),\qquad
R_{c,N}(w)=A_N f_c^N(w/A_N)
 =w^2+\beta_{c,N}w^4+w^6\widetilde E_N(w),
\tag{2}
$$

where $A_N\ne0$ and both remainders are polynomials. Thus
$\beta_{c,N}=B_N/A_N^3$ is an actual coefficient of an actual iterate in the
specified dynamical coordinate. It is not a coefficient attached to an abstract model.

The ratio is unchanged by any nonzero linear change of the critical coordinate:
under the conjugacy $w=sz$, the two coefficients become $A_N/s$ and
$B_N/s^3$. Their ratio is still $B_N/A_N^3$. This is formally recorded as
`linear_conjugate_quartic_invariant` alongside the actual conjugated-return identity.

Here “integral” always means **integral over $\mathbf Z$**, equivalently a complex
algebraic integer. All exponents below are nonnegative integers.

### Theorem A — the return has an exact denominator

$$
\boxed{\quad
2^k\beta_{c,N}\text{ is integral}\quad\Longleftrightarrow\quad k\ge 2N-1.
\quad}
\tag{3}
$$

The stronger certificate proves that
$u=2^{2N-1}\beta_{c,N}$ is integral and that there exist integral $v,t$ with

$$
uv=1+2t.
\tag{4}
$$

This proves exact noncancellation, not merely an upper bound on denominators.

### Theorem B — every coordinate producing an integral target pays an exact cost

Let $H,G\in\mathbf C[X]$ be arbitrary polynomials with

$$
H(0)=0,\quad H'(0)=1,\qquad
G_0=G_1=0,\quad G_2=1,
$$

where $G_j=[X^j]G$. In Lean, the coordinate conditions are
`H.coeff 0 = 0` and `H.coeff 1 = 1`. Assume only that $G_3,G_4$ are integral and that the
**genuine composition equation** holds through degree four:

$$
X^5\mid H\circ R_{c,N}-G\circ H.
\tag{5}
$$

There is no integrality or algebraicity assumption on $H$. Put
$a=[X^2]H$ and $b=[X^3]H$. Then

$$
2a\text{ is integral},\qquad
\boxed{\quad 2^k b\text{ is integral}\quad\Longleftrightarrow\quad k\ge2N.\quad}
\tag{6}
$$

This cost is attained. Taking $G=X^2$, the polynomial

$$
H(X)=X+\frac{\beta_{c,N}}2X^3
\tag{7}
$$

satisfies (5), and its cubic coefficient has the exact exponent $2N$.
This is a theorem about Böttcher **jets through degree four**. It does not assert
convergence, existence, or arithmetic properties of an entire infinite Böttcher series.

### Corollaries recorded in Lean

1. If the quadratic and cubic coefficients of a tangent-to-identity coordinate are
   integral, then the transformed quartic coefficient still has exact exponent
   $2N-1$. In particular such a coordinate cannot produce an integral quartic term.
2. If centers $c,d$ have exact periods $N,M\ge2$ and a field automorphism of
   $\mathbf C$ takes $\beta_{c,N}$ to $\beta_{d,M}$, then $N=M$.
   The return period can be recovered from the arithmetic of this fourth-order coefficient.
3. For any sequence of actual centers with unbounded exact periods, no single exponent
   $k$ makes all the normalized quartic coefficients integral after multiplication by
   $2^k$.
4. At the actual basilica center $c=-1$, $N=2$, the concrete Lean theorem
   proves $\beta=-1/8$. The optimal-coordinate module also verifies the exact
   period-two hypotheses and supplies an actual coordinate jet with exact cubic
   denominator exponent four. For explanation, direct substitution gives
   $R_{-1,2}(w)=w^2-w^4/8$, and the general coordinate law gives the cubic
   Böttcher-jet coefficient $-1/16$; these last two formulas are explanatory
   specializations, not separate named Lean exports.

## Evidence

### 1. The archive's precise remaining hypothesis

At base commit `cb37633f2dee57c0bd7dfe7a417823a7067aabfb`, the named missing
hypothesis is **`UNIVERSAL_PROTECTED_TOWER_CLOSURE`**, the six-clause Universal
Protected-Tower Compactness and Rigidity Proposition (UPTCR), quantified over every
infinitely renormalizable quadratic. The ledger records `UPTCR_IMPLIES_MLC` as proved
**conditional on that hypothesis**. The package itself is open.

The six clauses require an actual canonical construction, exact analytic realization,
a finite calibrated response state, uniform backward transitions, coercive compactness,
and tower rigidity together with singleton parameter fibers and connected relative
neighborhoods. Its open prerequisites include `H1_MARKED_CONSTRUCTION`, `MBTT` and its
H2 inputs, `H3_COERCIVITY`, and `H4_RIGIDITY`.

Exact source locations are
[Proposition UPTCR, section 5](../../research/mlc_unified/mlc_closure_proposition.md),
[Theorem 4.1](../../research/mlc_unified/uptcr_cross_validation.md), and the corresponding
rows in `ledger.json`. There is an additional formalization distinction:
[`ResearchGates.lean`](../../ResearchGates.lean) is an abstract specification whose
`conditional_local_connectivity` consumes a separate `TerminalBridge` and complement
theorem. It does not instantiate the written analytic reduction with actual quadratic
objects. This contribution neither assumes nor supplies those missing bridges.

Having identified this gap, the proof below leaves that machinery entirely.

### 2. The arithmetic mechanism and the route it obstructs

The mechanism is the arithmetic of formal coordinates at the prime dividing the critical
local degree. One might begin an arithmetic approach to infinitely renormalizable fibers
with algebraic critical centers, pass to actual return maps, normalize their critical germs,
and try to retain bounded denominator control while comparing successive levels. Equations
(3) and (6) prove that this particular transport cannot have a bound independent of return
period. The loss is exactly linear in physical return time, and passing to another coordinate
with integral target cubic and quartic coefficients transfers the loss into the coordinate.

This is an arithmetic obstruction in a specifically defined normalization. It is not an
abstract metric, sampling, or covering criterion for fibers. No KKL Waves, widths, collars,
protected carriers, mapping telescopes, or tip families occur in its proof.

The source of noncancellation is simple but rigid: every nonzero point in a periodic critical
orbit is an algebraic unit; after the first nonlinear contribution to the return, every later
contribution to the scaled quartic coefficient is even. The first contribution therefore
survives modulo two at every period. The coordinate equation cannot cancel it with the
lower-denominator terms permitted by an integral target.

### 3. Actual orbit points are units — the classical input rederived

The actual return has an explicit factorization

$$
f_c^{m+1}(z)-P_{m+1}(c)=z^2Q_m(c,z),
$$

where

$$
Q_0=1,\qquad
Q_{m+1}=\bigl(f_c^{m+1}(z)+P_{m+1}(c)\bigr)Q_m.
\tag{8}
$$

A critical-return parameter is integral: it is a root of the monic integer polynomial
$P_N$. Thus every critical-orbit point is integral. Let $z=P_j(c)\ne0$.
Critical periodicity gives $f_c^N(z)=z$. Evaluating (8) with $m=N-1$ gives

$$
z=z^2Q_{N-1}(c,z),\qquad zQ_{N-1}(c,z)=1.
$$

The quotient is integral by its recurrence. It is an explicit integral inverse of $z$.
This is a familiar dynamical-unit phenomenon, not the novelty claim.

Lean source:
[`QuadraticCriticalUnits.lean`](../../formalization/weighted/QuadraticCriticalUnits.lean),
especially `criticalReturnQuotient_factor`, `center_orbit_integral_inverse`, and
`orbit_unit_of_center`.

### 4. The actual return coefficients and their arithmetic

For a return of length $j\ge1$, put

$$
f_c^j(z)=P_j(c)+A_jz^2+B_jz^4+z^6E_j(z).
$$

Squaring the polynomial and adding $c$ proves, with no asymptotic approximation,

$$
A_1=1,\quad B_1=0,\qquad
A_{j+1}=2P_jA_j,\quad B_{j+1}=A_j^2+2P_jB_j.
\tag{9}
$$

The code constructs $E_j$ as a polynomial and proves an equality of entire iterate
polynomials. Evaluation then identifies it with the genuine function iterate.

Set $V_j=\prod_{r=1}^{j-1}P_r(c)$. Before the first return all its factors are units,
so $V_j$ and its inverse are integral. Equation (9) gives

$$
A_j=2^{j-1}V_j.
\tag{10}
$$

For $j\ge2$, write $B_j=2^{j-2}U_j$. Then

$$
U_2=1,\qquad U_{j+1}=2^{j-1}V_j^2+P_jU_j.
\tag{11}
$$

An integral element is called `OddIntegral` in the proof when it has an integral inverse
modulo two, in the explicit sense (4). Such elements are closed under multiplication and
under adding twice an integral element. Since $P_j$ is an integral unit and $j\ge2$,
(11) proves by induction that every relevant $U_j$ is `OddIntegral`.

Combining (10) and (11) at the terminal time gives

$$
2^{2N-1}\beta_{c,N}=U_N V_N^{-3}.
\tag{12}
$$

This is integral and invertible modulo two. An `OddIntegral` element $u$ cannot have
$u/2$ integral: from $uv=1+2t$ one would obtain
$2((u/2)v-t)=1$ in the algebraic integers, contradicting the nonintegrality of $1/2$.
If $k<2N-1$, integrality of $2^k\beta$ would imply integrality of $u/2$ after
multiplication by a further nonnegative power of two. This proves the forward implication
of (3); the reverse implication follows from (12).

Lean sources:
[`QuadraticReturnJet.lean`](../../formalization/weighted/QuadraticReturnJet.lean) and
[`QuadraticReturnArithmetic.lean`](../../formalization/weighted/QuadraticReturnArithmetic.lean).
The main names are `actual_center_return_jet_denominator`,
`normalizedQuartic_odd_numerator`, and `normalizedQuartic_integral_iff`.
The Lean index is shifted: `n` denotes physical period `N = n + 2`, so `2*n+3 = 2*N-1`.

### 5. A real coordinate equation, not an assumed coefficient law

Write

$$
H(w)=w+aw^2+bw^3+O(w^4),\qquad
G(w)=w^2+\gamma w^3+\delta w^4+O(w^5).
$$

Extracting the cubic and quartic coefficients of the genuine composition defect in (5)
gives

$$
\gamma=-2a,\qquad
\delta=\beta+5a^2+a-2b.
\tag{13}
$$

The code proves these equations for arbitrary polynomials with unrestricted higher
coefficients. It does not define “conjugacy” to mean the desired coefficient equations.

If $a,b$ are integral, the difference $\delta-\beta$ is integral. Adding an integral
quantity cannot alter the threshold in (3). This proves the integral-coordinate obstruction.

For the stronger Theorem B, assume only $\gamma,\delta$ integral. Equation (13) makes
$2a$ integral. With $r=5a^2+a-\delta$,

$$
4r=5(2a)^2+2(2a)-4\delta
$$

is integral, while $2b=\beta+r$. Put $e=2N-1\ge3$. Then

$$
2^{e+1}b=2^e\beta+2\bigl(2^{e-3}(4r)\bigr).
\tag{14}
$$

The first summand is `OddIntegral`, and the second is twice an integral element.
Thus $2^{e+1}b$ is also `OddIntegral`, giving the exact threshold $e+1=2N$.
The explicit polynomial (7) proves attainment through degree four.

Lean sources:
[`QuadraticJetConjugacy.lean`](../../formalization/weighted/QuadraticJetConjugacy.lean),
[`QuadraticReturnCoordinateObstruction.lean`](../../formalization/weighted/QuadraticReturnCoordinateObstruction.lean),
and [`QuadraticReturnOptimalCoordinate.lean`](../../formalization/weighted/QuadraticReturnOptimalCoordinate.lean).
Main names: `integral_coordinate_preserves_denominator`,
`actual_bottcher_jet_exists_with_exact_denominator`,
`actual_integral_target_coordinate_denominator`, and
`actual_integral_target_coordinate_cost_attained`.

### 6. Galois and sequence consequences

Algebraic integrality is preserved and reflected by a field automorphism of $\mathbf C$,
and such an automorphism fixes powers of two. Hence if it takes one normalized quartic
coefficient to another, their least allowed exponents in (3) agree. This proves equality
of the physical return periods. No irreducibility conjecture for Gleason polynomials is used.

For a sequence with unbounded periods, a fixed proposed denominator exponent $k$ is
smaller than $2N-1$ at some member. Equation (3) gives the contradiction. These statements
are `normalizedQuartic_galois_period_rigidity` and
`no_uniform_normalizedQuartic_denominator`.

### 7. Validation and reproducibility

All six Lean modules are registered by the repository's existing contribution tool. The
source index uses `METADATA` because no existing physical bridge or ledger status is being
promoted; the new theorems themselves directly mention the actual quadratic orbit and iterate.

The project pins Lean and Mathlib `v4.32.0`. Reproduce with:

```sh
cd formalization/weighted
lake exe cache get
lake build QuadraticCriticalUnits QuadraticReturnJet QuadraticReturnArithmetic \
  QuadraticJetConjugacy QuadraticReturnCoordinateObstruction QuadraticReturnOptimalCoordinate
cd ../..
python code/contribute.py check
python code/verify_lean_coverage.py --audit weighted
```

The existing weighted workflow compiles every registered default target, then audits the
transitive axioms of every declaration in the weighted project. Its allowlist is exactly
`propext`, `Classical.choice`, and `Quot.sound`. No workflow, checker, status record, or
existing theorem is changed. No proof holes, new axioms, or external-computation trust
shortcuts are permitted.

The complete project build and transitive axiom audit passed at commit
`0c7388a7214a4747823009a8af373bd6d8ab09ce` in
[weighted CI run 46106863256](https://github.com/dovvnloading/loops-research-archive/actions/runs/46106863256),
[job 140861465323](https://github.com/dovvnloading/loops-research-archive/actions/runs/46106863256/job/140861465323).
The final audit reported **242 modules and 6,087 declarations**, with only the permitted
standard axioms. All six new modules were included. This checks compiled declarations,
including private and generated declarations, and their transitive dependencies.

`python code/contribute.py check` passes without the draft exemption. The source-coverage
check reports 291 registered Lean files (44 root, 242 weighted, 5 standalone) and no
prohibited source tokens. The PR's contribution-intake, source-index, root/standalone
kernel checks, and other research checks also passed at that head.

Local installation of the pinned toolchain failed because of insufficient disk space;
CI supplied the compilation and kernel-audit evidence above. The final documentation
update changes exposition and a module docstring, with theorem statements and proof bodies
identical to the validated source. The CI checks on
[PR #255](https://github.com/dovvnloading/loops-research-archive/pull/255) record validation
of the current head. The PR was opened before the proof work and retains the incremental
research, proof-fix, and main-branch synchronization commits.

## Dependencies

The proofs depend on Mathlib and the archive's
[`QuadraticCriticalTransversality.lean`](../../formalization/weighted/QuadraticCriticalTransversality.lean):
its actual orbit/return definitions, monic-orbit integrality theorem, and the proved fact that
an algebraic integer cannot be an inverse of two. The critical-unit and polynomial-jet
arguments are rederived in the new modules. No analytic theorem is imported as an assumption
or added as an axiom.

The relevant **background**, rather than unproved premises of the Lean theorems, is:

- J. Milnor, *Arithmetic of Unicritical Polynomial Maps*, Theorem 3.2 and Lemma 3.1,
  [2012 preprint](https://arxiv.org/pdf/1203.5447), published in *Frontiers in Complex
  Dynamics* (2014). These are antecedents for arithmetic integrality and units.
- X. Buff, A. L. Epstein, and S. Koch, *Eigenvalues of the Thurston operator*,
  *Journal of Topology* 13 (2020), 969–1002;
  [author manuscript](https://public.websites.umich.edu/~kochsc/eigenvalues.pdf),
  sections 9.2–9.3, particularly Lemma 9.5 (Poonen) on resultant units. The unit input is
  classical, and no resultant-unit theorem is presented as new here.
- A. Salerno and J. H. Silverman, *Integrality properties of Böttcher coordinates for
  one-dimensional superattracting germs*, *ETDS* 40 (2020), 248–271;
  [preprint](https://arxiv.org/pdf/1708.09275), Proposition 1, Theorems 3–4, and
  Remark 8. These concern formal existence, general integrality/denominator bounds,
  and explicit low-order coordinate coefficients.
- H. Fu and H. Nie, *Böttcher coordinates at wild superattracting fixed points*,
  *Bulletin of the London Mathematical Society* 56 (2024), 1698–1715,
  [DOI](https://doi.org/10.1112/blms.13021). This is nearby work on wild-prime
  Böttcher arithmetic and convergence radii.

- R. Ren, *Coefficient-Level Böttcher Theory for Wild Superattracting Germs of
  Degree $p^e$*, [arXiv:2604.02014v3](https://arxiv.org/html/2604.02014v3)
  (May 2026). This nearby coefficient and radius theory assumes odd $p$ and
  $e\ge2$; it does not treat the local-degree-two center-return statements here.

## Boundary

**Exactly the route excluded.** There is no bound independent of physical return period
on the powers of two needed for the canonical normalized quartic coefficient. Moreover,
any coordinate making the target's cubic and quartic coefficients integral must itself
have cubic denominator exponent exactly twice that period. This prevents a proposed
arithmetic comparison of such critically normalized germs from silently retaining uniformly
bounded denominators.

**What is not excluded.** The return remains linearly conjugate to the original integral
polynomial $f_c^N$. There is no claim of bad reduction in dynamical moduli, failure of
potential good reduction, or failure of complex renormalization compactness. Nonintegral
coordinates do change the quartic coefficient; Theorem B calculates their necessary cost.
Arithmetic methods with a different, period-dependent normalization or adelic metric remain
possible. No Weil-height theorem, nonarchimedean convergence radius, or equidistribution
statement is counted as formalized here.

**What remains for MLC.** The theorem is at exact critical centers. It does not produce a
limit theorem for non-PCF infinitely renormalizable parameters, control Galois embeddings
inside a parameter fiber, or turn arithmetic information into separation or connected
neighborhoods in the complex parameter plane. A future arithmetic route must specify and
prove that bridge while accounting for the coordinate cost above. None of H1–H4, MBTT,
UPTCR, or MLC changes status; no status promotion is requested.

**Why the other seed was not used.** Bromberg's non-local-connectivity mechanism includes a
specific parameter-space separation phenomenon and a second deformation dimension; a mere
extra geometric limit does not supply its quadratic analogue. Parabolic implosion occurs
at quadratic parameters where local connectivity is known. See Bromberg's
[introduction and dimension comparison](https://www.math.utah.edu/~bromberg/papers/nonlocal.pdf)
and Tan Lei's [Theorem 1.1 and introduction](https://math.univ-angers.fr/~tanlei/papers/root.pdf).
This packet claims no result about Lavaurs maps or exclusion of that mechanism at infinite
renormalization.

## Attribution

The archive's actual-orbit formalization and arithmetic transversality are credited above.
Dynamical units, formal Böttcher coordinates, and the elementary coefficient-conjugacy
calculation are not claimed as discoveries. The contribution developed here is the exact
all-period exponent for the normalized genuine quadratic return, the optimal integral-target
coordinate cost, and the stated Galois-period and unbounded-period consequences.

A scoped primary-literature search checked the works above and combinations of quadratic
critical centers/returns, dyadic or 2-adic coefficients, Gleason polynomials, arithmetic
renormalization, and quartic/Böttcher coefficients. No matching all-period statement
(3), (6), or its actual-center integral-coordinate obstruction was located. This is a
novelty check with identified comparators, not a proof of global priority or a claim that
nobody has ever considered arithmetic renormalization.

The proofs and source checks were developed by OpenAI ChatGPT, GPT-6 Astra Pro, with
independent arithmetic, actual-jet, and adversarial literature/coordinate reviews. Human
specialist review: none. The contribution is released under the repository's CC0 license.
