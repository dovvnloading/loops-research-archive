# Weighted spectral reduction: mathlib formalization

This isolated Lake workspace pins **Lean 4.32.0** and
**mathlib v4.32.0**, with its complete transitive lockfile. It imports
the five existing graph-theoretic Lean modules from the repository root.

## Kernel-checked theorems

The exact five-vertex graph has first-return multiplicities 1 at base
lengths 2 and 3 from gate e to f, and 1 at length 2 from f to e.
The graph-derived (negative-weight) two-gate operator is

\[
H(t)=\begin{pmatrix}
0&t^{-2}+t^{-3}\\
t^{-2}&0
\end{pmatrix}.
\]

| Module | Exact result |
|---|---|
| [WeightedReturn.lean](WeightedReturn.lean) | For every n and real t ≠ 0, H(t) has eigenvalue t^n with an eigenvector whose second coordinate is nonzero **iff** t^(2n+5)=t+1. Under t>0, explicitly gives a positive eigenvector (t^(n+2),1). |
| [WeightedReturn.lean](WeightedReturn.lean) | Defines the competing *positive-power* return operator separately. For t>1 satisfying the actual polynomial, this operator cannot have eigenvalue t^n with a nonzero second coordinate. |
| [GraphWeightedBridge.lean](GraphWeightedBridge.lean) | Imports the five original core-Lean modules and constructs H(t) from the graph's already-checked integer R₂=DC and R₃=DQC coefficients. Proves the exact equality with the real-valued weighted operator and transports the eigenproblem theorem. |
| [CloneBounds.lean](CloneBounds.lean) | For every n and t>1 with t^(2n+5)=t+1, proves t^(2n+4) < 2 < t^(2n+6), a uniform-in-n integer-power bracket. |
| [CloneRoot.lean](CloneRoot.lean) | For every natural n, proves a **unique real root greater than 1** of t^(2n+5)=t+1 exists; it lies strictly between 1 and 2. |
| [FullCloneEigen.lean](FullCloneEigen.lean) | For every n and root t>1, constructs the explicit positive full vector x_i=t^i for i≤n and x_i=t^i/(t+1) for i>n; verifies all local adjacency equations, including the shortcut and wrap. |
| [FullCloneMatrix.lean](FullCloneMatrix.lean) | Constructs the complete (2n+5)-vertex 0/1 adjacency matrix directly from the certified Edge relation, proves its full finite row sums equal the local action, and checks the positive eigenpair using Matrix.mulVec. |
| [SpectralDominance.lean](SpectralDominance.lean) | Proves a reusable finite-dimensional inequality: for any nonnegative real matrix with a strictly positive real eigenvector of eigenvalue t, every complex eigenvalue μ satisfies ‖μ‖≤t. Specializes it to every cloned adjacency matrix. |
| [FullCloneSpectralMax.lean](FullCloneSpectralMax.lean) | Casts the checked real eigenvector to an actual nonzero complex eigenvector and proves its eigenvalue t attains the maximum modulus of all complex eigenvalues of the full matrix. Thus t is the spectral radius in the usual finite-dimensional sense. |

Both Lean projects build without proof holes or custom axioms.
An additional standard-library Fraction regression checks the
negative-weight identity at 357 exact rational test points.

**Passing CI:** The completed full-matrix and spectral-dominance theorem suite was checked in [mathlib build #42038972966](https://github.com/dovvnloading/loops-research-archive/actions/runs/42038972966). The separate root Lean/Python suite is also checked. Newer commits require their own head-specific CI before merge.

## Strict spectrum and nonuniformity — all delays (Lean 4.32.0)

The previously open **strict complex spectral gap** and **geometric
eigenvector uniqueness** for the full cloned graph are now proved
directly from its actual adjacency rows, without importing a general
Perron–Frobenius theorem.

| Module | Exact kernel-checked result |
|---|---|
| [FullClonePolynomial.lean](FullClonePolynomial.lean) | Every nonzero complex eigenvector has nonzero hub coordinate; every complex eigenvalue `μ` of the full `(2n+5)×(2n+5)` adjacency matrix satisfies `μ^(2n+5)=μ+1`, for all `n≥0`. No guessed polynomial premise. |
| [FullCloneStrictGap.lean](FullCloneStrictGap.lean) | At the unique positive real root `t_n>1`, *every other* complex eigenvalue satisfies `‖μ‖<t_n`. The equality case is excluded by comparing squared complex norms. |
| [FullCloneEigenline.lean](FullCloneEigenline.lean) | Every complex eigenvector at `t_n` is its hub value times the existing explicit positive vector. Thus the leading complex eigenspace is one-dimensional (geometric simplicity). |
| [CloneRootRate.lean](CloneRootRate.lean) | `(2n+4)*(t_n-1)≤1`, and for **every** `ε>0` some delay has `1<t_n<1+ε`. Primitive graphs therefore do not yield a stage-uniform positive expansion factor from primitivity alone. |

A separate [cycle-cover argument](../../research/independent_audits/clone_strict_spectrum_and_no_uniform_expansion_20261107.md)
derives the exact characteristic polynomial
`det(λI-A_n)=λ^(2n+5)-λ-1`, and hence algebraic
simplicity of `t_n`. This determinant identity is a **written**
proof, not a kernel-checked `Matrix.charpoly` theorem. The
[independent regression](../../research/independent_audits/verify_clone_strict_gap.py)
checks 144 exact finite-field determinants plus small-n spectral gaps.
The written cycle-cover/Vieta argument additionally proves the
all-delay spectral-gap-collapse estimate
`0 < t_n - r_n ≤ 1/(n+2)`, where `r_n` is the greatest modulus of
the other full-matrix eigenvalues. Thus this family has **no uniform
spectral separation** even though every individual graph is
primitive; the Vieta step and the gap-collapse bound are not yet Lean
`charpoly`-checked. Nothing here establishes a native KKL
prime-end or edge-incidence realization.

**Passing branch CI:** [mathlib build #42402605130](https://github.com/dovvnloading/loops-research-archive/actions/runs/42402605130)
and [root research validation #42402714782](https://github.com/dovvnloading/loops-research-archive/actions/runs/42402714782).
These verify the encoded all-n theorems and the regression without
proof holes or custom axioms. New commits require their own CI.

## Verified real period-27 quadratic center (mathlib)

Three further modules reuse the core Lean sound interval certificates and
**close the real-variable period-27 parameter bridge**:

- [Period27RealCenter.lean](Period27RealCenter.lean) proves fraction-to-real
  recurrence compatibility, the ordinary calculus derivative identity
  \(P'_n(c)=D_n(c)\) for every \(n,c\), exact real endpoint signs and
  existence of a real zero of \(P_{27}\) by the intermediate value theorem.
- [Period27RealUniqueness.lean](Period27RealUniqueness.lean) transports a
  *uniform negative derivative bound* from all rational parameters to all
  real parameters via density and continuity, then uses strict
  monotonicity to prove uniqueness inside the specified dyadic bracket.
- [Period27RealExactPeriod.lean](Period27RealExactPeriod.lean) transports
  arbitrary-horizon orbit enclosures to real parameters, checks all 26
  earlier iterates are nonzero and proves that the unique real center has
  **exact minimal critical period 27** for \(x\mapsto x^2+c\).

The [full theorem dependency and scope audit](../../research/independent_audits/lean_period27_real_center_20261105.md)
explains the exact statement and why this does **not** construct KL rays,
sheets or a nonattracting source stage. The superattracting center fails
Paper 2's \(K(f)=J(f)\) requirement and no MLC gate is closed.

## General phase-memory cardinality bound (mathlib)

[PhaseMemoryCardinality.lean](PhaseMemoryCardinality.lean) imports the
root project's [all-period clock theorem](../../PhaseMemoryGeneral.lean)
and upgrades its injection statement to a finite-cardinality result:

- For every positive p,k and every finite memory type M, retaining
  the future of the **single Boolean zero-phase sensor** after a
  `Fin (p*k) → Fin p` quotient forces `k ≤ Fintype.card M`.
- `Fin r` cannot be a future-faithful memory alphabet if `r<k`.
  This holds without a chosen transition on the memory alphabet.
- For three-level periods p, p*m, p*m*n, retaining the full p*m*n
  zero-sensor future at the outer p-level needs at least m*n states.
- The original mixed-radix address with exactly k memory states
  attains the bound and carries a deterministic, correct successor
  for the full future of every observable.

These are sharp **finite symbolic information** theorems.
They are not realization theorems for KKL prime-end markings or actual
holomorphic sheets, and they do not close MLC gates.

Build this companion with `lake build PhaseMemoryCardinality`
from this weighted directory. It is part of the weighted project's
default targets and its hole/axiom CI check.

## Meaning and limitations

These are **formal proofs of encoded finite-dimensional statements**.
They provide rigorous mathematical checks of the two competing formulae,
not a formal verification of the complete Kahn–Kapiamba–Lyubich
preprint and not an unconditional proof of MLC.

Outstanding obligations:

1. Kernel-check the **exact characteristic polynomial**
   `det(λI-A_n)=λ^(2n+5)-λ-1` and its **algebraic simplicity**
   consequence using mathlib's determinant/charpoly API. The all-n
   complex root equation, strict dominance and *geometric*
   simplicity are already kernel-checked; the determinant formula
   currently has a separate written cycle-cover proof.
2. Connect the theorem to mathlib's named spectral-radius operator and
   eigenvalue spectrum API (the current characterization uses exact
   complex eigenpairs).
3. Generalize beyond the explicit five-vertex cycle-with-shortcut graph
   to arbitrary finite nilpotent-Q cross sections, proving the
   Schur/first-return spectral reduction with precise typing and
   quantifying conditions that guarantee **uniform** expansion.
4. Obtain independent expert and original-author review of the literal
   Appendix C conventions and novelty. This research does **not**
   establish that the source's main complex-dynamics result is false.
5. MLC analytic gates (marked construction, calibration, coercivity,
   rigidity) remain open. Nothing here proves MLC.

The independent [full adjacency test](../../research/independent_audits/verify_full_clone_adjacency.py)
checks 528 exact rational full-matrix residual identities. The
[spectral regression](../../research/independent_audits/verify_full_clone_spectral_radius.py)
compares numerical eigenspectra and positive roots for 34 clone
lengths. These support the all-n Lean proofs but are not substitutes.

## Reproduce

From the formalization/weighted directory, execute:

    lake exe cache get
    lake build

This workspace has its own workflow at
.github/workflows/weighted-lean.yml. The dependency-free root Lean
and Python workflow remains separate and continues to run.
