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

## Meaning and limitations

These are **formal proofs of encoded finite-dimensional statements**.
They provide rigorous mathematical checks of the two competing formulae,
not a formal verification of the complete Kahn–Kapiamba–Lyubich
preprint and not an unconditional proof of MLC.

Outstanding obligations:

1. Prove **strict** complex spectral dominance and simplicity using the
   already verified primitivity of the graph, or cite an appropriate
   formal Perron–Frobenius theorem. The current proof establishes the
   non-strict modulus bound and attainment, sufficient to identify the
   spectral radius, but not a strict gap.
2. Connect the theorem to mathlib's named spectral-radius operator and
   eigenvalue spectrum API (the current mathematical characterization
   is stated directly in terms of complex eigenpairs).
3. Generalize beyond the explicit five-vertex cycle-with-shortcut graph
   to arbitrary finite nilpotent-Q cross sections and prove the
   general Schur/first-return spectral reduction with precise typing.
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
