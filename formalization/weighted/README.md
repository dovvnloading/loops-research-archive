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

Both Lean projects build without proof holes or custom axioms.
An additional standard-library Fraction regression checks the
negative-weight identity at 357 exact rational test points.

**Passing CI:** [mathlib build #42032197008](https://github.com/dovvnloading/loops-research-archive/actions/runs/42032197008) and the separate root Lean/Python suite.
Newer commits require their own head-specific CI check before merging.

## Meaning and limitations

These are **formal proofs of encoded finite-dimensional statements**.
They provide rigorous mathematical checks of the two competing formulae,
not a formal verification of the complete Kahn–Kapiamba–Lyubich
preprint and not an unconditional proof of MLC.

Outstanding obligations:

1. Show directly that the full (2n+5)-vertex **cloned adjacency matrix**
   has a positive eigenvector with the same eigenvalue t. The
   current graph-to-return bridge is formally checked, but the
   full-clone matrix eigenpair elimination is not yet formalized.
2. Identify the full adjacency and two-gate positive eigenvalues
   with the **Perron spectral radius**, and optionally prove the
   exact spectral-radius limit. No full Perron theorem is invoked here.
3. Generalize to arbitrary finite nilpotent-Q cross sections,
   with explicit graph orientations, types, and hypotheses.
4. Obtain independent expert and original-author review of the
   *printed source conventions* and novelty; none of these proofs
   establishes that the source's main dynamical theorem is false.
5. MLC analytic gates (marked construction, calibration,
   coercivity and rigidity) remain open and are not touched.

## Reproduce

From the formalization/weighted directory, execute:

    lake exe cache get
    lake build

This workspace has its own workflow at
.github/workflows/weighted-lean.yml. The dependency-free root Lean
and Python workflow remains separate and continues to run.
