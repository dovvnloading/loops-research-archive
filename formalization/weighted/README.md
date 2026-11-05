# Exact weighted two-gate spectral reduction (Lean + mathlib)

This is an independently pinned research workspace, not a replacement for
the existing core-Lean modules. It uses Lean 4.32.0 and mathlib v4.32.0,
with a complete transitive Lake manifest.

## Mathematical statement

Previously verified clone-graph proofs establish exactly one first-return
path of each type, for every delayed clone length n >= 0:

| Source to target | Base return length | Delayed length | Count |
|---|---:|---:|---:|
| e to f | 2 | n+2 | 1 |
| e to f | 3 | n+3 | 1 |
| f to e | 2 | n+2 | 1 |

No other first returns occur. The resulting base first-return matrix is

\[
H(t)=\begin{pmatrix}
0&t^{-2}+t^{-3}\\
t^{-2}&0
\end{pmatrix}.
\]

The parameterized eigenproblem is \(H(t)v=t^n v\).
The theorem in [WeightedReturn.lean](WeightedReturn.lean) is:

For \(t\ne0\) and \(n\in\mathbb N\), a vector \(v=(e,f)\) with \(f\ne0\)
satisfies \(H(t)v=t^n v\) **if and only if**
\[
\boxed{t^{2n+5}=t+1}.
\]

The proof explicitly clears denominators and eliminates gate coordinates.
When \(t>0\) satisfies the scalar equation, it also constructs the
positive eigenvector \(v=(t^{n+2},1)\). This is an exact quantified
Real-number result, not a numerical interpolation.

## Boundary

This verifies the **weighted eigenproblem and exact polynomial identity**.
It does not yet certify the Perron spectral radius, a positive-root
existence theorem, a full-clone matrix reduction, or any MLC gate.
The coefficients have already been verified in the five core-Lean graph
modules, but they are not yet imported into the new mathlib workspace
as a single explicit theorem dependency chain.

Do not represent this as a proof of MLC or as peer-reviewed confirmation
of the proposed issue in the Kahn–Kapiamba–Lyubich preprint.

## Reproduce

From this directory, run:

    lake exe cache get
    lake build

The GitHub workflow at .github/workflows/weighted-lean.yml runs the
mathlib-backed checks and rejects proof placeholders and custom axioms.
The existing core-Lean and Python validation workflow remains intact.

## Next tasks

1. Formally relate the full-clone adjacency eigenproblem to the weighted
   first-return equation, with exact row/column conventions.
2. Show that the positive eigenvalue is the Perron spectral radius and
   prove existence/uniqueness of its positive scalar root.
3. Encode the competing positive-power operator in Appendix C and prove
   the exact mathematical incompatibility at t > 1.
4. Derive all-delay quantitative bounds and ultimately a general
   nilpotent-Q Schur reduction with explicitly typed hypotheses.

These are finite-dimensional mathematical obligations. MLC remains open.
