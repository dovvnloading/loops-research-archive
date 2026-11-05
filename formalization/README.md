# Formal proof program — Lean 4

The formalization is a **separate verification track**. A successful Lean build checks the exact encoded statements; it does not certify that the encoding matches all hypotheses of a cited analytical theorem. Mandelbrot Local Connectivity remains open.

## Verified graph formalization (2026-11-05)

The repository pins **Lean 4.32.0**, with three source files compiled by Lake and GitHub Actions.

1. [LoopsFormal.lean](../LoopsFormal.lean) proves that the two-state operator with matrix
   \[
   R=\begin{pmatrix}0&2\\1&0\end{pmatrix}
   \]
   has no strictly positive power, for any natural exponent.

2. [CloneGraph.lean](../CloneGraph.lean) defines every length-\(n\) delayed clone of the five-vertex graph, in the exact vertex order
   \[
   e_0,\ldots,e_n,b,a,f_0,\ldots,f_n,c.
   \]
   Every edge is a cycle edge except the shortcut \(e_n\to a\). **For all \(n\ge0\)** it constructs a common walk length \(T=2(2n+5)^2\) between every ordered pair of vertices, hence proves that each clone is primitive. It additionally constructs walks of lengths \(n+2,n+3\) from gate \(e_0\) to \(f_0\), and of length \(n+2\) from \(f_0\) to \(e_0\).

3. [FirstReturn.lean](../FirstReturn.lean) defines a first-return path to a gate as one avoiding **both gates** at all intermediate vertices. It proves that no first return from a gate to itself exists, that \(e_0\to f_0\) first returns have length **only** \(n+2\) or \(n+3\), and that \(f_0\to e_0\) first returns have length **only** \(n+2\). It constructs gate-avoiding path witnesses of all three permitted lengths.

**Passing CI:** [GitHub Actions run #42021592679](https://github.com/dovvnloading/loops-research-archive/actions/runs/42021592679). The build uses Lean 4.32.0 and includes a proof-placeholder rejection check.

### The explicit primitivity certificate

Let \(L=2n+5\), \(M=2L\). For a source vertex at index \(u\) and target at index \(v\), set \(a=L-u\), \(b=v\), and \(d=a+b\), so \(d\le M\). Travel \(a\) edges to \(e_0\); use \(d\) shortcut cycles of length \(L-1\) and \(M-d\) ordinary cycles of length \(L\); then travel \(b\) edges to \(v\). The common length is

\[
a+d(L-1)+(M-d)L+b=ML=2L^2.
\]

Lean checks the complete construction, including all bounds and path compositions.

## Remaining formal obligations

**Exact return-path multiplicities:** The currently verified support theorem classifies possible first-return lengths, but does not yet prove uniqueness of the edge-occurrence path at each allowed length. A typed path-count proof is required to obtain the return matrix \(R\) directly from the graph instead of taking it as a separate explicit operator.

**General spectral theorem:** A pinned compatible mathlib version could support formalization of weighted first-return matrices, Schur-complement elimination, Perron–Frobenius arguments, and the two-sided finite-clone estimates. The sign of return-length exponents must be checked against explicitly declared source/target matrix conventions.

**Longer-term topology:** Paper 1's abstract covering-space arguments and Paper 3's prime ends and compacta cohomology are separate substantial formalization tasks. No open MLC gate has been closed by the finite graph work.

## Reproduce

From the repository root, run the command:

    lake build

The relevant files are lean-toolchain, lakefile.toml, lake-manifest.json and .github/workflows/lean-proofs.yml. Do not promote research obligations based only on a passing build; specification review and independent expert review remain distinct requirements.
