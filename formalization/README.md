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

## Completed next pass: exact multiplicities and graph-derived matrix

Two additional Lean 4.32.0 modules now close the finite combinatorial path-counting gap.

- [ReturnBlocks.lean](../ReturnBlocks.lean) reconstructs the base five-vertex graph, with internal atom order (a,b,c) and gate order (e,f). It *checks all entries* of the typed adjacency blocks Q, C and D against the graph's edge relation. It proves Q²=0, computes R₂=DC and R₃=DQC, and verifies R=R₂+R₃=[[0,2],[1,0]]. It proves that the graph-derived R inherits the previous nonprimitivity theorem.
- [ReturnPaths.lean](../ReturnPaths.lean) uses a **Type-valued** inductive path data structure, rather than only the earlier Prop-valued first-return reachability predicate. It proves paths of equal source, target gate and length are equal, so their multiplicity is at most one. Combined with constructive witnesses, it proves each of the three permitted returns has exactly one concrete path for **every n≥0**, and that other first-return types have none. It also proves if-and-only-if support criteria for both cross-gate directions.

This formalization establishes the claimed integer return multiplicities **for the particular explicit cycle-with-shortcut graph**. The graph has no parallel edge occurrences, so an edge predicate uniquely identifies each actual edge. The proof does not rely on finite enumeration or unverified existential claims.

Independent [integer path-count regressions](../research/independent_audits/verify_clone_first_returns.py) enumerate all gate-avoiding edge sequences for n=0,...,64, verify the absence of cycles between gates and reproduce the same multiplicities. These are supplementary diagnostics; the Lean theorem holds for all n.

**Passing build:** [GitHub Actions run #42027021716](https://github.com/dovvnloading/loops-research-archive/actions/runs/42027021716), which builds five Lean modules and runs the expanded Python suite.

The next unproved steps are the general weighted matrix-valued renewal identity, its Perron-root reduction, and an expert source-convention check of the external complex-dynamics paper. A finite graph calculation is not a proof of Mandelbrot Local Connectivity.

## Weighted spectral extension (mathlib v4.32.0)

A **separate mathlib-backed Lean project** at
[formalization/weighted](weighted/README.md) now imports the original
five graph modules in its own kernel-checked dependency chain.

It proves for every clone length n:

- The weighted first-return eigenproblem for the **graph-derived**
  matrix \(H(t)=\bigl(\begin{smallmatrix}0&t^{-2}+t^{-3}\\
  t^{-2}&0\end{smallmatrix}\bigr)\) has a nonzero-gate eigenvector
  at eigenvalue \(t^n\) iff \(t^{2n+5}=t+1\), for \(t\ne0\).
- The competing literal positive-power return operator cannot
  have eigenvalue \(t^n\) at a real clone root \(t>1\).
- There is exactly one real root \(t>1\) for each n, lying in (1,2).
- At this root, \(t^{2n+4}<2<t^{2n+6}\).

The original weighted-return pass above concerned the two-gate
operator. A later kernel-checked extension now establishes the
positive eigenpair and complex eigenvalue modulus dominance for the
**full** cloned adjacency matrix (see below). All source interpretation
remains subject to expert review, and MLC remains open.

**CI example:** [mathlib proof build 42032197008](https://github.com/dovvnloading/loops-research-archive/actions/runs/42032197008).
Newer commits require their own green checks.

## Full cloned matrix and Perron-radius characterization

The mathlib workspace now imports the complete graph formalization
and has four further verified theorem modules:

- [FullCloneEigen.lean](weighted/FullCloneEigen.lean):
  a strictly positive eigenvector \(x_i=t^i\) for \(i\le n\),
  \(x_i=t^i/(t+1)\) for \(i>n\), satisfying all ordinary,
  shortcut and wrap adjacency equations for every delay.
- [FullCloneMatrix.lean](weighted/FullCloneMatrix.lean):
  constructs the full \(2n+5\)-vertex adjacency matrix using
  the graph's exact Edge predicate; proves the row-sum
  representation and the Matrix.mulVec eigenvector equation.
- [SpectralDominance.lean](weighted/SpectralDominance.lean):
  proves the general positive-eigenvector modulus bound
  \(\lvert\mu\rvert\le t\) for every complex eigenvalue of a
  finite nonnegative real matrix, and applies it to the clones.
- [FullCloneSpectralMax.lean](weighted/FullCloneSpectralMax.lean):
  gives a nonzero complex eigenvector of eigenvalue \(t\) for
  every cloned graph and proves **all** complex eigenvalue
  moduli are at most \(t\). Thus the unique positive
  clone root **attains the spectral radius**.

These theorems hold for all natural delays, not merely a finite
numerical range. The spectral radius is characterized in terms
of explicit complex eigenvectors; direct integration with
mathlib's named spectralRadius definition, strict spectral
gap/simplicity, and the *general* nilpotent-Q Schur reduction
are separate formalization tasks.

The matching computational suite includes 528 exact
rational adjacency-vector identities and 34 numerical full
eigenspectrum comparisons. The root Lean/Python and pinned
mathlib builds remain separate.

**Kernel check:** [mathlib run #42038972966](https://github.com/dovvnloading/loops-research-archive/actions/runs/42038972966).
A newer PR-head build is required before merging.


## New finite phase-tower formalization (2026-11-05)

[`PhaseTower.lean`](../PhaseTower.lean) and
[`PhaseTower27.lean`](../PhaseTower27.lean) formalize a general
**lossless-marking criterion** for nested finite return clocks:
a fine-phase label factors through a coarser projection **if and only if**
it is constant on every projection fiber. When the fine clock is strictly
larger, any injective fine-phase marking cannot factor through the smaller
clock. Projected clocks compose when periods divide each other, and a
separate conditional theorem transports actual physical iterates through
nested forward-invariant return sets.

At periods 3, 9, and 27, the second module constructs an exactly reversible
three-digit clock address, verifies its carry automaton, proves conjugacy
for every iterate, and checks that its period is exactly 27. These are
finite/conditional statements, **not** the KL access/sheet realization or
an MLC result.

See the [mathematical theorem and boundary note](phase-tower.md)
for the exact statements, proof structure, and reproduction instructions.

## Future-observable phase quotients and minimal memory

Two successor modules continue the finite phase-tower work:
[`PhaseFuture.lean`](../PhaseFuture.lean) proves the universal
**future-sound quotient criterion** (for surjective, transition-compatible
quotients, current-observable factorization is equivalent to preservation
of every future reading). It proves a single Boolean zero-phase sensor,
read over at most one full period, distinguishes all phases of **every**
positive-length cyclic clock.

[`PhaseFuture27.lean`](../PhaseFuture27.lean) turns this into concrete
3/9/27 memory obligations. Any augmentation of the 3-phase clock that
retains all future Boolean readings must distinguish nine states over a
single coarse fiber; a 9-phase augmentation must distinguish three.
Both bounds are met by explicit reversible encodings with completely
specified induced transitions and all-time readouts.

See [the precise future-observability audit](phase-future.md).
These are symbolic clock facts, not a KL access/sheet atlas or any
MLC global gate.

## Remaining formal obligations

**General weighted return operators:** Exact integer first-return multiplicities and the base adjacency blocks are now kernel-checked. The all-n weighted return operator, its Perron equation, and its comparison to the published conventions still require distinct theorems.

**General spectral theorem:** The explicit cloned graph's weighted eigenvalue and maximal-complex-eigenvalue characterization are kernel-checked. The remaining nontrivial generalization is a source-typed nilpotent-Q Schur/first-return theorem for arbitrary finite cross-sections, plus formal strict spectral dominance and direct use of mathlib's spectral-radius API.

**Longer-term topology:** Paper 1's abstract covering-space arguments and Paper 3's prime ends and compacta cohomology are separate substantial formalization tasks. No open MLC gate has been closed by the finite graph work.

## Reproduce

From the repository root, run the command:

    lake build

The relevant files are lean-toolchain, lakefile.toml, lake-manifest.json and .github/workflows/lean-proofs.yml. Do not promote research obligations based only on a passing build; specification review and independent expert review remain distinct requirements.
