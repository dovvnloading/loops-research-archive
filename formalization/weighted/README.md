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

The [original cycle-cover argument](../../research/independent_audits/clone_strict_spectrum_and_no_uniform_expansion_20261107.md)
now has a complete Lean algebraic companion:

| Module | Exact kernel-checked result |
|---|---|
| [ClonePolynomialRoots.lean](ClonePolynomialRoots.lean) | The complex polynomial `X^(2n+5)-X-1` is separable and squarefree, has exactly `2n+5` distinct roots, and their moduli have product one. The derivative argument holds for every degree at least two. |
| [FullCloneCharpoly.lean](FullCloneCharpoly.lean) | Reuses the existing actual eigenvectors from `FullCloneRenewal` to prove `Matrix.charpoly` equality and `det(μI-A)=μ^(2n+5)-μ-1`. Proves simple characteristic roots, semisimplicity, and that all complex eigenspaces span the full space. |
| [FullCloneGapCollapse.lean](FullCloneGapCollapse.lean) | For every delay and its root `t>1`, produces an actual nonleading eigenvalue with `0<t-‖μ‖<1/(n+2)`; proves tolerance-quantified absolute and relative gap nonuniformity. |

The new determinant proof uses separability, root inclusion, and equal monic
degrees. The written cycle-cover expansion remains an independent argument.
The gap module states an actual eigenvalue witness, so no maximum or spectral
gap is assumed as an input. The sharper cubic renewal asymptotic remains
written. The [verification report](../LEAN_VERIFICATION_20261125.md) records
the exact CI evidence and remaining work. A native KKL prime-end or
edge-incidence realization is still a separate obligation.

**Verified proof revision `a9dcbb89f6a6105f36610de0be930002b01f25bb`:**
[weighted build and axiom audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45707763695)
and [root research validation](https://github.com/dovvnloading/loops-research-archive/actions/runs/45707763753)
both pass. The transitive audit covers every declaration in all 56 weighted
modules and permits only `propext`, `Classical.choice`, and `Quot.sound`.
New commits require their own CI.

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

1. Formalize the explicit positive stationary probability, affine invariant
   measure, and complete cylinder law in the clone renewal/readout notes.
   Then formalize the cubic spectral-gap asymptotic with controlled remainders.
2. Connect the already-proved complex eigenvalue and characteristic-polynomial
   statements to mathlib's named spectral-radius operator.
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

## Paper 3 attachment-defect rank ledger (2026-11-23)

[AttachmentDefectLedger.lean](AttachmentDefectLedger.lean) checks the precise
finite-dimensional rational linear-algebra consequence of Paper 3's two
attachment short exact sequences. Under explicitly supplied injective and
surjective linear maps, exactness of both sequences, and the reduced
degree-zero component-count identity, it proves

`finrank(New) + finrank(Trace) + 1 = finrank(Old) + components`

and the equivalent corrected, natural-number subtraction form, including
the essential **negative** trace-separation correction. In particular,
a connected trace with positive H¹ rank must decrease separation rank.
The file also has a finite arithmetic anti-monotonicity regression and
prints the axioms of its principal theorems.

This is **not yet a planar/Čech cohomology theorem**: the actual
Mayer–Vietoris maps, Alexander duality, finite-rank assumptions, and
geometric attachment criteria remain to be supplied and proved. It does
not modify the H1–H4/UPTCR/MLC status. See
[the scoped audit](../LEAN_RISK_REGISTER_20261123.md) and
[draft PR #111](https://github.com/dovvnloading/loops-research-archive/pull/111).

CI: [successful weighted build at commit 6a3bac5](https://github.com/dovvnloading/loops-research-archive/actions/runs/45258094941).

## Realizations on actual orbits and compact planar sets

[Period27RealKneading.lean](Period27RealKneading.lean) evaluates the sign word and all adjacent order comparisons on the real quadratic iterates in the isolated parameter bracket. [PlanarFullification.lean](PlanarFullification.lean) constructs the operator filling bounded complementary components of actual subsets of the complex plane, proves compactness on compact inputs, and applies the existing finite-packet theorem to that operator. The [proof guide](../PHYSICAL_BRIDGES_CONTRACTS.md) gives the independent hypotheses for ray landing and protected-access survival.

## Physical interval rows and clone renewal normalization

[Period27RealMarkov.lean](Period27RealMarkov.lean) proves that the archived
26-edge table has exactly the claimed whole-interval images and unique/no
preimage meanings for the actual period-27 real quadratic center. It supplies
the parameter using the independently proved existence theorem. The separate
[spectral note](../../research/independent_audits/period27_real_markov_bridge_20261123.md)
proves the three Fibonacci factors by a written cycle argument.
[FiniteMarkovFibers.lean](FiniteMarkovFibers.lean) and
[Period27FiniteFibers.lean](Period27FiniteFibers.lean) now prove the complete
finite-path/actual-inverse-fiber equivalence and matrix-power count in Lean,
for every horizon including zero. Finiteness and the closed orbit-core
column-sum count are included; outside-core preimages are outside this claim.

[FullCloneRenewal.lean](FullCloneRenewal.lean) concerns the **different** primitive
clone adjacency. It constructs the positive-eigenvector normalization, proves
nonnegative rows summing to one, computes both branch probabilities, and
constructs an actual nonzero complex eigenvector for every polynomial root.
`clone_stochastic_root_mode` packages the probability law and normalized mode
on the same real root and matrix. The
[renewal note](../../research/independent_audits/clone_renewal_clock_20261123.md)
supplies the separately written cubic asymptotic and measure-theoretic realization.
Neither Lean file postulates a native KL identification.

[FiniteMarkovCorrelation.lean](FiniteMarkovCorrelation.lean) proves the finite
stationary two-time laws, centered mode, positive second moment, normalized
correlation, and the fair holding matrix transformation.
[FullCloneCorrelation.lean](FullCloneCorrelation.lean) instantiates these
statements with the actual clone matrix, retaining the stationary positive
probability vector as an explicit premise. The explicit stationary formula,
affine invariant measure and full cylinder law are supplied in writing.
The [readout continuation](../../research/independent_audits/clone_resonant_readout_20261123.md)
then proves vanishing ordinary averaging variance, the two-rotation window,
quartic readout contrast, and the random-clock counterexamples. Those
analytic and measure-theoretic conclusions are not labeled Lean proofs.

All six modules are default targets; reproduce them with `lake build`.
Their principal declarations print their kernel dependencies in the
[PR 115 checks](https://github.com/dovvnloading/loops-research-archive/pull/115/checks).

## Reproduce

From the formalization/weighted directory, execute:

    lake exe cache get
    lake build

This workspace has its own workflow at
.github/workflows/weighted-lean.yml. The dependency-free root Lean
and Python workflow remains separate and continues to run.
