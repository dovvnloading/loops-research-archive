# The overlooked characteristic polynomial of the cloned graph

**Date:** 2026-11-07. **Scope:** complete complex spectral analysis of
the archive's explicitly formalized five-vertex cycle-with-shortcut
clones. This closes an internal *finite-graph* obligation. The graph is
a testbed for checking proposed return-matrix conventions. No conclusion
about actual Kahn–Kapiamba–Lyubich edge-incidence realizations, canonical
WADs, renormalization estimates, or Mandelbrot local connectivity follows.

## The direct scalar reduction

For each delay n≥0, the actual directed graph in
[CloneGraph.lean](../../CloneGraph.lean) has
`d=2n+5` vertices indexed `0,...,d-1`, the ordinary directed
cycle `i → i+1 mod d`, and precisely one shortcut
`n → n+2` (skipping vertex `n+1`). Let A_n be the graph's full
**row-source** 0/1 adjacency matrix, *not* its two-gate first-return
matrix or a synthetic rank-two surrogate.

For a complex eigenpair `A_n z = μ z`, every ordinary row except the
shortcut and wrap gives `z_(j+1)=μ z_j`. Thus

```
z_j = μ^j z_0                          (0 ≤ j ≤ n)
z_(n+1+j) = μ^j z_(n+1)              (0 ≤ j ≤ n+3)
```

The **two exceptional rows** become

```
(μ+1) z_(n+1) = μ^(n+1) z_0          (shortcut)
μ^(n+4) z_(n+1) = z_0               (wrap)
```

Crucially, `z_0 ≠ 0` for every nonzero eigenvector, including at
potential μ=0 or μ=-1. Multiplying these relations and cancelling the
nonzero hub coordinate yields the exact identity

[
\boxed{\mu^{2n+5}=\mu+1.}
]

**Lean certificate:** [FullClonePolynomial.lean](../../formalization/weighted/FullClonePolynomial.lean)
formalizes the complex 0/1 row sums, both chain recurrences, exceptional
rows, hub nonvanishing and the universally quantified complex polynomial
theorem, for all n and all nonzero complex eigenvectors of the *actual*
matrix. It never assumes this polynomial as a spectral premise.

## A strict gap without invoking Perron–Frobenius

The existing [SpectralDominance.lean](../../formalization/weighted/SpectralDominance.lean)
already establishes `‖μ‖ ≤ t_n` using the explicit positive
eigenvector, where `t_n>1` is the unique positive root of the same
polynomial. If `‖μ‖=t_n` then

[
|\mu+1|=|\mu|^{2n+5}=t_n^{2n+5}=t_n+1.
]

Writing `μ=a+ib`, the two norm squares give
`a²+b²=t_n²` and `(a+1)²+b²=(t_n+1)²`.
Subtract to obtain `a=t_n`, hence `b=0`. Thus **equality in
the spectral bound implies μ=t_n**, so every other complex eigenvalue
has **strictly smaller modulus**.

**Lean certificate:** [FullCloneStrictGap.lean](../../formalization/weighted/FullCloneStrictGap.lean)
checks this equality-case rigidity and its instantiation with every
nonzero complex eigenvector of the actual full adjacency matrix.

## An independent algebraic simplicity argument

There is a short exact determinant proof, not requiring an analytic
Perron theorem:

[
\boxed{\det(\lambda I-A_n)=\lambda^{2n+5}-\lambda-1.}
]

Expand by directed cycle covers. Each nonzero Leibniz term chooses
diagonal factors λ at omitted vertices and edges `-A[i,j]` forming
disjoint directed cycles. In this graph every directed cycle uses the
hub: the only simple cycles are the full ordinary cycle of length
`d` and the shortcut cycle of length `d-1`, which omits exactly the
vertex `n+1`. These two cycles overlap and cannot be selected
together. Accordingly the only terms are the all-diagonal term
`λ^d`, the full-cycle term `-1`, and the short-cycle term `-λ`.
A directed cycle of any length L contributes `(-1)^(L-1)` from its
permutation and `(-1)^L` from off-diagonal entries, totaling `-1`.

Since `p_n'(t_n)=d t_n^(d-1)-1>0`, the positive root is also
**algebraically simple**. This last determinant/derivative statement
is a *written combinatorial proof*, not yet a Lean `Matrix.charpoly`
theorem. It is independently tested by the deterministic
[finite-field determinant regression](./verify_clone_strict_gap.py).

For geometric simplicity Lean additionally proves, in
[FullCloneEigenline.lean](../../formalization/weighted/FullCloneEigenline.lean),
that every complex eigenvector at `t_n` is exactly its hub value
times the previously checked positive full vector. The proof derives
the claim directly from both chain recurrences.

## A missing quantitative caveat: primitive ≠ uniformly expanding

The positive root is larger than 1 for every n, but its excess
collapses with delay. Elementary Bernoulli arithmetic gives

[
t_n^{2n+5}=(1+(t_n-1))^{2n+5}
\ge 1+(2n+5)(t_n-1).
]

Since the left side equals `2+(t_n-1)`,

[
\boxed{0<t_n-1\le\frac1{2n+4}.}
]

Consequently **for every ε>0 there is a delay n with
`1<t_n<1+ε`**. The root estimate and this full quantifier
statement are the targets of
[CloneRootRate.lean](../../formalization/weighted/CloneRootRate.lean).

This rules out deducing a stage-uniform **Perron expansion factor**
`t_n≥1+ε` from abstract primitivity of the clone family. It does
*not* by itself prove that the separation between the first and
second eigenvalue vanishes uniformly; that is a different inequality.

The regression separately computes the non-leading eigenvalue modulus
for small n:

| n | d | t_n (approx.) | t_n − max other ‖μ‖ (approx.) |
|---:|---:|---:|---:|
| 0 | 5 | 1.167304 | 0.068304 |
| 2 | 9 | 1.085070 | 0.008937 |
| 10 | 25 | 1.028700 | 0.000346 |

These observations suggest increasingly slow spectral mixing, but are
**finite numerical diagnostics**, not an all-n proof of a gap decay
rate.

## Reproduction and trust boundary

```bash
cd formalization/weighted
lake exe cache get
lake build FullClonePolynomial FullCloneStrictGap FullCloneEigenline CloneRootRate
lake build
cd ../..
python research/independent_audits/verify_clone_strict_gap.py
```

The pinned mathlib CI runs all modules with proof-hole and custom-axiom
checks and reports `#print axioms` on the key theorems. The root
research workflow runs the independent finite-field determinant
regression. The exact determinant identity is documented with a
written cycle-cover proof but is **not** yet formalized using the
mathlib determinant or characteristic-polynomial API.

**Next relevant open task:** formalize the determinant equality and
algebraic multiplicity in Lean, and separately characterize any
uniform spectral estimate under actual source-defined geometric
hypotheses. This finite graph work does not supply the missing native
prime-end immersion/Wave bridge of Issue #40, or any MLC gate.
