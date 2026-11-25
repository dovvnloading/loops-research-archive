# The overlooked characteristic polynomial of the cloned graph

**Date:** 2026-11-07. **Scope:** complete complex spectral analysis of
the archive's explicitly formalized five-vertex cycle-with-shortcut
clones. This closes an internal *finite-graph* obligation. The graph is
a testbed for checking proposed return-matrix conventions. No conclusion
about actual Kahn–Kapiamba–Lyubich edge-incidence realizations, canonical
WADs, renormalization estimates, or Mandelbrot local connectivity follows.

## Lean closure, 25 November 2026

The previously open formalization steps in this dated note now have
kernel-checked companions:
[scalar separability and exact Vieta product](../../formalization/weighted/ClonePolynomialRoots.lean),
[actual-matrix characteristic polynomial, determinant, and diagonalizability](../../formalization/weighted/FullCloneCharpoly.lean),
and [absolute and relative gap nonuniformity](../../formalization/weighted/FullCloneGapCollapse.lean).
The actual eigenvector converse is reused from the earlier
[renewal module](../../formalization/weighted/FullCloneRenewal.lean).
The characteristic-polynomial proof uses separability and equal monic
degrees; the cycle-cover proof below remains an independent written argument.

The exact Lean gap statement produces, for each delay, an actual nonleading
eigenvalue with `0<t_n-‖μ‖<1/(n+2)`; the maximum-modulus formulation below
follows immediately because that maximum is at least the exhibited modulus.
The modules also prove the corresponding tolerance-quantified absolute
and relative nonuniformity. They do not define a maximum-spectrum sequence
or formalize the later cubic asymptotic.
[Verification evidence and remaining scope](../../formalization/LEAN_VERIFICATION_20261125.md).

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

In fact **every root is algebraically simple**, and the complete
matrix `A_n` is diagonalizable over `ℂ`. To see this, suppose
`p_n(μ)=p_n'(μ)=0`. Then `μ^(d-1)=1/d`; multiplying by `μ`
and comparing with `μ^d=μ+1` gives
`μ/d=μ+1`, or `μ=-d/(d-1)`. Thus `|μ|>1`,
contradicting `|μ|^(d-1)=1/d<1`. So the monic
characteristic polynomial is squarefree; its `d` complex roots
are distinct, giving a full simple spectrum and diagonalizability.

The determinant, derivative nonvanishing, and diagonalizability statements
now have the Lean proofs linked in the November 25 update. Diagonalizability
is stated as the complex eigenspaces spanning the full vector space.
The deterministic [finite-field determinant regression](./verify_clone_strict_gap.py)
remains an independent finite check. The leading-eigenline uniqueness is
also separately Lean-proved below.

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
`t_n≥1+ε` from abstract primitivity of the clone family.

### Theorem — the strict spectral gap itself collapses

The **written exact characteristic-polynomial identity above** permits
a further new conclusion, stronger than merely `t_n→1`. Write
`r_n=max{|μ|:μ≠t_n is an eigenvalue of A_n}`, counting the
other `d-1` roots with algebraic multiplicity. Because `d=2n+5`
is odd and the constant term of the monic characteristic polynomial
is `-1`, Vieta's product identity gives

[
t_n\prod_{\mu\ne t_n}|\mu|=1.
]

In particular `r_n^(d-1)≥1/t_n`, whence
`r_n≥t_n^(-1/(d-1))≥1/t_n` (as `t_n>1` and
`d-1≥4`). Combining this with the **Lean-verified** strict
spectral separation and root excess bound yields

[
\boxed{
0<t_n-r_n\le t_n-t_n^{-1/(d-1)}
\le t_n-1/t_n
<2(t_n-1)\le\frac2{d-1}=\frac1{n+2}.
}
]

Therefore

[
\boxed{\lim_{n\to\infty}(t_n-r_n)=0,\qquad
\lim_{n\to\infty}\frac{r_n}{t_n}=1.}
]

So **even though every graph is primitive and its leading root is
strictly separated for that n, the family has no stage-uniform
absolute or relative spectral gap**. This proves nonuniformity of
spectral separation in the specific full cloned-graph family, not just
of the leading eigenvalue's expansion factor.

**Trust split:** leading strictness, the eigenvalue equation, eigenline
uniqueness, root bound, exact characteristic polynomial, algebraic
multiplicities, and product identity are now Lean-kernel-checked.
The new gap theorem uses an actual nonleading eigenvalue witness at each
delay and gives both tolerance-quantified nonuniformity statements.
The displayed maximum-based sequence limits are mathematical corollaries
of the explicit bound; the new Lean files do not define that sequence.
The independent determinant regression remains supplementary. This is
not a native KKL `T_F` spectral-gap estimate.

The regression separately computes the non-leading eigenvalue modulus
for small n:

| n | d | t_n (approx.) | t_n − max other ‖μ‖ (approx.) |
|---:|---:|---:|---:|
| 0 | 5 | 1.167304 | 0.068304 |
| 2 | 9 | 1.085070 | 0.008937 |
| 10 | 25 | 1.028700 | 0.000346 |

These observations are **finite numerical diagnostics** illustrating
the independently proved all-n bound `0<t_n-r_n≤1/(n+2)` above.
The displayed numerical decay appears much faster than that crude
universal bound; no sharper rate is claimed. The exact bound is a
consequence of the characteristic polynomial and product calculation.
The November 25 Lean proof additionally supplies a strict witness bound
at every delay, as described above.

**Subsequent result, 2026-11-23.** The [renewal-clock proof](clone_renewal_clock_20261123.md)
now identifies the actual subleading conjugate pair and proves
$(2n+9/2)^3(1-r_n/t_n)\to\pi^2/2$, sharpening the above dated bound.
It separately constructs a stochastic normalization and an actual affine
interval map with the corresponding exact correlation law. The analytic
asymptotic is a written proof. The general simplicity and positive-root
dominance facts for $x^d-x-1$ already appear in Shallit and Yamron,
[*On Linear Recurrences and Divisibility by Primes*](https://www.fq.math.ca/Scanned/22-4/shallit2.pdf),
Theorem, pp. 367–368 (1984); the actual graph identification remains a
distinct part of the archive's work.

## Reproduction and trust boundary

```bash
cd formalization/weighted
lake exe cache get
lake build FullClonePolynomial FullCloneStrictGap FullCloneEigenline CloneRootRate
lake build ClonePolynomialRoots FullCloneCharpoly FullCloneGapCollapse
lake build
cd ../..
python research/independent_audits/verify_clone_strict_gap.py
```

The pinned mathlib CI builds every module and enforces a transitive
axiom allowlist for every declaration. The root workflow also checks
all standalone Lean sources and the independent determinant regression.
[Exact verification evidence](../../formalization/LEAN_VERIFICATION_20261125.md).

**Next relevant open tasks:** formalize the cubic renewal asymptotic,
the explicit stationary probability and physical measure realization,
and any uniform estimate under independently proved source-defined
geometric hypotheses. The native prime-end immersion/Wave interface
and the global MLC gates retain their separate statuses.

The November 25 formalization used OpenAI GPT-6 Astra Pro assistance.
No independent human specialist review is asserted.
