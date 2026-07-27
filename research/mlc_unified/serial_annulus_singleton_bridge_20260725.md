# Serial-annulus singleton bridge

Date: 2026-07-25  
Status: proved implication; dynamical annulus realization remains open  
Scope: separate subresearch artifact. Original manuscript and original PDFs are read-only.

## The theorem that can be closed

Let (A_0,A_1,ldots) be pairwise disjoint annuli in a bounded planar
region, nested in the sense that the inner complementary component of
(A_{n+1}) lies in the inner complementary component of (A_n). Let
(K_n) be the corresponding nested inner components and put

\[
K=\bigcap_{n\ge 0}K_n.
\]

If

\[
\sum_{n\ge0}\operatorname{mod}(A_n)=+\infty,
\tag{S}
\]

then (K) is a singleton.

This is the standard Grötzsch divergence principle. A source-locked
statement appears as Proposition 6.16 in M. Lyubich's *Conformal Geometry
and Dynamics of Quadratic Polynomials*:

<https://www.math.stonybrook.edu/~mlyubich/book.pdf>

The same source states the two ingredients used here:

1. pairwise disjoint nested subannuli satisfy the Grötzsch inequality
   (sum operatorname{mod}(A_n)le operatorname{mod}(A)) for the enclosing
   annulus (A); and
2. an annulus whose two complementary components are both non-singletons
   has finite modulus.

If (K) contained two points, an enclosing annulus bounded by a fixed outer
cross-section and (K) would have finite modulus. Grötzsch would force that
same modulus to be at least the divergent sum in (S), a contradiction.

## Exact logical repair

This closes the following implication:

```text
actual pairwise-disjoint nested annuli
+ one common end fiber in every inner component
+ divergent accumulated modulus
------------------------------------------------
=> the end fiber is a point.
```

It is stronger than the fixed-modulus finite-lift interface and is compatible
with the earlier no-go: a fixed terminal quadratic-like modulus does not give
the pairwise serial annuli required here.

## Machine-checkable model

For a round model, let (m_n>0), (S_n=sum_{j=0}^n m_j), and

\[
r_n=\exp(-2\pi S_n),
\qquad
A_n=\{r_n<|z|<r_{n-1}\}.
\]

Then

\[
\operatorname{mod}(A_n)=
\frac{1}{2\pi}\log\frac{r_{n-1}}{r_n}=m_n.
\]

For (m_n=1/(n+1)), the harmonic sum diverges and (r_n	o0), so the
nested closed disks have singleton intersection. For (m_n=2^{-(n+1)}),
the sum is finite and the intersection is a nondegenerate disk of radius
(exp(-2\pi)). The validator checks both exact formulas and finite numerical
approximations.

## Why this does not yet close the direct-decoration branch

The checked Kahn--Lyubich decoration source gives actual univalent pullbacks
and a finite separating family of pieces attached to boundary rays. It does
not, by itself, give for every infinite address:

- an annulus, rather than a pinched sector or a collection of side pieces;
- pairwise disjoint serial placement around one fixed end fiber;
- a common outer cross-section and no bypass through a side component;
- a divergent modulus sum after all root, collar, and obstacle enlargements.

Thus the new theorem closes the analytic end-collapse implication but not the
source-facing realization obligation
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION` or the global virtual bridge.
It also does not prove the prime-end cofinality obligation: a nested angular
address can still have multiple exterior sectors unless compatible inverse
lifts and cofinal crosscuts are supplied.

## Dynamic consequence for the active MLC proof

The exact remaining target can now be stated without ambiguity:

> For every proof-used direct or virtual infinite address, construct actual
> protected serial annuli/collars satisfying the hypotheses above, or prove
> an equivalent extremal-width divergence theorem with all side ports and
> bypasses audited.

Once that target is established, this bridge supplies singleton dynamical end
fibers. Parameter-side connectedness, marked rigidity, and complete mixed-tower
coverage remain separate obligations; the global MLC conjecture is not promoted
by this lemma alone.

Machine output: `serial_annulus_singleton_bridge_20260725.json`; expected status
`SERIAL_ANNULUS_SINGLETON_BRIDGE_VALID`; `original_artifacts_written=false`.

