# The exterior support condition in the terminal rigidity argument

Date: 2026-11-23  
Base revision: `ed64c7ad839dcc8b799d53379434f892fdc92a2c`  
Status: explicit counterexample to a weak normalization, and a corrected
conditional rigidity theorem. No no-line-field theorem for an open
parameter class is proved here.

AI disclosure: GPT-6 Astra Pro was used for proof search, source comparison,
drafting, and exact symbolic verification. No new human mathematical
verification is represented.

## 1. The exact inference to make explicit

[UPTCR-6 and its terminal proof](../../mlc_unified/mlc_closure_proposition.md)
and [CV-4 in the cross-validation](../../mlc_unified/uptcr_cross_validation.md)
use a global quasiconformal conjugacy “normalized at infinity”, an
invariant limiting Beltrami coefficient, and absence of invariant line
fields to conclude that the conjugacy is conformal.

In the standard dynamical usage, the no-invariant-line-field assertion is
an assertion **on the Julia set**. To make the indicated argument valid,
the Beltrami coefficient must first be shown to vanish on the Fatou set.
For the periodically repelling connected case, the Fatou set is just the
basin of infinity. Agreement there with the normalized Böttcher conjugacy
provides exactly the required vanishing.

Merely fixing infinity, or even fixing three points of the sphere, does
not provide it. If “normalized at infinity” is already intended to mean
agreement with the Böttcher conjugacy on an exterior neighborhood, the
repair below makes that intended premise explicit; it does not contradict
that stronger interpretation.

Conversely, interpreting “no invariant line fields” as an assertion on
the whole sphere would be too strong: the basin of infinity itself
carries invariant measurable line fields. The issue is their support.

## 2. Exact Chebyshev self-conjugacy

Let

\[
 p(z)=z^2-2,\qquad J(w)=w+w^{-1}\quad(w\in\mathbb C^*).
\]

The map `J` has two inverse values `w` and `1/w`, and

\[
 p\circ J(w)=J(w^2).
\tag{2.1}
\]

For any `a > 0` set

\[
 R_a(w)=w|w|^{a-1}.
\]

The radial stretch satisfies

\[
 R_a(1/w)=1/R_a(w),\qquad
 R_a(w^2)=R_a(w)^2.
\tag{2.2}
\]

The first identity makes the following definition independent of which
inverse of `J` is selected:

\[
 h_a(J(w))=J(R_a(w)),\qquad h_a(\infty)=\infty.
\tag{2.3}
\]

### Proposition 2.1

The map `h_a` is a quasiconformal homeomorphism of the sphere, with
dilatation `max(a,1/a)`. It commutes with `p` and fixes the entire Julia
set `[-2,2]` pointwise. If `a != 1`, it is not conformal.

#### Proof

The descent in (2.3) is continuous. Its inverse is `h_{1/a}` because
`R_{1/a}` is inverse to `R_a`. Thus it is a homeomorphism. Away from
the two critical values `+2,-2` of `J`, a conformal inverse branch of
`J` exhibits `h_a` as a conformal change of coordinates of `R_a`.
The radial stretch is quasiconformal, since

\[
 (R_a)_w=\frac{a+1}{2}|w|^{a-1},\qquad
 (R_a)_{\bar w}=\frac{a-1}{2}w^2|w|^{a-3},
\]

so

\[
 \mu_{R_a}(w)=\frac{a-1}{a+1}\frac{w}{\bar w}.
\tag{2.4}
\]

Its dilatation is `max(a,1/a)`. The continuous homeomorphic extensions
at the finitely many omitted points are quasiconformal by removability
of isolated points for bounded quasiconformal distortion. This includes
infinity in its local coordinate.

Equations (2.1)--(2.2) give

\[
 h_a\circ p\circ J
 =J\circ R_a\circ(w\mapsto w^2)
 =J\circ(w\mapsto w^2)\circ R_a
 =p\circ h_a\circ J.
\]

Surjectivity of `J` gives `h_a p = p h_a`. On `|w|=1` the radial
stretch is the identity. Since `J` maps the unit circle onto `[-2,2]`,
`h_a` fixes that interval pointwise.

When `a != 1`, the coefficient (2.4) is nonzero on an open set, so
`h_a` is not conformal. For example, with `a=3`,

\[
 h_3(5/2)=h_3(J(2))=J(8)=65/8\ne5/2.
\tag{2.5}
\]

It nevertheless fixes `0`, `1`, and infinity. QED.

The Julia set of `p` has planar measure zero and therefore supports no
measurable invariant line field on a set of positive area. The example
thus satisfies:

* a global quasiconformal dynamical conjugacy;
* a fixed normalization at `0,1,infinity`;
* pointwise preservation of all Julia markings;
* preservation of every external ray angle; and
* no invariant line field on its Julia set.

Its conjugacy is still nonconformal. The changing coordinate is the
external potential: it is multiplied by `a`.

This disproves the inference from those listed hypotheses to conformity
of the *chosen conjugacy*. It is not a counterexample to parameter
rigidity: the two polynomials in the example are the same. It also is
not an infinitely renormalizable counterexample to MLC or to a fully
specified UPTCR theorem.

## 3. Why the support cannot be ignored

In the `w`-coordinate the unit-modulus Beltrami tensor

\[
 \nu(w)=\frac{w}{\bar w}
\]

satisfies

\[
 \nu(w^2)\frac{\overline{2w}}{2w}
 =\frac{w^2}{\bar w^2}\frac{\bar w}{w}
 =\nu(w).
\tag{3.1}
\]

Hence it is invariant on the exterior disk. Pulling it back through
the Böttcher map of any polynomial with connected filled Julia set
gives an invariant line field on its basin of infinity. This is why
the dynamical no-line-field hypothesis is ordinarily restricted to
the Julia set.

For a global quasiconformal conjugacy, invariance of its Beltrami
coefficient alone does not locate the coefficient's support. The
Chebyshev example locates it entirely in the Fatou set.

## 4. Corrected terminal theorem

### Theorem 4.1: externally conformal rigidity

Let `p_c(z)=z^2+c` and `p_d(z)=z^2+d` have connected filled Julia sets
with `K_c=J_c` and `K_d=J_d`. Let `h` be a global quasiconformal
conjugacy from `p_c` to `p_d`, fixing infinity. Assume:

1. on `C \ K_c`, it equals the normalized Böttcher conjugacy

\[
 h=\phi_d^{-1}\circ\phi_c;
\tag{4.1}
\]

2. `p_c` supports no invariant measurable line field on a
   positive-area subset of `J_c`.

Then `h` is the identity and `c=d`.

#### Proof

The map in (4.1) is conformal, so `mu_h=0` almost everywhere off
`J_c`. Differentiating `h p_c = p_d h` in the quasiconformal sense,
away from the finite critical set and null sets, gives

\[
 \mu_h(z)=\mu_h(p_c(z))
             \frac{\overline{p_c'(z)}}{p_c'(z)}.
\tag{4.2}
\]

If `mu_h` were nonzero on a set of positive measure, its support
would lie in `J_c` modulo a null set. Normalize it there by its
modulus. Equation (4.2) would give an invariant line field on that
positive-measure set, contradicting assumption 2. Therefore `mu_h=0`
almost everywhere on the sphere, and `h` is conformal.

A conformal sphere homeomorphism fixing infinity is affine:
`h(z)=Az+B`, with `A != 0`. Comparing coefficients in
`h p_c = p_d h` gives

\[
 A=A^2,\qquad 2AB=0,\qquad Ac+B=B^2+d.
\]

Thus `A=1`, `B=0`, and `c=d`. QED.

If bounded Fatou components are allowed, replace (4.1) by the
requirement that `h` be conformal on the entire Fatou set, or supply
the relevant conformal internal conjugacies as well. No theorem here
deduces that extra requirement from a normalization at infinity.

## 5. Passing the exterior normalization to a limit

The following elementary condition is sufficient for the limiting
conjugacy used by UPTCR-6. Let `h_N` converge locally uniformly in
the spherical metric to the global homeomorphism `h`. Let
`B=phi_d^{-1} phi_c` on the basin of infinity. Suppose for every
compact subset `E` of that basin there is an `N_E` such that

\[
 h_N|_E=B|_E\qquad(N\ge N_E).
\tag{5.1}
\]

Then `h|_E=B|_E` for every such `E`, hence (4.1) holds. A weaker
uniform convergence `sup_E dist(h_N,B)->0` is also sufficient.
This separates the QC compactness argument from the support control.

An alternative convenient premise is agreement with the Böttcher
conjugacy on one exterior neighborhood **for an already exact global
conjugacy**. Pulling that equality back through the dynamics gives
the exterior equality, with the branch fixed by the external marking.
Merely saying that some moving far-out neighborhood is normalized for
each finite approximation is not the compact-exhaustion condition
(5.1) and should not silently be substituted for it.

## 6. Proposed precise replacement for UPTCR-6

The following is a mathematical wording repair, not a proof of its
antecedents:

> The finite-depth pullback conjugacies are normalized by the same
> Böttcher conjugacy on every compact subset of the basin of infinity
> once that compact subset is covered by the pullback construction.
> The compact limit therefore agrees with this conformal exterior
> conjugacy. In the periodically repelling case its Beltrami coefficient
> is supported on the Julia set. The separate no-invariant-line-field
> theorem for the controlled tower makes that coefficient vanish.
> The limit is affine; monic centered quadratic normalization gives
> equality of parameters.

The proof of the no-line-field theorem, the bounded-dilatation pullback,
the existence and marking of the limit, and the connected relative
parameter-neighborhood basis remain the original analytic obligations.
This repair prevents a false use of ordinary three-point normalization
without changing the intended conclusion of the conditional reduction.

## 7. Verification, scope, and attribution

`verify_exterior_gauge.py` checks the `a=3` conjugacy, descent,
Beltrami invariance, pointwise unit-circle boundary condition, and the
explicit nonidentity value with exact symbolic identities. The
quasiconformal descent and corrected rigidity theorem are written
proofs, not consequences of those finite checks.

Radial quasiconformal stretches, the Joukowski semiconjugacy, and the
Beltrami proof of rigidity are classical. The contribution here is an
explicit support check at the exact UPTCR-6 inference and a fully
specified repair. No new no-line-field theorem is claimed.

Prepared with GPT-6 Astra Pro assistance. Independent human specialist
review has not occurred in this session.
