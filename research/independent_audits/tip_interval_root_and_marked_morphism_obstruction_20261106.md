# The fine root is an interval, and no full-root Kahn morphism maps it to the coarse root

**Date:** 2026-11-06. **Target:** Issue #29's source-defined filled
localization transition. **Status:** written proof from the certified
same-parameter quadratic-like restrictions and the named classical inputs
below, with a deterministic exact phase certificate. No new Lean
formalization or independent human specialist review is represented.

## 1. Precise result

Let `f(z)=z^2+c_tip` be the certified nonattracting parameter, write
`x_j=f^j(0)`, and let `K3,K9` be the connected filled Julia sets of the
degree-two returns `G=f^3` and `H=f^9`. The [terminal-nest proof](tip_kl_terminal_first_child_20261106.md)
identifies these sets with the actual terminal KL puzzle roots.

The new conclusions are

\[
\boxed{K_9=[x_9,x_{18}],\qquad x_{18}=-x_9,}
\]

and

\[
\boxed{K_3\text{ contains an embedded four-arm star with vertex }0.}
\]

Consequently, for **any** Riemann-surface neighborhoods of these full
marked roots, there is no holomorphic Kahn marked-pair morphism

\[
g:(S,K_9)\longrightarrow(T,K_3),\qquad
K_9=g^{-1}(K_3).                                      \tag{1.1}
\]

The conclusion also holds for the corresponding rooted localization
surfaces, whose root neighborhoods are biholomorphic to the physical
ones. It does not assume that `g` is injective, is a covering, preserves
the critical point, or is one of the physical iterates. The obstruction
is the source's **exact inverse-image requirement**, not a failure of
finite angle labels to match.

There is a sharper local statement for the physical candidates:
**for every integer `n>=0`, the equality
`K9 = (f^n)^(-1)(K3)` fails already as a germ at `0`.** Shrinking the
physical source domains cannot repair the identity or `f^6` candidate.

This rules out the full-root morphism route in Kahn's category. It does
not rule out the [restricted common-exterior comparison](tip_localization_refinement_peripheral_monodromy_20261106.md),
partial protected-boundary comparisons, or a morphism whose target marked
root is also `K9`. Those have different domains or different marked sets.

## 2. Source definitions and analytic dependencies

Kahn, [*A priori bounds for some infinitely renormalizable quadratics I*](https://arxiv.org/pdf/math/0609045),
**version 3, §7.4.1, printed p. 43**, defines a marked surface `(S,A)`
using a compact, connected, full set `A`. A morphism to `(T,B)` is
holomorphic and must satisfy `A=g^(-1)(B)`. A *local cover* additionally
bijections the marked roots and covers their complements. **Theorem
7.12, p. 44**, constructs the localization functor on this category; its
proof glues an actual root neighborhood into the localization and makes
the projection biholomorphic on that neighborhood. These are distinct
conditions: the theorem cannot be applied to an exterior map merely
because it has compatible subgroup data there.

The complex-dynamical input is Douady–Hubbard,
[*On the dynamics of polynomial-like mappings*](https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf),
**Chapter I, §1, Theorem 1, printed p. 296**: a degree-two polynomial-like
map with connected filled Julia set has a quadratic straightening,
unique up to affine conjugacy. We normalize it to `Q_c(w)=w^2+c`, with
critical point `0`. The normalized quadratic parameter is then unique.
The straightening conjugates the dynamics near the filled set and maps
the entire filled set homeomorphically to `K(Q_c)`.

The parameter, strict critical preperiod 10/eventual period 9, connected
3/9 restrictions, nested invariant real intervals and disjoint physical
phases are the already established inputs in the
[tip certificate](period27_misiurewicz_tip_ray_access_20261106.md),
[complex certificate](nonattracting_tip_complex_two_scale_20261106.md),
and [terminal-first-child proof](tip_kl_terminal_first_child_20261106.md).
All statements below concern this exact parameter.

No symmetry-equivariant choice of the straightening homeomorphism is
needed for the new argument. In particular, exact equality of `K9` to
the physical interval will follow from its two endpoints and the
previously certified interval inclusion.

## 3. The inner quadratic straightening is exactly Chebyshev

The defining parameter relation and exact orbit certificate give

\[
x_{18}=-x_9,\qquad x_{19}=x_{10},\qquad x_{27}=x_{18}.
\]

The critical orbit of `H=f^9` is therefore

\[
0\longmapsto x_9\longmapsto x_{18}\longmapsto x_{18},
\]

with the first three points distinct. Its exact preperiod is two and its
eventual period is one. Let `h9` straighten `H` to `Q_d(w)=w^2+d`.
Normalization and conjugacy give

\[
h_9(0)=0,\qquad h_9(x_9)=d,\qquad
h_9(x_{18})=d^2+d,
\]

where `d^2+d` is fixed. Hence

\[
0=Q_d^3(0)-Q_d^2(0)=d^4+2d^3=d^3(d+2).
\]

The critical point is not periodic, so `d!=0`. Thus `d=-2`, and

\[
h_9(x_9)=-2,\qquad h_9(x_{18})=2.                       \tag{3.1}
\]

For completeness, `K(Q_-2)=[-2,2]` follows directly from the Joukowsky
formula. The map `J(w)=w+w^(-1)` sends `|w|>1` conformally onto the
complement of `[-2,2]` and satisfies

\[
Q_{-2}(J(w))=J(w^2).
\]

Every point outside the interval therefore escapes. Points in the
interval have the form `2 cos(t)` and iterate to `2 cos(2^n t)`, so remain
bounded. Thus `K9` is a topological arc with endpoints `x9,x18`.

The existing all-time invariant-interval proof gives

\[
I_9=[x_9,x_{18}]\subset K_9.
\]

A connected subset of an arc that contains both endpoints is the whole
arc: its image under an arc parametrization is a connected subset of a
real interval containing both endpoints. Applying this to `I9` and
(3.1) proves the exact physical equality

\[
\boxed{K_9=I_9=[x_9,x_{18}].}                           \tag{3.2}
\]

This uses neither a numerical picture nor the unsupported inference
that real postcritical points force an entire Julia set to be real.

## 4. All nine physical fine phases are exact intervals

For `D_j=f^j(K9)`, all phases are now intervals, not just continua in
the old phase enclosures. The complete list is

| Physical phase `j` | Exact interval `D_j` | Restriction of `f` | Image |
| ---: | --- | --- | --- |
| 0 | `[x9,x18]` | Two branches, unique minimum at `0` | `D1` |
| 1 | `[x1,x10]` | Decreasing | `D2` |
| 2 | `[x11,x2]` | Increasing | `D3` |
| 3 | `[x12,x3]` | Increasing | `D4` |
| 4 | `[x13,x4]` | Decreasing | `D5` |
| 5 | `[x5,x14]` | Increasing | `D6` |
| 6 | `[x6,x15]` | Decreasing | `D7` |
| 7 | `[x16,x7]` | Decreasing | `D8` |
| 8 | `[x8,x17]` | Increasing | `D0` |

The first image follows from `x18=-x9` and the unique minimum of
`f(x)=x^2+c_tip` at zero. Each subsequent interval excludes zero, so the
sign of `2x` determines its orientation. Its endpoints are the indicated
critical-orbit points; `x19=x10` and eventual period nine reduce all
later endpoint indices. The [exact checker](verify_tip_root_topology.py)
verifies every strict endpoint order, all pairwise phase gaps, and each
orientation and endpoint arrow using outward integer arithmetic at
resolution `2^-224`. The [manifest](../../results/tip_root_interval_geometry.json)
records the rational endpoint enclosures as well as the algebraic
endpoint labels.

The physical coarse phase containing `D_j` is `j mod 3`, by the earlier
nesting certificate. In particular, the fine obstacle set is exactly a
union of nine pairwise disjoint real intervals.

## 5. The outer root contains a four-arm star

The critical orbit of `G=f^3` has exact preperiod four and eventual
period three. These numbers follow from the exact physical preperiod
10 and period nine: the first multiple of three at least ten is twelve,
and advancing by three has order three on the physical nine-cycle.

Let `h3` straighten `G` to `Q_c`. Its normalized parameter is real.
Indeed, the physical restriction and its domains are invariant under
complex conjugation. Reflecting a straightening produces a straightening
to `Q_(conjugate c)`. Uniqueness for connected filled sets gives
`c=conjugate c` in the normalized quadratic family. This argument does
not require `h3` itself to commute with conjugation.

In fact

\[
-2<c<0.                                                \tag{5.1}
\]

For a real parameter below `-2`, the critical orbit escapes: its second
iterate exceeds `-c`, after which `x^2+c>x` and the positive iterates
grow without bound. The parameter `-2` has eventual critical period one,
which is excluded here. At `c=0` the critical point is fixed. For `c>0`
its orbit is strictly increasing and cannot be eventually periodic with
period three. These facts prove (5.1) from the certified orbit, without
an assumed tuning-component identity.

Put

\[
\beta=\frac{1+\sqrt{1-4c}}2\in(1,2),\qquad
s=\sqrt{\beta+c}=\sqrt{\beta(2-\beta)}>0.
\]

The real interval `[-beta,beta]` is forward invariant because its image
is `[c,beta]` and `c>-beta`. Also

\[
Q_c(iy)=c-y^2\in[-\beta,c]\qquad (|y|\le s).
\]

Consequently

\[
[-\beta,\beta]\ \cup\ i[-s,s]\ \subset K(Q_c).           \tag{5.2}
\]

The set in (5.2) is an embedded four-arm star with center zero. Its
inverse image under `h3` is such a star in `K3`, centered at the physical
critical point zero. An interval cannot contain an embedded three-arm
star, and hence cannot contain this four-arm star. To see this directly,
an embedding into a real interval would put at least two arms on the
same side of the image of the vertex; their connected images overlap,
contradicting injectivity.

Thus `K3` is not an arc. Moreover, every physical neighborhood of zero
contains points of `K3` outside the real axis: otherwise sufficiently
short initial segments of the four arms would embed in the real axis.
Since `K9` is real, these points are in `K3\K9`.

## 6. A general obstruction for marked-pair morphisms

The following elementary lemmas expose the precise source failure.

### Lemma 6.1 — a marked morphism maps its compact root onto the target root

Let `g:S→T` be a nonconstant holomorphic map between connected Riemann
surfaces. Let `A⊂S` be nonempty and compact, let `B⊂T` be connected,
and suppose `A=g^(-1)(B)`. Then `g(A)=B`.

**Proof.** The image `g(A)` is nonempty and compact, hence closed in
the Hausdorff space `B`. For `b=g(a)` with `a∈A`, take an open
neighborhood `U` of `a`. The open mapping theorem makes `g(U)` an open
neighborhood of `b`. Every point of `B∩g(U)` has a preimage in `U`, and
that preimage belongs to `A` by the exact inverse-image hypothesis.
Therefore `B∩g(U)⊂g(A)`, proving that `g(A)` is relatively open in `B`.
Connectedness of `B` now gives `g(A)=B`. ∎

No properness or finite global degree of `g` is assumed in this lemma.

### Lemma 6.2 — branching cannot pull back into an arc

Under Lemma 6.1's hypotheses, if `A` is a topological arc, then `B`
cannot contain an embedded `r`-arm star for any `r>=3`.

**Proof.** Let `b` be the star vertex. Lemma 6.1 supplies `a∈A` with
`g(a)=b`. In local complex coordinates, a nonconstant holomorphic map
has the form `g(z)-g(a)=z^d u(z)`, where `d>=1` and `u(0)!=0`.
On a small disk choose a holomorphic `d`th root of `u`; changing the
source coordinate puts the map in the form `z↦z^d`.

Shorten all `r` target arms to a coordinate disk around `b`. Each arm
minus its vertex has `d` disjoint lifts. Lifts of distinct arms are
disjoint, and all these lifts extend to `a`, since their moduli tend to
zero there. Their union is an embedded `rd`-arm star contained in
`g^(-1)(B)=A`. Since `rd>=3`, an arc cannot contain it. ∎

This is a local topological argument about arbitrary Jordan arms;
smoothness of the target star is unnecessary.

### Theorem 6.3 — no full fine-to-coarse Kahn marked morphism exists

For the actual roots `K9,K3`, there is no holomorphic map satisfying
(1.1), in any Riemann-surface neighborhoods of the full roots.

**Proof.** The source root is an arc by §3, while the target root
contains a four-arm star by §5. Lemma 6.2 excludes every nonconstant
map. A constant map has inverse image of `K3` either empty or the whole
source surface, neither of which is the nonempty proper compact arc
`K9`. ∎

Kahn's localization projection is biholomorphic on a root neighborhood
(Theorem 7.12's construction). It therefore preserves the interval and
star properties used here. The theorem applies equally to the complete
canonical localization pairs with roots `K9` and `K3`.

For *local covers* there is also an immediate obstruction in either
direction: a local cover must biject the compact roots. Such a bijection
is a homeomorphism, whereas an arc is not homeomorphic to a continuum
containing a four-arm star. The general morphism theorem above is
stronger in the fine-to-coarse direction; it does not assert the
nonexistence of every reverse marked morphism.

## 7. Every physical iterate fails even the local root condition

Theorem 6.3 already excludes every physical iterate as a morphism on a
neighborhood of the whole fine root. A separate local argument proves
that its exact inverse-image requirement fails in **every neighborhood
of zero**, before the rest of the root is considered.

* If `n` is not divisible by three, `f^n(0)` lies in a coarse phase
  disjoint from `K3`. Thus zero is in `K9` but not in
  `(f^n)^(-1)(K3)`.
* If `n=0`, every neighborhood of zero contains the nonreal points
  of `K3\K9` established in §5.
* If `n=3k>0`, the local degree of `f^n` at zero is exactly two:
  the physical critical orbit never returns to zero, so there is
  only one critical factor. The point `h3(G^k(0))` lies strictly
  inside `[-beta,beta]`. It cannot equal either endpoint, since those
  endpoints have eventual period one, while this critical orbit has
  eventual period three. Thus `K3` contains a two-sided topological
  arc through `G^k(0)`, namely a subarc of
  `h3^(-1)([-beta,beta])`. Its pullback by a local degree-two map
  is a four-arm star through zero. Such a star cannot lie in the
  interval `K9`.

In the final case one can shorten the target arc arbitrarily. Hence
the extra preimage points occur arbitrarily close to zero, giving the
claimed germ failure. The proof does not require the pulled-back
real-spine arc to be physically straight.

In particular, the earlier point witnesses against the identity and
`f^6` on entire deleted complements cannot be repaired by simply
shrinking their root neighborhoods.

## 8. Consequences for the issue and surviving comparisons

This is a **negative resolution of the full-root Kahn-morphism route**
at the exact certified parameter. There is no missing choice of basepoint,
ray, collar height or sheet representative that turns a holomorphic
`K9→K3` full-root morphism into an object of Kahn's category: the
inverse-image axiom is incompatible with the proved root topology.

It is not a claim that every comparison relevant to renormalization is
impossible. In particular:

* The common-exterior covering comparison has no filled roots in its
  domain and remains valid. Its maximal boundary extension is analyzed
  in the [access-lift note](tip_localization_access_lifts_and_germ_alignment_20261106.md).
* A finite pseudo-piece immersion whose source and target both retain
  the same marked root is a different interface. The
  [source-type audit](tip_kl_marking_source_types_20261106.md) explains
  the distinction between pseudo-puzzle sides and localization covers.
* A comparison between direct period-nine localization and iterated
  period-three localization can mark `K9` on **both** sides. The
  interval-versus-star theorem says nothing against that correctly
  matched-root construction.
* A map only between selected exterior or protected prime-end regions
  need not satisfy (1.1). Such a proposal must state its actual domain,
  marked sets and required side incidences before the present theorem
  can be applied or avoided.

No global ledger hypothesis, width calibration, rigidity theorem,
UPTCR statement or MLC claim is changed. The source-defined finite
obstruction must retain its full-root category qualifier.

## 9. Reproduction and trust boundary

```sh
python research/independent_audits/verify_tip_root_topology.py --check-manifest
python research/independent_audits/verify_tip_root_topology.py --print-json
```

The checker imports the exact tip certificate and independently computes
the stage clocks, the polynomial relation for the inner straightening,
all nine interval endpoint orders, phase disjointness, and their physical
map arrows. Its JSON manifest is deterministic. It does not claim to
compute an unknown hybrid conjugacy or to formalize the open mapping,
straightening or branched-cover arguments. Those proofs are given above.

**Attribution and review:** Douady and Hubbard supply straightening;
Kahn supplies the marked-surface category and localization theorem.
The elementary clopen-image and star-pullback arguments are written
explicitly here. OpenAI GPT-6 Astra Pro assisted proof search, source
comparison, exact computation and writing. Separate agents reviewed the
root geometry and general morphism obstruction; this is AI review, not
independent human specialist review.
