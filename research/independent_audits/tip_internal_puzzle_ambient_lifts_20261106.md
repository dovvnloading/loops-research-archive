# Actual ambient ray lifts of the second KL puzzle

**Target:** Issue #29, objective 3. **Date:** 2026-11-06.

## The new result

Let `f(z)=z^2+c_tip` be the certified nonattracting polynomial, let
`G=f^3` be its central quadratic-like return, and let `a=alpha_G` be the
positive dividing fixed point of `G`. The two **ambient f-rays** at `a` are

\[
\boxed{2/9,\ 7/9},\qquad
\boxed{\Pi_3(2/9)=2/3,\quad\Pi_3(7/9)=1/3.}
\]

This note proves their landing and eligibility, then lifts the entire
`G`-internal alpha puzzle through depth six to explicit ambient rational
angles. At internal depth six the certificate lists **64 vertices, 128
ambient rays and their 128 corresponding internal angles**. These are
actual accesses to the same points of `K3`, interpreted using the already
established Levin correspondence. The second puzzle's first-return child
has four vertices, and all four receive explicit ambient labels here.

This is not a substitution-based guess at dynamical ray labels. It uses the
actual ambient first-child domain, analytic inverse branches, the landing
part of Levin's theorem, and the finite cyclic order of the angle map.
The additional `O/xi/eta` localization markings remain a separate obligation.

## 1. Dependency order and the source theorem

The [ambient alpha-tree note](tip_puzzle_ray_tree_20261106.md) proves

\[
G=f^3:\operatorname{int}Y^6\longrightarrow\operatorname{int}Y^3
\]

is a proper degree-two polynomial-like representative with filled Julia set
`K3`, the same set as the previously certified round-disk return. That
argument uses only the ambient dividing fixed point's ray pair, the existing
complex certificate and the polynomial-like germ-uniqueness input in
**Levin, §1.2, printed p. 2**. It does not use the second-scale table below.

The earlier [KL top-puzzle audit](kl_tip_primitive_puzzle_and_localization_20261106.md)
identifies `a` as the dividing fixed point of `G`, with

\[
3/32<a<1/10,\qquad G(a)=a,
\]

and internal rays `1/3,2/3`. Its physical `f`-period is exactly three:
`f^3(a)=a`, while it is neither of the two fixed points of `f`.

The [Carathéodory/Levin audit](levin_tip_p2_carathéodory_two_scale_20261106.md)
has already established the actual map

\[
\Pi_3:\Lambda_3\longrightarrow\mathbb R/\mathbb Z,
\quad\Pi_3(8\theta)=2\Pi_3(\theta)\pmod1,
\]

where `Lambda3` consists of ambient rays landing in `K3`. We use Genadi
Levin, [*Rays to Renormalizations*](https://arxiv.org/pdf/2010.15386),
**Theorem 1**, printed p. 5, for equality of landing points and prime-end
equivalence; **Theorem 3(b),(d)**, printed p. 6, for semiconjugacy and a
monotone degree-one circle extension. All these analytic inputs remain
written/imported mathematics, not Python or Lean theorems.

## 2. Eligibility before angle identification

The depth-six **ambient** critical face has boundary pairs

\[
(43,53)/192,\quad(55,137)/192,\quad
(139,149)/192,\quad(41,151)/192.
\]

The two angles `2/9,7/9` lie strictly in this face's external arcs, and
multiplication by eight exchanges them. The checker tests strict arc
membership using the complete landed graph; neither angle is a boundary ray.

Every rational ray lands for this connected polynomial. One precise reference
is Milnor's [1991 notes](https://abel.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf),
**Theorem 18.1, Corollary 18.4 and Lemma 18.7**, printed pp. 18-2–18-4.
Strict external-arc membership first places each landing point in the
**closure** of `Y^6`. It cannot lie on the positive-potential equipotential
part of its boundary. Nor can it be a boundary vertex: the alpha-tree proof
shows that each such vertex has exactly its two listed rays, and neither
`2/9` nor `7/9` is listed there. Their landing points therefore belong to
`int(Y^6)`, and all iterates under `G` remain in that same domain because
the two angles are exchanged.
Consequently they belong to its filled Julia set `K3`. This proves
`2/9,7/9 in Lambda3` **before** using any proposed internal angle value.

Since `64 theta=theta` for these angles, semiconjugacy shows that their
internal images belong to `{0,1/3,2/3}`. The existing six-angle certificate
gives four useful brackets:

\[
\begin{array}{lll}
110/511<2/9<114/511,&
\Pi_3(110/511)=4/7,&\Pi_3(114/511)=5/7,\\
397/511<7/9<401/511,&
\Pi_3(397/511)=2/7,&\Pi_3(401/511)=3/7.
\end{array}
\]

Monotonicity on these positively oriented intervals now forces
`Pi3(2/9)=2/3` and `Pi3(7/9)=1/3`: each closed internal interval contains
exactly one of the three possible residues. There is no wrap ambiguity
because the other already certified angles fix the cyclic degree-one lift.
Levin's landing equivalence identifies both ambient landing points with the
internal dividing fixed point `a`.

### Completeness of this seed pair

Milnor's **Lemma 18.3**, printed p. 18-2 and proof on p. 18-4, implies that
all ambient rays at this periodic point are periodic with the same angle
period as `2/9`, namely six. They must therefore have angles `k/63`.
Because `a` belongs to `K3`, their angles and their images under multiplication
by eight lie in the critical face `Y^6`.

An exact enumeration of all `1<=k<63` leaves only

\[
\{2/9,\ 2/7,\ 5/7,\ 7/9\}.
\]

The middle two have angle period three, so they are excluded. This proves
that `2/9,7/9` are **all** the ambient rays at `a`, not just a subportrait.

## 3. Central pullbacks give every higher-depth landing target

Use the actual analytic inverse branches `b_0,b_1` on the ambient
critical-value slit defined in the alpha-tree note. For each ray pair landing
at a vertex `v` in the backward `G`-orbit of `a`:

1. Apply three ambient inverse steps to obtain eight pairs landing at all
   eight points of `f^(-3)(v)`.
2. Retain precisely the pairs whose angles lie in the depth-six ambient
   critical face `Y^6`.
3. Those two pairs land at the two central preimages of `v` under the
   proper degree-two map `G:Y^6 -> Y^3`.

There is no boundary ambiguity: an ambient `Y^6` vertex eventually lands at
the ambient fixed point alpha, whereas the points selected here eventually
land on the different physical period-three orbit of `a`. No ray in this
construction is a boundary ray of `Y^6`. Thus angular face membership is an
exact test for the relevant landing point being in the central domain.

The critical orbit of `f` eventually has period nine and does not enter the
period-three orbit of `a`. Hence all these inverse points are simple and
each has exactly two ambient rays. At depth `m` the retained collection has
`2^m` vertices and `2^(m+1)` rays, exactly the inverse-alpha graph of the
degree-two germ `G`. Their targets are explicitly

\[
b_{i_1\ldots i_{3m}}(a),
\]

with the recorded ambient inverse word and central-domain test at each
three-step block. The words denote actual analytic branches, not finite
stand-ins for localization sheets.

## 4. Why cyclic order uniquely determines every internal label

At internal depth `m` the entire internal angle set is

\[
T_m=\left\{\frac{u+j}{2^m}:
u\in\{1/3,2/3\},\quad 0\le j<2^m\right\}.
\]

Every selected ambient ray is eligible for `Pi3`. Its image is an internal
ray at the same physical vertex under straightening. The two rays at any
selected vertex have **different** internal images: after `m` applications
of doubling their images are the different seed angles `1/3,2/3`.
There are exactly two internal rays at each of the `2^m` vertices, by
noncritical pullback of the internal alpha pair. Thus `Pi3` restricts to a
bijection from the selected ambient rays onto `T_m`.

A monotone degree-one map restricts to a cyclic-order-preserving bijection
on a finite set where it is injective. Sort the ambient angles and `T_m`.
There is therefore just a cyclic offset to determine. The seed angle `2/9`
occurs at every depth, because `G(a)=a`, and its image is already known to
be `2/3`. That single anchor uniquely fixes the offset. The checker then
independently verifies the second seed anchor, agreement with every previous
level and **every** semiconjugacy equation

\[
\Pi_3(8\theta)=2\Pi_3(\theta)\pmod1.
\]

For comparison, a separate internal slit pullback with critical-value angle
`25/56` produces exactly the same internal pair table. That angle is the
one obtained from the orientation-reversed `G` critical-value itinerary
`100(101)^infinity` using Zakeri's signed Gray-code rule. This cross-check is
not needed to choose or authenticate the ambient labels; the argument above
already determines them from eligibility, landing and monotonicity.

## 5. Selected proof-used vertices and their actual ambient accesses

The correspondence in each row is given by the full manifest, so the order
of the two internal labels need not be the increasing order of the ambient
labels. In particular, the seed pair is reversed as an ordered pair.

| `G` puzzle depth | Internal ray pair | Ambient ray pair at the same point | Role |
|---|---|---|---|
| 0 and higher | `1/3,2/3` | `2/9,7/9` | dividing fixed point `a` |
| 1 and higher | `1/6,5/6` | `5/18,13/18` | symmetric preimage `-a` |
| 3 | `7/24,17/24` | `257/1152,895/1152` | one vertex of `V_G^0=Y_G^3` |
| 3 | `5/24,19/24` | `319/1152,833/1152` | other vertex of `V_G^0` |
| 6 | `55/192,137/192` | `131585/589824,458239/589824` | real first-child vertex |
| 6 | `139/192,149/192` | `131647/589824,163265/589824` | nonreal first-child vertex |
| 6 | `41/192,151/192` | `163327/589824,426497/589824` | real first-child vertex |
| 6 | `43/192,53/192` | `426559/589824,458177/589824` | conjugate nonreal first-child vertex |

The table describes **ambient accesses representing internal prime ends**.
Levin's theorem gives their prime-end equivalence. It does not say that the
ambient external rays themselves are the literal polynomial-like rays used
to draw the finite `G` puzzle boundaries, nor that ambient equipotential
height should be used as internal equipotential height. Internal depth six
means six `G`-steps, or eighteen physical inverse `f`-steps from `a`; it is
not depth six in the original ambient alpha puzzle.

All two-sided angular sectors and cyclic orders here are available for a
subsequent marked construction. The selected obstacles, based path classes
and `O/xi/eta` designations must still be specified before claiming
naturality on those marked localization surfaces.

## 6. Reproduction and review boundary

```sh
python research/independent_audits/verify_tip_puzzle_ray_tree.py --check-manifest
python research/independent_audits/verify_tip_internal_ray_lifts.py --check-manifest
```

The [second exact manifest](../../results/tip_internal_ray_lifts.json) records
all vertices at all seven depths, ambient branch words, minimal return times
to `a`, paired ambient/internal angles, all cyclic orders and critical-face
membership. The second checker uses no floating point. It verifies every
eight-to-two central inverse selection, the complete finite angle bijections,
the independent internal slit table, and forward dynamics.

The analytic inputs and the new landing deductions above are written
mathematics. The finite rational certificate does not formalize them.
No external specialist has reviewed this new deduction. The source-locked
465-entry ledger, H1–H4, UPTCR and MLC status are unchanged.

**AI disclosure:** OpenAI GPT-6 assisted the proof derivation, source comparison,
exact checker and table. The cited authors are responsible for their original
theorems, not for this new application; no endorsement or human verification
is represented.
