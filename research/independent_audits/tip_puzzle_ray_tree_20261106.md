# A complete ambient alpha-ray pullback table through depth six

**Target:** Issue #29, the higher-depth landed-ray part of objective 3 and the
first-child boundary check in objective 2. **Date:** 2026-11-06.

## Result and precise scope

At the exact nonattracting parameter `c_tip`, the ambient alpha puzzle has **64
distinct vertices and 128 distinct rays at depth six**. The table below and the
[complete JSON certificate](../../results/tip_puzzle_ray_tree.json) identify their
landing points by actual analytic inverse branches, their forward images,
minimal times to the fixed point alpha, cyclic ray order and the two sides cut
out by each ray pair. The construction is valid at every finite depth; the
committed rational certificate checks depths zero through six.

The critical piece `Y^3` has two vertices. Its first child `Y^6` has **four**:
two real vertices and a conjugate nonreal pair. Their boundary rays have no
overlap. Together with the existing first-return result, this gives the strict
Jordan containment `Y^6` compactly inside `int(Y^3)`. This is a property of the
actual ray/equipotential puzzle, rather than an identification of its boundary
with the round-disk representative.

The entries are **ambient** dynamical rays. They do not give the ambient lifts
of the internal rays of `G=f^3`, choose Paper 2's additional `O/xi/eta`
markings, or define a localization-sheet map between scales. Those are distinct
parts of #29. No source-locked ledger entry or global MLC claim is changed.

## 1. Inputs, source conventions and quantifiers

Write `f(z)=z^2+c_tip`, where the exact parameter is isolated in
[the Misiurewicz certificate](period27_misiurewicz_tip_ray_access_20261106.md).
Its critical point is strictly preperiodic to a repelling cycle of exact period
nine. In particular, its postcritical orbit never meets the negative fixed
point

\[
\alpha=\frac{1-\sqrt{1-4c_{\rm tip}}}{2}.
\]

The [existing source-level top-puzzle audit](kl_tip_primitive_puzzle_and_localization_20261106.md)
identifies the two rays at alpha as `1/3,2/3`. The critical-value ray

\[
R_\tau,\qquad \tau=\frac{116791}{261632},
\]

lands at `c_tip`, by Zakeri's **Theorems 3.1 and 3.3**, in
[*External Rays and the Real Slice of the Mandelbrot Set*](https://www.math.stonybrook.edu/preprints/ims02-02.pdf),
printed pp. 8–9, applied in the tip certificate. These are landing inputs, not
inferences from agreement between angle words.

We use the normalized Böttcher coordinate at infinity. Milnor,
[*Dynamics in One Complex Variable*, 1991 notes](https://abel.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf),
**§18, printed p. 18-1**, defines this normalization and gives
`f(R_theta)=R_(2 theta)`. **Lemma 18.7**, pp. 18-3–18-4, gives the
corresponding landing relation. The puzzle convention is Kahn–Lyubich,
[*Decorations*](https://www.math.stonybrook.edu/preprints/ims06-06.pdf),
**§2.1, printed pp. 4–5**: choose any positive ambient equipotential height
`h`; the depth-`m` graph uses its preimage of height `h/2^m` and all rays in
`f^(-m)({R_(1/3),R_(2/3)})`. Pieces are closed Jordan puzzle disks in that
source convention. The earlier audit verifies that the critical orbit avoids
the graph.

**Theorem (all finite pullbacks, with a finite certificate).** For every integer
`m>=0` and every `h>0`, apply the inverse rule in §2 recursively to the pair
`{1/3,2/3}` exactly `m` times. The resulting `2^m` pairs land at the
`2^m` distinct points of `f^(-m)(alpha)`, with exactly two rays at each point.
Their cyclic order and pairings describe the depth-`m` puzzle graph. The
machine-readable table verifies every rational operation used for `0<=m<=6`.

## 2. An analytic inverse rule, not an assumed pairing rule

Put `kappa=tau/2` and remove the actual landed critical-value ray:

\[
S=\mathbb C\setminus\bigl(R_\tau\cup\{c_{\rm tip}\}\bigr).
\]

The removed set is a simple proper arc from `c_tip` to infinity. Thus `S` is
simply connected and avoids the only critical value of `f`. Equivalently,
`z-c_tip` has a holomorphic square root on `S`. Its two square roots define
holomorphic inverse branches `b_0,b_1` of `f` on `S` with disjoint images.
The boundary rays of these images have angles `kappa,kappa+1/2` and land at
the critical point. Normalize `b_0` as the branch whose image meets the angular
semicircle

\[
I_0=(\kappa,\kappa+1/2)
\]

near infinity, and `b_1` as the other branch, with the complementary open
semicircle `I_1`. Angles are always taken modulo one. These are inverse
branches on actual slit domains in the dynamical plane.

For an angle `theta` different from `tau`, its two preimages are `theta/2`
and `(theta+1)/2`. Exactly one belongs to each `I_i`. Define

\[
L_i(\theta)=\text{the unique member of }
\{\theta/2,(\theta+1)/2\}\cap I_i.
\]

Suppose the two rays of a pair `{a,b}` land at a point `v` in the backward
orbit of alpha. The point `v` is different from `c_tip`: otherwise the critical
orbit would eventually land at alpha, contradicting its eventual exact period
nine. Both rays and `v` are therefore in `S`. Continuity of the analytic
branch at `v` proves that

\[
R_{L_i(a)},R_{L_i(b)}\quad\hbox{land at }b_i(v).
\]

The identification of the lifted curves with these particular external rays
uses the Böttcher identity near infinity and unique path lifting. This proves
the **pairing**, not just the fact that individual rational rays land.

Iterate the rule. Every point in `f^(-m)(alpha)` avoids the critical point at
all intermediate times, since a critical encounter would put alpha on the
postcritical orbit. Consequently `f^m` has `2^m` simple preimages of alpha.
The recursive branches exhaust them. Any additional ray at one of these
points would map to a ray at alpha; each of those two rays has exactly one
lift ending at the selected simple preimage. Hence there are exactly two rays
there. This proves the theorem by induction.

The target notation in the JSON is literal:

\[
b_{i_1\cdots i_m}(\alpha)
  =b_{i_1}\circ\cdots\circ b_{i_m}(\alpha).
\]

These are algebraic roots of `f^m(z)=alpha`, selected unambiguously by analytic
branch domains. No floating-point root ordering or plotted ray tracing is
needed. A point can recur in tables at several depths because alpha is fixed;
`first_depth` records its minimal preperiod to alpha. Its **point** period is
one, whereas its two rays have eventual angle period two.

## 3. Critical faces and the first child

The four actual rays at `0`, from the existing tip certificate, have angles

\[
\frac{116791}{523264},\quad\frac{144841}{523264},\quad
\frac{378423}{523264},\quad\frac{406473}{523264}.
\]

Each vertex ray pair, completed by its landing point, separates the plane.
All four critical accesses lie on the same side, since none of the graph's
vertices is `0`. Thus the critical face can be recovered without guessing a
real-line picture: cut the angle circle at the first critical access, take for
each pair the open angular interval on the side away from that cut, and keep
the intervals maximal under inclusion. Their pairs are exactly the vertices
on the critical face. The checker verifies that none of these excluded
intervals contains any of the other three critical accesses.

Pairwise unlinkedness is checked for every pair of vertices at each depth.
For the actual graph it follows also from disjointness of external rays and
distinctness of their landing points. The order at infinity and these ray
pairings determine the faces by planar separation. Straight chords used in
this combinatorial calculation do not stand for the shapes of physical rays.

| Puzzle depth | All vertices | All rays | Critical-piece boundary pairs, in cyclic face order |
|---|---:|---:|---|
| 0 | 1 | 2 | `(1/3,2/3)` |
| 1 | 2 | 4 | `(1/3,2/3)`, `(1/6,5/6)` |
| 2 | 4 | 8 | same two vertex pairs, at a lower equipotential |
| 3 | 8 | 16 | `(7/24,17/24)`, `(5/24,19/24)` |
| 4 | 16 | 32 | `(11/48,13/48)`, `(7/24,17/24)`, `(35/48,37/48)`, `(5/24,19/24)` |
| 5 | 32 | 64 | same four vertex pairs, at a lower equipotential |
| 6 | 64 | 128 | `(43/192,53/192)`, `(55/192,137/192)`, `(139/192,149/192)`, `(41/192,151/192)` |

At depth four, `(11/48,13/48)` and `(35/48,37/48)` are conjugate vertices,
each nonreal. If either vertex were real, conjugation would supply two more
rays there, contradicting the exactly-two-ray result. This disproves the
tempting rule of pairing every rational angle with `1-theta` at every depth.

At depth six, `(43/192,53/192)` and `(139/192,149/192)` are likewise a
nonreal conjugate pair. The remaining two vertices are real: their ray pairs
are invariant under conjugation, so uniqueness of landing fixes the vertex.

The earlier source-level audit proves that the first return of `0` to `Y^3`
is at physical time three. The central first child is therefore `Y^6`.
Its eight boundary angles are disjoint from the four boundary angles of
`Y^3`; under multiplication by eight they map onto those four angles, each
exactly twice. The source gives nested closed Jordan pieces. Their
equipotential parts have different positive heights, their ray parts cannot
intersect at positive potential, and their distinct vertex pairs cannot land
at the same point. Their boundaries are consequently disjoint. Hence

\[
\boxed{Y^6\Subset\operatorname{int}(Y^3).}
\]

The comparison with positive-potential arcs needs this last detail: rays of
`Y^6` have height at most `h/64`, strictly below the outer equipotential
`h/8`; the outer rays are distinct from all inner rays. Thus there is no
ray/equipotential crossing between the two boundaries. The proper degree-two
first-return map follows from KL §2.2's central-child construction. Terminal
nest identification requires the accompanying argument about the entire
critical orbit; the finite angle table alone does not supply that argument.

**Filled-Julia identification used by the next ray table.** The already
certified `K3` is compactly contained in `int(Y^3)`, contains `0`, and is
invariant under `f^3` (the existing top-puzzle audit proves these facts).
Consequently it lies in the central component `int(Y^6)` of the preimage:
connectedness places the whole set in the component containing `0`. In
particular the entire critical orbit of the first-return map stays there,
so its polynomial-like filled Julia set is connected. It has the same filled
Julia set `K3` as the round-disk representative. The precise germ-uniqueness
input is the equivalence of polynomial-like representatives in **Levin,
[Rays to Renormalizations](https://arxiv.org/pdf/2010.15386), §1.2, printed
p. 2**, which cites McMullen's Theorem 5.11: the maps agree near `K3`, and
the component of their target intersection containing `K3` contains that
whole connected set. This is an imported analytic uniqueness theorem; the
angle checker does not prove it. This identification uses only the ambient
alpha table and the prior complex certificate, not the second-scale ray
table.

## 4. Prime ends, sides and the remaining marking obligation

For each ray in the table, its normalized external angle identifies its
ambient prime end in the complement of `K(f)`. For a pair `(a,b)`, the two
ordered angular intervals `(a,b)` and `(b,a)` select the two complementary
components of the completed ray pair. Both ordered endpoint lists are
recorded in `ccw_sector_endpoints`. This supplies genuine geometric side
information with an explicit orientation convention.

It does **not** identify those two sides with `O`, `xi`, or `eta` in a
specified marked localization surface. The manifest deliberately records
`localization_O_xi_eta: null`. Those labels depend on which obstacles,
protected accesses and based paths the proposed localization comparison uses.
An ambient prime end does not by itself define a prime end of every deleted
or covered surface appearing later.

## 5. Reproduction, independent checks and trust boundary

```sh
python research/independent_audits/verify_tip_puzzle_ray_tree.py --check-manifest
```

The dependency-free checker uses only exact integers and fractions. Besides
regenerating the committed table, it independently checks each complete
inverse-angle set against the closed formula

\[
\left\{\frac{a+j}{2^m}:a\in\{1/3,2/3\},\ 0\le j<2^m\right\},
\]

pairwise noncrossing, conjugation, antipodal symmetry, reconstruction from
every branch word, every forward ray arrow, the critical faces and the
eight-to-four first-return boundary map. It also checks agreement with the
previously named depth-three pairs. The JSON retains every vertex, including
vertices outside the critical pieces.

The **written slit-domain argument** is what proves landing and pairing. The
Python certificate checks the finite rational consequences. Neither it nor
the existing Lean arithmetic formalizes the analytic inverse branches or the
source puzzle topology. Independent mathematical specialist review has not
occurred.

**Attribution and AI disclosure:** the new derivation, exact checker and table
were prepared with OpenAI GPT-6 assistance. Zakeri, Milnor and Kahn–Lyubich
are credited for the explicitly imported inputs. No human review, source-author
endorsement, or global MLC conclusion is asserted.
