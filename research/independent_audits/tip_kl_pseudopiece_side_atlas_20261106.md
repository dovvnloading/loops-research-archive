# An actual ordinary KL side atlas and finite side collisions at the two tip stages

**Date: 2026-11-06. Target: Issue #29, the source side/access interface.**

The two landed ray trees determine the actual ordinary Kahn–Lyubich
pseudo-piece sides for `P`, `Q_L`, `Q_R`, `V^0=Y^3` and the terminal first
child `W=Y^6`, at both the `f` and `G=f^3` stages. This note gives their
gluing intervals, tile tags, winding normalization and physical ambient
endpoint representatives. It also constructs same-root holomorphic
immersions into the actual period-three and period-nine canonical
localizations. A specific pair of finite `eta/xi` side points collides
under a source-defined inclusion at each stage, with its common image
in the target's **interior**.

These are ordinary-stage pseudo-pieces, equipped with the original KL
side definitions. The comparison is not an identification of their
entire boundaries with the native pseudo-pieces of a canonically
localized return. The collisions are within a stage; they do not supply
the protected inter-scale functor requested elsewhere in Issue #29.

## 1. Objects, sources and the meaning of a side

Use the exact algebraic tip and the connected filled Julia sets `K9⊂K3`
from the [nonattracting complex certificate](nonattracting_tip_complex_two_scale_20261106.md).
At the first stage let `F=f` and `K(F)=K(f)`; its terminal root is `K3`.
At the second stage let `F=G`, the central degree-two polynomial-like
germ of `f^3`, and `K(F)=K3`; its terminal root is `K9`. The
[terminal-nest audit](tip_kl_terminal_first_child_20261106.md) proves
`q=2,n=1`, `E0=int(Y3)`, `E1=int(Y6)`, and `chi=1` at both stages.

The analytic inputs for the finite geometry are the
[ambient slit-pullback tree](tip_puzzle_ray_tree_20261106.md) and the
[actual ambient lifts of the internal tree](tip_internal_puzzle_ambient_lifts_20261106.md).
They prove actual landing and branch pairing, rather than only an
unlinked combinatorial portrait. Their depth-six manifests contain all
the vertices used below.

The primary source is Kahn–Lyubich,
[*A priori bounds for some infinitely renormalizable quadratics: II.
Decorations*, IMS 2006/6](https://www.math.stonybrook.edu/preprints/ims06-06.pdf),
also [arXiv:math/0609046](https://arxiv.org/pdf/math/0609046): ordinary
puzzle and separator definitions in **§2.1, pp. 5–6**, the closed
separator lemma **Lemma 2.1, p. 6**, pseudo-piece gluing and its path-space
equivalence in **§3.2.1 and Lemma 3.3, pp. 11–12**, naturality in
**Lemma 3.4, pp. 12–13**, and the boundary notation in **§3.2.4, p. 13**.
These are printed page numbers.

Write `Psi_F(Y)` for the source pseudo-piece associated with an ordinary
piece `Y` of depth `m`. Each exterior component of `Y\K_Y` selects a
separate copy of the universal cover of the carrier annulus
\(A_m=\mathcal U_F^m\setminus K(F)\). The copy is
glued to the central piece along that component. KL's `lambda_i` is the
outer ideal side of this tile; `xi_i,eta_i` are the remaining inner
sides. With positive cyclic indexing,

\[
\partial_O\Psi_F(Y)=\bigcup_i\lambda_i,\qquad
\partial_J\Psi_F(Y)=\bigcup_i(\xi_i\cup\eta_i),\qquad
\partial^{v_i}\Psi_F(Y)=\eta_i\cup\xi_{i+1}.             \tag{1.1}
\]

In particular, the two sides attached to one vertex belong to
**adjacent tiles**, not to the two ends of a single tile. The source's
inclusion immersion extends continuously to the ideal closure, but its
boundary need not map into the target boundary. Section 5 exhibits this
phenomenon with exact landed accesses.

## 2. A based coordinate convention that retains all winding

Fix the stage's marked external angle, an ordinary puzzle height
`h>0`, and a larger carrier height `H=2h`.
For `f`, use its normalized Böttcher marking. For `G`, use the fixed
real-symmetric straightening and its marked external foliation. Its
normalized degree-two polynomial supplies the angle and height; pull
them back to the physical `G` plane. Choose the initial neighborhood
small enough that even the carrier neighborhood lies in the previously
certified `U3=D(0,1/4)`. The geometric puzzle is formed in the smaller
ordinary polynomial-like restriction inside that carrier, as in KL
§3.2.1. In particular, its **closed** finite equipotential boundary is
contained in the **open** carrier; it is not the carrier's boundary.

**The `G` angle-height coordinates are topological coordinates.** A
hybrid straightening does not make them a conformal Böttcher coordinate
for the physical degree-eight polynomial `f^3`. All coverings, gluing
maps and holomorphic immersions below use the physical Riemann-surface
structure. An annulus can be conformally uniformized separately; no
claim identifies its metric angle with these rational labels.

Put `h_m=h/2^m` and `H_m=H/2^m`. The geometric depth-`m` puzzle
uses height `h_m`; its carrier annulus `A_m` uses height `H_m`. In the
marked angle-height coordinates the universal cover of `A_m` has
strip coordinates

\[
(x,t)\in\mathbb R\times(0,H_m),\qquad
(x,t)\longmapsto(x\bmod 1,t).                         \tag{2.1}
\]

If an exterior component has angular interval `(a_i,b_i)`, choose its
lift with these actual real endpoints in `(0,1)`. The chosen lift can
equivalently be specified by a based path: start at angle zero and
height `h/256`, increase the angle to `(a_i+b_i)/2` at that height, and
then change height to `h_m/2`. Since `m≤6`, the entire path is in `A_m`.
This fixes the integer offset in each tile. The convention is made
separately at the two stages; it does not identify their basepoints.

The interior of the finite gluing component lifts to
`(a_i,b_i)×(0,h_m)`; its finite equipotential edge is still inside the
larger tile. The tile's ideal
sides are therefore represented by

\[
\begin{array}{c|c|c}
\text{side}&\text{coordinate interval}&\text{ends}\\\hline
\lambda_i&t=H_m,\quad -\infty<x<+\infty&\omega_i^-,\omega_i^+\\
\xi_i&t=0,\quad -\infty<x\le a_i&\omega_i^-,v_{i-1}\\
\eta_i&t=0,\quad b_i\le x<+\infty&v_i,\omega_i^+
\end{array}                                                        \tag{2.2}
\]

Here `omega_i^-` and `omega_i^+` are the two infinitely wrapping ideal
points of the strip. The real half-line convention declares which
source side is named `xi` and which is named `eta`; the cyclic incidence
(1.1) fixes its consistency with KL.

The open bottom interval `(a_i,b_i)` is glued to the central copy of
`K_Y`. It is not part of the remaining ideal `J`-boundary. Its landing
map need not be one-to-one, so this statement does not identify a
Euclidean interval with an embedded arc of the Julia set. At each
vertex, the actual pair of ray labels is

\[
\{b_i\bmod 1,\ a_{i+1}\bmod 1\}.                       \tag{2.3}
\]

The last index wraps cyclically. Formula (2.3) is precisely the common
finite endpoint of `eta_i` and `xi_(i+1)` in the glued ideal circle.
Every integer translate in (2.1) remains present. A finite list of tiles
does not replace the infinite sheet coordinate by a finite quotient.

These wrapping ends are ideal points of the **whole glued pseudo-piece**.
For `M>b_i`, the tile tail `x>M` meets neither its finite gluing component
nor any other tile; its vertical crosscuts are crosscuts of the glued
surface. The nested positive tails approach the joint
`omega_i^+=lambda_i∩eta_i`. Negative tails similarly approach
`omega_i^-=lambda_i∩xi_i`. Consequently, for every fixed interior tile
point `z`, its integer translates tend to these respective whole-piece
prime ends as the integer tends to positive or negative infinity.
This verifies the endpoint interpretation needed when a later map
uses the full tile, not just its central gluing interval.

**Justification of the ideal coordinate model.** For the normalized
polynomial the exterior is a genuine annulus in Böttcher coordinates,
and its universal cover is a strip. Its finite-height and finite-angle
prime ends give (2.2). For `G`, straightening is a quasiconformal
homeomorphism of the relevant annular neighborhood. It lifts to the
universal covers and extends to their prime ends, preserving their
cyclic order and their two wrapping ends. Thus it supplies the same
topological labels for the physical tiles. KL's gluing then removes
the open inner seam from the tile boundary and identifies the adjacent
finite endpoints as in (2.3). This proves the claimed source-side
interpretation without assuming that the transported coordinates are
conformal.

## 3. Complete finite table for the five source pieces

At either stage the marked angle intervals are the following. Indices
start at zero and increase in the displayed order.

| Piece | Depth | Exterior seam intervals `(a_i,b_i)` |
|---|---:|---|
| `P=Y1` | 1 | `(1/6,1/3)`, `(2/3,5/6)` |
| `QL` | 3 | `(7/24,1/3)`, `(2/3,17/24)` |
| `QR` | 3 | `(1/6,5/24)`, `(19/24,5/6)` |
| `V0=Y3` | 3 | `(5/24,7/24)`, `(17/24,19/24)` |
| `W=Y6` | 6 | `(41/192,43/192)`, `(53/192,55/192)`, `(137/192,139/192)`, `(149/192,151/192)` |

There are twelve exterior tiles at each stage and twenty-four in
total. Equations (2.2)–(2.3) specify all their source-labelled sides
and their adjacent-vertex incidences.

**Proof that these are the actual pieces.** Cut the complete landed
ray-pair graph at a probe angle in the indicated face. For every pair,
the open circular interval not containing the probe is its excluded
side. The maximal excluded intervals are exactly the face's boundary
pairs; the complementary intervals on the angle circle are its
exterior components. The checker performs this construction from the
whole depth-`m` tree, rather than accepting the table as its input.
For `P,V0,W` it also checks against the independently recorded critical
faces. The probes for `QL,QR` are `5/16,3/16`.

The `QL` face shares the two rays at `alpha_F` with `P`; the `QR` face
shares those at `alpha'_F`. Their angles map under multiplication by
four to the two seams of `P`. The source's unique attached univalent
pullbacks are therefore these faces. Closed disjointness is supplied
by KL Lemma 2.1 with the already verified `q=2,n=1`, not merely by the
disjointness of their interiors. At the `G` stage the source attachment
point `alpha_G=a>0` is physically on the right, so `L` and `R` must
not be read as physical left and right.

The actual ambient counterparts of every internal endpoint are listed
below. The entries in the second column correspond **in the same
order** to the two internal angles in the first column.

| Internal `G` ray pair | Actual ambient `f` representatives in that order |
|---|---|
| `1/3, 2/3` | `7/9, 2/9` |
| `1/6, 5/6` | `13/18, 5/18` |
| `7/24, 17/24` | `895/1152, 257/1152` |
| `5/24, 19/24` | `833/1152, 319/1152` |
| `41/192, 151/192` | `426497/589824, 163327/589824` |
| `43/192, 53/192` | `426559/589824, 458177/589824` |
| `55/192, 137/192` | `458239/589824, 131585/589824` |
| `139/192, 149/192` | `131647/589824, 163265/589824` |

These are the actual landing/access correspondences from the internal
ray-lift theorem. They do not identify a whole interval between two
ambient representatives with a whole internal angle interval: Levin's
monotone map can have nontrivial fibers. Nor is a physical ambient ray
the same curve as its associated internal ray. For the `f` stage, the
stage labels already are the physical ambient ray labels.

The finite maps of exterior components are also exact:

| Source map | Tile-index map | Stage time | Physical time at `f` / `G` |
|---|---|---:|---:|
| `QL→P` | `0→0, 1→1` | 2 | 2 / 6 |
| `QR→P` | `0→1, 1→0` | 2 | 2 / 6 |
| `W→V0` | `0→1, 1→0, 2→1, 3→0` | 3 | 3 / 9 |
| inclusion `W⊂V0` | `0,1→0; 2,3→1` | — | — |

The first two maps are univalent and the third has degree two. For
the dynamic maps the checker verifies both the stage angular
multiplication and the physical ambient multiplication at every
endpoint. For inclusions it checks containment of the gluing intervals
and the zero integer shift imposed by our based convention. These
interval calculations encode the maps supplied analytically by KL
Lemma 3.4; they do not prove holomorphic naturality by themselves.

## 4. Same-root immersions into the actual canonical localizations

Let

\[
C_r=f^r(K_3)\quad(0\le r<3),\qquad
D_{r,k}=f^{r+3k}(K_9)\quad(0\le r,k<3).
\]

The existing complex certificate proves that the three `C_r` are
disjoint, the nine `D_(r,k)` are disjoint, and `D_(r,k)⊂C_r`. In a
common ambient disk `U0`, put

\[
T_3=U^0\setminus(C_1\cup C_2),\qquad
T_9=U^0\setminus\bigcup_{(r,k)\ne(0,0)}D_{r,k}.          \tag{4.1}
\]

These are the marked target surfaces with distinguished roots
`K3=C0` and `K9=D_(0,0)` in the actual localization construction. Let
`L_p:(T_hat_p,K_hat_p)→(T_p,K_p)` be their canonical local covers.

**Theorem 4.1.** At either stage, for each `Y` in `{P,V0,W}`, the
ordinary pseudo-piece projection is a marked-pair morphism

\[
\pi_Y:(\Psi_F(Y),K_p)\longrightarrow(T_p,K_p),
\quad (F,p)=(f,3)\ \text{or}\ (G,9),                    \tag{4.2}
\]

with `pi_Y^(-1)(K_p)` equal to the central copy of `K_p`. There is a
unique holomorphic immersion

\[
j_Y:\Psi_F(Y)\longrightarrow\widehat T_p,
\qquad L_pj_Y=\pi_Y,                                   \tag{4.3}
\]

agreeing near the root with its canonical local section. For the
ordinary pseudo-piece inclusions among `W⊂V0⊂P`, these immersions
commute with inclusion.

**Proof: the first-stage range check.** The only points of `K(f)` on
the closed boundary of `P` are `alpha,-alpha`. The
[exact top-puzzle bounds](kl_tip_primitive_puzzle_and_localization_20261106.md),
checked again by `verify_tip_kl_puzzle.py`, give

\[
|\alpha|<1,\qquad
\operatorname{Re}C_1<-1,\qquad \operatorname{Re}C_2>9/8.
\]

Thus `C1,C2` avoid `∂P`. Each is connected and contains the real
orbit point `x1` or `x2`, respectively; these lie outside the real
spine `[alpha,-alpha]` of `P`. A connected set disjoint from the
boundary of a Jordan domain cannot enter and leave that domain.
Consequently both phases are disjoint from closed `P`. This argument
uses connectedness and boundary avoidance, not a claim that the
whole puzzle piece lies in a vertical strip. Every attached tile
projects into the carrier annulus \(\mathcal U_f^m\setminus K(f)\), so its image
avoids both phases as well.
This proves that `pi_Y` takes values in `T3` for `Y⊂P`.

**The second-stage range check.** The physical neighborhood used for
the `G` puzzle lies in `U3=D(0,1/4)` and is disjoint from `C1,C2`;
this follows from the same strict phase bounds. Therefore it avoids
every `D_(r,k)` with `r≠0`. The two remaining excluded continua are
`D_(0,1)=G(K9)` and `D_(0,2)=G^2(K9)`. The source boundary of `P_G`
meets `K3` only at `a,-a`.

The fixed point `a` cannot lie in the disjoint three-cycle
`K9,G(K9),G^2(K9)`: being fixed, it would then belong to two distinct
members. Since `G(-a)=a` and that union is forward invariant, `-a`
also lies outside it. Hence both excluded continua avoid `∂P_G`.
They contain `x3` and `x6`, respectively, with the certified bounds

\[
3/32<a<1/10<1/8<x_3,\qquad x_6<-1/10<-a.
\]

Both real points are outside the critical spine `[-a,a]`. Connectedness
and boundary avoidance again exclude the entire continua from `P_G`.
The `G` tiles project into \(\mathcal U_G^m\setminus K_3\), so they avoid these two continua
and, by their range in `U3`, all other excluded physical phases. Thus
the projection takes values in `T9`.

**Marked preimage and localization.** At either stage, a tile projects
outside `K(F)` while `K_p⊂K(F)`. Only the central copy can map to
`K_p`, and its projection is the identity. This proves the exact
preimage equality in (4.2). The terminal-nest theorem gives
`K_p⊂⊂int(W)⊂int(Y)`, so the marked root is compact and nondegenerate.

The glued pseudo-piece is a disk. To see this, use slight open collar
enlargements of the central piece with its ideal vertices omitted and
of its attaching components; the strict carrier margin makes these
available inside the source gluing. The central set is simply connected;
each simply connected tile meets it in one simply connected exterior
component, and different tiles have disjoint images in the glued
surface by KL Lemma 3.3. Van Kampen applied successively gives simple
connectivity. The nonconstant bounded projection rules
out a parabolic uniformization. Removing the full compact root gives
a connected annulus: the central complement is connected, and the
tiles are attached away from the root along connected overlaps.
Thus `(Psi_F(Y),K_p)` is already a **local marked pair**.

Kahn's [*A priori bounds … I*, §7.4.1, definitions on p. 43 and
Theorem 7.12 on p. 44](https://arxiv.org/pdf/math/0609045) localizes
every marked morphism. Since our source pair is local, its localization
is itself. Applying that theorem to (4.2) yields (4.3); the source also
states that localization preserves immersions. The canonical section
near the root fixes the lift. Uniqueness proves the asserted
commutation with inclusions. This proves the theorem. ∎

No assertion in Theorem 4.1 changes immersion to embedding. Its target
is the actual canonical marked disk. It does not say that the image
equals the native KL pseudo-piece formed from that disk, or that the
map has a continuous extension at every ideal-boundary point.

## 5. An exact collision of two finite source sides

Let `i: Psi_F(W)→Psi_F(V0)` be the inclusion immersion. Consider the
two distinct source ideal points

\[
e_0=(\text{tile }0,\eta_0,x=11/48),\qquad
e_1=(\text{tile }1,\xi_1,x=11/48).                     \tag{5.1}
\]

They exist because

\[
43/192<11/48<13/48<53/192,
\]

while both `11/48,13/48` lie in the first `V0` seam `(5/24,7/24)`.
Let `zeta_F` denote the actual landing point of the ray pair
`11/48,13/48` in the stage coordinates.

**Theorem 5.1.** At both stages, `e0≠e1`, and the continuous source
extension of `i` satisfies

\[
i(e_0)=i(e_1)=\zeta_F\in\operatorname{int}(V^0)\setminus K_p.
                                                               \tag{5.2}
\]

The inclusion also identifies the two distinct **interior** points
with tile indices zero and one, the same angle `11/48`, and height
`h_6/2`. Their common image is the point at that angle and height in
the central exterior component of `V0`.

The actual ambient labels of this common landing vertex are

| Stage | Stage pair at `zeta_F` | Physical ambient pair |
|---|---|---|
| `f` | `11/48,13/48` | `11/48,13/48` |
| `G` | `11/48,13/48` | `6665/9216,7159/9216` |

**Proof.** The two points lie in the interiors of distinct adjacent
arcs `eta_0,xi_1`. Their only common endpoint is the vertex represented
by `43/192,53/192`, so they are distinct. The included exterior
components `W_0,W_1` both lie in `V0_0`. By the based normalization,
their universal-tile maps are the same lift of the inclusion
`A6→A3`, with zero angular translation. Taking angle `11/48` and
height tending to zero in either tile therefore has the same target
limit, namely `zeta_F` in the central copy of `V0`.

At the positive height `h_6/2`, both points are outside their own
finite gluing components, since their common angle lies strictly
between those components. They belong to different embedded tiles
of `Psi_F(W)` and are distinct by KL Lemma 3.3. Both tile maps take
them to the same point of the first `V0` component, because the angle
lies in its seam and `h_6/2<h_3`. This proves the interior assertion.

The full landed ray tree places both rays of `zeta_F` strictly inside
the excluded interval `(43/192,53/192)` for `W`, and strictly inside
the first exterior interval of `V0`. Its distinct ray pair is not a
boundary pair of either piece. Hence `zeta_F∉W` and
`zeta_F∈int(V0)`. Since `K_p⊂W`, it is outside the terminal root.
This also gives the claimed continuity directly; it agrees with the
source's continuous extension in §3.2.4. The ambient pair at the `G`
stage is read from the proved internal-to-ambient landing
correspondence, not inferred from angle multiplication alone. ∎

**Corollary 5.2 (collision in the actual canonical target).** The
same-root immersion `j_W` of Theorem 4.1 extends at the two points
in (5.1), and

\[
j_W(e_0)=j_W(e_1)=j_{V^0}(\zeta_F)\in
\widehat T_p\setminus\widehat K_p.                    \tag{5.3}
\]

Indeed `j_W=j_(V0)∘i` on the interior by uniqueness of the localized
lift. The common limit in (5.2) is an interior point of the domain of
the holomorphic map `j_(V0)`. Composition therefore supplies the two
extensions in (5.3). The marked preimage equality excludes the
distinguished root from their image.

This is a finite, actual collision of two **source-labelled** side
points under a specified source-defined map. Its images are interior
points, rather than two target side markings. It is neither an
annular-deck collision relabelled as a tile collision nor a comparison
between the two scales. In particular it does not show that a
protected endpoint chosen by the program collides: such a claim would
require that endpoint's actual tile and crosscut selection.

## 6. Reproduction, dependencies and remaining interface

Run from the repository root:

```bash
python research/independent_audits/verify_tip_kl_side_atlas.py --check-manifest
```

The result is `EXACT_TIP_KL_ORDINARY_SIDE_ATLAS_PASS`. The
[machine-readable atlas](../../results/tip_kl_side_atlas.json) records
all twenty-four tiles, every seam endpoint and ambient representative,
the two half-lines, their adjacent-vertex tags, all branch and inclusion
routes, the full integer-lift convention, and both collisions. The
[checker](verify_tip_kl_side_atlas.py) calls the two original ray-tree
certificates and the top-puzzle bounds, independently extracts the
faces, and uses exact `Fraction` arithmetic throughout.

The analytic statements in Sections 2, 4 and 5 are written proofs with
the imported dependencies identified above. Python does not prove
prime-end theory, ray landing, Kahn's localization theorem or the
source naturality lemma. No new Lean proof is claimed.

The [separate boundary-access comparison](tip_localization_access_lifts_and_germ_alignment_20261106.md)
constructs the annular comparison's two open ideal intervals and
integer-valued access lifts, and identifies the physical finite puzzle
germ with the localized return sufficiently near the root. Together
with Theorem 4.1 this supplies concrete same-stage maps and finite
source sides. The remaining protected inter-scale problem still has
to specify the appropriate carrier or correspondence and its actual
chosen accesses. In particular, neither the finite atlas nor the
restricted exterior comparison `q` identifies whole canonical
pseudo-piece boundaries or supplies a filled `O/xi/eta` transport.
The separate [root-topology obstruction](tip_interval_root_and_marked_morphism_obstruction_20261106.md)
constrains any proposed filled fine-to-coarse marked morphism; it does
not forbid these same-root immersions. The
[source-type audit](tip_kl_marking_source_types_20261106.md) explains
why a canonical renormalization at `K9` still has target marking `K9`,
and why replacing that marking by the entire `K3` changes the question.

The 465-entry ledger, the global `H1_MARKED_CONSTRUCTION`,
`H2_CALIBRATION`, `H3_COERCIVITY`, `H4_RIGIDITY`, UPTCR and MLC statuses
are unchanged. The local Paper 2 standing hypotheses remain the
one-stage assertions already proved in the terminal audit.

**Attribution and AI disclosure.** The imported constructions and
theorems are due to Kahn, Kahn–Lyubich, and the authors cited in the
preceding ray and straightening audits. GPT-6 Astra Pro was materially
used for source comparison, proof development, exact code generation,
and editing. No independent human specialist review is represented
as having occurred.
