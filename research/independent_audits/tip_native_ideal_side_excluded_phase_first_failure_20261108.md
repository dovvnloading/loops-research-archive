# A finite-angle failure on **every actual KL W ideal J-side** at the 3/9 tip

**Date:** 2026-11-08. **Status:** Source-specific negative result for the ordinary
`G=f^3` KL pseudo-piece, with exact finite data and a written topological
non-extension proof. **Not:** a proof of the full KKL proper-restriction
condition, a global interscale side functor, or the remaining based connector
words. The previous rooted puzzle-core results remain valid on their actual
domains.

## 1. Result and why it matters

PR #60 gives a canonical root-normalized holomorphic section over the entire
**geometric central disk** `W_G=int Y_G^6`, and labels eight surviving physical
rays in the four *open gluing seams*. Its `C4` incidence relation is expressly
not a map of the native KL `O/xi/eta` ideal sides. PR #37 had already proved
failure at infinitely wrapping `lambda/xi` and `lambda/eta` joints for a
specific native canonical-stage pseudo-piece comparison.

Here the failure is **at finite, non-wrapping, interior points of the actual
ordinary `G`-stage `W` ideal `xi/eta` arcs**. It uses the real critical-value
orbit and *four source-certified external G angles*, not a synthetic tile
partition or an arbitrary winding countermodel. There are explicit excluded
fine-phase landing points on **both `xi_i` and `eta_i` for every original
`W` tile `i=0,1,2,3`**. There are in fact infinitely many corresponding
integer-translated ideal points on each of the eight J-sides.

The obstruction is to a **continuous extension taking values in the actual
fine canonical localization** and commuting with its physical projection.
It does not rule out a map into a separately constructed boundary
compactification, or a restricted side interval avoiding these points.

### Theorem 1 (explicit first failure for every native W J-side)

Let `f=f_{c_*}`, `G=f^3`, and let `K9 subset K3` be the certified nonattracting
tip filled sets. Define the fine physical target and canonical localization

\[
T_9=U^0\setminus\bigcup_{(r,j)\ne(0,0)}D_{r,j},\qquad
D_{r,j}=f^{r+3j}(K_9),\qquad
\pi_9:\widehat T_9\to T_9.
\]

`D_(0,0)=K9`, `D_(0,1)=G(K9)` and `D_(0,2)=G^2(K9)` are pairwise disjoint.
Write `Psi_G(W)` for **Kahn--Lyubich's ordinary source pseudo-piece** of
the actual geometric first child `W=Y_G^6`, with *four universal-carrier
cover tiles*, as defined by KL II §3.2.1, Lemma 3.3. Let

\[
p_W:\Psi_G(W)\to U_G^6
\]

be its source projection. The merged same-root localization argument gives
a holomorphic immersion `j_W:Psi_G(W)->T_hat9` with `pi9 j_W=p_W`
on the interior, because the whole physical source range avoids the other
fine obstacles. This is not an assertion that `j_W` is globally injective.

For every original tile `i` and for **each** of its open ideal J-arcs
`xi_i^circ` and `eta_i^circ`, there are source-defined finite-angle prime
ends `e_{i,side,3}` and `e_{i,side,6}`, with **distinct** physical
limits

\[
\lim_{z\to e_{i,side,3}} p_W(z)=x_3\in D_{0,1},\qquad
\lim_{z\to e_{i,side,6}} p_W(z)=x_6\in D_{0,2}.\tag{1.1}
\]

These are bona fide inner ideal side points, not the source's removed
open gluing seams, finite W vertices, or infinite-winding tile ends.
Consequently `j_W` has **no continuous extension at any of these 16
explicit points with value in `T_hat9`**. More generally, **no** continuous
map from the interior of the same pseudo-piece to `T_hat9` commuting
with `pi9` and `p_W` can extend there, regardless of the based sheet
chosen. On each `xi_i` and `eta_i` there are infinitely many such
integer-winding translates, landing in **each** of the two excluded
fine phases.

### Corollary 1.1 (no whole-side root-preserving fine transport)

No root-compatible projection-preserving map from the whole ordinary
`Psi_G(W)` to the fine canonical surface can extend continuously *into that
surface* on **all** of any of the eight KL J-side arcs. In particular,
the four adjacent-tile **channel indices** from PR #60 cannot be
promoted to a full `O/xi/eta` ideal-side transport merely by choosing
coset representatives or proving a finite angle-permutation identity.

The corollary is stronger in *location* than a wrapping-joint-only
failure but **narrower in target category**: it concerns `T_hat9` itself.
It does not prohibit extensions into other compactifications that add
boundary points corresponding to `D_(0,1),D_(0,2)`.

### Proposition 1.2 (a positive local extension on every J-side)

The negative theorem does **not** imply that the whole `xi/eta` boundary
has to be discarded. Let `a` be the dividing fixed point of the
polynomial-like map `G` and consider the actual source rays
`1/3,2/3` landing at `a` (KL source puzzle and the merged internal
ray-lift table). Since `G(a)=a` and the three sets
`K9,G(K9),G²(K9)` are pairwise disjoint and permuted by `G`, this
fixed point belongs to none of them. It is also outside all the
other coarse phases, so **`a in Omega9`**.

Each of the four original W tiles has strict finite ideal side points

\[
\xi_i^\circ:\ x=-2/3\quad (\theta=1/3),\qquad
\eta_i^\circ:\ x=4/3\quad (\theta=1/3).\tag{1.2}
\]

These points **do** admit unique local continuous extensions of
the existing holomorphic immersion `j_W` into the actual fine exterior
`T_hat9\K_hat9`. Every integer translate far enough into a side
tail has the same local extension property (the extended images need
not coincide across different deck translates).

More generally, at **any finite source ideal J-side prime end whose
single G-ray landing target lies in `Omega9`**, a given interior
projection-preserving lift extends uniquely, at least locally among
nearby ideal points with targets remaining in `Omega9`. This is the
standard evenly-covered-neighborhood lifting argument and needs no
new selection of a relative coset. At finite ideal points whose
physical targets lie in the **removed** sets `D_(0,1)` or `D_(0,2)`,
Theorem 1 rules out extension **into the same fine surface**. The
third case, landings on the marked `K9`, is different: root versus
nonroot sheet convergence must be analyzed with the full based
monodromy and cannot be decided from the projected point alone.

Thus **each one of the eight original J-sides contains both explicitly
extendible and explicitly nonextendible finite ideal points**.
There is no contradiction with PR #60's rooted core section: that
section and the global native universal-tile boundary have different
domains and boundary objects.

## 2. The four postcritical source rays are genuine, not guessed

The source-certified 3/9 Levin table
[`results/tip_nested_full_ray_census_20261107.json`](../../results/tip_nested_full_ray_census_20261107.json)
identifies the **outer G-internal rays landing at physical `0`** as

\[
\Theta_0=\{25/112,31/112,81/112,87/112\}.\tag{2.1}
\]

This is also recorded in the full source-certified ambient-to-G internal
ray-lift argument
[`tip_internal_puzzle_ambient_lifts_20261106.md`](tip_internal_puzzle_ambient_lifts_20261106.md),
§4. The result imports the classical landing/straightening theory rather
than deriving landing from the rational residues alone.

The marked degree-two external `G` angle map is `theta -> 2 theta (mod 1)`.
Since `G(0)=f^3(0)=x3` and `G^2(0)=f^6(0)=x6`, it follows from
actual ray dynamics that the following *pairs* land at the same two
specified physical points:

| Physical point | Fine phase containing it | External `G` ray pair |
|:--|:--|:--|
| `x3=G(0)` | `D_(0,1)=G(K9)` | `25/56`, `31/56` |
| `x6=G²(0)` | `D_(0,2)=G²(K9)` | `3/28`, `25/28` |

Both landing targets are excluded from `T9`. This uses the **actual**
real exact-interval manifest
[`results/tip_root_interval_geometry.json`](../../results/tip_root_interval_geometry.json),
which identifies `D_(0,1)=[x12,x3]` and `D_(0,2)=[x6,x15]`, and proves
their pairwise separation from `D_(0,0)=K9`. There is no appeal to
pixel plotting or an assumed real-line face picture.

The right-hand table is *not* the eight-ray table of PR #60: the latter
consists of rays entering the **open W gluing seams** and landing on
`K9`, while the present four ray angles land on the **other two fine
phase intervals**. Conflating them would erase the obstruction.

## 3. Exact original-source side placement: 16 canonical witnesses

At the original `G:W` stage the source-certified open gluing seams are

\[
(a_i,b_i)=\left(\frac{41}{192},\frac{43}{192}\right),
\left(\frac{53}{192},\frac{55}{192}\right),
\left(\frac{137}{192},\frac{139}{192}\right),
\left(\frac{149}{192},\frac{151}{192}\right).\tag{3.1}
\]

For every tile `i`, the *actual universal tile* has an integer-unwrapped
angle coordinate `x in R`, with the KL ideal sides

\[
\xi_i:\quad x\le a_i,\qquad
\eta_i:\quad x\ge b_i,
\]

on the inner boundary. These are the **remaining** J-sides: the finite
open interval `(a_i,b_i)` has been glued to the central piece and is
not a J-side. The two tails terminate at the separately named
`lambda_i/xi_i` and `lambda_i/eta_i` infinite-winding joints. These
coordinate labels are topological (from straightening), not asserted to
be a physical conformal Böttcher coordinate. See
[`tip_kl_pseudopiece_side_atlas_20261106.md`](tip_kl_pseudopiece_side_atlas_20261106.md),
§2 and its literal
[`tip_kl_side_atlas.json`](../../results/tip_kl_side_atlas.json).

**The same four rational lifts supply two excluded phases on both
J-sides of *every* tile:**

| Ideal side (each `i=0,1,2,3`) | Lifted angle `x` | `x mod 1` | Landing / excluded phase |
|:--|:--|:--|:--|
| `xi_i^circ` | `-31/56` | `25/56` | `x3` / `D_(0,1)` |
| `xi_i^circ` | `3/28` | `3/28` | `x6` / `D_(0,2)` |
| `eta_i^circ` | `81/56` | `25/56` | `x3` / `D_(0,1)` |
| `eta_i^circ` | `25/28` | `25/28` | `x6` / `D_(0,2)` |

For all original seams `(a_i,b_i)` in (3.1), the exact inequalities are

\[
-31/56 < 0 < a_i,\qquad 3/28<a_i,
\]
\[
 b_i<1<81/56,\qquad b_i<25/28.
\]

Thus every point is **strictly interior** to its claimed ideal side.
The stage external angle modulo one determines its physical landing
target; replacing `x` with `x+n` only changes the source tile's
unwrapped deck coordinate, **not** the landing point.

In fact for **each** postcritical ray angle
`theta in {25/56,31/56,3/28,25/28}` and every tile `i`,

\[
\theta+n<a_i\quad(n\le -1),\qquad
\theta+n>b_i\quad(n\ge 1).\tag{3.2}
\]

Each side therefore contains infinitely many distinct *finite* ideal
prime ends landing on `x3` or `x6`. Distinctness holds in the actual
KL universal-cover tile, not just in a list of angle labels: different
integer lifts correspond to different prime ends in its ideal strip.
This is logically separate from the two limiting deck **ends** at
`n -> +/-infinity`.

## 4. Proof of nonextension, and what it does **not** prove

**Proof of Theorem 1.** Fix a tile `i`, one of the 16 named ideal points
`e`, and let `q` be its certified physical landing point (`x3` or `x6`).
The actual source tile is the universal cover of the `G`-carrier
annulus `U_G^6\setminus K3`. By KL II §3.2.1 and Lemma 3.3, the
chosen strict finite ideal angle determines a genuine interior J-side
prime end, approached by a radial/carrier-access path
`gamma:[0,1)->Psi_G(W)` within that tile. Its source projection has

\[
p_W(\gamma(t))\longrightarrow q\quad\text{as }t\to1.
\]

Since `q in D_(0,1) union D_(0,2)`, the fine target omits `q`:
`q notin T9`. Suppose a continuous map `J` on the source interior
commutes with the physical fine projection, `pi9 o J=p_W`, and extends
continuously **to a point of `T_hat9`** at `e`, taking value `\hat q`.
Then `J(gamma(t))->\hat q` and, by continuity of `pi9`,

\[
q=\lim_t p_W(\gamma(t))
 =\lim_t \pi_9(J(\gamma(t)))=\pi_9(\hat q)\in T_9,
\]

which is impossible. This proof does not use or choose any fiber coset,
peripheral winding word, or annular deck representative. Therefore it
applies **simultaneously to every possible based lift** with the stated
target and projection. The strict finite side placement and all-integer
translates are (3.1)--(3.2), completing the proof. `square`

**Proof of Proposition 1.2.** The source atlas puts the pair
`1/3,2/3` at the actual fixed point `a`. The cyclic phase disjointness
and `G(a)=a` exclude its belonging to any of the three cyclic fine
root phases; phase separation excludes every fine obstacle in a
nonzero coarse phase. Thus `a in Omega9`. The inequalities
`-2/3<0<a_i<b_i<1<4/3` place the two claimed finite lifts strictly
inside the source J-side half-lines. Fix either prime end and choose a
small simply connected disk `B` about `a` that is evenly covered by
`pi9:T_hatOmega9->Omega9`. Carathéodory landing in the source
polynomial-like annulus gives a connected terminal collar of that
ideal point whose **physical** projection lies in `B`, and the
landing map is continuous on a sufficiently small adjacent ideal
interval. Since the interior lift `j_W` is continuous, the connected
collar lies in a single sheet of `pi9^{-1}(B)`. Compose the physical
projection with the inverse of that sheet; it gives the unique
continuous extension of `j_W` on the collar and its ideal boundary
interval. Uniqueness follows from the interior and the local covering
homeomorphism. This proof works verbatim for any finite source
landing in `Omega9`, but **not** for a landing on `K9` where the fine
localization is no longer an exterior covering. `square`

**Important nonimplications.** The theorem is about the failure of a
whole-side extension to the uncompactified fine canonical surface
`T_hat9`. It does *not* exclude a boundary map into a separately
specified compactification, nor a proper-path relation that purposely
allows ends at removed fine obstacles. It says nothing about the
`O`-side `lambda_i` away from its joints. It does not determine the
KL-prescribed connector defect words `g_theta` or settle the proper
restriction/unique-endpoint hypotheses of KKL. Most importantly, it
never equates the finite `xi/eta` side points with PR #60's interior
root-adjacent gluing seam rays.

## 5. Exact checker, trust boundary, and next branch of the investigation

The exact checker
[`verify_tip_native_ideal_side_exclusions.py`](verify_tip_native_ideal_side_exclusions.py)
uses only the **merged, original** KL atlas, the full 3/9 Levin table,
and the exact physical-phase manifest. It recomputes both image-ray
pairs by rational doubling, verifies all four source tile side intervals,
checks the original fine-obstacle labels and their disjointness,
constructs 16 strictly nonextendible and eight locally extendible
finite original J-side witnesses, and performs 640 exact
integer-translation regressions. The stored manifest
[`tip_native_ideal_side_exclusions_20261108.json`](../../results/tip_native_ideal_side_exclusions_20261108.json)
is deterministic. Run at repository root:

```sh
python -m py_compile research/independent_audits/verify_tip_native_ideal_side_exclusions.py
python research/independent_audits/verify_tip_native_ideal_side_exclusions.py --check-manifest
lake build TipNativeSideExclusion
```

Lean formalizes the finite exact rational inequalities and doubling
identities, not analytic ray landing, Kahn--Lyubich gluing, prime-end
topology, or the nonextension argument. The analytic inputs are the
already documented source-specific classical arguments, and the
conclusion is a new **logical deduction** from those inputs, not
specialist-certified theorem priority.

**The remaining research target is now narrower and better
typed.** First explicitly choose a protected set of original native
`xi/eta` ideal points with a typed physical landing class
(`Omega9`, removed phase, or marked `K9`), and define
what *target compactification* is allowed. On that selected set, use
source KL Lemmas 3.3/3.4 to compute the prescribed access paths and
relative words `g_theta in pi1(Omega9)` (not free choices of fine
connectors), with full deck integer and left-coset/right-monodromy
bookkeeping. Only then investigate proper-end and unique-restriction
claims, allowing a source-defined negative result if they fail.

Keep `H1--H4`, `UPTCR`, and `MLC` **OPEN**. This contribution changes
no ledger theorem status and does not close the broader KKL side/edge
obligation. Primary attribution: Kahn--Lyubich, *A priori bounds ... II.
Decorations*, §3.2 and Lemmas 3.3--3.4
(https://www.math.stonybrook.edu/preprints/ims06-06.pdf), and the
classical landing, straightening and Carathéodory arguments cited in
the repository's previous tip audits. OpenAI GPT-6 assisted the
source-specific derivation and exact verification; independent
specialist review remains necessary.
