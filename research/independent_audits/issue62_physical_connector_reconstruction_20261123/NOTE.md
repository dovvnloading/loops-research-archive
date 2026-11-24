# Actual KL connector words from physical external-ray cuts

**23 November 2026 — written physical reconstruction for [Issue #62](https://github.com/dovvnloading/loops-research-archive/issues/62).**

## Result and exact scope

There is a concrete physical gauge in which the original ordinary
`G=f^3`, `W=Y_G^6` KL tile connectors have the complete noncommutative word

\[
 g_{j,\theta,n}
 =\operatorname{red}\left(P_j^{-1}(b_{00}b_{01}b_{02})^nQ(\theta)\right).
 \tag{1}
\]

This construction uses actual pulled-back external rays as cuts. The
source coordinate is used as a homeomorphic chart of the actual physical
carrier, so ordered intersections can be proved exactly without treating
the topological straightening coordinate as a Euclidean or conformal
coordinate. The source tile, its original integer lift, and its physical
endpoint are retained.

The formula holds for **every actual root-landing angle in the four W
seams and every integer n**, including the one angle placed on the root
cut, with the one-sided convention below. In particular, the independent
direct-crossing calculation for the archive's entire 88-row strict-J
cohort gives exactly **8 words in H and 80 outside H**, agreeing with every
historical root/nonroot classification. An actual nontrivial example is

\[
 g_{2,3/14,0}=b_{01}^{-1}b_{00}^{-1}.
 \tag{2}
\]

Two necessary qualifications are part of the result:

1. The prefix is in `W\K9`, as permitted by the **original KL path
   definition**. It is not required to remain in the coarse exterior
   `Omega3`. The older connector-defects note imposed the latter extra
   condition. The present note explicitly corrects that additional
   requirement for connectors representing points of the actual KL
   pseudo-piece; it does not claim to supply that stricter, different
   class of connectors.
2. The archive specified a **compatible family** of based meridian
   choices, characterized in particular by
   `beta0=b00*b01*b02`; it did not specify nine unique physical access
   arcs. The present cuts realize one such compatible physical basis.
   These are actual words in that fixed realization, not recovery of a
   unique previously specified but unavailable collection of whiskers.

The physical realization below is written mathematics with explicit
imported analytic inputs. The Python certificate verifies the exact
arithmetic and full free-word computations. Neither the program nor this
note claims a Lean formalization of the straightening, landing, or
topological cut arguments, independent specialist review, a general KKL
unique-proper-restriction theorem, or full closure of Issue #62.

## 1. Actual objects and source inputs

Let `f(z)=z^2+c_tip` be the archived nonattracting algebraic tip. Let
`G=f^3` be its ordinary second-stage quadratic-like germ, with connected
locally connected filled set `K3`. Its finer return has filled set

\[
 K_9=[-p,p],\qquad
 D_{r,k}=f^{r+3k}(K_9),\quad 0\leq r,k<3.
\]

The nine `D_(r,k)` are disjoint closed physical real intervals. Exactly
`D00,D01,D02` lie in `K3`. The other six lie in the two disjoint other
coarse phases. Put

\[
 \Omega_9=U^0\setminus\bigcup_{r,k}D_{r,k},\quad
 T_9=\Omega_9\cup K_9,\quad
 \Gamma=\pi_1(\Omega_9,x),\quad H=\langle b_{00}\rangle.
\]

The fine localization is Kahn's actual cover, not a substitute abstract
coset model. Its root section on W is the archived `s_W`; its exterior
cover has fiber `H\Gamma` with right monodromy.

Write

\[
 \phi:\mathbb R/\mathbb Z\times(0,H_6)\longrightarrow N\setminus K_3
\]

for the **actual** G angle-height homeomorphism supplied by the fixed
marked straightening, where `H6=h/32`. We take N to be the Jordan carrier
bounded by its positive height `H6` equipotential. Its closure is inside
the larger original carrier, which is itself inside the certified
`D(0,1/4)`. It contains the three `r=0` fine intervals and is disjoint from
the other six. The actual W geometric disk is compactly contained in N.

The following are the exact original W seam data, not a new partition:

| j | original open seam I_j | midpoint m_j | V parent p(j) |
|---|---|---|---|
| 0 | `(41/192,43/192)` | `7/32` | 0 |
| 1 | `(53/192,55/192)` | `9/32` | 0 |
| 2 | `(137/192,139/192)` | `23/32` | 1 |
| 3 | `(149/192,151/192)` | `25/32` | 1 |

Each actual component `W_j` of `W\K3` is
`phi(I_j x (0,h/64))`. The source atlas chooses its lift with these
specific endpoints in `(0,1)`. Its angle-zero route starts at height
`h/256`, goes in increasing angle to `m_j`, and then goes to the tile
mark at height `h/128`. A point of the j-th original tile at coordinate
`theta+n` retains this exact integer n.

We use the actual root-landing sets

\[
 A_i=\{\theta\in I_i:L_G(\theta)\in K_9\}.
 \tag{3}
\]

The [exact octal reconstruction](../issue62_octal_reconstruction_20261123/README.md)
identifies the complete physical angle sets as

\[
 C=\left\{\sum_{k\ge1}a_k8^{-k}:a_k\in\{3,4\}\right\},
 \qquad A_i=(C+u_i)/16,\qquad(u_0,u_1,u_2,u_3)=(3,4,11,12).
 \tag{3a}
\]

Thus (1) has an explicit complete physical input domain. The construction
and word proof below only need the already established containment of
every root-landing angle in exactly one I_i. They do not assume the Ai
contain intervals or replace them with the eight finite anchors. In
particular the physical landing proof for the selected root cut in
Section 3 is independent of the octal reconstruction.

### Source map

All archive paths here are relative to the repository root at
the checkout containing this packet.

| Input used | Exact source |
|---|---|
| Original KL path space, arbitrary initial point in Y, terminal-fixed equivalence, universal-cover gluing | Kahn–Lyubich II, [arXiv:math/0609046v2 §3.2.1, Lemma 3.3](https://arxiv.org/html/math/0609046v2); [printed pp. 11–12](https://www.math.stonybrook.edu/preprints/ims06-06.pdf) |
| Literal W-to-V naturality and original ideal-side types | Same source, §3.2.2 Lemma 3.4(ii), §3.2.4 |
| Actual G chart, all four seams, midpoint routes, and phase avoidance | `research/independent_audits/tip_kl_pseudopiece_side_atlas_20261106.md`, §§2–4; `results/tip_kl_side_atlas.json` |
| K9 is an interval; nine physical intervals are disjoint | `research/independent_audits/tip_interval_root_and_marked_morphism_obstruction_20261106.md`; `results/tip_root_interval_geometry.json` |
| Actual W avoids all eight other fine intervals, and `G^3:W->V` is proper degree two with filled set K9 | `research/independent_audits/tip_rooted_native_KL_section_and_four_tile_prime_end_cycle_20261108.md`, §§1–3; terminal-first-child sources cited there |
| Four root seam sets, actual critical-ray anchors | `research/independent_audits/tip_native_C4_wake_root_sheet_naturality_20261109.md`, §§3–5 |
| `25/112 -> 25/56 -> 25/28` actual G-ray landing ladder | `research/independent_audits/tip_native_finite_J_side_target_trichotomy_20261109.md`, §3 |
| Compatible based meridians, `beta0=b00*b01*b02`, left cosets/right monodromy | `research/independent_audits/tip_localization_refinement_peripheral_monodromy_20261106.md`, §§2,5 |
| Root section and uniqueness of the marked root chart | Kahn I, [arXiv:math/0609045v3 §7.4.1 Theorem 7.12](https://arxiv.org/pdf/math/0609045v3); rooted-native-KL note above, Theorems 2.2–2.3 |
| Original 88 rows, still null historically | `research/independent_audits/issue62_connector_defects_20261116/finite_j_side_footprints.json`; `research/independent_audits/issue62_connector_words_20261116/word_status.json` |

The original KL source was re-read at the primary arXiv HTML, especially
the definition immediately before Lemma 3.3. The decisive point is that
the path starts somewhere in Y, and only its terminal point is fixed in
the defining equivalence. The source does not require the initial Y
prefix to avoid all of the coarser filled set.

## 2. The original path category and the archived tile calibration

For W let `K_W=W cap K3` and
`S_W=closure(K3\K_W)`. An original KL classifying path is in
`U_G^6\S_W`, starts in W, and satisfies: whenever a prefix ends in
`K_W`, it is endpoint-rel homotopic to a path in W. Equivalence is a
homotopy through this path space with the **terminal endpoint fixed**.
The footnote's stronger sufficient condition says that, after its first
exit from W, the path never meets K3 again.

**Calibration lemma.** Let a path a lie wholly in W and end at
`x_j=phi(m_j,t0)` with `t0=h/256`. Let d be any path in `N\K3` beginning
at x_j, whose lift in the original annular coordinate starts at
`(m_j,t0)`. Then `a*d` represents exactly the point obtained by starting
at the actual central point x_j and following d in the archived j-th
tile, with no additional integer shift.

**Proof.** Every path wholly in W is admissible. If a is parameterized
on `[0,1]`, the paths `a_s(t)=a(s+(1-s)t)` contract a to the constant
path at x_j through paths in W, fixing the terminal endpoint. Their
initial points are allowed to move because the source definition fixes
only the terminal point. Appending d gives an admissible homotopy:
every encounter with K3 occurs in the initial W prefix, and after d
starts there is no further encounter with K3. Lemma 3.3 therefore
identifies the resulting class with the unique continuation from the
central gluing point in the j-th universal cover. The fixed atlas
embedding sends that gluing point to `(m_j,t0)`. Uniqueness of annular
path lifting gives exactly the endpoint unwrapped coordinate of d.

The source's tile mark at height `h/128` gives the same statement:
the vertical segment at m_j from `t0` to `h/128` lies in W_j and has zero
angular displacement. No new tile torsor normalization has been made.
The angle-zero-to-midpoint atlas route calibrates this annular lift; it
does not require a common physical fine-basepoint whisker to equal that
route. This distinction is explicit in the atlas itself. QED.

This lemma is why a prefix that crosses `K3\K9` **inside W** is valid.
Such crossings are forbidden in an `Omega3`-only path but permitted by
the original KL definition. Here every actual prefix also avoids K9,
so it is a path in the same physical fine exterior in which the
connector defect is measured. The homotopy used to identify its KL
source class need not avoid K9; invariance of its fine based word is
only claimed under the separate fine-exterior homotopies below.

## 3. Three exact physical cuts and a full nine-cut basis

Set

\[
 \alpha=249/896,\qquad a_1=25/56,\qquad a_2=25/28.
 \tag{4}
\]

For each of these three angles, take the actual G ray from its landed
point to the equipotential boundary of N, with the landing point itself
included as an endpoint of the cut. Call these arcs `C00,C01,C02`.

### Actual landing of C00, independent of a new entropy argument

The ray at `d=25/112` is an authenticated ray landing at 0 in K9. The
exact arithmetic gives

\[
 8\alpha\pmod1=25/112,\qquad
 53/192<\alpha<9/32<55/192.
\]

Thus the whole sufficiently low ray at alpha lies in the actual W1
component. Under `G^3:W->V` its tail maps to the actual d-ray tail,
which tends to 0. Choose a compact neighborhood of 0 contained in V.
Properness of `G^3:W->V` puts the corresponding alpha-ray tail in a
compact subset of W. The actual Carathéodory landing q therefore lies
in W and satisfies `G^3(q)=0`. Since 0 lies in the filled set of this
proper polynomial-like return, q also lies in its filled set K9.

This is a physical landing proof: a rational preimage identity alone
would not locate the landing in the fine root. Properness of the actual
W restriction supplies the missing physical localization.

The new exact octal theorem independently authenticates the same cut:
`16*alpha-4=25/56`, and

\[
 \frac{25}{56}=\frac38+\sum_{k\ge2}4\,8^{-k}
              =0.3\overline{4}_{\,(8)}\in C.
\]

Consequently `alpha in (C+4)/16=A1`. The two arguments use different
certificates for the chosen physical root cut; no numerical landing
inference is made from its decimal location.

### Actual landings of the other two cuts

The archived actual ray ladder under G sends the d-ray to angle
`25/56`, landing at `x3=G(0)` in D01, and then to angle `25/28`, landing
at `x6=G^2(0)` in D02. The three landed points belong to different
disjoint fine intervals. The ray interiors are disjoint because phi
is a homeomorphism, and their interiors lie outside K3. Each ray plus
its landed endpoint is a Jordan arc: its positive-height part is
injective, and its endpoint is in K3 whereas every other point is not.

The exact source seam table gives

\[
 C_{00}\cap(W\setminus K_9)=\{\phi(\alpha,t):0<t<h/64\},
 \qquad C_{01}\cap W=C_{02}\cap W=\varnothing.
 \tag{5}
\]

In particular, C00 is a proper cut of the root annulus `W\K9` from
its inner prime-end boundary to its outer boundary.

### Cut-complement lemma and completion outside N

A disk with three disjoint slit intervals, cut along disjoint proper
arcs joining each inner boundary to the outer boundary, has a connected
simply connected cut complement. This is the usual finite planar-surface
cut lemma, applied to prime-end boundary circles of the slit intervals;
equivalently, thicken each slit slightly and use a regular neighborhood
adapted to its attached Jordan ray. Each cut joins a different inner
boundary to the outer one, so successive cuts reduce the number of
inner boundary components by one and do not disconnect the domain.

Apply this to `N\(D00 union D01 union D02)` and the three actual rays.
The resulting domain F is simply connected. Set the common physical
basepoint

\[
 x=\phi(m_0,t_0),\qquad m_0=7/32,\quad t_0=h/256.
 \tag{6}
\]

It lies in F and in W. Define b00,b01,b02 by the cut-dual loops based
at x: travel inside F to one bank, cross the corresponding cut once
in the positive angular direction, and return inside F. Simply
connectedness of F makes this a uniquely defined based class for each
cut. These are genuine positive peripheral meridians of the respective
physical intervals.

The other six fine intervals are outside the closed N. Complete the
three ray cuts to the outer boundary of U0, and add one cut from each
remaining fine interval, all with interiors outside N. Such a disjoint
completion exists in the finite planar surface

\[
 U^0\setminus\left(\operatorname{int}N\cup
                    \bigcup_{r=1,2;k=0,1,2}D_{r,k}\right).
\]

Here is an explicit topological construction argument. Choose an arc
from the N boundary to the U0 boundary avoiding the six holes. Use a
thin collar of that arc and of the N boundary to route the three
specified ray endpoints to distinct U0 endpoints in their cyclic
order. The routes can be chosen disjoint and their thin collar regions
can avoid all six holes. The remaining regions are finite planar
surfaces. In each such region, join its inner boundary components to
the outer boundary by a disjoint tree of arcs, and separate parallel
branches in a thin regular neighborhood. This gives the six remaining
cuts, still outside N. The construction can be performed relative to
the disjoint coarse-phase Jordan neighborhoods used in the archived
compatible-access construction, giving the same block ordering
`b_r0*b_r1*b_r2` for each coarse phase.

All nine resulting cuts are disjoint in their interiors and avoid every
fine interval except at their designated endpoints. The full cut
complement in Omega9 is simply connected. Its cut-dual basis is a
physical free basis of F9. The first three dual loops can be chosen
wholly in N, so they agree **exactly**, not just up to conjugacy, with
the three loops already defined in F.

The six outside-N arcs are not needed as numerical input: the theorem
holds for **every** compatible disjoint completion just described.
Every loop computed below is contained in N, never meets those six
cuts, and uses the same first three based meridians. Changing the
completion leaves these words unchanged. This is an independence
statement about unused basis generators, not a claim that unprovided
physical arcs have somehow been recovered.

The positive carrier loop from angle m0 to m0+1 at height t0 meets
the three cuts in the exact order

\[
 m_0<\alpha<a_1<a_2<m_0+1.
\]

Consequently its complete based word is

\[
 \beta_0=b_{00}b_{01}b_{02}.
 \tag{7}
\]

This proves compatibility with the archive's fixed coarse-product
convention. A root loop inside W crosses C00 once and no other cut;
therefore its based subgroup is exactly `H=<b00>`. The basis change
on every generator occurring in the result is the identity in this
physical realization. For an independently fixed *different* compatible
access system, one must apply its actual based change-of-marking
automorphism to the words and H; no such separate system is specified
by the old archive.

## 4. One fixed root reference for all endpoints

Define

\[
 D=W\setminus(K_9\cup C_{00}).
 \tag{8}
\]

By (5) and the annulus cut lemma, D is a connected simply connected
proper plane domain containing x. It is contained in the full nine-cut
complement. For each y in D choose the unique hyperbolic geodesic
`kappa_y` from x to y **in the actual physical domain D**. The constant
path is used for y=x. This specifies an actual curve, not merely its
sheet or an independently adjustable rowwise homotopy class. One may
equivalently define its unique endpoint-rel homotopy class in D; the
geodesic selects a representative continuously as y varies.

Every such reference lies in `W\K9`, misses all nine cuts, and lifts
from `s_W(x)` to `s_W(y)`. Define `kappa_j=kappa_(phi(m_j,t0))`.
These four prefixes are fixed once for all endpoints and integer
shifts; none is selected to force a desired reduced word.

### The cut angle is included, with a fixed lower-angle bank convention

At `theta=alpha`, y=`phi(alpha,t)` is on the root cut and is not in D.
Set the positive rational

\[
 \epsilon=\frac{\alpha-53/192}{8}.
\]

Let `y_-=phi(alpha-epsilon,t)`, and let sigma_t be the increasing
horizontal segment at height t from `alpha-epsilon` to alpha. Both
its endpoints and its interior lie in W1; its interior is on the
lower-angle bank of C00. Define

\[
 \kappa_{\alpha,t}=\kappa_{y_-}*\sigma_t.
 \tag{9}
\]

This is an actual rooted path in `W\K9` with the original physical
endpoint y. Any other sufficiently small positive epsilon in the
same W1 half-strip gives the same based reference class, by a homotopy
in the cut domain followed by a common terminal segment. This is the
**lower-angle bank** reference, fixed globally for that angle and all n,j.

If one instead uses the upper-angle bank reference, the reference class
differs by the corresponding root loop and the defect changes by
right multiplication by b00. This is the previously documented
root-reference gauge, not a new source tile shift. All formulas below
use (9), so the cut angle is not removed from the all-angle claim.

## 5. Actual prescribed native connectors

Fix `theta in A_i`, `j in {0,1,2,3}`, any integer n, and a positive
height `t<t0`. For finite manifest rows we take `t=h/1024`.

Let `d_(j,theta,n,t)` be the following actual path, defined by phi:

1. The horizontal path at height t0 whose **unwrapped** coordinate
   goes from m_j to `theta+n`.
2. The vertical path at angle `theta mod 1` from height t0 to t.

Its endpoint is the actual physical point `y=phi(theta,t)`. Define

\[
 \kappa'_{j,\theta,n,t}=\kappa_j*d_{j,\theta,n,t},\qquad
 g_{j,\theta,n}=[\kappa'_{j,\theta,n,t}*\kappa_{\theta,t}^{-1}].
 \tag{10}
\]

For theta unequal to alpha, use the D-geodesic reference; for alpha,
use (9). All paths in (10) are in the **same actual Omega9**. The
prefix lies in W, which avoids the other eight fine obstacles. The
annular part is outside K3 and inside N, so avoids all nine. The
terminal endpoint is inside W_i because theta is in I_i and t<h/64.

The original KL subordination rule holds: any point of K_W met by
the path is met during the initial prefix contained in W, whereas
the rest of the path never meets K3. The stronger footnote condition
also holds after the first exit from W. By the calibration lemma,
this path represents **exactly** the archived j-th tile point with
unwrapped coordinate `theta+n`. It does not represent an arbitrarily
translated version of that tile, nor a new path quotient.

The map from the actual source pseudo-piece to the fine target has
central restriction s_W. Therefore the initial lifted prefix ends
at the root-normalized central point `s_W(x_j)` and the continued
lift is precisely the actual native tile lift. This also follows
directly by uniqueness of lifting the annular path from its central
gluing point. Thus the comparison in (10) measures the actual source
tile, not an unrelated physical path with the same final angle.

## 6. Full ordered word computation

Use traversal-order multiplication. A positive crossing is from the
lower-angle bank to the upper-angle bank. For a cut oriented from its
fine interval to the outer boundary, these are its right and left
banks, respectively. Because phi is orientation preserving, this
is exactly increasing angular coordinate. A negative crossing is
the opposite. Every cut-free prefix and reference contributes no
letters. For theta unequal to alpha, the terminal vertical segment
also contributes no letters. Hence the complete word is the signed
ordered list of crossings by the horizontal segment in (10).

These are intersections of **actual physical curves**: phi is an
injective chart on the carrier, the cuts are constant-angle curves
in that chart, and the connector segment is a constant-height curve.
There is a single transverse topological intersection for each lifted
cut angle lying strictly between its unwrapped endpoints. No claimed
metric or Euclidean intersection is involved.

For the increasing baseline path at height t0 from m0 to m_j, the
cut words are

\[
 (P_0,P_1,P_2,P_3)=(1,b_{00},b_{00}b_{01},b_{00}b_{01}).
 \tag{11}
\]

The baseline word from m0 to theta, for theta in the four root seams,
is

| endpoint angle | Q(theta) |
|---|---|
| `theta in A0` | `1` |
| `theta in A1`, `theta <= 249/896` | `1` |
| `theta in A1`, `theta > 249/896` | `b00` |
| `theta in A2 or A3` | `b00*b01` |

For theta in A0 slightly below m0 the baseline is decreasing, but
crosses no cut, so its word is still 1. At the exceptional cut angle
the table uses the fixed lower-angle bank convention (9).

**Word theorem.** With exactly the physical choices above, formula
(1) holds for every theta in the actual Ai and every integer n.

**Proof away from the cut angle.** In the lifted carrier strip, the
path from m_j to `theta+n` is endpoint-rel homotopic to the path that
first goes from m_j to m0, then from m0 to `m0+n`, then from `m0+n`
to `theta+n`. This homotopy is in the actual annulus after applying
phi. The three pieces have words `P_j^-1`, `beta0^n`, and Q(theta),
respectively. This proves (1) in the full free group, retaining order
and all cancellations. Equivalently, count the signed intersections
of the original monotone path directly; the resulting reduced word
is the same. This argument uses arbitrary integer n, not a finite
sample of deck shifts.

**At theta=alpha.** Replace the end of the annular path by the path
to `phi(alpha-epsilon,t)` followed by sigma_t. The original path
and this one are endpoint-rel homotopic in the physical annular
rectangle, and their lifts have the same unwrapped endpoint
`alpha+n`. In (10) the common final sigma_t cancels its inverse in
the reference (9). The reduced loop is therefore the one with
endpoint `alpha-epsilon`, whose Q word is 1. This proves the stated
lower-angle bank formula without changing the actual endpoint or deleting
the cut angle. QED.

The symbols P_j in (11) are **calibration words**, not substitutes
for the physical prefixes kappa_j. The latter are cut-free W paths.
Their difference from the exterior baseline is exactly the defect
being measured. In particular, (1) does not identify the W prefix
with a coarse-exterior path.

### An exact first-symbol algorithm for all irrational root angles

The complete physical angle reconstruction (3a) turns the Q table into
a finite first-symbol rule. Every C point has a unique expansion with
octal digits 3 and 4. Write `C3=(3+C)/8` and `C4=(4+C)/8` for its first-
digit cylinders. Since the minimum and maximum of C are `3/7` and `4/7`,
their exact convex hulls are

\[
 \operatorname{hull}(C_3)=[3/7,25/56],\qquad
 \operatorname{hull}(C_4)=[31/56,4/7].
 \tag{11a}
\]

In the physical A1 seam these give

\[
 \operatorname{hull}((C_3+4)/16)=[31/112,249/896],
\]
\[
 \operatorname{hull}((C_4+4)/16)=[255/896,2/7],
\]

and the exact original midpoint lies strictly in the intervening gap:

\[
 \boxed{\alpha=249/896<m_1=252/896<255/896.}
 \tag{11b}
\]

Thus the cut is the **maximum of the first-digit-3 cylinder**, not a
threshold requiring an arbitrary-real equality decision. The declared
lower-angle reference at that endpoint makes the rule uniform on each
entire physical cylinder:

| actual root seam i | first octal digit of `16*theta-u_i` | Q(theta) |
|---|---:|---|
| 0 | 3 or 4 | `1` |
| 1 | 3 | `1` |
| 1 | 4 | `b00` |
| 2 or 3 | 3 or 4 | `b00*b01` |

Given the actual source tile j, physical root seam i, first octal
symbol, and integer n, formula (1) now computes the complete based
physical F9 word without reading any further digits. This includes
every irrational angle in the physical Ai. The program's `address_word`
implements this rule, and the certificate records the exact cylinder
endpoints and the word assigned to each of the eight `(i, first digit)`
cases. It also compares this independent address rule with the direct
crossing word of every archived finite row.

The unbounded integer n is retained and produces infinitely many
distinct cosets. This first-symbol rule is not a finite sheet quotient;
nor does it identify different physical landing points whose relative
word happens to be the same in the chosen rooted-reference gauge.

### Native integer shifts and their actual based conjugators

The positive native turn at m_j has the based word

\[
 D_j=P_j^{-1}\beta_0P_j,
\]

so

| original tile | actual based native positive turn |
|---|---|
| W0 | `b00*b01*b02` |
| W1 | `b01*b02*b00` |
| W2 | `b02*b00*b01` |
| W3 | `b02*b00*b01` |

The exact all-integer law is

\[
 g_{j,\theta,n}=D_j^n g_{j,\theta,0}.
 \tag{12}
\]

Thus the source-native turn is not silently replaced by a common
left prefix beta0 in every tile. The based conjugators have now
been physically calibrated by the actual cuts.

The endpoint reference in (10) identifies the endpoint fiber with
the based fiber by returning along `kappa_(theta,t)^-1`; hence its
coordinate is `H g_(j,theta,n)`, with the original **left-coset/right-
monodromy** convention. Distinct integers give distinct left cosets:
if `H g_n=H g_m`, then

\[
 g_n g_m^{-1}=D_j^{n-m}\in H.
\]

Its winding about D02 is `n-m`, whereas H has winding zero there.
Thus n=m. This uses the full native based word and the correct
left-coset equality test.

### Finite examples without suppressing root words

| original source | actual endpoint angle | n | exact reduced defect |
|---|---|---:|---|
| W1 | qR=`3/14` | 0 | `b00^-1` |
| W2 | qR=`3/14` | 0 | `b01^-1*b00^-1` |
| W0 | e=`31/112` | 0 | `1` |
| W0 | pR=`2/7` | 0 | `b00` |
| W0 | pL=`5/7` | 0 | `b00*b01` |
| W1 | pL=`5/7` | 0 | `b01` |
| W3 | pL=`5/7` | 0 | `1` |

The nontrivial root words show that the gauge did not artificially
set every rooted comparison to the identity. Full signed crossing
lists and all nine winding entries are included for all 88 rows in
[`certificate.json`](certificate.json).

## 7. A genuinely different physical representative and its homotopy

The second representative uses horizontal height `t1=h/512` instead
of t0 and the following unwrapped horizontal vertices:

\[
 m_j,\quad m_0,\quad m_0+n,\quad\theta+n.
 \tag{13}
\]

Its prefix is the D-geodesic from the same fixed x to
`phi(m_j,t1)`; its last segment is vertical to the same endpoint
`phi(theta,h/1024)`. The first horizontal leg may backtrack relative
to the final displacement. Its unreduced crossing list is therefore
usually different from that of the monotone first representative,
and it can contain nontrivial cancellations.

There is an actual endpoint-fixed homotopy in Omega9 through
KL-admissible paths:

1. Interpolate the horizontal height from t0 to t1. The corresponding
   D-geodesic prefixes vary continuously with their endpoints. All
   remaining segments stay in the carrier outside K3.
2. In the lifted strip at t1, homotope the monotone horizontal path
   to the three-leg path (13), keeping its endpoints fixed. A linear
   homotopy of their unwrapped coordinate functions suffices. Applying
   phi gives a homotopy in the actual annulus, so the source integer
   coordinate is retained at every stage.
3. Keep the rooted reference fixed. For theta=alpha use the common
   terminal sigma_t cancellation from Section 6 throughout.

Every intermediate prefix is in W and every subsequent segment is
outside K3. Thus both the fine-exterior requirement and the original
KL subordination condition hold during this homotopy. The verifier
computes the ordered signed crossings of all three second-path legs,
reduces the concatenation in F9, and compares it against the direct
monotone first path and the independent formula (1).

This is not a second drawing of the same polygon or an assertion that
two paths with equal abelianization are homotopic. The actual lifted-
strip homotopy supplies the analytic topological proof, and the full
reduced words provide its exact finite check.

## 8. Root membership, every angle and every integer

Let p(i)=0 for i=0,1 and p(i)=1 for i=2,3. The explicit P and Q tables
give, for all actual theta in Ai,

\[
 w_{01}(g_{j,\theta,n})=n+p(i)-p(j),\qquad
 w_{02}(g_{j,\theta,n})=n.
 \tag{14}
\]

If n is nonzero, the second equality rules out H. If n=0 and the
parents differ, the first equality rules out H. If n=0 and the
parents agree, full reduction of `P_j^-1 Q(theta)` leaves only a
power of b00 (possibly empty). Thus the exact criterion is

\[
 g_{j,\theta,n}\in H
 \quad\Longleftrightarrow\quad
 n=0\ \text{and}\ p(i)=p(j).
 \tag{15}
\]

The last implication is a **nonabelian calculation**, not a claim
that vanishing winding suffices for arbitrary F9 words. It succeeds
because the complete word is already known from the physical cuts.

For strict original J-side instances the own tile `j=i,n=0` is absent:
it is the glued open seam. Of the two same-parent tiles, the other is
the original mate. Equation (15) is therefore exactly the old mate-
tile zero-shift criterion on the full actual root-landing domain,
and not only on the eight rational anchors.

The finite manifest comparison is a falsification check, not an input
to word extraction. The program reads all 88 original source rows,
constructs their crossings from tile midpoint, actual cut angles,
and unwrapped endpoint, computes their reduced words, and **then**
compares H membership with the old annotation. It finds:

| original cohort | in H | outside H |
|---|---:|---:|
| strict zero-shift J rows | 8 | 16 |
| n=-1 or n=+1 rows | 0 | 64 |
| all rows | **8** | **80** |

### A concrete impossibility for the extra coarse-only prefix condition

The correction of the old `Omega3`-only prefix requirement has an exact
physical obstruction, not merely a different preferred convention. Keep
the common basepoint x in W0 fixed as in (6). Let c be **any** path in
Omega3 from x to `y=phi(theta,t)`, where `theta in Ai`. Let c0 be the
actual W0 horizontal-then-vertical carrier path to y with zero integer
shift. Both c and c0 are in Omega3, so `c*c0^-1` is an Omega3 loop.
The winding function of such a loop is locally constant off its trace
and hence constant on the connected K3. In particular its windings
about D01 and D02 agree. Thus

\[
 \delta([c\kappa_{\theta,t}^{-1}])
 =\delta([c_0\kappa_{\theta,t}^{-1}])
 =\delta(Q(\theta))=p(i).
 \tag{16}
\]

For every theta in A2 or A3 this is 1. Consequently **no Omega3-only
connector from this common x can be root-compatible at those endpoints**.
Changing it by any coarse loop, or changing the rooted reference by
any root loop, does not repair the nonzero character.

For a smallest authenticated strict-J example take the original
`W3` mate-side point at `theta=pL=5/7`, `n=0`. Its actual source-native
word in the present physical construction is 1, so it is rooted. Every
Omega3-only connector from the same x to the same positive-height
endpoint instead has delta=1 and is nonroot. The archived original KL
tile and a globally coarse-only whisker therefore cannot both be
preserved in that extra requirement. The allowed W prefix resolves
this specific incompatibility exactly as the original KL definition
requires; it is not a way of ignoring a realizable stricter gauge.

### Actual root convergence and proper nonroot ends

H membership means the source tail agrees with the actual rooted lift
`s_W` and hence converges to the marked fine root. Here is the converse
with its physical hypotheses made explicit. Choose a confocal ellipse
neighborhood B of the real interval K9 compactly contained in W. It
avoids all eight other fine obstacles. Such a B exists by compactness
of K9 in the open W. Explicitly, for R>1 sufficiently close to 1, the
Joukowski map `J(w)=(p/2)(w+w^-1)` sends `1<|w|<R` conformally onto
`B\K9`. Transport a basepoint of this annulus to x by a rooted W
connector. Its based peripheral image is H, independently of that
rooted choice. Thus the annulus `B\K9` has peripheral subgroup H.
The actual covering components above it are indexed by `H\Gamma/H`.
The component containing our terminal lift has double-coset label
`H g_(j,theta,n) H`. The H component is the root-adjacent one-sheeted
component, filled by the marked K9; every other component is universal
because

\[
 H\cap g^{-1}Hg=\{1\}\quad(g\notin H).
\]

For completeness, this malnormality follows from the free-product
normal form `Gamma=H*F(b01,b02,b10,...,b22)`: remove the maximal H
syllables at both ends of a non-H word; conjugating a nontrivial H
element by its remaining word leaves nonempty complementary-factor
syllables and cannot lie in H. These are exactly the actual subgroup
and pullback components identified in the rooted-native-KL source,
Theorem 2.2, not a newly chosen cover.

Every G ray at theta in Ai lands in K9 and therefore eventually lies
in B. The actual real-symmetric marked chart puts I0 and I1 in the
physical lower half-plane, and I2 and I3 in the upper half-plane.
Consequently its tail approaches the definite lower or upper slit
prime end at its physical landing point. This follows explicitly by
taking the appropriate bank limit of the inverse Joukowski map; the
two limits at q in the interior of K9 are
`q/p +/- i*sqrt(1-(q/p)^2)`, and at q=+/-p they coincide at +/-1.
Thus at a slit endpoint the two banks meet at the one endpoint prime
end. In a sufficiently small
prime-end collar it cannot make an extra full turn around K9.
Its lift in any universal component therefore has a unique finite
inner-boundary endpoint in that annular component's universal strip.
This last statement is about the component's prime-end compactification;
no identification with an additional full-target marking is assumed.

If the non-H lifted tail had a compact accumulation in the **filled
fine surface** `T_hat9`, continuity of the actual projection would put
that accumulation over its physical point of K9. Kahn's marked root
is the only preimage of K9 and has a neighborhood on which projection
is biholomorphic. A visit by the tail to a sufficiently small such
neighborhood would make that visit the rooted inverse of its projected
point. Uniqueness of path lifting then makes its preceding positive-
height lift the rooted one, contrary to `g notin H`. Thus it has no
compact accumulation and escapes every compact subset of `T_hat9`.

This proves, for **all** theta in Ai, all four original source tiles,
and every integer n, that (15) is exactly root convergence versus a
proper nonroot **end**. For strict original J-side points this is the
mate-zero-shift rule. The claim concerns terminal ends; it does not
assert that an arbitrary extension of the tail to a two-ended path is
proper at its other end. It also does not decide the separate set-valued
KKL proper-restriction operation for arbitrary proper paths or markings.

### Sign audit against the old C4 note

For the explicitly fixed loop direction `g=kappa_prime*kappa^-1`,
(14) gives

\[
 (w_{01}-w_{02})(g)=p(i)-p(j).
\]

This agrees with the old **increasing-angle** wake edge table: the
passage from source tile 1 to a tile-2 endpoint winds positively
around D01. The old text's later source-relative comparison printed
`p(j)-p(i)`, the reverse sign. Its root/nonroot proofs only use that
an opposite-parent value is nonzero, and every one of its 88 root
decisions agrees with the present direct construction. The signed
formula here follows the stated physical path direction and is not
quietly identified with that opposite convention.

## 9. What has been supplied, and what has not

The construction supplies the originally absent ingredients for one
explicit compatible physical gauge:

* A common actual physical basepoint and a single global rule for all
  W prefixes and rooted references.
* A proof in the **original** KL path category that those prefixes
  produce the archived tile and integer lift, without altering them.
* Three physically landed, disjoint G-ray cuts, a proof of a disjoint
  full nine-cut completion outside the actual carrier, and independence
  of all computed words from that completion.
* Exact ordered physical intersections certified in the actual
  homeomorphic chart, full F9 reduction, native deck conjugators, and
  all-integer formulas.
* A second actual representative with an endpoint-fixed admissible
  homotopy and independently computed unreduced crossing list.
* An all-root-angle H-membership theorem and a complete 88-row check
  against the old classifications, preserving every original source
  side and proof-role label.

The historical requirement for **Euclidean polygon vertex enclosures**
was a proposed way to certify actual intersections, not part of KL's
definition or a mathematical necessity. Here the cut curves themselves
are chosen from the physical marked foliation, and its injective chart
proves every intersection and nonintersection exactly. The fine
reference paths avoid the cuts by definition of their single fixed
domain D. No merely rational angle is declared to be a physical
polygon vertex.

The strict `Omega3`-only initial-whisker problem remains a different
problem. Those paths cannot in general be substituted for our W
prefixes while keeping their relative fine words unchanged. Likewise,
the literal result in an additional independently specified historical
access system would require transporting the basis by that system's
actual change-of-marking automorphism. This note does not fill old
fields with words while pretending those extra choices were already
fixed.

No general claim is made about complete outer sides, infinite wrapping
joints, all proper path classes, KKL unique restriction, or global MLC.
The current result is stronger than an abstract coset identity because
it physically constructs the connectors and computes nontrivial
ordered words for every root-sector ray in every native tile.

## 10. Reproduction

From the repository root:

```sh
python research/independent_audits/issue62_physical_connector_reconstruction_20261123/verify.py --check-manifest
python research/independent_audits/issue62_physical_connector_reconstruction_20261123/test_verify.py
```

To regenerate this packet’s certificate, use `--write`; to point at a
different checkout, add `--repo /absolute/path/to/loops-research-archive`.
The script reads the original source JSON files and never edits them.
It uses only the Python standard library. Exact Fraction arithmetic is
used for every source comparison and cut intersection. The manifest
records SHA-256 hashes of the three directly imported source manifests.

The full proof is above, and all 88 complete row records are in
[`certificate.json`](certificate.json). The verifier checks finite arithmetic
and words; the all-integer statement follows from the lifted-strip
proof and the symbolic formula, not a large finite sample. Physical
ray landing, the marked chart, the source gluing theorem, and the
planar cut arguments remain explicit written analytic dependencies.

**Attribution and review.** The original pseudo-piece construction and
localization are due to Kahn and Lyubich as cited above. GPT-6 Astra Pro
materially assisted with the ray-cut construction, proof search, source
comparison, exact word verifier, and exposition. Automated regression
and source checks are documented by this packet. Independent human
specialist correctness or novelty validation has not been established.
