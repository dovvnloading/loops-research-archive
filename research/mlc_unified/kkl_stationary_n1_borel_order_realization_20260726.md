# Gate N1 — Borel ordered-Wave realization from nested planar domains

## 0. Status and scope

This note addresses only the remaining measurable interface in

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION
```

after the analytic leafwise-directed proof in
`kkl_stationary_relative_wave_continuation.md`.

It constructs a standard-Borel leaf space and a Borel proper-path
evaluation for every proof-used annular Wave from:

1. the native KL06/KKL assertion that each arc-class sublamination is
   a proper Borel lamination;
2. planar nesting of disjoint representatives of one boundary-parallel
   arc class;
3. a full-support finite Borel measure on the annulus;
4. the Arsenin--Kunugui projection theorem;
5. the Lusin--Souslin theorem; and
6. Burgess's Borel-selector theorem for smooth orbit equivalence
   relations of Polish-group actions.

The result is a **candidate closure of the Borel part of Gate N1**.
It is not promoted in this note.  Promotion requires an independent
audit of the source reading

```text
ARC_CLASS_SUBLAMINATION_IS_PROPER_BOREL
```

recorded precisely in Section 2, and an audit of the Borel maximal-lift
calculus in Section 7.

The analytic theorem, Gate N2, VAAPC-I, UPTCR, and MLC are not changed
here.

## 1. Frozen inputs and external measurable theorems

### 1.1 Native sources

The local source copies are:

| source | SHA-256 | clauses used |
|---|---|---|
| KKL, `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` | 1839--1875, 1901--1914, 2065--2168 |
| KL06, `.tmp_kl06_source/wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` | 23--50, 66--85, 100--103, 142--160 |
| DL, `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` | 2813, 2821--2842 |

The relevant native statements are:

1. KL06 `wad.tex` 142--143 defines a proper lamination as a Borel
   point set explicitly realized as a union of disjoint proper paths.
2. KL06 144--150 writes a proper lamination as the union of its
   arc-class sublaminations \(\mathcal F(\alpha)\), and calls each
   \(\mathcal F(\alpha)\) a sublamination.
3. KKL 1911 repeats this convention: for any lamination
   \(\mathcal F\) and arc \(\alpha\), \(\mathcal F(\alpha)\) is the
   sublamination consisting of leaves represented by \(\alpha\).
4. KKL 1904--1908 gives a finite support bound in the proof-used
   finite marking; countability would already suffice below.
5. KKL 1844--1875 supplies the metrizable ideal boundary, proper
   paths, ideal endpoints, marked arcs, Waves, bases, ends, and crests.
6. KKL 2081--2142 supplies immersion restriction and the two
   restriction filters.
7. DL 2813 defines a Wave above a fixed boundary side leaf by leaf.
8. DL 2821--2842 performs deck-span decomposition and removes
   outermost order buffers.

### 1.2 External standard-Borel facts

Three classical facts are used.

#### Fact LS (Lusin--Souslin)

If \(X,Y\) are standard Borel spaces and \(h:X\to Y\) is Borel and
injective, then \(h(X)\) is Borel and \(h^{-1}:h(X)\to X\) is Borel.

#### Fact AK (Arsenin--Kunugui)

If \(B\subset X\times Y\) is Borel, \(X,Y\) are Polish, and every
vertical section \(B_x\) is \(\sigma\)-compact, then
\(\operatorname{proj}_X B\) is Borel.

A primary-source discussion is D. G. Larman,
“Projecting and uniformising Borel sets with \(\sigma\)-compact
sections I,” *Mathematika* 19 (1972), 231--243,
<https://doi.org/10.1112/S0025579300005696>.

#### Fact B (Burgess selector)

Let a Polish group act continuously on a Polish space.  On an invariant
Borel subset, if the orbit equivalence relation is countably separated
(equivalently, smooth), then it has a Borel transversal.

The primary source is J. P. Burgess,
“A selection theorem for group actions,” *Pacific J. Math.* 80
(1979), 333--336,
<https://doi.org/10.2140/pjm.1979.80.333>.

No numerical or computational statement is used.

## 2. Exact source-reading interface

### Definition 2.1 (arc-class Borel reading)

Write

\[
 \mathscr S(\alpha)
 :=
 \{\gamma\in\mathscr S:[\gamma]=\alpha\}.
 \tag{2.1}
\]

The **arc-class Borel reading** is:

> When KL06 145--150 or KKL 1911 calls
> \(\mathscr S(\alpha)\) a sublamination, it is a proper lamination in
> the standing KL06 sense; hence its geometric union is Borel.

This is the natural literal reading because KL06 144 says that all
laminations under consideration are proper, and “proper lamination”
was defined two lines earlier to have Borel geometric union.

The locked lines do not separately restate the word “Borel” after
“sublamination.”  Therefore an audit which interprets “sublamination”
as a merely set-theoretic leaf subset would leave Definition 2.1 as an
additional hypothesis.  Every conclusion below records that exact
dependence; no countable atlas is used to manufacture it.

### Lemma 2.2 (countable arc-class decomposition)

For a proof-used KKL Wave \(\mathscr S\), the nonempty
\(\mathscr S(\alpha)\)'s admit a countable enumeration

\[
 \mathscr S
 =
 \mathop{\dot\bigcup}_{a\in A}\mathscr S_a,
 \qquad A\subset\mathbb N.
 \tag{2.2}
\]

Under Definition 2.1 every \(\mathscr S_a\) has Borel geometric union.

#### Proof

The surface has finite topology and a countable ideal marking, so its
marked arc set is countable.  In the actual finite KKL marking, KKL
1908 gives the stronger finite support bound

\[
 \#\operatorname{supp}W_{\mathscr S}
 \leq
 3|\chi(V)|+|\mathcal I|.
 \tag{2.3}
\]

Distinct leaves in different arc classes are allocated to exactly one
class, giving (2.2).  Borelness is precisely Definition 2.1.
\(\square\)

## 3. Planar order inside one Wave arc class

Let

\[
 V=\mathcal U\setminus\mathcal T.
\]

Its prime-end compactification is a closed annulus
\(\overline V^{\,\rm pe}\).  Every Wave leaf used below is a proper
embedded path with both ideal endpoints on the inner boundary
component and is boundary-parallel.

For a leaf \(\gamma\), let \(O_\gamma\) be the component of

\[
 \mathcal U\setminus(\mathcal T\cup\gamma)
\]

which does not meet the outer boundary of \(\mathcal U\).  Its
prime-end trace on the inner boundary is the singleton Wave base.
For a DL-directed packet above \(J\), \(O_\gamma\) is exactly the
component whose prime-end boundary contains \(J\).

### Lemma 3.1 (common arc class gives a common boundary direction)

Fix one nonempty Wave arc class \(\mathscr S_a\).  There is a marked
open boundary interval \(Q_a\) such that

\[
 Q_a\subset\partial_{\rm pe}O_\gamma
 \qquad
 (\gamma\in\mathscr S_a).
 \tag{3.1}
\]

#### Proof

Leaves in one marked arc class have the same two marked endpoint
classes and the same boundary-parallel homotopy direction between
them.  A KKL path is not subordinate to a multi-interval of
combinatorial length at most two (KKL 1868--1869).  Consequently the
boundary trace between its two marked ends contains at least one
marked open interval which is not an end interval.  That intervening
marked interval depends only on the marked arc class.  Choose one and
call it \(Q_a\). \(\square\)

### Lemma 3.2 (nested-domain lemma)

If \(\gamma,\delta\in\mathscr S_a\), then

\[
 O_\gamma\subset O_\delta
 \quad\text{or}\quad
 O_\delta\subset O_\gamma.
 \tag{3.2}
\]

If \(\gamma\ne\delta\), the inclusion is strict and the difference
between the two domains contains a nonempty open set.

#### Proof

The two embedded proper leaves are disjoint.  The closure of either
leaf together with its inner-boundary trace is a separating
prime-end crosscut.  The interior of \(\delta\), being connected and
disjoint from \(\gamma\), lies in one component of the complement of
\(\gamma\).

Both \(O_\gamma\) and \(O_\delta\) have \(Q_a\) on their prime-end
boundary by (3.1).  Therefore the two boundary-side components cannot
be disjoint.  The crosscut separation theorem now forces one to lie
inside the other, proving (3.2).

If the leaves are distinct, choose an interior point of the outer
leaf which is not on the inner leaf.  A sufficiently small disk about
that point avoids the inner leaf.  The side of this disk between the
two crosscuts belongs to the set difference of the two domains.  Thus
the inclusion is strict and the difference has nonempty interior.
\(\square\)

This proof is entirely in the prime-end annulus.  It assumes neither
local connectivity of \(\mathcal T\) nor a monotone map from an actual
Julia set to a combinatorial model.

## 4. The nested-area Borel coordinate

Choose once and for all a finite Borel measure \(\mu\) on \(V\) such
that

\[
 \mu(W)>0
 \quad\text{for every nonempty open }W\subset V.
 \tag{4.1}
\]

For example, choose a countable relatively compact coordinate-disk
basis \((D_m)\), smooth probability measures \(\mu_m\) with full
support in \(D_m\), and put

\[
 \mu:=\sum_{m\geq1}2^{-m}\mu_m.
 \tag{4.2}
\]

Let \(Z_a\subset V\) be the Borel geometric union of
\(\mathscr S_a\).  Define, set-theoretically,

\[
 \tau_a(x):=\mu(O_\gamma)
 \quad\text{when }x\in\gamma\in\mathscr S_a.
 \tag{4.3}
\]

Disjointness of the leaves makes this well-defined.

### Lemma 4.1 (the area coordinate separates leaves)

For \(\gamma,\delta\in\mathscr S_a\),

\[
 \mu(O_\gamma)=\mu(O_\delta)
 \quad\Longleftrightarrow\quad
 \gamma=\delta.
 \tag{4.4}
\]

#### Proof

If the leaves differ, Lemma 3.2 gives a strict inclusion whose
difference contains a nonempty open set.  Equation (4.1) makes the
measure difference strictly positive. \(\square\)

### Lemma 4.2 (Borelness without a pre-existing leaf quotient)

The function

\[
 \tau_a:Z_a\longrightarrow\mathbb R
 \tag{4.5}
\]

is Borel.

#### Proof

Fix \(r\in\mathbb Q\) and put

\[
 U_r
 :=
 \bigcup_{\mu(O_\gamma)<r}O_\gamma.
 \tag{4.6}
\]

This is open, since it is an arbitrary union of open domains.

If \(\mu(O_\delta)\geq r\), then \(\delta\cap U_r=\varnothing\).
Indeed, for every \(\gamma\) entering (4.6), nesting and strict
monotonicity give

\[
 O_\gamma\subset O_\delta.
\]

The boundary leaf \(\delta\) is disjoint from \(O_\delta\), and hence
from \(O_\gamma\).

Now suppose \(\mu(O_\delta)<r\).  If there exists
\(\gamma\) with

\[
 O_\delta\subsetneq O_\gamma,
 \qquad
 \mu(O_\gamma)<r,
 \]

then the boundary leaf \(\delta\) lies in \(O_\gamma\), so
\(\delta\subset U_r\).  The only possible exception is a leaf
\(\delta_r\) whose domain is maximal among those of measure less than
\(r\).  Total nesting implies that there is at most one such leaf.

Consequently

\[
 \tau_a^{-1}((-\infty,r))
 =
 Z_a\cap U_r
 \quad\text{or}\quad
 (Z_a\cap U_r)\cup\delta_r.
 \tag{4.7}
\]

The first term is Borel.  A proper path has closed image in \(V\):
the path map is proper, hence closed, into the locally compact
Hausdorff surface.  Therefore the optional \(\delta_r\) is Borel as
well.

Equation (4.7) proves that every rational strict sublevel set is
Borel, hence \(\tau_a\) is Borel. \(\square\)

The “at most one maximal leaf” term is essential.  Dropping it would
silently assume order-density of the lamination.

### Lemma 4.3 (the leaf-coordinate range is Borel)

Put

\[
 T_a:=\tau_a(Z_a).
 \tag{4.8}
\]

Then \(T_a\subset\mathbb R\) is Borel, and

\[
 G_a
 :=
 \{(\tau_a(x),x):x\in Z_a\}
 \subset T_a\times V
 \tag{4.9}
\]

is Borel.  Its vertical section at \(t\in T_a\) is exactly one leaf.

#### Proof

The map

\[
 x\longmapsto(\tau_a(x),x)
\]

is Borel and injective.  Fact LS makes its image \(G_a\) Borel.
Lemma 4.1 identifies each section \((G_a)_t\) with one leaf.

Every leaf is the image of a proper embedded copy of \(\mathbb R\).
It is closed in \(V\) and \(\sigma\)-compact.  Fact AK applied to the
Borel set \(G_a\subset\mathbb R\times V\) therefore makes its
projection \(T_a\) Borel. \(\square\)

Thus \(T_a\), with its inherited real order, is a standard-Borel leaf
space constructed from the Borel geometric union itself.

## 5. Borel proper-path parametrization

The previous section gives a Borel closed-set field of leaves.  This
section produces the jointly Borel evaluation required for maximal
lift continuation.

Let \(C(\mathbb R,V)\) have the compact-open Polish topology, using a
complete compatible metric on \(V\).  Let

\[
 \operatorname{PEmb}(\mathbb R,V)
\]

be the set of proper topological embeddings \(h:\mathbb R\to V\).

### Lemma 5.1 (proper embeddings form an invariant Borel set)

\(\operatorname{PEmb}(\mathbb R,V)\) is a Borel subset of
\(C(\mathbb R,V)\), invariant under precomposition by
\(\operatorname{Homeo}(\mathbb R)\).

#### Proof

Injectivity is the countable condition

\[
 \forall k\geq1\ \forall p,q\in\mathbb Q,\quad
 |p-q|\geq1/k
 \Longrightarrow
 d(h(p),h(q))>0,
\]

after replacing the final strict inequality by the equivalent
countable compact-separation conditions on bounded rational boxes and
using continuity.  This is Borel.

For properness, fix a compact exhaustion

\[
 K_m\subset\operatorname{int}K_{m+1},
 \qquad \bigcup_mK_m=V.
\]

The preimage of \(K_m\) is closed.  It is compact exactly when it is
bounded, which can be expressed as

\[
 \exists N\ \forall q\in\mathbb Q,\quad
 |q|\geq N\Longrightarrow h(q)\notin K_m.
 \tag{5.1}
\]

To make (5.1) closed under passage from rationals to all reals, one
may equivalently require avoidance of \(K_m\) while using
\(\operatorname{int}K_{m+1}\) in the converse direction.  The two
exhaustions give the same properness predicate.  Hence properness is
Borel.

Precomposition by a homeomorphism preserves injectivity and
properness. \(\square\)

For \(h\in\operatorname{PEmb}(\mathbb R,V)\), let

\[
 q(h):=h(\mathbb R)\in F(V),
 \tag{5.2}
\]

where \(F(V)\) is the Effros standard-Borel space of closed subsets of
\(V\).

### Lemma 5.2 (the image map is Borel and classifies reparametrization)

The map \(q\) is Borel.  For
\(h_1,h_2\in\operatorname{PEmb}(\mathbb R,V)\),

\[
 q(h_1)=q(h_2)
 \quad\Longleftrightarrow\quad
 h_2=h_1\circ\varphi
 \text{ for some }\varphi\in\operatorname{Homeo}(\mathbb R).
 \tag{5.3}
\]

#### Proof

For an open \(W\subset V\),

\[
 q(h)\cap W\ne\varnothing
 \quad\Longleftrightarrow\quad
 \exists s\in\mathbb Q:\ h(s)\in W,
 \tag{5.4}
\]

by continuity.  Equation (5.4) proves Effros Borelness.

If the images agree, both maps are homeomorphisms from
\(\mathbb R\) to the same embedded leaf, so
\(\varphi=h_1^{-1}\circ h_2\) is a homeomorphism of \(\mathbb R\).
The converse is immediate. \(\square\)

### Lemma 5.3 (Borel parametrization of the leaf field)

There exists a Borel map

\[
 \Theta_a:T_a\longrightarrow
 \operatorname{PEmb}(\mathbb R,V)
 \tag{5.5}
\]

such that

\[
 \Theta_a(t)(\mathbb R)=(G_a)_t.
 \tag{5.6}
\]

Consequently

\[
 e_a:T_a\times\mathbb R\longrightarrow V,
 \qquad
 e_a(t,s):=\Theta_a(t)(s),
 \tag{5.7}
\]

is jointly Borel, continuous in \(s\) for every \(t\), proper and
embedded on every fiber, and injective on
\(T_a\times\mathbb R\).

#### Proof

First show that

\[
 t\longmapsto (G_a)_t
 \tag{5.8}
\]

is Borel into \(F(V)\).  For open \(W\subset V\), the hit set in
(5.8) is the projection of

\[
 G_a\cap(T_a\times W).
\]

Its sections are open subsets of a proper leaf and hence
\(\sigma\)-compact.  Fact AK makes this projection Borel.

The map (5.8) is injective.  Fact LS therefore makes its range

\[
 \mathcal L_a:=\{(G_a)_t:t\in T_a\}
 \tag{5.9}
\]

Borel in \(F(V)\), with Borel inverse to (5.8).

The Polish group \(\operatorname{Homeo}(\mathbb R)\) acts continuously
on \(C(\mathbb R,V)\) by precomposition.  The invariant set

\[
 Y_a
 :=
 \{h\in\operatorname{PEmb}(\mathbb R,V):q(h)\in\mathcal L_a\}
 \tag{5.10}
\]

is Borel by Lemmas 5.1--5.2.  Its orbit equivalence relation is smooth:
the Borel map \(q\) reduces it to equality on \(\mathcal L_a\).
Fact B supplies a Borel transversal \(B_a\subset Y_a\).

The restriction

\[
 q|_{B_a}:B_a\longrightarrow\mathcal L_a
\]

is a Borel bijection.  Fact LS makes its inverse Borel.  Compose this
inverse with (5.8) to obtain \(\Theta_a\).

The evaluation map

\[
 C(\mathbb R,V)\times\mathbb R\to V
\]

is continuous.  This proves joint Borelness in (5.7).  Fiberwise
properties follow from membership in \(\operatorname{PEmb}\), and
global injectivity follows from disjointness of distinct leaves.
\(\square\)

### Lemma 5.4 (Borel ideal endpoints)

The two ideal endpoint maps of the family (5.7) are Borel.

#### Proof

Use the metrizable prime-end compactification
\(\overline V^{\,\rm pe}\).  Properness and KKL's proper-path
compactification statement imply that, for each \(t\),

\[
 e_a^\pm(t)
 :=
 \lim_{n\to\infty}\Theta_a(t)(\pm n)
 \tag{5.11}
\]

exist on the ideal boundary.  Every map
\(t\mapsto\Theta_a(t)(\pm n)\) is Borel.  A pointwise limit of Borel
maps into a compact metrizable space is Borel, proving the claim.

If an orientation is required, compare the two endpoints with the
two fixed marked ends of the arc class and reverse
\(\Theta_a(t)\) when necessary.  This is a Borel two-case operation.
\(\square\)

## 6. Assembly over all arc classes

Define

\[
 T_{\mathscr S}
 :=
 \mathop{\bigsqcup}_{a\in A}(\{a\}\times T_a)
 \tag{6.1}
\]

and

\[
 e_{\mathscr S}(a,t,s):=e_a(t,s).
 \tag{6.2}
\]

### Theorem 6.1 (standard-Borel realization of a proper KKL Wave)

Assume the arc-class Borel reading in Definition 2.1.  Every proper
Borel KKL Wave in the proof-used annulus admits:

1. a standard-Borel leaf space \(T_{\mathscr S}\);
2. a jointly Borel proper-path evaluation (6.2);
3. Borel ideal endpoint maps;
4. Borel arc, endpoint-marking, base, crest, and leafwise direction
   predicates; and
5. on every leafwise common-crest packet, a Borel real order agreeing,
   up to reversal, with the native annular order.

#### Proof

A countable disjoint union of standard-Borel spaces is standard
Borel.  Equations (5.7) and (6.2) give the evaluation.  Lemma 5.4 gives
the endpoints.

The arc-class index is discrete.  Within one class, the two endpoint
marking intervals and the boundary-parallel homotopy direction are
fixed.  Therefore base, crest, and the predicate

\[
 BL_j\subset\operatorname{crest}(\{\gamma\})
\]

are finite cyclic-order predicates in the endpoint and class codes.
They are Borel.

For a leafwise packet above a fixed interval \(J\), every \(J\)-side
domain contains \(J\); the proof of Lemma 3.2 applies across all arc
classes in that packet.  Its area coordinate is strictly monotone
with the nesting order.  Repeating Section 4 gives a Borel real order
on the whole packet.  This is the same order as the lift/deck order
used by DL, up to reversal, because both are the separation order of
the same disjoint crosscuts. \(\square\)

### Red-team qualification 6.2

Theorem 6.1 does **not** follow from the bare assertion that the total
geometric union is Borel.  It uses the native source assertion that
each arc-class sublamination is itself proper Borel.  A countable
atlas controls lifts of an already Borel path code; it cannot create
that initial arc-class Borel decomposition.

## 7. Filtered immersion occurrences

Let

\[
 \iota:V'\to V
\]

be the KKL holomorphic immersion, hence a local homeomorphism.  Let
\((T_{\mathscr S},e_{\mathscr S})\) be Theorem 6.1's presentation.

### Lemma 7.1 (Borel maximal-lift occurrence relation)

The relation

\[
 \mathscr R_\iota(t,\omega)
\]

saying that \(\omega\) is one maximal proper component of the
\(\iota\)-restriction of the leaf \(e_{\mathscr S}(t,\mathbb R)\),
surviving both KKL filters, is Borel and has countable sections over
\(t\).

#### Proof

Choose a countable family of relatively compact simply connected
target disks \((D_m)\) such that every component of
\(\iota^{-1}(D_m)\) supports one inverse branch.  Second countability
of \(V'\) makes the set of such source components countable.

Enumerate the fiber

\[
 \iota^{-1}(e_{\mathscr S}(t,q))
\]

at a rational seed time \(q\) by Lusin--Novikov; the fiber is discrete
and hence countable.  A lift code consists of:

\[
 (t,q,m,r,\mathbf w),
 \tag{7.1}
\]

where \((m,r)\) selects the initial inverse chart and
\(\mathbf w\) is a finite or countable continuation word in the
chart atlas.

For a compact rational time interval \([u,v]\), compatibility with
one finite continuation word is Borel.  Indeed, membership of the
fiber path in an open chart for every \(s\in[u,v]\) can be checked on
the countable dense rational times: \(s\mapsto e_{\mathscr S}(t,s)\)
is continuous, while every rational evaluation is Borel in \(t\).
Equivalently, the relevant compact suprema of distance-to-complement
are countable suprema over rational times.

Continuation over every compact time interval is a countable
intersection of these Borel predicates.  Maximality is expressed by
failure of continuation in every larger rational interval.

Fix a compact exhaustion

\[
 K_m'\subset\operatorname{int}K_{m+1}'\subset V'.
\]

Proper escape of the lifted path is the Borel condition

\[
 \forall m\ \exists N,k\ \forall q\in\mathbb Q,\quad
 |q|\geq N
 \Longrightarrow
 d(\widetilde\gamma(q),K_m')\geq1/k.
 \tag{7.2}
\]

The positive distance in (7.2) is needed.  The weaker condition
“rational points do not belong to \(K_m'\)” would not exclude an
irrational contact or asymptotic accumulation on \(K_m'\).
Continuity extends (7.2) from rational to all real times, and the
compact exhaustion makes it equivalent to properness.

The Borel endpoint maps from Lemma 5.4 make fine-marking membership
Borel.  The explicit pulled-interval formula at KKL 1254--1260 makes
subordination to a single coarse interval a finite endpoint/deck
predicate, hence Borel.

Two codes describe the same maximal lift exactly when their
evaluations agree at every rational time in their common domain; this
is Borel.  Retain the lexicographically first code.  The resulting
occurrence relation is Borel.

Finally, a local homeomorphism between second-countable surfaces has
countable point fibers.  A maximal lift is determined by one rational
seed and one point in such a fiber.  Hence every source leaf has only
countably many occurrence codes. \(\square\)

### Lemma 7.2 (Borel directed restriction and successor)

Let \(\mathscr S=\mathscr S^{\rm nbr}\) and
\(\mathscr S\uparrow I\).  Put \(J=\iota^*I\).  Then:

1. the directed occurrence set \(B_I(\mathscr S)\) is Borel in the
   occurrence space;
2. its geometric union is a proper Borel lamination;
3. on an unbreakable source family, the unique untagged successor
   \(\Phi_1\) is Borel; and
4. for every Borel target leaf set \(E\), the full source saturation
   \(\Phi_1^{-1}(E)\) is a Borel leaf set with Borel geometric union.

#### Proof

Individual direction above \(J\) is a cyclic endpoint/deck predicate
in the occurrence code and is Borel.  Lemma 7.1 supplies a Borel
countable-section occurrence relation.  Finite directionalization
gives at least one directed occurrence for every source leaf.

The occurrence evaluation is Borel and fiberwise continuous.  After
duplicate occurrence codes are removed, it is injective on the
parameterized occurrence space.  Fact LS makes the geometric union
Borel.  Components remain disjoint by the local-homeomorphism
argument, so it is a proper lamination.

Compose each occurrence with the covering map \(f\).  This is Borel
on path codes.  Unbreakability says that every retained occurrence
has the same untagged output.  Taking the output of the least
occurrence code therefore defines the native \(\Phi_1\) and is Borel.

The inverse image of \(E\) is Borel in the source leaf space.  The
restriction of the injective evaluation to that leaf set is Borel;
Fact LS makes its geometric image Borel. \(\square\)

## 8. DL pruning needs order, not a new transverse measure

### Lemma 8.1 (Borel deck classes)

In a directed annular packet, the DL deck-span class of a leaf is a
Borel integer-valued function.

#### Proof

Lift the two Borel ideal endpoint maps to a fixed fundamental interval
of the universal-cover boundary.  Their relative deck displacement is
integer-valued and Borel.  The dyadic class at DL 2830--2838 is a
finite arithmetic predicate in that integer. \(\square\)

### Lemma 8.2 (every outer order cut is Borel)

Let \(T\subset\mathbb R\) be the Borel leaf-coordinate set of a
directed packet.  Every initial or terminal order segment of \(T\) is
Borel.

#### Proof

Every downward-closed subset \(D\) of a real linear order has one of
the forms

\[
 T\cap(-\infty,a),
 \qquad
 T\cap(-\infty,a]
\]

for \(a=\sup D\), with the evident empty/all variants.  These sets are
Borel.  The terminal case is identical. \(\square\)

### Corollary 8.3 (Borel DL retained packet)

The DL retained packet \(B^\sharp\) and discarded packet
\(B^{\rm bad}\) at DL 2821--2842 are Borel.

#### Proof

The finitely many dyadic deck-span classes are Borel by Lemma 8.1.
The final deleted “outermost curves” are an initial and/or terminal
order segment in the native annular order.  The area order of
Theorem 6.1 agrees with that order up to reversal, so Lemma 8.2 makes
the cuts Borel.

No transverse measure is needed to prove **measurability** of the cut.
Extremal width is used only to prove that the chosen buffer has the
stated bounded width. \(\square\)

This separates two issues which were previously conflated:

```text
existence and width of the DL buffer:  native DL 2830--2841
Borelness of the outer order cut:      Lemma 8.2
```

## 9. Borel stationary induction

This section applies the preceding construction to the analytic N1
proof.  It makes one harmless change at the initial two-direction
step.

### Hypothesis 9.1 (native initial proper Wave)

The source-defined

\[
 A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}
 \tag{9.1}
\]

is a proper Borel KKL Wave in the native standing sense.

KKL line 1548 uses \(A_0\) as a subwave, while KL06/KKL standing
conventions make proof-used laminations proper.  If an audit refuses
that source reading, Hypothesis 9.1 must remain explicit; this note
does not derive Borelness of (9.1) from a bare Borel union \(A\).

### Lemma 9.2 (Borel initial direction split)

Under Hypothesis 9.1 and Definition 2.1, the leafwise classes

\[
 A_0^+\uparrow BL_1,
 \qquad
 A_0^-\uparrow BL_{-1}
 \tag{9.2}
\]

from the two-direction lemma are Borel leaf sets with proper Borel
geometric unions.

#### Proof

Theorem 6.1 supplies a standard-Borel leaf space and Borel endpoints,
arc class, and crest predicates for \(A_0\).  Membership of the whole
finite marked block \(BL_1\) in a singleton crest is therefore Borel.
The positive class is that Borel set; the negative class is its
complement.  Fact LS applied to the restricted evaluations gives
Borel geometric unions. \(\square\)

### Proposition 9.3 (Borel initial continuation without cross-packet
saturation)

For \(q>2\), apply the analytic one-packet proposition only to
\(A_0^+\).  Let

\[
 P_{C,0}^+\subset A_0^+,
 \qquad
 \Phi_1(P_{C,0}^+)=C_1.
 \tag{9.3}
\]

Define

\[
 A_1:=P_{C,0}^+,
 \qquad
 S_1:=C_1.
 \tag{9.4}
\]

Then \(A_1,S_1\) are proper Borel laminations,

\[
 \Phi_1(A_1)=S_1
\tag{9.5}
\]

exactly, and

\[
 \mathcal W(A_0\setminus A_1)
 \leq
 c_{\rm pre}+c_b^{\rm step}.
\tag{9.6}
\]

For \(q=2\), set \(A_1=S_1=\varnothing\); the precritical estimate
bounds all of \(A_0\).

#### Proof

The positive packet is Borel by Lemma 9.2 and has Theorem 6.1's
ordered presentation.  Lemmas 7.1--8.3 make the one-packet retained
set, output trichotomy, and central preimage Borel.  This gives (9.3)
as a Borel leaf set and (9.5) by the exact one-packet construction.

Unlike the analytic draft, do **not** saturate \(P_{C,0}^+\) across
the already charged negative packet.  The two discarded families are
disjoint:

\[
 A_0\setminus A_1
 =
 A_0^-
 \mathbin{\dot\cup}
 (A_0^+\setminus P_{C,0}^+).
\]

The precritical and one-packet estimates give (9.6) by the Parallel
Law.  No width is lost by declining to retain additional negative
parents which happen to have the same untagged output. \(\square\)

This modification is analytically conservative and measurably
stronger: it avoids asking for a successor map on a packet which has
already been charged and discarded.

### Proposition 9.4 (Borel inductive continuation)

Suppose \(1\leq n<N-1\), \(A_n\) is a Borel leaf subset of the
standard-Borel source space inherited from \(A_1\), and

\[
 S_n=\Phi_n(A_n)
\]

is either empty or a Borel directed Wave ending at \(BL_0\).
Then the analytic one-packet construction produces a Borel
\(P_{C,n}\subset S_n\), and

\[
 A_{n+1}
 :=
 A_n\cap\Phi_n^{-1}(P_{C,n})
\tag{9.7}
\]

is a Borel leaf set with proper Borel geometric union.  Moreover,

\[
 \Phi_{n+1}(A_{n+1})=C_{n+1}
\tag{9.8}
\]

exactly.

#### Proof

Theorem 6.1 and Lemmas 7.1--8.3 make every directed restriction,
DL retained packet, output label, and one-step successor Borel.
Thus \(P_{C,n}\) is Borel.

The map \(\Phi_n\) is the composition of the already constructed
Borel one-step successors on \(A_1\).  Hence (9.7) is Borel in the
source leaf space.  Restricting its injective evaluation and applying
Fact LS makes its geometric union Borel.

Full preimage in (9.7), together with
\(P_{C,n}\subset\Phi_n(A_n)\), gives

\[
 \Phi_n(A_{n+1})=P_{C,n}.
\]

Composition with the exact one-step equality
\(\Phi_1(P_{C,n})=C_{n+1}\) proves (9.8). \(\square\)

### Theorem 9.5 (candidate Borel closure of Gate N1)

Assume:

1. the arc-class Borel reading in Definition 2.1;
2. the native initial proper-Wave reading in Hypothesis 9.1; and
3. the analytic leafwise-directed N1 theorem and its constants.

Then all \(A_n,S_n\) in the modified construction
(9.4), (9.7) are proper Borel laminations, every retained/discarded
occurrence packet is Borel, and

\[
 \mathcal W(A_n\setminus A_{n+1})\leq C_b
 \qquad(0\leq n<N-1)
\tag{9.9}
\]

with the same admissible choice

\[
 C_b
 =
 \max\left\{
 c_{\rm pre}+c_b^{\rm step},
 2^{b+1}c_b^{\rm step}
 \right\}.
\tag{9.10}
\]

The constant is independent of \(q\), the Wave, the corridor length,
and all analytic widths.

#### Proof

Proposition 9.3 gives the Borel initial step and the first term of
(9.10).  Proposition 9.4 iterates through exactly the transitions

\[
 1\leq n\leq N-2=b+1.
\]

The analytic sequential relative transfer gives

\[
 \mathcal W(A_n\setminus A_{n+1})
 \leq
 2^n c_b^{\rm step}
 \leq
 2^{b+1}c_b^{\rm step}.
\]

All measurable statements were proved before this width estimate.
\(\square\)

## 10. Correct source-loss partition

At a noncritical one-packet step, define

\[
 \begin{aligned}
  \mathsf K
  &:=
  \{\alpha\in S:\Phi_1(\alpha)\in C\}=P_C,\\
  \mathsf D_{\rm bad}
  &:=
  (S\setminus P_C)\setminus S^\sharp,\\
  \mathsf D_E
  &:=
  (S\setminus P_C)\cap S^\sharp .
 \end{aligned}
\tag{10.1}
\]

These are a genuine Borel disjoint partition.  They satisfy

\[
 \mathcal W(\mathsf D_{\rm bad})
 \leq c_{\rm DL},
\qquad
 \mathcal W(\mathsf D_E)
 \leq2\mathcal W(E).
\tag{10.2}
\]

The first inequality follows because every directed occurrence of a
\(\mathsf D_{\rm bad}\)-parent lies in \(B^{\rm bad}\).  The second
follows because a retained occurrence of a
\(\mathsf D_E\)-parent lies in

\[
 B_E=B^\sharp\cap f^{-1}(E)\subset f^*E.
\]

This replaces the overlapping three-class ledger formerly printed as
(10.4) in the analytic draft.

## 11. Adversarial audit

### 11.1 No hidden leaf quotient

The leaf coordinate \(\tau_a\) is defined set-theoretically from the
declared leaves, but its Borelness is proved directly on the Borel
geometric union by (4.7).  No same-leaf equivalence relation is assumed
Borel.

### 11.2 No false projection theorem

The projection \(T_a\) is not called Borel merely because it is an
image of a Borel map.  Fact AK is invoked only after every vertical
section is identified as one closed \(\sigma\)-compact proper leaf.

### 11.3 Order gaps

The optional maximal leaf in (4.7) handles jumps in the leaf order.
The proof assumes neither order density nor a full foliation of the
annular region.

### 11.4 Non-locally-connected carrier

All separation takes place in the prime-end annulus.  No landing of
prime ends on unique points of \(\mathcal T\) and no local
connectivity are used.

### 11.5 Parameterization is selected only after smoothness

A Borel selector for path parametrizations is not inferred from an
arbitrary Borel surjection.  Burgess applies because reparametrization
is a Polish-group orbit relation and the closed leaf image is a Borel
complete invariant.

### 11.6 Properness test

The lift properness predicate uses the positive-distance condition
(7.2).  Checking only that rational samples avoid a compact set is
insufficient and is rejected.

### 11.7 Outer buffer

Borelness of a DL buffer comes from its being an order interval in a
Borel subset of \(\mathbb R\).  No claim is made that extremal width is
a countably additive transverse measure on an arbitrary lamination.

### 11.8 Initial saturation

The initial negative packet is bounded and discarded.  Saturating the
positive central output across that negative packet is unnecessary
and could reintroduce a measurable source relation.  Proposition 9.3
does not do it.

### 11.9 Repeated untagged outputs

Repeated source parents with one untagged output do not break the
Borel successor: unbreakability makes the output single-valued.
They also do not duplicate the width charge, because the disjoint
source partition is (10.1), while the covering multiplicity appears
only as

\[
 \mathcal W(B_E)\leq2\mathcal W(E).
\]

### 11.10 Constants and horizon

No measurable theorem introduces a numerical constant.  The only
factor added by backward source transfer remains

\[
 2^{N-2}=2^{b+1}.
\]

No \(A_N\) is constructed.

## 12. Exact status after this pass

| item | status in this note |
|---|---|
| nested-domain coordinate on one Borel arc class | proved |
| Borelness of the coordinate | proved |
| Borel leaf-coordinate range | proved via AK |
| jointly Borel proper-path parametrization | proved via Burgess |
| Borel endpoints and cyclic predicates | proved |
| Borel maximal filtered occurrence calculus | proved in Lemma 7.1, audit required |
| Borel DL outer cuts | proved from real order |
| Borel N1 induction | proved under Definition 2.1 and Hypothesis 9.1 |
| `ARC_CLASS_SUBLAMINATION_IS_PROPER_BOREL` | native-source reading; independent audit required |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` for proof-used N1 Waves | candidate proved subject to the preceding source reading |
| universal theorem for arbitrary undecomposed Borel path unions | not claimed |
| Gate N1 ledger promotion | not performed here |
| Gate N2, VAAPC-I, UPTCR, MLC | open |

The first possible failure certificate is now exact:

```text
source Wave S
arc class alpha
KL06/KKL reason S(alpha) is or is not a proper Borel sublamination
first rational sublevel r for which equation (4.7) fails
first maximal-lift chart word whose continuation predicate is non-Borel
first DL deleted set which is not an order interval
```

If Definition 2.1 is accepted in the standing native sense and
Lemma 7.1 survives independent audit, no further measurable interface
remains in Gate N1.
