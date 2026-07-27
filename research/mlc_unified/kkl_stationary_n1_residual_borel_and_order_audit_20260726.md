# Gate N1 residual audit: ordered limb blocks and measurable saturated cores

## 0. Scope and exact verdict

This note audits only the following two residual claims in the directed,
leafwise-common-crest route to

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION
```

1. the cyclic order of the limb multi-intervals \(BL_j\), including the
   non-locally-connected KKL model; and
2. the standard-Borel status of the explicit occurrence-saturated
   continuation cores.

The conclusions are different.

### Ordered limb blocks

The required statement is **proved below without using a monotone
projection from the actual filled Julia set to the rational-lamination
model**.  The proof uses only:

- KKL's actual planar cyclic ordering of the limbs;
- the actual lifted Hubbard-tree vertices, edges, and sides;
- KKL's assertion that each \(BL_j\) is a connected multi-interval; and
- the side inventory used in KKL's proof of
  \(\ell(BL_j)\leq 6b\).

### Measurable saturated cores

The locked sources do **not** supply a complete standard-Borel
construction for an arbitrary KKL Wave.  In particular, the KL06
definition that a proper lamination is a Borel subset of the surface
does not by itself provide:

- a standard-Borel space of leaves;
- a Borel quotient map from points to leaves;
- a Borel relation of maximal filtered immersion-lift occurrences; or
- a Borel choice of the "outermost" buffers removed in the DL annular
  pruning proof.

A complete conditional construction is given in Section 4 under an
explicit **standard-Borel ordered-Wave presentation**.  The exact
missing source theorem is isolated in Section 5.  Until that theorem,
or an equivalent foliation-level realization, is proved, any claim that
the explicit saturated cores are Borel for every arbitrary KKL input
Wave is open.

This descriptive-set qualification does not invalidate extremal width
for the underlying literal path families: KL06 defines extremal width
and its Parallel Law for arbitrary path families.  It does prevent
promotion of an additional theorem clause that specifically requires
standard-Borel leaf spaces and Borel saturated cores.

Nothing here addresses the later stationary alignment, VAAPC-I, UPTCR,
rigidity, parameter fibers, or MLC.

## 1. Frozen source record

The local source copies used here are:

| source | SHA-256 |
|---|---|
| KKL, `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| Dudko--Lyubich, `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| KL06, `.tmp_kl06_source/wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |
| KL06, `.tmp_kl06_source/appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |

The exact source clauses relevant to this audit are:

1. KKL 497--503: the actual limbs \(\mathcal F L_j\) are labeled in
   counterclockwise cyclic order around \(\alpha_F\);
2. KKL 512--543: the Hubbard tree, its vertices and edges, and the
   lifted objects in the non-locally-connected case;
3. KKL 757: the ideal marking is induced by the actual sides of the
   lifted vertex/edge carrier;
4. KKL 838--842: \(BL_j=\partial_{\rm C}\mathcal L_j\) is a connected
   multi-interval;
5. KKL 856--866, especially 861: every marked interval in \(BL_j\)
   is a side of a vertex different from \(\alpha_F\), or a side of an
   edge, in the limb subtree \(G_j\);
6. KKL 1254--1274: the explicit pulled-interval formula and the
   combinatorial action;
7. KKL 1477--1478: the full filtered restriction of the unbreakable
   part is a common-crest Wave;
8. KKL 1839--1875: ideal markings, multi-intervals, paths, laminations,
   bases, ends, and crests;
9. KKL 2081--2142: immersion restrictions and the two marking filters;
10. KL06 `wad.tex` 142--160: a proper lamination is a Borel subset of
    the surface explicitly realized as a union of disjoint proper
    paths;
11. KL06 `appendix.tex` 13--36 and 59--68: extremal width and the
    Parallel Law apply to arbitrary path families; and
12. DL 2821--2842: the annular deck-span pruning and the deletion of
    finitely many outer buffers.

No statement at KKL 542--543 that the projection to the combinatorial
model is monotone is used below.

## 2. Ordered limb blocks without a monotone quotient

Let

\[
 V=\mathcal U\setminus\mathcal T .
\]

Since \(\mathcal U\) is a conformal disk and \(\mathcal T\) is connected
and full, the inner ideal-boundary component of \(V\) is a circle.  Let
\(\mathcal I\) be KKL's marking by actual sides of the lifted
Hubbard-tree carrier.

For a multi-interval \(J\), define its marked support by

\[
 \operatorname{supp}_{\mathcal I}(J)
 :=
 \{\mathcal B I\in\mathcal I:\mathcal B I\subset J\}.
 \tag{2.1}
\]

### Lemma 2.1 (disjoint marked interiors)

If \(j\neq k\), then

\[
 \operatorname{supp}_{\mathcal I}(BL_j)
 \cap
 \operatorname{supp}_{\mathcal I}(BL_k)
 =
 \varnothing .
 \tag{2.2}
\]

The closures of \(BL_j\) and \(BL_k\) may share marked endpoints, but
their open marked interiors do not overlap.

#### Proof

Let \(G_j\) be the limb subtree used in KKL's proof of the combinatorial
size bound.  KKL 861 states that every interval of \(BL_j\) is the side
of one of the following actual lifted objects:

1. a vertex of \(G_j\) different from \(\alpha_F\); or
2. an edge of \(G_j\).

The components \(\mathcal L_j=\mathcal F L_j\cap\mathcal T\) are
pairwise disjoint away from \(\alpha_F\).  Consequently, for
\(j\neq k\),

\[
 (G_j\setminus\{\alpha_F\})
 \cap
 (G_k\setminus\{\alpha_F\})
 =
 \varnothing ,
 \tag{2.3}
\]

both at the vertex level and at the edge level.

A marked ideal interval is one actual side of one such lifted object.
It cannot simultaneously be a side of two different objects in the
disjoint sets in (2.3).  Sides incident only to the sector at
\(\alpha_F\) do not create an exception: KKL 861 explicitly excludes
\(\alpha_F\) from the vertex list contributing intervals to \(BL_j\).
Thus no marked interval belongs to both supports, proving (2.2).
\(\square\)

### Lemma 2.2 (native ordered-limb-block lemma)

The connected multi-intervals

\[
 BL_0,BL_1,\ldots,BL_{q-1}
 \tag{2.4}
\]

are noninterleaving blocks on the inner ideal-boundary circle.  Their
cyclic order is

\[
 BL_0,BL_1,\ldots,BL_{q-1},
 \tag{2.5}
\]

up to reversal if the orientation of the ideal-boundary circle is
reversed.

This statement holds in the non-locally-connected KKL case.

#### Proof

KKL 838 states that every \(BL_j\) is a connected multi-interval.
Lemma 2.1 shows that the marked interiors of two different \(BL_j\)'s
are disjoint.  Two connected open blocks with disjoint interiors on a
circle cannot interleave.  This proves the block assertion.

It remains to identify the order.  Work with the actual lifted
Hubbard-tree objects, not with a map from the actual filled Julia set
to its combinatorial model.  At \(\alpha_F\), the first actual
vertex/edge germ entering each component \(\mathcal L_j\) inherits the
ribbon order from the orientation of the dynamical plane.  KKL's
labeling at 501 is precisely the counterclockwise cyclic order of these
limb germs.

For each \(j\), the two sides of an edge germ entering
\(\mathcal L_j\), followed along the boundary of a sufficiently small
regular neighborhood of that germ, lie in the prime-end block
\(\partial_{\rm C}\mathcal L_j=BL_j\).  Because \(BL_j\) is connected
and the different blocks cannot interleave, replacing an edge germ by
the entire connected limb subtree cannot change the cyclic position of
its block.  Hence the block order is exactly the ribbon order of the
limb germs, which is (2.5).

In the non-locally-connected case, KKL 542--543 first constructs the
vertices, edges, and their ribbon incidences in the locally connected
combinatorial Hubbard tree and then **lifts those actual objects and
sides** to the dynamical carrier.  The preceding proof uses only the
lifted edge germs, their actual planar sides, and the connectedness
assertion at KKL 838.  It neither takes an inverse image of a
prime-end interval under the model projection nor requires that
projection to be monotone.

When \(q=2\), there are only two blocks, so the order assertion is
tautological; the residue classes \(1\) and \(-1\) coincide.  Shared
endpoints between adjacent block closures do not affect the statement,
which concerns open marked interiors and cyclic order.
\(\square\)

### Corollary 2.3 (two-direction singleton dichotomy)

Let \(\gamma\) be a nonshort Wave leaf with an endpoint in \(BL_0\).
Then

\[
 BL_1\subset\operatorname{crest}(\{\gamma\})
 \quad\text{or}\quad
 BL_{-1}\subset\operatorname{crest}(\{\gamma\}).
 \tag{2.6}
\]

If the singleton base is the whole inner boundary, both alternatives
hold unless an endpoint interval removes one of them; in the latter
case the other alternative holds.  For \(q=2\), nonshortness forces
the single noncentral block \(BL_1=BL_{-1}\) into the crest.

#### Proof

The endpoint interval in \(BL_0\) prevents the singleton crest from
containing all of \(BL_0\).  Nonshortness therefore supplies a full
block \(BL_j\), \(j\neq0\), in the crest.  Traverse the connected
singleton base from the selected \(BL_0\)-end toward that full block.
By Lemma 2.2, the first complete noncentral block in the chosen
direction is \(BL_1\) or \(BL_{-1}\).  It lies before the full
\(BL_j\)-block and is not an endpoint interval, so it lies in the
crest.  The whole-boundary and \(q=2\) cases follow by the same
argument. \(\square\)

## 3. What “Borel lamination” does and does not give

KL06 `wad.tex` 142--143 defines a proper lamination to be a Borel set
\(Z\) in the surface, explicitly realized as a union of disjoint proper
paths.  This provides a Borel **point set**

\[
 Z\subset V.
 \tag{3.1}
\]

It does not, as stated, provide a standard-Borel set \(L\) and a Borel
map

\[
 \operatorname{ev}:L\times(0,1)\longrightarrow V
 \tag{3.2}
\]

whose fibers are exactly the leaves.  In particular, it does not state
that the equivalence relation

\[
 x\,E_Z\,y
 \quad\Longleftrightarrow\quad
 x\text{ and }y\text{ lie on the same leaf of }Z
 \tag{3.3}
\]

is Borel or smooth.

This distinction is essential.  For an arbitrary Borel subset of a
Polish surface, the connected-component relation need not have a
Borel transversal, and saturating a Borel point set by components need
not be a Borel operation.  The word “explicitly” in the KL06
definition records a leaf decomposition, but the cited passage does
not impose a standard-Borel structure on that decomposition.

The following later operations therefore are not automatically Borel
from (3.1):

1. partitioning leaves by the \(+\)/\(-\) crest direction;
2. taking all proper components of
   \(\iota^{-1}(\gamma)\) which survive both KKL marking filters;
3. identifying the unique untagged successor of an unbreakable leaf;
4. taking the full leaf saturation of a terminal subfamily; and
5. deleting an “outermost” transverse buffer in the DL proof.

Lusin--Novikov cannot be invoked until a Borel leaf/occurrence relation
on standard-Borel spaces has first been constructed.  Lusin--Souslin
cannot be invoked until the geometric evaluation map and its
injectivity have first been supplied.  Those theorems do not create the
missing leaf presentation.

## 4. Conditional standard-Borel construction

This section records the exact additional structure under which all
explicit protected cores are Borel.

### Definition 4.1 (standard-Borel ordered-Wave presentation)

A proper Wave \(\mathscr S\) has a standard-Borel ordered-Wave
presentation if it is supplied with:

1. a standard-Borel leaf space \(L_{\mathscr S}\);
2. a jointly Borel evaluation map
   \[
      e_{\mathscr S}:L_{\mathscr S}\times(0,1)\to V
      \tag{4.1}
   \]
   such that \(e_{\mathscr S}(\ell,\cdot)\) is a proper embedded path
   for every \(\ell\), different leaves have disjoint images, and the
   geometric union is \(\mathscr S\);
3. Borel endpoint maps into the metrizable ideal-boundary circle;
4. on every common-crest annular packet, a Borel linear order of leaves
   compatible with the annular deck order; and
5. a Borel transverse width measure for which the “outermost
   width-\(a\)” initial and terminal segments are Borel for every fixed
   \(a<\infty\).

Clause 5 is precisely the measurable structure used, but not formally
stated, when the DL proof removes outermost buffers.

### Proposition 4.2 (Borel occurrence calculus under Definition 4.1)

Assume every proof-used Wave has a presentation as in Definition 4.1,
and assume the presentation is preserved by restriction to Borel leaf
subsets.  Then:

1. the \(+\)/\(-\) direction classes are Borel;
2. the retained immersion-occurrence space is standard Borel with
   countable fibers over source leaves;
3. on an unbreakable family, the untagged successor is a Borel map;
4. the DL retained and discarded packets are Borel;
5. central, over-critical, and away/localized output classes are Borel;
   and
6. every full untagged saturation used in the explicit stationary core
   is a proper Borel sublamination.

#### Proof

Choose a countable family of simply connected target disks
\((D_m)\), each relatively compact in a slightly larger disk on which
every inverse branch of \(\iota\) is defined.  Since the source surface
is second countable and \(\iota\) is a local homeomorphism, the
components of \(\iota^{-1}(D_m)\) form a countable family.  Enumerate
them by \(r\).

A maximal lift occurrence is coded by:

\[
 (\ell,m,r,s),
 \tag{4.2}
\]

where \(\ell\in L_{\mathscr S}\), \(s\in\mathbb Q\cap(0,1)\) is the
first rational seed time used by the code,
\(e_{\mathscr S}(\ell,s)\in D_m\), and the inverse branch indexed by
\((m,r)\) analytically continues along the leaf.

For rational \(0<a<b<1\), continuation over \([a,b]\) is witnessed by
a finite chain in the countable inverse-branch atlas.  It is therefore
a Borel predicate in the code (indeed it is a countable union of finite
chart-consistency predicates).  Continuation over all compact
subintervals is a countable intersection of these predicates.
Properness at an end can be written, for a fixed compact exhaustion
\((K_t)\) of the source, as

\[
 \forall t\ \exists n\ \forall u\in
 (0,1/n)\cup(1-1/n,1):
 \widetilde\gamma(u)\notin K_t,
 \tag{4.3}
\]

after checking on rational \(u\)'s and using continuity.  This is
Borel.  Membership of the two ideal endpoints in the countable fine
marking, and rejection for subordination to one coarse interval, are
Borel endpoint/deck-class predicates under Definition 4.1.

Discard duplicate seed codes by retaining the lexicographically first
code for each analytically continued maximal lift.  Equality of two
such lifts is determined on a rational compact exhaustion and is
Borel.  The resulting occurrence set

\[
 \mathscr O_\iota\subset L_{\mathscr S}\times\mathbb N
 \tag{4.4}
\]

is standard Borel and has countable vertical sections.

Composition with the covering \(f\) is Borel on path codes.  On an
unbreakable source family, all retained occurrence outputs represent
one untagged path.  Taking the output of the least occurrence code
therefore defines the same untagged successor as \(F_*\), and it is a
Borel function.

The leafwise predicates

\[
 BL_{\pm1}\subset\operatorname{crest}(\{\gamma\}),\qquad
 \gamma\text{ has an endpoint in }BL_0,
 \tag{4.5}
\]

are Borel because, in the annular universal cover, they are finite
cyclic-order and integer deck-class predicates in the Borel endpoint
coordinates.  The same observation applies to the central,
over-critical, and away/localized labels.

In the DL pruning, the deck-span class is an integer-valued Borel
function.  Definition 4.1(4)--(5) makes every dyadic span class and
every deleted outer buffer Borel.  Hence both the retained occurrence
packet and its complement are Borel.

Finally, the preimage of a Borel terminal leaf set under the Borel
untagged successor is Borel in \(L_{\mathscr S}\).  Restricting the
evaluation map (4.1) to that leaf set gives a Borel injective map on
the standard-Borel parametrized leaf space.  Lusin--Souslin implies
that its geometric image is Borel in \(V\).  It is a union of disjoint
proper leaves, so it is a proper Borel sublamination. \(\square\)

### Qualification 4.3

Proposition 4.2 is not a proof that an arbitrary KL06/KKL proper
lamination admits Definition 4.1.  It proves that, once the missing
presentation is supplied, no further measurable-selection obstruction
remains in the explicit saturated-core construction.

## 5. Exact unresolved descriptive-set theorem

The minimally sufficient missing result is the following.

### `STANDARD_BOREL_ORDERED_WAVE_REALIZATION`

Every proper Borel KKL Wave used in the stationary construction, and
every full filtered restriction packet produced from it, admits a
standard-Borel ordered-Wave presentation satisfying Definition 4.1,
such that:

1. endpoint, base, crest, and deck-span data are Borel;
2. the relation of maximal proper immersion-lift occurrences surviving
   both KKL filters is Borel with countable sections;
3. unbreakability induces a Borel untagged terminal map;
4. the DL outer-buffer pruning is a Borel leaf operation; and
5. geometric realization of a Borel leaf subset is again a Borel
   proper lamination.

The locked KKL, DL, and KL06 passages do not state or prove this
theorem.

There are two safe resolutions.

1. **Foliation-level resolution.**  Prove
   `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` for all proof-used Waves,
   for example by replacing each path family by an explicitly
   parameterized countable union of ordered rectangle foliations and
   proving that every restriction, buffer deletion, and saturation
   preserves that presentation.
2. **Minimal extremal-width formulation.**  State Gate N1 only in its
   literal path-family form.  KL06 extremal width and the Parallel Law
   apply in this category, so the two-direction/DL width construction
   does not require a Borel leaf quotient.  Do not then call the
   resulting cores “Borel” or invoke Lusin--Novikov/Lusin--Souslin.

An unsupported hybrid is not acceptable: one cannot start only with a
Borel union \(Z\subset V\) and infer the standard-Borel leaf and
occurrence spaces required by Proposition 4.2.

## 6. Corrections required in the current directed-route drafts

### 6.1 Ordered blocks

Replace any sentence of the form

> the quotient is monotone, so inverse images of connected access
> blocks are connected

by Lemmas 2.1--2.2 above.  Monotonicity is not stated at KKL 542--543
and is unnecessary.

### 6.2 Borel occurrence calculus

A claim that a countable inverse-branch atlas alone makes the leaf
occurrence relation Borel is incomplete.  The atlas controls lifts of
an already Borel **path code**.  It does not construct a standard-Borel
space of leaves from the bare Borel union of a lamination.

Likewise, writing “the outer buffer is a Borel initial segment” assumes
the ordered measurable leaf presentation that must first be proved.

The current proof should therefore either:

- add Definition 4.1 as an explicit hypothesis and cite Proposition
  4.2; or
- remove “Borel” from the minimal Gate N1 statement and record
  `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` as an open formal-interface
  refinement.

### 6.3 No effect on the two-direction analytic mechanism

The ordered-block proof validates the leafwise dichotomy, including:

- \(q=2\);
- shared prime-end block endpoints;
- a whole-inner-boundary singleton base; and
- the non-locally-connected KKL carrier.

It does not by itself prove the Borelness of the two direction
subfamilies.  Set-theoretically they are a disjoint exhaustive
partition.  They are Borel under Definition 4.1 by (4.5).

## 7. Final status

| item | status after this audit |
|---|---|
| ordered \(BL_j\) blocks in the locally connected case | proved |
| ordered \(BL_j\) blocks in the non-locally-connected KKL case | proved without a monotone projection |
| two-direction singleton dichotomy, including \(q=2\) and whole-boundary bases | proved |
| explicit saturated cores as literal path families | unaffected by this audit |
| explicit saturated cores as Borel sublaminations under Definition 4.1 | proved conditional |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` for arbitrary KKL Waves | open |
| Borel inclusion-maximal continuation | unnecessary for the explicit-core route and not supplied by the locked sources |
| Gate N1 with an added universal Borel-interface clause | not promoted by this note |
| VAAPC-I | open |
| UPTCR | open |
| MLC | open |

The immediate manuscript action is therefore exact:

1. install Lemmas 2.1--2.2 as the non-locally-connected ordered-block
   proof;
2. remove the unsupported monotonicity sentence;
3. choose either the literal path-family Gate N1 statement or the
   stronger Definition 4.1 hypothesis; and
4. do not assert unconditional Borel saturated cores until
   `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` is proved.
