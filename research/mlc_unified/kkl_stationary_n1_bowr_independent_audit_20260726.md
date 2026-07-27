# Gate N1: independent audit and repaired realization theorem

## 0. Scope, claim boundary, and verdict

This note audits only the remaining descriptive-set interface

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION
```

in

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION.
```

The audited candidate is
`kkl_stationary_n1_borel_ordered_wave_realization_20260726.md`.
No statement about Gate N2, VAAPC-I, UPTCR, rigidity, parameter
fibers, or MLC is considered here.

The verdict has two parts.

1. The central new idea is valid: on one proper Borel Wave packet,
   strict planar nesting and a finite full-support area measure give a
   Borel injective leaf coordinate.  Arsenin--Kunugui then gives a
   standard-Borel leaf space.  This is a genuine arbitrary-Wave
   realization argument and does not assume rectangle-foliation
   provenance.
2. The candidate is not correct as written.  Its first version omits
   nonempty zero-width arc classes, assumes incorrectly that every
   compactified leaf is an arc with two distinct ideal endpoints,
   counts restriction occurrences rather than distinct untagged
   outputs when testing breakability, and leaves four Borel coding
   steps implicit.  Each defect has an exact repair below.

The repaired result is conditional on one source-typing convention:

```text
ARC_CLASS_SUBLAMINATION_IS_PROPER_BOREL.
```

That convention is the natural literal reading of KL06
`wad.tex` 142--150 and KKL 1911, but it is a convention imported from
the word "sublamination", not a consequence of Borelness of the total
geometric support alone.

Accordingly, this audit does not promote either Gate N1 obligation.
Promotion requires integrating all repairs in Section 10 and making
the source-typing convention explicit in the theorem statement.

## 1. Frozen source record

| source | SHA-256 |
|---|---|
| KL06, `.tmp_kl06_source/wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |
| KL06, `.tmp_kl06_source/appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| KKL, `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| DL, `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |

The exact source clauses used in this audit are:

- KL06 `wad.tex` 23--50: proper paths and their images;
- KL06 `wad.tex` 83--101: arcs are proper-homotopy classes of
  nontrivial embedded paths, and disjoint arc diagrams have bounded
  cardinality;
- KL06 `wad.tex` 142--150: a proper lamination has Borel geometric
  support, all laminations under consideration are proper, and
  \(\mathcal F(\alpha)\) is called a sublamination;
- KKL 406: a proper path has a continuous two-tail extension to the
  ideal closure;
- KKL 1180--1182: the short part is the unique maximal short subwave;
- KKL 1355--1358: the \(n\)-unbreakable part is the subwave of leaves
  with single-path outputs through the stated horizon;
- KKL 1547--1548: the stationary construction starts with
  \(A^{N\text{-nbr}}\setminus A^{\rm sh}\);
- KKL 1844--1875: ideal boundary, ideal marking, marked paths, arcs,
  laminations, and Waves;
- KKL 1904--1914: finite marked arc diagrams and arc-class
  sublaminations;
- KKL 2065--2142: covering pushforward and filtered immersion
  restriction;
- KKL 2161--2162: breakability is defined by whether the untagged
  pushforward is a single path; and
- DL 2821--2842: deck-span decomposition and deletion of outermost
  buffers.

The descriptive-set inputs are Arsenin--Kunugui for Borel sets with
sigma-compact sections, Lusin--Novikov for countable sections,
Lusin--Souslin for injective Borel images, and Burgess's selection
theorem for smooth orbit relations of Polish group actions:

J. P. Burgess, *A selection theorem for group actions*, Pacific
Journal of Mathematics 80 (1979), 333--336,
doi:10.2140/pjm.1979.80.333.

## 2. The source-typing questions

### Proposition 2.1 (arc-class packet: exact source conclusion)

Assume the standing KL06 word "sublamination" retains its declared
type.  Then the geometric union of every

\[
 \mathcal F(\alpha)
 =
 \{\gamma\in\mathcal F:[\gamma]=\alpha\}
\tag{2.1}
\]

is Borel.

#### Proof

KL06 `wad.tex` 142--143 defines a proper lamination to be a Borel
geometric set explicitly decomposed into disjoint proper paths.
Line 144 states that all laminations under consideration are proper.
Lines 145--150 call \(\mathcal F(\alpha)\) a sublamination.  Under the
ordinary typed reading, a sublamination is again a lamination under
consideration and is therefore proper; Borel geometric support is part
of that definition.  KKL 1911 repeats the same sublamination syntax.
\(\square\)

This proof must not be replaced by the false inference

```text
the total union is Borel, therefore every saturated leaf subset is
Borel.
```

That implication fails for arbitrary equivalence-class
decompositions.  Proposition 2.1 records the semantic force of the
source's typed word.  If that reading is rejected editorially, (2.1)
must remain an explicit hypothesis.

### Proposition 2.2 (the correct finite packet index)

Let

\[
 \mathcal A(\mathcal F)
 =
 \{\alpha:\mathcal F(\alpha)\ne\varnothing\}.
\tag{2.2}
\]

Then \(\mathcal A(\mathcal F)\) is finite in the stationary
finite-marked surface.  It is not legitimate to replace
\(\mathcal A(\mathcal F)\) by
\(\operatorname{supp}W_{\mathcal F}\).

#### Proof

KL06 145--147 says that the nonempty arc classes form an arc diagram.
They are pairwise disjoint topological arcs.  The finite-topology
arc-diagram bound therefore makes their number finite.  Equivalently,
place coefficient one on every class in (2.2); the resulting
coefficient-one WAD has the same finite support and the KKL
finite-marked bound applies.

In contrast, a nonempty packet may have extremal width zero.  A single
proper leaf is the basic example.  Such a class is absent from the
support of the induced WAD but is still part of the geometric
lamination.  Therefore the decomposition must be

\[
 \mathcal F
 =
 \mathop{\dot\bigcup}_{\alpha\in\mathcal A(\mathcal F)}
 \mathcal F(\alpha),
\tag{2.3}
\]

not a union over positive-width support. \(\square\)

### Proposition 2.3 (short and unbreakable source subwaves)

Under the same typed-sublamination convention:

1. \(A^{\rm sh}\) is a proper Borel Wave;
2. \(A^{n\text{-nbr}}\) is a proper Borel Wave for every finite \(n\);
3. the leafwise difference
   \[
     A^{n\text{-nbr}}\setminus A^{\rm sh}
   \tag{2.4}
   \]
   has Borel geometric support and is a proper Borel sublamination.

#### Proof

KKL 1182 calls \(A^{\rm sh}\) the unique maximal short subwave.
KKL 1356 calls \(A^{n\text{-nbr}}\) the subwave consisting of the
specified leaves.  A subwave is, in particular, a sublamination, so
Proposition 2.1 supplies properness and Borel geometric support.

The geometric support of (2.4) is the set difference of the two Borel
supports.  Leaves of the ambient lamination are pairwise disjoint, so
this point-set difference removes whole leaves and remains a union of
disjoint proper embedded paths.  It is therefore a proper Borel
sublamination.  It remains subordinate to the connected parent base,
so whenever the analytic N1 construction uses it as a Wave, the Wave
typing is unchanged. \(\square\)

This is the safe route for \(h\)-unbreakability.  Section 7 proves why
raw restriction-occurrence counting is not an equivalent
reconstruction.

## 3. Planar order, including coincident ideal tails

Let \(V=\mathcal U\setminus\mathcal T\) be the stationary annulus.
Fix one Borel arc-class packet \(P\), and orient its marked
proper-homotopy class only for the purpose of choosing a side.

For a leaf \(\gamma\), let \(O_\gamma\) be the component on the
preferred boundary side.  In the universal annular strip, this is the
side bounded by a selected lift of \(\gamma\) and the boundary interval
containing a fixed lift of the singleton crest.  The definition also
covers a leaf whose two projected ideal tails agree: its selected lift
has distinct deck-related endpoints.

### Counterexample 3.1 (two distinct endpoints are not automatic)

In

\[
 A=\{1<|z|<2\},
\]

define

\[
 \gamma(t)
 =
 \left(1+\frac14\sin(\pi t)\right)e^{2\pi i t},
 \qquad 0<t<1.
\tag{3.1}
\]

Then:

1. \(\gamma\) is injective, since equality of the angular factors for
   \(s,t\in(0,1)\) forces \(s-t\in\mathbb Z\), hence \(s=t\);
2. it is proper, since both tails approach the missing inner boundary
   and the preimage of a compact subset of \(A\) stays away from
   \(0,1\);
3. both ideal tails converge to the same inner prime end \(1\); and
4. its prime-end closure is a Jordan circle, not a compact arc.

If the inner boundary has at least three marked intervals and the
common endpoint is inside one interval, (3.1) represents the generator
around the inner boundary.  A collar of a proper connected
multi-interval of combinatorial length at most two does not carry that
generator.  Thus the path is not excluded by KKL 1869 merely because
its two ideal values agree.

Consequently, the assertions "the boundary incidence section has
exactly two points" and "every \(K_s\) is a compact arc" are false for
the printed KKL path class.

### Lemma 3.2 (strict nesting with both tail types)

For distinct \(\gamma,\eta\in P\), exactly one of

\[
 O_\gamma\subsetneq O_\eta,
 \qquad
 O_\eta\subsetneq O_\gamma
\tag{3.2}
\]

holds.  The larger domain minus the closure of the smaller contains a
nonempty open set.

#### Proof

Pass to the closed universal annular strip.  A leaf with distinct
projected ideal endpoints lifts to a crosscut with distinct boundary
endpoints.  A nontrivial embedded leaf with coincident projected
endpoints lifts to a crosscut joining two distinct deck lifts of that
point.  Its deck displacement is nonzero; zero displacement would be
boundary-null and subordinate to an arbitrarily small boundary
multi-interval.  Embeddedness forces the displacement to be primitive.

Choose the deck translate of every lifted leaf for which the preferred
boundary interval contains one fixed lift of the crest.  If two such
boundary intervals were not nested, their endpoint pairs would
alternate in the boundary order.  The planar crosscut separation
theorem would force the two lifted leaves to meet.  Their projections
are distinct leaves of a lamination and are disjoint, so this is
impossible.

For nested boundary intervals, disjoint crosscuts bound nested
preferred-side regions.  Otherwise one crosscut would have points in
both complementary sides of the other and would meet it by
connectedness and separation.  Equality of the regions would make
their interior crosscut boundaries equal, again impossible for
distinct disjoint leaves.  Finally, the region between two distinct
crosscuts contains an open disk.  Projection gives (3.2) and the
nonempty open difference in \(V\). \(\square\)

The same proof works for a finite union of arc classes whose leaves are
all directed over one fixed nondegenerate marked interval \(J\): use
the \(J\)-side and a fixed lift of \(J\).  Equality of arc tags is not
needed.

### Lemma 3.3 (Borel area coordinate)

Choose a finite Borel measure \(\mu\) on \(V\) with full support and set

\[
 t(\gamma)=\mu(O_\gamma).
\tag{3.3}
\]

Regard \(t\) as the leaf-constant function on the Borel geometric
support \(Z_P\).  Then \(t:Z_P\to\mathbb R\) is Borel and is injective
between leaves.

#### Proof

Strict nesting and full support imply

\[
 O_\gamma\subsetneq O_\eta
 \Longrightarrow
 t(\gamma)<t(\eta),
\tag{3.4}
\]

so \(t\) is a strict order coordinate.

For rational \(r\), let

\[
 U_r=
 \bigcup_{\eta\in P,\ t(\eta)<r}O_\eta.
\tag{3.5}
\]

This is open without any measurability assumption on the leaf
quotient.  If \(\gamma\) meets \(U_r\), it lies on the preferred side
of some \(\eta\) with \(t(\eta)<r\), so strict nesting gives
\(t(\gamma)<t(\eta)<r\).  Conversely, if
\(t(\gamma)<t(\eta)<r\), the leaf \(\gamma\) lies in \(O_\eta\).

Thus \(Z_P\cap U_r\) contains precisely the leaves with coordinate
below \(r\), except possibly the unique leaf whose coordinate is

\[
 \max(t(P)\cap(-\infty,r)).
\tag{3.6}
\]

There is at most one such leaf by injectivity.  A proper embedded path
has closed image in \(V\), so adjoining that possible leaf preserves
Borelness.  Hence every rational strict sublevel of \(t\) is Borel,
and rational sublevels generate the Borel sigma algebra of
\(\mathbb R\). \(\square\)

### Lemma 3.4 (standard-Borel leaf coordinate)

The realized set \(L_P=t(P)\) is Borel in \(\mathbb R\), and the
relation

\[
 G_P=
 \{(s,x)\in\mathbb R\times V:
       x\in Z_P,\ t(x)=s\}
\tag{3.7}
\]

is a Borel field whose nonempty sections are exactly the leaves.

#### Proof

Lemma 3.3 makes \(G_P\) Borel.  Every section is empty or one closed
proper leaf and is therefore sigma-compact.  Arsenin--Kunugui makes
its projection \(L_P\) Borel. \(\square\)

This completes the genuinely new quotient construction.

## 4. A parameterization repair that includes based circles

The compact-initial-subarc construction in the candidate is correct
on the distinct-tail stratum, but Counterexample 3.1 shows that it
cannot cover all KKL leaves.  The following path-space construction
handles both distinct and coincident tails uniformly and avoids an
unstated distinct-endpoint hypothesis.

Let \(C(\mathbb R,V)\) carry the compact-open Polish topology.  Fix a
proper metric on \(V\) and a compact exhaustion

\[
 K_m\Subset\operatorname{int}K_{m+1},
 \qquad
 \bigcup_mK_m=V.
\tag{4.1}
\]

### Lemma 4.1 (proper embeddings form a Borel set)

The set \(\operatorname{PEmb}(\mathbb R,V)\) of proper topological
embeddings is Borel in \(C(\mathbb R,V)\).

#### Proof

For \(M,k\ge1\), let

\[
 D_{M,k}=
 \{(s,u)\in[-M,M]^2:|s-u|\ge1/k\}.
\]

This is compact.  A continuous map \(h\) is injective exactly when

\[
 \forall M,k,\qquad
 \min_{(s,u)\in D_{M,k}}
 d(h(s),h(u))>0.
\tag{4.2}
\]

The minimum in (4.2) depends continuously on \(h\) in the compact-open
topology.  Thus injectivity is a countable intersection of Borel
conditions.

Properness is equivalent to

\[
 \forall m\ \exists N,k\ \forall q\in\mathbb Q,\ |q|\ge N:
 \quad d(h(q),K_m)\ge1/k.
\tag{4.3}
\]

If \(h\) is proper, its tails eventually avoid \(K_{m+1}\); compact
containment in (4.1) gives the positive distance required in (4.3).
Conversely, continuity extends (4.3) from rational to real tail
times.  Then \(h^{-1}(K_m)\) is closed and contained in a bounded
interval, hence compact.  Formula (4.3) is countable and Borel.

A proper continuous injection into the Hausdorff locally compact
surface is a closed topological embedding. \(\square\)

### Lemma 4.2 (Borel image invariant)

For \(h\in\operatorname{PEmb}(\mathbb R,V)\), set

\[
 q(h)=h(\mathbb R)\in F(V),
\tag{4.4}
\]

where \(F(V)\) is the Effros standard-Borel space of closed subsets.
Then \(q\) is Borel and

\[
 q(h_1)=q(h_2)
 \Longleftrightarrow
 h_2=h_1\circ\phi
 \quad\text{for some }\phi\in\operatorname{Homeo}(\mathbb R).
\tag{4.5}
\]

#### Proof

For open \(W\subset V\),

\[
 q(h)\cap W\ne\varnothing
 \Longleftrightarrow
 \exists r\in\mathbb Q:\ h(r)\in W,
\]

which proves Effros Borelness.  If the images agree, each proper
embedding is a homeomorphism onto the same leaf, so
\(\phi=h_1^{-1}\circ h_2\) is a homeomorphism.  The converse is
immediate. \(\square\)

### Proposition 4.3 (joint Borel proper-leaf evaluation)

There is a jointly Borel map

\[
 e_P:L_P\times\mathbb R\longrightarrow V
\tag{4.6}
\]

whose fiber at \(s\) is a proper embedding onto \((G_P)_s\).
No assumption that the two ideal tails are distinct is needed.

#### Proof

First, \(s\mapsto(G_P)_s\) is Borel into \(F(V)\).  For an open
\(W\subset V\), its hit set is the projection of

\[
 G_P\cap(L_P\times W).
\]

The sections are open subsets of one proper leaf and are
sigma-compact, so Arsenin--Kunugui applies.  The field is injective;
Lusin--Souslin therefore makes its range

\[
 \mathcal L_P=\{(G_P)_s:s\in L_P\}
\tag{4.7}
\]

Borel and gives a Borel inverse.

The Polish group \(\operatorname{Homeo}(\mathbb R)\) acts
continuously on \(C(\mathbb R,V)\) by precomposition.  Let

\[
 Y_P=
 \{h\in\operatorname{PEmb}(\mathbb R,V):q(h)\in\mathcal L_P\}.
\tag{4.8}
\]

This is an invariant Borel set.  Lemma 4.2 shows that its orbit
equivalence relation is reduced by \(q\) to equality on
\(\mathcal L_P\), hence is smooth.  Burgess's selection theorem gives
a Borel transversal.  Restriction of \(q\) to that transversal is a
Borel bijection to \(\mathcal L_P\), so Lusin--Souslin gives a Borel
inverse.  Composing with the field in (4.7) selects one proper
embedding for each \(s\).  Continuous evaluation on
\(C(\mathbb R,V)\times\mathbb R\) gives (4.6). \(\square\)

Reparameterizing \(\mathbb R\) by \((0,1)\) gives the format used in
the N1 occurrence calculus.

### Corollary 4.4 (Borel ideal endpoints)

The two, not necessarily distinct, KKL ideal-tail maps are Borel.

#### Proof

KKL 406 gives the limits in the compact metrizable ideal closure:

\[
 e_P^\pm(s)=\lim_{n\to\infty}e_P(s,\pm n).
\tag{4.9}
\]

Each approximating map is Borel, and a pointwise limit into a
metrizable space is Borel. \(\square\)

When the two endpoints lie in distinct marked intervals, reverse the
selected parameterization on the Borel subset where its orientation
opposes the fixed arc tag.  When they agree, KKL paths are unoriented
by default and no orientation choice is needed for the transverse
leaf order.

The candidate's compact-arc parameterization may instead be retained
after a separate Borel based-circle branch is supplied.  Proposition
4.3 is a shorter uniform repair and is the route used below.

## 5. Complete variable-interval immersion code

Let

\[
 e:L\times(0,1)\to V
\]

be the evaluation from Proposition 4.3 and let
\(\iota:V'\to V\) be the KKL holomorphic immersion.  A holomorphic
immersion of Riemann surfaces is a local homeomorphism.

### 5.1 Countable germs and compact-margin continuation

Choose countable locally finite families

\[
 D_i^-\Subset D_i^+\Subset V
\]

of simply connected disks and enumerate every inverse branch

\[
 \psi_{i,j}:D_i^+\to V'
\]

of \(\iota\).  Second countability makes the enumeration countable.

A germ is coded by

\[
 \omega=(\ell,q,j),
 \qquad q\in\mathbb Q\cap(0,1),
 \qquad
 \iota(\psi_{i,j}(e(\ell,q)))=e(\ell,q).
\tag{5.1}
\]

The preimage fiber of an immersion is discrete and hence countable in
a second-countable surface.  The germ relation is Borel, so
Lusin--Novikov supplies natural-number indices for the fibers.  Those
indices, not raw points \(z'\), must be used for lexicographic
selection later.

For rational \(r<q\), continuation over \([r,q]\) is the countable
union over:

1. finite rational subdivisions
   \(r=t_0<\cdots<t_m=q\);
2. finite inverse-branch words; and
3. compact-containment conditions
   \[
     e(\ell,[t_{u-1},t_u])\Subset D_{i_u}^+.
   \tag{5.2}
   \]

Condition (5.2) is Borel: it is equivalent to a strictly positive
infimum of the distance to \(V\setminus D_{i_u}^+\), and the infimum
over a compact interval equals the infimum over its rational points.
Equality of consecutive inverse-branch values at subdivision points
is Borel.  Every actual continuation over a compact interval has such
a finite compact-margin word by compactness and the Lebesgue-number
argument.  Thus rational reachability is Borel in both directions.

The maximal continuation interval

\[
 I_\omega=(a_\omega,b_\omega)\subset(0,1)
\tag{5.3}
\]

has endpoints

\[
\begin{aligned}
 a_\omega&=
 \inf\{r\in\mathbb Q:r<q
       \text{ and continuation exists on }[r,q]\},\\
 b_\omega&=
 \sup\{r\in\mathbb Q:r>q
       \text{ and continuation exists on }[q,r]\}.
\end{aligned}
\tag{5.4}
\]

They are Borel real-valued functions.

### 5.2 Joint real-time evaluation

Borel evaluation at rational original times does not by itself justify
the sentence "continuity determines the full lift."  The required
construction is explicit.

On

\[
 D=\{(\omega,t):a_\omega<t<b_\omega\},
\]

let \(q_n(\omega,t)\) be the first rational in a fixed enumeration
satisfying

\[
 a_\omega<q_n(\omega,t)<b_\omega,
 \qquad
 |q_n(\omega,t)-t|<1/n.
\tag{5.5}
\]

This is a Borel choice from a countable list.  The rational lift
evaluations are Borel and, by path-lift continuity,

\[
 \widetilde e(\omega,t)
 =
 \lim_{n\to\infty}
 \widetilde e(\omega,q_n(\omega,t))
\tag{5.6}
\]

exists.  Hence the full variable-domain evaluation is jointly Borel.

For normalized \(r\in(0,1)\), use the original time

\[
 t_\omega(r)=a_\omega+(b_\omega-a_\omega)r.
\tag{5.7}
\]

The rational approximants must approximate \(t_\omega(r)\) in the
original source interval.  Treating normalized rational \(r\) itself
as an original rational time would be a type error.

### 5.3 Properness is a positive-distance predicate

After normalization, fix

\[
 K_m'\Subset\operatorname{int}K_{m+1}',
 \qquad
 \bigcup_mK_m'=V'.
\tag{5.8}
\]

The lifted component is proper exactly when

\[
 \forall m\ \exists N,k\ \forall
 r\in
 \left((0,1/N)\cup(1-1/N,1)\right)\cap\mathbb Q:
 \quad
 d(\widetilde e(\omega,t_\omega(r)),K_m')\ge1/k.
\tag{5.9}
\]

If the lift is proper, its normalized tails eventually avoid
\(K_{m+1}'\); compact containment supplies the positive distance from
\(K_m'\).  Conversely, continuity extends (5.9) to all tail times, so
the preimage of \(K_m'\) is closed and lies in a compact central
parameter interval.  Thus it is compact.  Formula (5.9) is a
countable Borel predicate.

Mere rational nonmembership in \(K_m'\) is insufficient: an irrational
contact or asymptotic approach to \(K_m'\) could remain.

### 5.4 Prime-end convergence is independent of properness

Properness does not force one ideal limit on either tail.  In a
complete metric \(d_{\rm pe}\) on the compact ideal closure, require

\[
 \forall k\ \exists N\ \forall
 r,s\in(0,1/N)\cap\mathbb Q:
 \quad
 d_{\rm pe}(
 \widetilde e(\omega,t_\omega(r)),
 \widetilde e(\omega,t_\omega(s)))
 <1/(2k),
\tag{5.10}
\]

and the analogous terminal condition.  The factor \(2\) makes the
dense-rational passage literal; it is not mathematically essential
but prevents a strict-inequality bookkeeping error.

Continuity turns (5.10) into the full-tail Cauchy condition.  Compact
completeness gives the limits.  They are Borel pointwise limits of,
for example, the Borel sequences at normalized times \(1/n\) and
\(1-1/n\).  Membership of both limits in the closed ideal boundary is
Borel.

### 5.5 Marked proper-homotopy and the two KKL filters

The phrase "finite-subordination predicate" is not enough, because an
annular winding/deck tag can be countable even for a finite marking.
Use the following standard marked-arc code.

For each ordered pair of endpoint marking intervals, choose a lift of
the first interval in the universal cover.  Lift the compactified
simple occurrence path from that initial lift.  The lift of its second
endpoint belongs to one deck translate of a fixed lift of the second
interval.  The endpoint-interval pair and this deck element form a
countable relative proper-homotopy tag.

The tag is Borel.  Indeed, the jointly Borel compactified path field is
Borel as a map into the continuous-path space (its Borel structure is
generated by evaluation on a fixed countable dense set).  On a
countable decomposition into evenly covered endpoint charts, path
lifting depends continuously on the path and the initial lift.  The
terminal deck element is locally constant there and hence Borel.

Moving endpoints inside their fixed open marking intervals and joining
them by the fixed short endpoint lifts does not change the relative
proper-homotopy class used by KKL.  Consequently, subordination to a
fixed marked multi-interval is a predicate on the countable tag: it
holds precisely for the predeclared tags admitting representatives in
every collar of that multi-interval.

Therefore:

1. rejection for not being a path in \((V',\mathcal I')\); and
2. rejection for subordination to one interval in
   \(\iota^*\mathcal I\)

are Borel unions of countable marked-arc tags.

### 5.6 Duplicate germs

Two germ codes describe the same maximal occurrence exactly when:

1. they have the same source leaf;
2. their maximal source intervals overlap nontrivially; and
3. their lifted evaluations agree at one rational time in that
   overlap.

The overlap condition cannot be omitted: universal agreement on an
empty overlap is vacuous.  A nonempty overlap contains a rational.
Uniqueness of path lifting then makes the two continuations agree
throughout the overlap, and maximality makes their intervals equal.

This is a Borel equivalence relation inside each countable
natural-number germ enumeration.  Retaining the least enumeration
index in each class gives a Borel occurrence space.  The evaluation in
(5.6)--(5.7), restricted to the predicates above, is a jointly Borel
proper-path evaluation.  Distinct retained preimage components are
disjoint; Lusin--Souslin makes their geometric union Borel.

## 6. Breakability and successor typing

### Counterexample schema 6.1 (occurrences are not outputs)

One source leaf can have two distinct retained restriction
occurrences \(\omega_1,\omega_2\) with

\[
 f(\widetilde\gamma_{\omega_1})
 =
 f(\widetilde\gamma_{\omega_2})
\tag{6.1}
\]

as the same untagged pushed path.  The occurrence section has
cardinality two, but \(F_*\gamma\) is a single path in the KKL sense.
Thus raw occurrence cardinality does not compute breakability.

The statement in the candidate that

```text
singleton versus nonsingleton occurrence count is Borel, hence the
unbreakable part is Borel
```

must be deleted.

### Proposition 6.2 (safe native-subwave route)

For Gate N1, use the source-typed Borel subwaves
\(A^{h\text{-nbr}}\) from Proposition 2.3.  On any such domain for
which the analytic N1 theorem supplies an actual target Wave \(R\),
the unique untagged successor is Borel.

#### Proof

Apply Sections 3--4 independently to the actual source Wave and the
actual target Wave \(R\).  Let \(L_R\) be the target leaf space and

\[
 j_R:L_R\to F(V)
\tag{6.2}
\]

its Borel closed-image code.  This map is injective; Lusin--Souslin
makes \(j_R(L_R)\) Borel and \(j_R^{-1}\) Borel on the range.

For a source leaf \(\ell\), enumerate its retained occurrences by
Section 5.  On the analytic packet where the covering pushforward is
an embedded target leaf, composition with \(f\) gives a Borel
closed-image code.  Define

\[
 Q(\ell,r)
 \Longleftrightarrow
 \exists\omega\in\Omega_\ell:
 q(f\circ\widetilde\gamma_\omega)=j_R(r).
\tag{6.3}
\]

The witness section is countable, so Lusin--Novikov makes \(Q\)
Borel.  KKL unbreakability and the analytic identification of \(R\)
make the \(r\)-section a singleton.  Lusin--Novikov therefore gives
the Borel successor

\[
 \Phi_1:L_{\rm source}\to L_R.
\tag{6.4}
\]

Multiple occurrences with the same untagged target leaf do not affect
(6.4). \(\square\)

This route deliberately avoids deciding equality of arbitrary
nonembedded parametrized pushforwards by compact image alone.
KL06 `appendix.tex` 84--88 warns that pushforwards are parametrized
paths and may retain traversal multiplicity.  Hyperspace equality is
safe here only after the analytic target is known to be an embedded
Wave leaf.

### Corollary 6.3 (well-typed finite iteration and saturation)

At each actual retained target Wave, use its own leaf space and (6.4).
Finite composition gives a Borel map \(\Phi_h\) between the correctly
typed source and target leaf spaces.

If \(E\subset L_R\) is Borel, then

\[
 \Phi_h^{-1}(E)
\tag{6.5}
\]

is Borel.  Restricting the injective source evaluation to this set and
applying Lusin--Souslin makes its geometric saturation Borel.

If a proof instead keeps \(\Phi_h\) hyperspace-valued, (6.5) must be
written

\[
 \Phi_h^{-1}(j_R(E)).
\tag{6.6}
\]

Writing \(\Phi_h^{-1}(E)\) with a hyperspace-valued \(\Phi_h\) and a
leaf-space subset \(E\) is a type error.

## 7. DL deck pruning and the width-measure correction

On a packet directed over one connected interval \(J\), Lemma 3.2
orders all leaves by inclusion of their \(J\)-side domains.  The
coordinate \(t\), or \(-t\), agrees with annular deck order.

Let \(L\subset\mathbb R\) be the resulting Borel coordinate set.  Every
downward-closed subset of \(L\) is

\[
 L\cap(-\infty,a)
 \quad\text{or}\quad
 L\cap(-\infty,a]
\tag{7.1}
\]

for its supremum \(a\), with the evident empty and unbounded cases.
Hence every initial or terminal order segment is Borel.

The deck-span classes in DL 2830--2838 are Borel endpoint/deck-tag
predicates by Section 5.5.  The extra deletion at DL 2841 is an
outermost, hence initial or terminal, order segment.  Therefore every
DL retained and discarded packet is Borel.

This conclusion is only a measurability statement.  DL supplies the
\(O(\log m)\) analytic width loss.  Extremal width is a capacity on
arbitrary path families; KL06's definition alone does not make it a
countably additive Borel measure on an arbitrary leaf quotient.

Therefore the original clause

```text
a Borel transverse width measure
```

in Definition 3.1(5) of
`kkl_stationary_relative_wave_continuation.md` is not proved here.
The exact clause actually used by the DL pruning is:

```text
BOREL_ORDERED_BUFFER:
each DL packet has a Borel real order agreeing, up to reversal, with
deck order, and each initial or terminal segment selected by the DL
pruning is Borel.
```

Gate N1 can use this repair only after the governing definition and
every dependency reference are amended consistently.  Proving
`BOREL_ORDERED_BUFFER` does not literally prove the older, stronger
Definition 3.1(5).

## 8. Adversarial checks

| test | result | reason |
|---|---|---|
| fat-Cantor transverse leaf set | pass | Lemma 3.3 uses Borel support and nesting, not a rectangle product |
| nonclosed total support | pass | rational sublevels use an open union plus at most one closed leaf |
| gaps in the order coordinate | pass | Arsenin--Kunugui proves \(t(P)\) Borel; no monotone-image shortcut |
| zero-width nonempty arc packet | failed in candidate; repaired | index by \(\mathcal A(\mathcal F)\), not induced-WAD support |
| two tails at one prime end | failed in candidate; repaired | Counterexample 3.1 and path-space Proposition 4.3 |
| non-locally-connected \(\mathcal T\) | pass | all endpoint statements use the metrizable ideal/prime-end closure |
| finite-time escape of an immersion lift | pass after expansion | \(I_\omega=(a_\omega,b_\omega)\) is part of the Borel record |
| irrational contact with a compact set | pass | positive-distance properness test (5.9) |
| proper lift oscillating among ideal points | pass | independent Cauchy test (5.10) |
| two germs with disjoint maximal intervals | pass | nonempty overlap is required before deduplication |
| multiple occurrences, one untagged output | failed in candidate; repaired | native unbreakable subwave plus target relation (6.3) |
| parametrized pushforwards with same image but different traversal | not collapsed | compact-image equality is used only for embedded analytic target leaves |
| annular winding hidden by finite marking | pass after expansion | countable marked-arc/deck tag, not a merely finite endpoint tag |
| terminal saturation in wrong codomain | failed in candidate; repaired | use target leaf map (6.5) or compact code (6.6) |
| DL outer-buffer cut at an arbitrary real value | pass | every order-initial subset of a Borel subset of \(\mathbb R\) is Borel |
| period growth \(q\to\infty\) | pass for measurability | no analytic constant and no sum over arc packets is introduced |

## 9. Dependency and circularity audit

The repaired descriptive chain is:

\[
\begin{array}{c}
\text{typed Borel arc packet}\\
\Downarrow\\
\text{strict planar nesting}\\
\Downarrow\\
\text{Borel area coordinate}\\
\Downarrow\\
\text{Arsenin--Kunugui leaf range}\\
\Downarrow\\
\text{Burgess proper-path selector}\\
\Downarrow\\
\text{countable immersion germs with variable intervals}\\
\Downarrow\\
\text{properness + ideal-tail + marked-arc filters}\\
\Downarrow\\
\text{native unbreakable domain + typed target successor}\\
\Downarrow\\
\text{DL Borel order cuts and full Borel saturation}.
\end{array}
\tag{9.1}
\]

No arrow in (9.1) uses:

- local connectivity of \(\mathcal T\);
- a pre-existing Borel leaf quotient;
- the false broad coefficient-one Wave extraction;
- KKL line 1576 or the later line-1603 alignment assertion;
- Gate N2 or any later stationary gate;
- VAAPC-I, UPTCR, rigidity, parameter fibers, or MLC.

The analytic width estimates are not reproved by the Borel chain.
They remain exactly the independent inputs of Theorem N1-A and DL
2821--2842.

## 10. Mandatory integration list and exact status

Before any promotion, the main BOWR note must:

1. replace \(\operatorname{supp}W_S\) in its packet decomposition by
   the set of all nonempty arc classes;
2. extend its nesting proof to the coincident-tail deck-lift case;
3. replace the two-endpoint compact-arc parameterization by
   Proposition 4.3 or a complete Borel based-circle branch;
4. expand finite inverse-chart words with compact margins;
5. construct joint real-time lift evaluation by the explicit Borel
   rational approximation (5.5)--(5.7);
6. retain the positive-distance properness predicate and the separate
   prime-end Cauchy predicate;
7. prove the countable marked-arc/deck tag lemma for both KKL filters;
8. deduplicate only within the same source leaf, require nonempty
   interval overlap, and select by the Lusin--Novikov natural index;
9. delete raw-occurrence counting as a test for unbreakability and use
   Proposition 2.3 plus the typed target relation (6.3);
10. insert the target leaf-code map in successor composition and
    saturation; and
11. replace the old transverse-width-measure interface everywhere by
    `BOREL_ORDERED_BUFFER`, or else separately prove the stronger
    measure assertion.

The status after this independent audit is:

| obligation | status |
|---|---|
| planar-area leaf coordinate | proved |
| standard-Borel leaf quotient | proved, conditional only on the typed Borel arc packet |
| joint proper-leaf evaluation for distinct and equal tails | proved via Burgess |
| variable-interval maximal-lift coding | proved after the explicit expansions in Section 5 |
| KKL filter measurability | proved via the marked-arc/deck tag |
| unbreakability by raw occurrence count | refuted |
| Borel successor on native unbreakable analytic packets | proved with target typing |
| DL ordered-buffer measurability | conditional on the chartwise order-ideal lemma isolated in Section 11.4 |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` in the unedited candidate | not proved |
| repaired `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | candidate proved subject to explicit integration and the source-typing convention |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | remains open pending integration audit |
| Gate N2, VAAPC-I, UPTCR, MLC | open |

The immediate next action on Gate N1 is therefore an integration pass,
not another width estimate: incorporate items 1--11 into one theorem,
then rerun a backward type and source audit on the actual families in
Theorem N1-A.

## 11. Post-integration audit of the frozen BOWR candidate

This section audits the integrated candidate

```text
kkl_stationary_n1_borel_ordered_wave_realization_20260726.md
```

at SHA-256

```text
C9F1C7BD37FD192E047B13B79023B3A88AC3148A5A11C5A79EC52B349114D318.
```

The file was frozen during this audit.  No conclusion below depends on
an unrecorded edit.

### 11.1 Source meaning of “sublamination”

There are two logically different assertions:

1. KL06 `wad.tex` 142--150 declares all laminations then under
   consideration proper and calls \(\mathcal F(\alpha)\) a
   sublamination.  Within KL06, the literal typed reading therefore
   makes \(\mathcal F(\alpha)\) a proper Borel lamination.
2. KKL 1911 repeats the word “sublamination,” but the KL06 phrase “in
   what follows” does not, by itself, govern a different paper.

The integrated candidate resolves (2) by an explicit convention at
its lines 23--26 and Lemma 2.1: every proof-used KKL Wave and its native
subwaves are interpreted in the KL06 proper-lamination sense.  This is
a legitimate theorem hypothesis/definition-level bridge.  It is not a
deduction from Borelness of the total support.  Any source-locked
version that declines this convention must retain

```text
ARC_CLASS_SUBLAMINATION_IS_PROPER_BOREL
```

as an explicit hypothesis.

Under the convention, KKL's native \(A^{\rm sh}\) and
\(A^{n\text{-nbr}}\) are proper Borel subwaves because KKL 1182 and
1356 explicitly type them as subwaves.  Their leafwise difference is
Borel.  No occurrence-count reconstruction of unbreakability is
valid.

### 11.2 First unsupported implication in line order

After granting the source convention, the first proof-detail gap in
the frozen candidate occurs in Lemma 3.1, lines 283--292.  For two
lifted crosscuts sharing an ideal endpoint, the text asserts that one
may simultaneously separate their terminal tails in an arbitrarily
small prime-end half-collar and perturb their landing points without
creating an intersection.

This is standard for planar Jordan crosscuts, but it is neither proved
nor source-cited there.  The exact repair is a standalone
shared-endpoint crosscut-order lemma:

> Let \(D\) be a closed topological disk and let \(a,b\) be Jordan
> crosscuts with disjoint interiors.  Choose for each crosscut the
> boundary subarc containing a fixed nondegenerate boundary interval
> \(J\).  If the chosen boundary subarcs are nested, then the
> corresponding \(J\)-side components are nested, including when the
> crosscuts share one or both endpoints.  Strictness holds for
> distinct crosscuts, and the region between them contains a nonempty
> open disk.

A direct proof avoids perturbation.  The interior of one crosscut is a
connected subset of one component of the complement of the other.
When one nonshared endpoint lies in the interior of the other's chosen
boundary arc, a boundary half-disk forces that component to be the
chosen side.  If both endpoints agree, the two disjoint crosscuts and
the two boundary arcs divide the disk into the boundary-side region,
the lens between the crosscuts, and the opposite boundary-side region;
the chosen-side regions differ by the lens and are nested.  Applying a
Schoenflies chart gives the same conclusion in a prime-end half-disk.

Until this lemma is inserted, Lemma 3.1 is not fully checkable.  This is
a local proof gap, not a counterexample to the order-coordinate
construction.

### 11.3 Two later repairable gaps

First, lines 865--875 choose compactly contained inverse-branch chart
sets \(W_{i,k}\) that “exhaust” \(W_i\), then infer that every compact
continued segment lies in one \(W_{i,k}\).  This follows if the
exhaustion is chosen nested:

\[
 \overline{W_{i,k}}\Subset W_{i,k+1}\Subset W_i,
 \qquad \bigcup_kW_{i,k}=W_i.
\]

For a merely nonnested exhaustion, only a finite subcover is automatic.
The proof is repaired either by imposing the displayed nested
exhaustion or allowing finite subwords covering one target segment.

Second, lines 984--1009 use relative homotopy classes in which endpoints
may move inside fixed marking intervals, whereas KKL 1868 defines
subordination by homotopy relative to the actual endpoints.  The
missing bridge is the endpoint-whisker lemma:

> If two compactified paths are homotopic while their endpoints move
> inside fixed marking intervals \(I,J\), then subordination to a
> multi-interval \(X\supset I\cup J\) is the same for both paths.

Indeed, for every neighborhood \(N\) of \(X\), join the old and new
endpoints by short tracks in \(I,J\subset N\), concatenate those tracks
with an \(N\)-representative of the old relative-endpoint class, and
use the moving-endpoint homotopy with the endpoint tracks attached to
obtain a homotopy relative to the new endpoints.  The converse is
symmetric.  This proves the invariance used by the two KKL filters.

The rational Cauchy test at lines 959--970 yields a non-strict
\(\le 1/k\) estimate at arbitrary real times from the printed
\(<1/k\) rational test.  Cauchyness still follows after reindexing.
Using \(1/(2k)\) in the rational test removes even this harmless
bookkeeping discrepancy.

### 11.4 Substantive remaining DL interface

The integrated candidate's lines 1127--1139 and Definition 8.1 assert:

```text
DL_BUFFER_CHARTWISE_ORDER_IDEAL:
every outermost family deleted by DL intersects every ordered arc
packet in an initial interval, a terminal interval, their union, or
the empty set.
```

If this statement is known, the measurability proof at lines
1141--1158 is correct: every down-set in a Borel subset of
\(\mathbb R\) is cut by one real threshold, hence is Borel.

The locked DL text does not state the chartwise order-ideal assertion.
DL 1791--1792 defines left and right buffers for a genuine rectangle.
DL 2827 says to remove \(O(\log m)\) “outermost curves,” and DL 2841
says to remove an extra \(O(1)\) outermost curves.  Those lines do not
formally identify the deleted set on an arbitrary finite ordered
arc-packet atlas, nor prove that opposite-side packets cannot be
interleaved by the chosen global deletion.

Therefore one of the following is still required:

1. reconstruct DL's universal-cover pruning and prove
   `DL_BUFFER_CHARTWISE_ORDER_IDEAL` from the planar/deck placement of
   every deleted family; or
2. add the order-ideal property as an explicit hypothesis of BOWR and
   keep the unconditional N1 gate open.

Calling the deletion “outermost” is not itself a proof of the
chartwise order-ideal statement.  This is the most substantive
remaining BOWR gap after the local shared-endpoint and endpoint-whisker
repairs.

### 11.5 Exact frozen-file verdict

The area coordinate, Arsenin--Kunugui range argument, equal-tail circle
parameterization, variable-interval lift code, positive-distance
properness test, native-unbreakable successor, typed target inverse,
and terminal saturation survive the frozen-file audit.

The frozen theorem is nevertheless **not yet promotable**:

- Lemma 3.1 needs the shared-endpoint crosscut-order lemma;
- the homotopy filters need the endpoint-whisker lemma;
- the chart atlas should be made nested; and
- unconditional DL pruning needs
  `DL_BUFFER_CHARTWISE_ORDER_IDEAL`.

There is also an interface mismatch outside the frozen file:
Definition 3.1(5) in
`kkl_stationary_relative_wave_continuation.md` still asks for a
“Borel transverse width measure,” whereas BOWR proves only the corrected
ordered-buffer clause.  The main N1 definition and every dependency
must be amended consistently before the corrected theorem can close
the ledger obligation.

Accordingly:

| obligation | frozen-file audit status |
|---|---|
| area-coordinate standard-Borel realization | proved |
| filtered variable-interval occurrence calculus | proved after the two explicit local repairs |
| Borel native-unbreakable successor and saturation | proved |
| DL chartwise ordered-buffer measurability | conditional on `DL_BUFFER_CHARTWISE_ORDER_IDEAL` |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | open |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | open |
| N2, VAAPC-I, UPTCR, MLC | open |
