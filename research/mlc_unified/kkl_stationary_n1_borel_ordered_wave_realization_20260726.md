# Gate N1 — Borel ordered realization of stationary Waves

## 0. Status and exact claim

This note addresses only the remaining measurable interface in

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION
```

namely

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION.
```

The setting is the stationary finite-marked annulus

\[
 V=\mathcal U\setminus\mathcal T
\]

of Kahn--Kapiamba--Lyubich (KKL).  A proof-used Wave is understood in
the literal Kahn--Lyubich (KL06) sense: its geometric support is a
Borel subset of \(V\), explicitly decomposed into pairwise disjoint
proper embedded paths.  No local product chart for that decomposition
is assumed.

The new point of this note is that planar order supplies the missing
leaf code.  Within one arc class, the preferred-side domains of the
leaves are strictly nested.  A finite full-support area measure
therefore assigns an injective order coordinate

\[
 t(\gamma)=\mu(O_\gamma).
\]

The coordinate is Borel even though no Borel leaf quotient is assumed
in advance.  The proof uses open sublevel saturations and the fact that
at most one extremal leaf is omitted.  The Arsenin--Kunugui projection
theorem then proves that the realized set of coordinates is Borel.

The theorem proved below is:

### Theorem BOWR (stationary Borel Wave realization and pruning)

Every KKL Wave used in the stationary finite-marked annulus admits a
finite disjoint decomposition into standard-Borel ordered arc packets.
Each packet has:

1. a standard-Borel leaf space;
2. a jointly Borel proper-path evaluation;
3. Borel prime-end endpoint maps;
4. a Borel order equal, up to a fixed reversal, to the planar nesting
   order within each arc packet; and
5. Borel initial and terminal order intervals within each packet.

This structure is preserved by:

1. finite arc, endpoint, direction, and short/nonshort partitions,
   together with the native proper subwaves \(A^{h\text{-nbr}}\) and
   \(A^{\rm sh}\);
2. both KKL immersion-marking filters;
3. the full proper-component restriction relation;
4. the finite-cover pushforward on an injective retained packet;
5. the DL set-theoretic pruning, after replacing its proof-internal
   bounded-width discard by the Borel width envelope of
   `kkl_stationary_n1_borel_width_envelope_20260726.md`; and
6. full terminal-output saturation under the unique untagged
   successor.

Consequently, every leaf family constructed in Theorem N1 of
`kkl_stationary_relative_wave_continuation.md` is a proper Borel KKL
subwave.

The phrase “transverse width measure” in the provisional Definition
3.1(5) of that note is removed.  The locked DL text also does not
formally identify its “outermost curves” with initial or terminal
intervals in every arc chart.  We make no such inference.  DL supplies
a set-theoretic injective retained family and, from its proof rather
than merely its displayed conclusion, a bounded-width discarded
family.  The Borel width-envelope theorem enlarges that discard to a
Borel family with only an absolute extra charge.  This produces the
Borel retained subwave actually used below.

This note proves no statement about Gate N2, terminal alignment,
VAAPC-I, UPTCR, rigidity, parameter fibers, or MLC.

## 1. Source and imported-theorem ledger

### 1.1 Frozen dynamics sources

| source | role | SHA-256 |
|---|---|---|
| `.tmp_wave_audit/waves-with-Misha.tex` | KKL master, arXiv:2606.27272 v1 | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_wave_audit/dl23/Feigen.tex` | DL annular Wave pruning | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_kl06_source/wad.tex` | proper Borel laminations and arc-class sublaminations | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |

The precise clauses used are:

- KL06 `wad.tex` 142--150: a proper lamination is a Borel geometric
  support explicitly decomposed into disjoint proper paths, and
  \(\mathcal F(\alpha)\) is the sublamination in one arc class;
- KL06 `wad.tex` 26--50 and KKL 406: path reparameterization and the
  precise convention under which a path may be identified with its
  image;
- KL06 `wad.tex` 156--158: finite-cover pullback preserves proper
  laminations;
- KKL 889 and 1907--1908: the stationary marking and the support of a
  WAD are finite;
- KKL 1839--1875: prime-end marking, paths, arcs, Waves, bases, ends,
  and crests;
- KKL 1911--1914: the arc-class sublamination
  \(\mathcal F(\alpha)\);
- KKL 2065--2142: covering pushforward and filtered immersion
  restriction; and
- DL 2821--2842: finite deck-span decomposition followed by deletion
  of finitely many outermost buffers.

### 1.2 Standard descriptive-set input

We use the following classical form of the Arsenin--Kunugui theorem.

> **AK.**  If \(X,Y\) are Polish spaces and
> \(G\subset X\times Y\) is Borel with every vertical section
> \(G_x\) sigma-compact, then \(\operatorname{proj}_X G\) is Borel.
> On the nonempty sections, \(G\) also admits a Borel
> uniformization.

Only the projection conclusion is essential below.  The theorem is
used twice: first for the graph whose sections are proper leaves, and
then for open pieces of compact arc sections.  No completion of a
measure and no “almost everywhere” selector is used.

A primary-source proof in the required sigma-compact-section setting
is D. G. Larman, *Projecting and uniformising Borel sets with
sigma-compact sections I*, Mathematika 19 (1972), 231--243,
doi:10.1112/S0025579300005696.

We also use the finite-section Lusin--Novikov theorem: a Borel
relation between standard-Borel spaces with finite sections admits a
Borel enumeration of those sections.

## 2. Reduction to finitely many Borel arc packets

Let \(S\) be a proof-used stationary Wave and let \(Z_S\subset V\)
be its Borel geometric support.

### Lemma 2.1 (native arc packets are proper Borel)

For every supported arc \(\alpha\), the geometric support of
\(S(\alpha)\) is Borel.

#### Proof

This is an imported definition-level clause, not a projection
argument.  KL06 `wad.tex` 142--143 defines a *proper lamination* to be
a Borel geometric set explicitly realized as a union of disjoint
proper paths.  The standing convention in the footnote at line 144 is
that every lamination subsequently considered is proper.  In the same
sentence sequence, lines 145--150 write a proper lamination as
\(\mathcal F=\bigcup_\alpha\mathcal F(\alpha)\), call
\(\mathcal F(\alpha)\) the sublamination represented by \(\alpha\),
and then regard that sublamination as a path family.  Thus, in the
native syntax, \(\mathcal F(\alpha)\) is itself a lamination and the
standing properness convention applies to it.  KKL 1911 repeats this
same construction verbatim for its marked surfaces.

Consequently the Borel support of \(S(\alpha)\) is part of the
imported meaning of the source object.  We are not using the invalid
inference that an arbitrary union or subfamily of leaves of a Borel
lamination is Borel. \(\square\)

Let

\[
 \mathcal A(S):=\{\alpha:S(\alpha)\ne\varnothing\}.
\]

This set is finite, including its zero-width classes.  Indeed, actual
leaves from two different classes are disjoint representatives, so
\(\mathcal A(S)\) is a pairwise nonintersecting arc diagram.  Equivalently,
assign coefficient \(1\) to every class in \(\mathcal A(S)\); this is
a WAD in the sense of KKL 1904, and the topological bound at KKL
1907--1908 gives

\[
 |\mathcal A(S)|\leq3|\chi(V)|+|\mathcal I|.
\]

This auxiliary coefficient-one WAD is used only for finiteness; it
does not assert that a zero-extremal-width class has positive induced
weight.  Lemma 2.1 applies to

\[
 S(\alpha)
 :=
 \{\gamma\in S:[\gamma]=\alpha\}
\tag{2.1}
\]

whose geometric support we denote by \(Z_\alpha\).  Thus

\[
 S=\mathop{\dot\bigcup}_{\alpha\in\mathcal A(S)}S(\alpha)
\tag{2.2}
\]

is a finite disjoint decomposition into Borel arc packets.

The singleton marked base and crest are constant on an arc class.
Indeed, the arc tag fixes the two endpoint marking intervals and the
homotopy route between them in the prime-end annulus.  Moving the
actual endpoints inside those same open intervals does not cross a
marking endpoint, so it cannot add or remove a whole marked interval
from that route.  Consequently, every direction, short/nonshort, and
endpoint-block predicate used below is a finite predicate on the arc
tag together with the endpoint intervals.

Fix one nonempty packet \(P=S(\alpha)\).  Orient the arc class once.
The orientation fixes which prime-end endpoint is first.  If the two
endpoints belong to the same marking interval, choose a lift of that
interval to the annular universal cover and use the oriented lift of
\(\alpha\); changing this choice applies one deck translation and does
not change any conclusion below.

The singleton crest of this arc class contains at least one complete
marked interval.  Otherwise the singleton path would be subordinate
to the union of its at most two endpoint intervals, contrary to KKL
1869.  Fix one such interval \(Q_\alpha\).  For
\(\gamma\in P\), let

\[
 O_\gamma\subset V
\tag{2.3}
\]

be the component of
\(\mathcal U\setminus(\mathcal T\cup\gamma)\) whose Carathéodory
boundary contains \(Q_\alpha\).  In the prime-end annulus this is the
preferred open disk-side domain of the leaf.  If the two endpoint
prime ends are distinct, its boundary is the leaf together with the
preferred ideal-boundary interval.  If they coincide, the
compactified leaf is a based Jordan circle and \(O_\gamma\) is its
preferred complementary disk.  Thus the definition covers both
endpoint types.  For a directed packet above \(J\), choose
\(Q_\alpha\subset J\); then this is exactly the \(J\)-side domain.

## 3. Planar nesting and the injective area coordinate

### Lemma 3.1 (strict nesting)

For two distinct leaves \(\gamma,\eta\in P\), exactly one of

\[
 O_\gamma\subsetneq O_\eta,
\qquad
 O_\eta\subsetneq O_\gamma
\tag{3.1}
\]

holds.  Moreover, the difference between the larger domain and the
closure of the smaller one contains a nonempty open set.

#### Proof

Pass to the prime-end compactification of \(V\), a closed annulus,
and lift the oriented arc class to the closed annular strip.  Choose
for every leaf the unique deck translate whose preferred side contains
one fixed lift of \(Q_\alpha\).  If a leaf has the same endpoint prime
end at both tails downstairs, its lift has distinct endpoints:
zero deck displacement would make the leaf subordinate to its one
endpoint marking interval, which KKL 1869 excludes.  Thus every
selected lift is an ordinary crosscut of the strip, including the
coincident-endpoint case downstairs.

The preferred boundary interval is on the same lifted side for every
selected leaf.  If the preferred-side domains of two disjoint lifted
crosscuts were not nested, their endpoint positions would alternate
on the lifted ideal boundary.  The Jordan separation theorem would
force the lifted crosscuts to meet.  Their projections would then
make the original leaves meet in \(V\), contradicting the lamination
property.  Hence the lifted domains are nested.  They are precisely
the lifts, containing the chosen lift of \(Q_\alpha\), of the
downstairs disk-side components defined in (2.3); covering projection
therefore gives the same nesting for \(O_\gamma,O_\eta\).

For reference, the shared-endpoint step is the following elementary
crosscut-order fact.

> **Shared-endpoint crosscut-order lemma.**  Let \(c_0,c_1\) be two
> embedded crosscuts of a closed topological disk or strip, with
> disjoint interiors.  Suppose that the selected ideal-boundary
> interval for each crosscut contains the same nondegenerate interval
> \(Q\).  If the two crosscuts have the same oriented proper-homotopy
> tag, then their selected complementary components are nested, even
> when one or both pairs of ideal endpoints coincide.

To prove the lemma, use the Jordan--Schoenflies theorem in a boundary
half-disk at each shared endpoint.  A finite family of disjoint
embedded terminal arcs has a well-defined local cyclic order and can
be simultaneously straightened to radial terminal arcs.  Truncate the
two crosscuts on a sufficiently small half-circle and give the
truncated arcs distinct endpoints in that same local order.  This
operation changes neither a witness to nonnesting nor the selected
boundary interval containing \(Q\).  If the selected components had
not been nested, the two resulting distinct endpoint pairs would
alternate on the boundary.  The Jordan crosscut theorem would force
the truncated crosscuts to meet, contrary to their construction.
Hence the original selected components are nested.

Apply this lemma to the selected lifted crosscuts.  It supplies exactly
the shared-endpoint case omitted by the distinct-endpoint argument.

Equality is impossible for distinct leaves because the interior
boundary of the preferred-side domain contains the leaf itself.
For strict nested crosscut domains, the region between the two
disjoint lifted crosscuts contains a nonempty open disk on which the
covering projection is injective.  Its image lies between the two
downstairs leaves, so the difference of the downstairs domains also
contains a nonempty open set. \(\square\)

Choose once and for all a finite Borel measure \(\mu\) on \(V\) which
has full support.  For example, take a positive smooth density and
multiply it by a positive integrable exhaustion weight.  Define

\[
 t(\gamma):=\mu(O_\gamma).
\tag{3.2}
\]

### Lemma 3.2 (order injection)

The map \(t\) is strictly increasing for domain inclusion and is
injective on the set of leaves of \(P\).

#### Proof

If \(O_\gamma\subsetneq O_\eta\), Lemma 3.1 gives a nonempty open set
inside \(O_\eta\setminus O_\gamma\).  Full support makes its
\(\mu\)-measure positive.  Hence

\[
 \mu(O_\gamma)<\mu(O_\eta).
\]

The strict nesting alternative in Lemma 3.1 proves injectivity.
\(\square\)

We use the same letter \(t\) for the function on \(Z_\alpha\) which is
constant on a leaf:

\[
 t(x)=t(\gamma)
\quad\text{when }x\in\gamma .
\tag{3.3}
\]

### Lemma 3.3 (Borel sublevel lemma)

The function \(t:Z_\alpha\to\mathbb R\) is Borel.

#### Proof

Fix \(r\in\mathbb Q\) and put

\[
 U_r:=
 \bigcup_{\gamma\in P,\ t(\gamma)<r}O_\gamma .
\tag{3.4}
\]

This is an arbitrary union of open sets and hence is open.

Let \(\gamma\in P\).  If \(\gamma\cap U_r\ne\varnothing\), then
\(\gamma\) lies in \(O_\eta\) for some \(\eta\) with
\(t(\eta)<r\).  Strict nesting gives

\[
 t(\gamma)<t(\eta)<r.
\tag{3.5}
\]

Conversely, if \(t(\gamma)<t(\eta)<r\), then the interior of
\(\gamma\) lies in \(O_\eta\), so
\(\gamma\subset U_r\).

It follows that

\[
 Z_\alpha\cap U_r
\tag{3.6}
\]

contains every leaf with \(t<r\), except possibly a leaf whose
\(t\)-value is the maximum of

\[
 t(P)\cap(-\infty,r).
\]

There is at most one such leaf by Lemma 3.2.  A proper embedded path
has closed image in \(V\).  Therefore

\[
 \{x\in Z_\alpha:t(x)<r\}
\tag{3.7}
\]

is either the Borel set \(Z_\alpha\cap U_r\), or its union with one
closed leaf.  It is Borel.  Rational sublevels generate the Borel
sigma-algebra of \(\mathbb R\), proving the lemma. \(\square\)

This is the step that avoids assuming a measurable leaf quotient.
The Borel coordinate is constructed directly on the given Borel
geometric support.

## 4. The standard-Borel leaf space

Define the swapped graph

\[
 G_\alpha
 :=
 \{(s,x)\in\mathbb R\times V:
      x\in Z_\alpha,\ t(x)=s\}.
\tag{4.1}
\]

Lemma 3.3 makes \(G_\alpha\) Borel.  Its section at \(s\) is either
empty or exactly one proper leaf.  Indeed, \(t\) is constant on a leaf
and injective between leaves.

Every nonempty section is closed in \(V\), because the leaf is proper.
It is sigma-compact because \(V\) is a sigma-compact locally compact
surface.  Apply AK to (4.1).  The projection

\[
 L_\alpha
 :=
 \operatorname{proj}_{\mathbb R}G_\alpha
 =
 t(P)
\tag{4.2}
\]

is Borel in \(\mathbb R\).  Hence \(L_\alpha\), with its ordinary
Borel structure, is a standard-Borel leaf space.  The order inherited
from \(\mathbb R\) is the nesting order by Lemma 3.2.

Taking the finite tagged disjoint union

\[
 L_S
 :=
 \bigsqcup_\alpha\{\alpha\}\times L_\alpha
\tag{4.3}
\]

gives a standard-Borel leaf space for the whole Wave.

## 5. Borel endpoints and a joint Borel evaluation

This section supplies a path evaluation rather than merely a quotient.

Let \(\overline V^{\,\rm pe}\) be the compact metrizable prime-end
annulus.  For \(s\in L_\alpha\), let

\[
 K_s:=\overline{(G_\alpha)_s}^{\,\overline V^{\,\rm pe}} .
\tag{5.1}
\]

Its intersection with \(V\) is the proper leaf.  Its intersection
with the ideal boundary consists of the one or two endpoint limits of
that leaf.  If the limits are distinct, \(K_s\) is a compact arc.  If
they coincide, \(K_s\) is a Jordan circle with that common ideal point
marked as its cut point.  The second case cannot simply be discarded:
the printed definition of a proper path does not explicitly prohibit
two tails from landing at the same prime end.

### Lemma 5.1 (Borel compactified-leaf field)

The map

\[
 s\longmapsto K_s
\tag{5.2}
\]

is Borel into the hyperspace
\(\mathcal K(\overline V^{\,\rm pe})\).

#### Proof

It is enough to test intersection with an open set \(W\) in a
countable base of \(\overline V^{\,\rm pe}\).  Because every
neighborhood of an ideal endpoint meets the interior of its proper
leaf,

\[
 K_s\cap W\ne\varnothing
\quad\Longleftrightarrow\quad
 (G_\alpha)_s\cap(W\cap V)\ne\varnothing .
\tag{5.3}
\]

The right side is the projection of the Borel set

\[
 G_\alpha\cap
 (L_\alpha\times(W\cap V)).
\]

Its section is an open subset of one proper leaf, hence is
sigma-compact.  AK makes the projection Borel.  This proves all
hyperspace hit predicates and hence (5.2). \(\square\)

The boundary-membership relation

\[
 E_\alpha
 :=
 \{(s,\xi):
   \xi\in K_s\cap\partial^{\rm pe}V\}
\tag{5.4}
\]

is Borel and has one- or two-point sections.  The one-point and
two-point loci are Borel by the finite-section Lusin--Novikov theorem.
Lusin--Novikov enumerates the endpoint set Borelly.  Fix any Borel
linear order on the prime-end boundary and sort the two-point sections
by that order; this remains valid when both points lie in the same
marked interval and requires no unproved lift comparison.  On the
one-point locus, repeat the unique endpoint.  This yields Borel maps

\[
 e_\alpha^-,e_\alpha^+:L_\alpha\to\partial^{\rm pe}V .
\tag{5.5}
\]

The oriented arc-class and winding tags remain separate discrete
coordinates.  If a later convention requires the opposite path
orientation, swapping (5.5) by that Borel discrete tag preserves every
conclusion.  The leaf nesting/deck order in Section 6 comes from
\(t\), not from the arbitrary endpoint enumeration.

On the two-point locus the continuous compactified leaf map is
injective on \([0,1]\), hence is a homeomorphism onto a compact arc.
On the one-point locus its only repeated value is the common value at
times \(0,1\); it descends to a continuous bijection
\(S^1=[0,1]/(0\sim1)\to K_s\), hence a homeomorphism.  This verifies
the arc/Jordan-circle dichotomy used below rather than assuming it
from endpoint cardinality alone.

For completeness, we now construct a canonical Borel parameter along
each compact arc and then treat the coincident-endpoint circle case.

### Lemma 5.2 (Borel ordered-arc parameterization)

Let \(K_s\) be a Borel field of compact arcs in a compact metric space,
with Borel ordered endpoint maps \(a_s,b_s\).  There is a Borel map

\[
 e:L\times[0,1]\to\overline V^{\,\rm pe}
\tag{5.6}
\]

such that \(e(s,\cdot)\) is the order-preserving homeomorphism from
\([0,1]\) onto \(K_s\), with endpoints \(a_s,b_s\).

#### Proof

We give the construction to avoid a hidden parametrization theorem.

For \(x,y\in K_s\), write \(y\preceq_s x\) when \(y\) belongs to the
initial subarc from \(a_s\) to \(x\).  This is a Borel relation in
\((s,x,y)\).  Indeed, apart from the equality case \(y=x\),
\(y\preceq_s x\) is equivalent to the assertion that \(a_s\) and
\(y\) lie in the same component of
\(K_s\setminus\{x\}\).  The latter is equivalent to the existence of
an integer \(m\) and a compact connected set

\[
 C\subset K_s\setminus B(x,1/m)
\]

containing \(a_s\) and \(y\).  Connected compact sets form a closed
subset of the compact hyperspace.  Before substituting the Borel
field \(s\mapsto K_s\), the incidence, containment, and distance
conditions are closed in the corresponding hyperspace variables.
After substitution they are Borel, and their sections in the
compact-set variable are compact.  AK therefore makes the projection
Borel.  Taking the countable union over \(m\) and adding the equality
cases gives the claimed order relation.

Consequently,

\[
 K_s[a_s,x]
 :=
 \{y\in K_s:y\preceq_s x\}
\tag{5.7}
\]

has a Borel graph and nonempty compact sections.  Its hit relation
with an open subset of the ambient compactum is a projection with
sigma-compact sections, so AK shows that (5.7) is a Borel
compact-valued field in \((s,x)\).

Choose a dense sequence \((q_n)\) in the ambient compact metric space
and define, for nonempty compact \(C\),

\[
 \Theta(C)
 :=
 \sum_{n=1}^\infty
 2^{-n}\frac{1}{1+d(q_n,C)} .
\tag{5.8}
\]

This is continuous on the compact hyperspace.  It is strictly
increasing under proper inclusion.  Monotonicity is immediate.  If
\(C\subsetneq D\), choose \(z\in D\setminus C\); compactness gives
\(d(z,C)>0\), and a sufficiently close \(q_n\) makes the \(n\)-th
summand strictly larger for \(D\), while every other summand is
nondecreasing.

Set

\[
 u_s(x)
 :=
 \frac{
 \Theta(K_s[a_s,x])-\Theta(\{a_s\})
 }{
 \Theta(K_s)-\Theta(\{a_s\})
 }.
\tag{5.9}
\]

The denominator is positive.  The map is Borel in \((s,x)\).
For fixed \(s\), initial subarcs vary continuously in the Hausdorff
topology as \(x\) moves along an arc.  Hence \(u_s\) is continuous.
Strict inclusion of initial subarcs makes it strictly increasing, and
its endpoint values are \(0,1\).  It is therefore a homeomorphism
from \(K_s\) to \([0,1]\).

The relation

\[
 \{(s,r,x):x\in K_s,\ u_s(x)=r\}
\tag{5.10}
\]

is Borel and has singleton \(x\)-sections.  Lusin--Novikov supplies
the Borel inverse \(e(s,r)\).  Fiberwise it is the inverse of a
homeomorphism, proving the lemma. \(\square\)

### Lemma 5.3 (Borel marked-circle parameterization)

Let \(K_s\) be a Borel field of Jordan circles in a compact metric
space and let \(a_s\in K_s\) be a Borel marked point.  There is a
Borel map

\[
 e_\circ:L\times[0,1]\longrightarrow \overline V^{\,\rm pe}
\tag{5.11}
\]

such that, for each \(s\),

1. \(e_\circ(s,0)=e_\circ(s,1)=a_s\);
2. \(e_\circ(s,\cdot)\) is injective on \([0,1)\); and
3. its image is \(K_s\).

#### Proof

First choose a second point Borelly.  For each \(n\geq1\), the field

\[
 D_{s,n}:=K_s\setminus B(a_s,1/n)
\]

is compact-valued and Borel on its nonempty locus.  Choose the least
\(n(s)\) for which it is nonempty and apply the
Arsenin--Kunugui uniformization clause to obtain a Borel
\(c_s\in D_{s,n(s)}\).

There are exactly two ordered pairs \((C,D)\) of nonempty compact
connected sets such
that

\[
 C\cup D=K_s,\qquad C\cap D=\{a_s,c_s\}.
\tag{5.12}
\]

This assertion is coded Borelly in the product hyperspace: compact
connectedness is closed, union is continuous, containment of the two
marked points is closed, and
\(C\cap D\subset\{a_s,c_s\}\) is the countable family of compact
avoidance tests against basic open sets whose closures miss
\(\{a_s,c_s\}\).  Because \(K_s\) is a Jordan circle, these conditions
force \(C,D\) to be its two complementary compact arcs.  The sections
are exactly the two swaps.  Lusin--Novikov enumerates them; a fixed Borel linear order on
the compact hyperspace selects one ordered pair
\((C_s,D_s)\).

Apply Lemma 5.2 to \(C_s\) with ordered endpoints
\((a_s,c_s)\), and to \(D_s\) with ordered endpoints
\((c_s,a_s)\).  Traverse the first arc on \([0,1/2]\) and the second
on \([1/2,1]\).  The resulting map is Borel, continuous on every
fiber, takes the common value \(c_s\) only at \(1/2\), and takes
\(a_s\) only at \(0,1\).  It has all three required properties.
\(\square\)

Apply Lemma 5.2 on the Borel two-endpoint locus and Lemma 5.3 on the
Borel one-endpoint locus.  Combining the two maps gives

\[
 e_\alpha:L_\alpha\times[0,1]\longrightarrow
 \overline V^{\,\rm pe}
\tag{5.13}
\]

whose restriction to \(L_\alpha\times(0,1)\) is a jointly Borel
evaluation of the original proper leaves in \(V\).  It is injective
on the product of the tagged leaf parameter with \((0,1)\): for a
fixed leaf this follows from Lemmas 5.2--5.3, and different leaf
images are disjoint in \(V\).

## 6. Compatibility with annular deck order

Do **not** impose one total order on an arbitrary DL Wave merely
because every leaf goes above the same interval \(J\).  Without common
collective end blocks, two arc classes can fan from a shared endpoint
on opposite sides of \(J\); their \(J\)-side domains overlap without
being nested.  The correct object is the finite ordered arc atlas.

For each nonempty Borel arc packet \(P=\mathscr B(\alpha)\), choose its
preferred side; when the packet is directed above \(J\), choose the
\(J\)-side.  Lemmas 3.1--3.3 give its Borel numeric order \(t_\alpha\).
In the universal annular cover, the deck order of the noncrossing
lifts in this one arc class is the same order or its reverse: two
leaves can exchange order only by crossing.  Fixing the orientation of
one boundary lift chooses the sign.  Thus either \(t_\alpha\) or
\(-t_\alpha\) is compatible with the DL deck order on that packet.

Section 2 gives only finitely many nonempty arc classes, including
zero-width classes.  Therefore

\[
 \left\{
   (L_\alpha,\preceq_\alpha):
   \alpha\in\mathcal A(\mathscr B)
 \right\}
\tag{6.1}
\]

is a finite Borel ordered atlas for the full DL Wave.  Every initial
or terminal interval in one chart is Borel.

Nothing in this paragraph identifies DL's informal global
“outermost-curves” deletion with an order interval in every chart.
That extra statement is false as an inference from the word
“outermost” alone and is not proved at DL 2827--2841.  Section 7.4
uses the Borel width-envelope theorem instead.  Consequently the
number of arc charts contributes neither a measurable selection nor
an analytic loss.

## 7. Closure under the stationary operations

We now audit every operation used in Theorem N1.

### 7.1 Finite discrete partitions

Arc class, endpoint marking interval, singleton base route,
leafwise direction, central/over/away type, and short/nonshort type
are finite or countable predicates on:

- the finite arc-class tag;
- the two Borel prime-end endpoints; and
- the finite cyclic marking.

Their leaf sets are Borel.  A Borel subset of \(L_S\) is again
standard Borel, and restricting the evaluation preserves all clauses.

The initial source family is Borel by the same native properness
convention as Lemma 2.1.  KKL 1356 explicitly calls
\(A^{N\text{-nbr}}\) a subwave, and KKL 1182 calls
\(A^{\rm sh}\) the unique maximal short subwave.  Hence both are
proper Borel laminations in the source's declared sense.  Their
leafwise difference

\[
 A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}
\]

has Borel geometric support and remains a lamination subordinate to
the base of \(A\), hence is a proper Borel Wave.

In particular, the initial split in Lemma 5.2 of the main N1 note is
not an unproved saturation.  By Section 2, each singleton crest is
constant on its arc tag.  Therefore

\[
\begin{aligned}
 S^+
 &=
 \mathop{\dot\bigcup}_{\alpha:\,
   BL_1\subset\operatorname{crest}(\alpha)}S(\alpha),\\
 S^-
 &=
 \mathop{\dot\bigcup}_{\alpha:\,
   BL_1\not\subset\operatorname{crest}(\alpha)}S(\alpha).
\end{aligned}
\tag{7.1a}
\]

These are finite unions of the Borel arc sublaminations supplied by
KL06.  The same argument makes the short part the union of the
short arc tags.

This import must not be replaced by occurrence counting.  Distinct
restriction occurrences can have the same image under \(f\), and KKL
then regards the source path as unbreakable.  Nor may one test general
unbreakability merely by equality of compact images: an unfiltered
pushed path need not be embedded, so its image can forget traversal
data.  Section 7.3 instead constructs a Borel successor only on the
already imported unbreakable subwave, where the unique untagged path
is known to exist.

### 7.2 Filtered immersion restriction

Choose a countable inverse-branch atlas for the holomorphic immersion
\(\iota:V'\to V\).  A lift germ is coded by

\[
 (\ell,q,z',\text{inverse-branch chart}),
\qquad
 q\in\mathbb Q\cap(0,1),
\quad
 \iota(z')=e_S(\ell,q).
\tag{7.1}
\]

The fiber in (7.1) is discrete and countable.  Its relation is Borel,
so Lusin--Novikov gives a Borel enumeration of the possible \(z'\)'s.

Path lifting gives one maximal continuation

\[
 \widetilde\gamma_\omega:
 I_\omega=(a_\omega,b_\omega)\longrightarrow V'
\tag{7.2}
\]

through a germ \(\omega\).  The interval need not be all of
\((0,1)\): a lift can escape from \(V'\) at a finite source time.
This interval is part of the occurrence record.

To see that the record is Borel, refine the inverse-branch atlas by a
nested countable exhaustion of each target chart:

\[
 \overline{W_{i,k}}\Subset W_{i,k+1}\Subset W_i,
 \qquad
 \bigcup_k W_{i,k}=W_i,
\]

where the inverse branch is defined on \(W_i\).  A continuation over a
compact rational interval is coded
by a rational subdivision and a finite sequence of such
compactly-contained charts.  The requirement that the source segment
over one subdivision interval remain in the closed set
\(\overline{W_{i,k}}\subset W_i\) is Borel: check its rational times
and use fiberwise continuity.  Since the exhaustion is nested, the
compact image of a segment contained in \(W_i\) lies in one
\(W_{i,k}\).  Thus compactness loses no valid continuation.  Adjacent inverse
branches are required to agree at the subdivision point.  Conversely,
compactness of a continued lift supplies a finite word with positive
chart margins.  Thus reachability of a rational time is exactly a
countable union of finite Borel word predicates.  Hence

\[
 a_\omega
 =
 \inf\{r\in\mathbb Q:r<q
       \text{ and the germ continues on }[r,q]\},
\quad
 b_\omega
 =
 \sup\{r\in\mathbb Q:r>q
       \text{ and the germ continues on }[q,r]\}
\tag{7.3}
\]

are Borel extended-real functions.  Evaluation of
\(\widetilde\gamma_\omega\) at every **original** rational time in
\(I_\omega\) is Borel.  After affine reparametrization, normalized
time \(r\in(0,1)\) corresponds to

\[
 u_\omega(r)=a_\omega+(b_\omega-a_\omega)r.
\]

Choose, from a fixed enumeration of \(\mathbb Q\), the first
\(q_n(\omega,r)\in I_\omega\) with
\[
 |q_n(\omega,r)-u_\omega(r)|
 <
 \min\!\left\{\frac1n,
 \frac{u_\omega(r)-a_\omega}{2},
 \frac{b_\omega-u_\omega(r)}{2}\right\}.
\]
This choice is Borel and converges to the correct original time.
Fiberwise continuity gives

\[
 \widetilde\gamma_\omega(u_\omega(r))
 =
 \lim_{n\to\infty}
 \widetilde\gamma_\omega(q_n(\omega,r)),
\]

so the full evaluation is jointly Borel, not merely determined
set-theoretically by its rational values.  From here onward
\(\widetilde\gamma_\omega(r)\) denotes this normalized evaluation at
\(r\in(0,1)\).

Fix a compact exhaustion

\[
 K_m'\subset\operatorname{int}K_{m+1}',
\qquad
 \bigcup_m K_m'=V'.
\]

Affinely reparametrize \(I_\omega\) by \((0,1)\).  Proper escape is
equivalent to

\[
\forall m\ \exists N,k\ \forall
r\in
\bigl((0,1/N)\cup(1-1/N,1)\bigr)\cap\mathbb Q:
\quad
d(\widetilde\gamma_\omega(r),K_m')\geq1/k .
\tag{7.4}
\]

The positive distance is essential: mere nonmembership at rational
times would not exclude an irrational contact or asymptotic
accumulation.  Continuity extends (7.4) to every tail time.
Conversely, (7.4) makes the inverse image of every \(K_m'\) closed and
contained in a compact parameter subinterval, hence compact.  Thus
(7.4) is exactly properness and is Borel.

Properness alone does not force either tail to converge to one prime
end.  Endpoint convergence is therefore tested before applying the
KKL filters.  In a compatible complete metric \(d_{\rm pe}\) on the
compact prime-end annulus, the initial-tail condition is

\[
\forall k\ \exists N\ \forall
r,s\in(0,1/N)\cap\mathbb Q:
\quad
d_{\rm pe}(\widetilde\gamma_\omega(r),
           \widetilde\gamma_\omega(s))<1/k ,
\tag{7.5}
\]

and similarly at the terminal tail.  These are Borel predicates.
Compact completeness gives the two limits; continuity makes the
rational Cauchy test equivalent to convergence of the full tails.
The limit maps are Borel as pointwise limits of the Borel sequences
\(\widetilde\gamma_\omega(1/(n+1))\) and
\(\widetilde\gamma_\omega(1-1/(n+1))\).  Require both limits to lie on
the ideal boundary.

It remains to justify the two homotopy filters rather than label them
“finite predicates.”  Adjoin the two limits to obtain
\(\overline\gamma_\omega\in
C([0,1],\overline V'^{\,\rm pe})\).  The map
\(\omega\mapsto\overline\gamma_\omega\) is Borel: evaluation at every
rational time is Borel, and those evaluations generate the Borel
sigma-algebra of the compact-open path space.

Fix two open marked endpoint intervals.  Relative homotopy classes of
paths whose endpoints may move inside those intervals are open in the
corresponding compact-open path space.  To verify this, cover the
compact image of one path by finitely many simply connected coordinate
disks and boundary half-disks with a common Lebesgue number.  A
sufficiently uniformly close second path can be joined to the first
inside the successive disks, including short endpoint joins inside
the fixed marking intervals.  These joins give a relative homotopy.
Thus every path has an open neighborhood contained in its relative
homotopy class.

The moving-endpoint convention is compatible with KKL subordination.
Indeed, if an endpoint moves along a track contained in a marked
interval \(I\subset X\), attach that track as a short endpoint whisker
to the old representative in a neighborhood of \(X\).  This produces
a representative with the new endpoint still subordinate to \(X\).
Running the whisker backward proves the converse.  Thus an
endpoint-moving relative homotopy inside the prescribed intervals
preserves, in both directions, subordination to every multi-interval
containing those endpoint tracks.

For fixed endpoint marking intervals, the relative homotopy classes
are pairwise disjoint open subsets of a second-countable path space,
so there are at most countably many; equivalently they are the
countable endpoint/deck-winding tags in the universal cover.
The endpoint-whisker argument proves that subordination is invariant
under these relative homotopies.  Hence the
property

```text
is subordinate to some fine multi-interval of length at most two
```

is a union of those open relative-homotopy classes, hence is open and
Borel.  This avoids enumerating all possible limit cuts of the ideal
boundary.  Subordination to one member of the countable coarse pulled
marking is handled in the same way, followed by a countable union.
Consequently:

1. endpoint membership in the fine marking and failure of
   subordination to every fine multi-interval of length at most two is
   Borel; and
2. failure of subordination to every single coarse pulled interval is
   Borel.

These are exactly the two filters at KKL 2096--2097.  This argument
also covers countably many annular winding tags; no false finiteness
claim is used.

One maximal occurrence contains a rational source time.  Two germ
codes represent the same occurrence exactly when their maximal source
intervals have nonempty overlap and their lifted evaluations agree at
one rational time in that overlap.  The nonempty-overlap clause is
essential: without it, universal agreement “on the overlap” would be
vacuous for two disjoint occurrences.  Uniqueness of path lifting then
identifies the two maximal lifts and their maximal intervals.  This is
a countable Borel predicate.  Use the natural-number indices supplied
by the Lusin--Novikov enumeration of fiber points and the fixed
enumerations of rational times and inverse charts; retain the
lexicographically least index tuple.  No nonexistent lexicographic
order on the raw point \(z'\) is invoked.
The resulting retained-occurrence relation is Borel with countable
source sections.  Its occurrence space is standard Borel by
Lusin--Novikov.  Composing the source evaluation with the selected
inverse branches and the affine reparametrization gives a jointly
Borel evaluation of every proper retained component.

Because distinct retained components form a lamination, the
evaluation is injective.  Lusin--Souslin makes its geometric union
Borel.  Therefore a full filtered restriction packet is again a
proper Borel lamination with a standard-Borel occurrence code.

### 7.3 Covering pushforward and the untagged successor

Composition of the occurrence evaluation with the holomorphic cover
\(f\) is Borel.  On a DL-retained packet, \(f\) is injective on the
geometric union, so Lusin--Souslin makes the image Borel.

For a general unbreakable source packet, the pushed images need not
collectively be a lamination, and a pushed path need not be embedded.
We therefore neither create a leaf space for all of \(F_*S\) nor
identify a general pushed path solely by its compact image.

Let \(\Omega(S)\to L_S\) be the countable Borel occurrence relation
from Section 7.2.  On the already imported unbreakable subwave every
source leaf has at least one retained occurrence, and all pushed
occurrences represent the same untagged path.  This is KKL's native
path convention: KKL 406 takes paths modulo reparameterization, while
KL06 `wad.tex` 26--48 defines reparameterization and permits a path to
be identified with its geometric image only as an explicit abuse of
notation.

Use the Lusin--Novikov enumeration of \(\Omega(S)\) to choose the
least retained occurrence and push its normalized path evaluation
through \(f\).  The retained endpoints lie in the pulled marking
where the finite cover extends continuously on the prime-end
boundary, so the two endpoint values are included as well.  The
result is a Borel map into the Polish path space

\[
 \widehat\Phi_1:L_S\longrightarrow
 C([0,1],\overline V^{\,\rm pe}).
\tag{7.6}
\]

The chosen parameterization can depend on the selected occurrence,
but its unparameterized KKL path does not.  This is all that is needed
to retain traversal information for the next operation.

When the output belongs to an actual retained image Wave \(R\), it is
embedded.  Let

\[
 j_R:L_R\longrightarrow
 \mathcal K(\overline V^{\,\rm pe}),\qquad
 j_R(r)=K_r
\tag{7.6a}
\]

be the compactified-leaf code of Section 5.  It is Borel and injective,
so Lusin--Souslin makes \(j_R(L_R)\) Borel and \(j_R^{-1}\) Borel on
that range.  The compact-image map

\[
 \operatorname{im}:
 C([0,1],\overline V^{\,\rm pe})
 \longrightarrow\mathcal K(\overline V^{\,\rm pe})
\]

is continuous in the uniform and Hausdorff metrics.  Hence, on the
Borel source set whose unique output is in \(R\),

\[
 \phi_{S,R}
 :=
 j_R^{-1}\circ\operatorname{im}\circ\widehat\Phi_1
\tag{7.6b}
\]

is the Borel map to the *leaf code* of \(R\).

Finite stationary iteration is performed by composing maps of the
form (7.6b) through the actual intermediate Waves
\(S_0,S_1,\ldots\), and by using each next Wave's own jointly Borel
path evaluation when constructing its restriction relation.  Thus no
compact-image code is incorrectly fed into the next restriction
operator, and no unfiltered pushforward is asserted to be a
lamination.

### 7.4 Borel regularization of the DL pruning

The set-theoretic DL proof gives an injective retained subwave
\(B^\sharp_{\rm DL}\subset B\).  Its displayed retained-width
inequality alone would not bound the width of the complement.  The
proof itself supplies the stronger relative statement

\[
 D_{\rm DL}:=B\setminus B^\sharp_{\rm DL},
 \qquad
 \mathcal W(D_{\rm DL})\le C_{\rm DL}.
\tag{7.6c}
\]

For degree two this follows from DL 2830--2839: there are
\(T=O(\log 2)=O(1)\) nonzero span packets, each of bounded width by the
Shift argument, followed at DL 2841 by one bounded outer deletion.
The Parallel Law bounds their union.  We record this proof-internal
input as `DL_RELATIVE_DISCARD_FAMILY_BOUND`; it is not inferred from
the aggregate inequality.

The family \(D_{\rm DL}\) need not have a Borel leaf predicate.  Apply
Theorem 1.1 of
`kkl_stationary_n1_borel_width_envelope_20260726.md` to the
standard-Borel source Wave \(B\), with \(\varepsilon=1\).  It produces
a Borel leaf set \(E_{\rm DL}\) such that

\[
 D_{\rm DL}\subset E_{\rm DL},
 \qquad
 \mathcal W(E_{\rm DL})\le C_{\rm DL}+1.
\tag{7.6d}
\]

Define

\[
 B^\sharp_{\rm Bor}:=B\setminus E_{\rm DL}.
\tag{7.6e}
\]

Then \(B^\sharp_{\rm Bor}\subset B^\sharp_{\rm DL}\), so the covering
is injective on its geometric union.  Both sides of (7.6e) are proper
Borel sublaminations.  Composition of their injective evaluation with
the covering gives a proper Borel target lamination by
Lusin--Souslin.  In the N1 application this target lies in the actual
unbreakable \(F_*\)-packet; KKL Proposition A.14, applied to each
singleton source/output pair, makes that singleton a Wave over the
same interval \(F_*I\).  Let \(C\) be the target ideal-boundary
component containing \(F_*I\).  The singleton base is contained in
\(C\), so every output path is subordinate to \(C\).  The whole
component \(C\) is an allowed multi-interval in KKL 1853--1856;
because the injective target family is already a proper Borel
lamination, KKL 1874 makes its union a target Wave subordinate to
\(C\).  Proposition A.14 separately supplies the leafwise direction
\(R\uparrow F_*I\).  It does not assert that the aggregate crest of
\(R\) contains \(F_*I\).  No source base is silently transported
through the covering.  All later degree-two pullback, direction, and
unbreakability statements are hereditary under passage to this
smaller retained family.

Thus the N1 proof uses \(B^\sharp_{\rm Bor}\) and the single
`metric-envelope discard` \(E_{\rm DL}\).  It never needs a Borel
predicate for an individual span class or outer buffer, and it never
assumes transverse countable additivity of extremal width.

### 7.5 Full terminal saturation

Let \(R\) be the actual terminal Wave, let \(E\subset L_R\) be its
Borel terminal leaf set, and let \(\phi_h\) be the finite composition
of the typed leaf-code maps (7.6b).  Then the full source saturation is

\[
 \phi_h^{-1}(E).
\tag{7.7}
\]

Equivalently, if one retains the compact code rather than applying
\(j_R^{-1}\), it is

\[
 (\operatorname{im}\widehat\Phi_h)^{-1}(j_R(E)),
\]

not the ill-typed expression
\(\widehat\Phi_h^{-1}(E)\).  The set \(j_R(E)\) is Borel by
Lusin--Souslin.  Therefore (7.7) is Borel in the source leaf space.
Restrict the source evaluation to this set.  It remains injective, so
Lusin--Souslin makes the geometric union Borel.  Hence full saturation
is a proper Borel sublamination.

This validates the explicit saturation in equations (7.9), (9.2),
and (9.5) of the main N1 proof.

## 8. Exact interface correction

An earlier provisional Definition 3.1 in the main N1 note required a
“Borel transverse width measure.”  That phrase risks asserting a
false additivity property: extremal width is a capacity on arbitrary
path families and is not, merely from the KL06 definition, a
countably additive measure on the leaf quotient.

The proof actually needs the following corrected clause.

### Definition 8.1 (Borel width-envelope pruning clause)

For each proof-used DL packet \(B\), the proof-internal set-theoretic
discard \(D_{\rm DL}\) satisfies

\[
 \mathcal W(D_{\rm DL})\le C_{\rm DL}.
\]

The Borel width-envelope theorem supplies a Borel super-discard
\(E_{\rm DL}\supset D_{\rm DL}\) with

\[
 \mathcal W(E_{\rm DL})\le C_{\rm DL}+1,
\]

and the proof uses the Borel retained family
\(B\setminus E_{\rm DL}\subset B^\sharp_{\rm DL}\).

Section 7.4 proves Definition 8.1 from the independently audited
width-envelope theorem.  DL 2830--2841 supplies the analytic relative
discard bound.  No claim about chartwise buffer convexity and no
transverse width measure is required.

The main N1 note now imports Definition 8.1 through its Theorem 3.1.
Sections 2--7 therefore prove all clauses of
`STANDARD_BOREL_ORDERED_WAVE_REALIZATION` used by Gate N1.

## 9. Adversarial audit

### 9.1 Fat-Cantor transverse sets

For \(E\subset(0,a)\) a fat Cantor set, the vertical family
\(\{x\}\times(0,1)\), \(x\in E\), is not a union of full open
rectangle foliations.  It is nevertheless covered by the theorem:
its side domains are nested, \(t\) is a strictly monotone Borel
function of \(x\), and its realized coordinate set is Borel.

Thus the proof does not smuggle in a full-rectangle hypothesis.

### 9.2 Nonclosed geometric support

The union \(Z_\alpha\) need only be Borel.  Lemma 3.3 uses open
unions and at most one individual closed leaf; it never takes the
closure of the whole lamination.  Accumulating leaves therefore cause
no failure.

### 9.3 Gaps and jumps in the leaf order

The set \(L_\alpha=t(P)\) may have arbitrary gaps and need not be
closed.  AK, rather than an unsupported monotone-image claim, proves
that it is Borel.  The sublevel proof explicitly handles a maximal
leaf immediately below a gap.

### 9.4 Shared ideal endpoints

Leaves may converge to, or share, ideal endpoints.  The order is
defined by nested open domains, not by injectivity of the endpoint
pair.  Endpoint multiplicity therefore does not collapse the leaf
code.

### 9.5 Non-local connectivity of \(\mathcal T\)

All boundary statements occur in the prime-end compactification.
No map from the geometric boundary of \(\mathcal T\) to a locally
connected model is used.

### 9.6 Countable inverse branches

The restriction relation is not declared Borel merely because
\(\iota\) is analytic.  Section 7.2 uses the Borel source evaluation,
a countable inverse-branch atlas, rational seed times, a compact
exhaustion, and both endpoint filters.  Countability enters only after
the source leaf code has been constructed.

### 9.7 Outer-buffer width

The Borel proof neither infers that extremal width is a transverse
measure nor assigns a chart order to DL's informal deletion.  It
imports the single proof-internal relative bound
\(\mathcal W(D_{\rm DL})=O(\log m)\) and envelopes the entire discard
once.  The new Borel discard has width at most
\(\mathcal W(D_{\rm DL})+1\).

### 9.8 Period dependence

The construction uses finitely many arc packets for each stationary
block but introduces no analytic constant.  The N1 width constant
continues to come solely from the degree-two lift, DL loss, KKL limb
bound, and the fixed horizon \(N=b+3\).  No sum of an additive error
over all \(O(bq)\) arc classes occurs.

### 9.9 Opposite-side fan

Two disjoint crosscuts can share one ideal endpoint and fan toward
two endpoints lying on opposite sides of a fixed interval \(J\).
Both leaves can be individually directed above \(J\), while their
\(J\)-side domains overlap and are not nested.  This refutes the
shortcut “one common directed interval gives one total leaf order.”

Section 6 does not use that shortcut.  It retains only the finite
arc-class order atlas needed for the leaf code.  Section 7.4 bypasses
all global chartwise-order claims through the Borel width envelope.

## 10. Status consequence

The width-envelope theorem has passed independent audit.  The
integrated BOWR statement remains a candidate until the repaired
shared-endpoint, occurrence, and backward-use clauses in this exact
file are independently re-audited:

| statement | status in this note |
|---|---|
| Borel arc-class packets | proved |
| injective planar order coordinate | proved |
| Borel leaf quotient | proved via AK |
| Borel endpoints and evaluation | proved |
| KKL filtered-restriction closure | proved |
| `DL_RELATIVE_DISCARD_FAMILY_BOUND` | imported from the discarded packets in DL 2830--2841 |
| `BOREL_WIDTH_ENVELOPE_PRUNING` | proved and independently audited |
| chartwise DL outer-buffer measurability | not proved and no longer required |
| full saturation closure | proved |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | candidate proved, pending integrated-file re-audit |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | remains open until integration audit |
| N2, VAAPC-I, UPTCR, MLC | open |

No result is promoted merely by the existence of this draft.
