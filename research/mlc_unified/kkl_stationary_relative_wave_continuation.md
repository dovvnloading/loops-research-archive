# Gate N1 — stationary relative Wave continuation by leafwise directed crests

## 0. Status, scope, and theorem boundary

This note addresses only

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION
```

for the stationary paragraph of Kahn--Kapiamba--Lyubich (KKL),
arXiv:2606.27272 v1.  It does not use the literal broad
coefficient-one Wave statement printed as KKL Lemma A.13.  That
statement is false under the printed definition of a Wave; the exact
fixed-degree counterexample is recorded in
`qa_extremal_wave_2026-07-26.md`.

The proof below replaces the invalid broad extraction by the narrower
annular source-pruning argument of Dudko--Lyubich (DL) on one actual
leafwise-directed source packet.  The point that makes the replacement
possible is a directed-limb observation:

> a nonshort leaf ending at \(BL_0\) is individually directed above
> \(BL_1\) or \(BL_{-1}\); the \(BL_{-1}\)-class has bounded width
> because its next directed crest is \(BL_0\), while the
> \(BL_1\)-class thereafter advances leaf by leaf as
> \(BL_1,BL_2,\ldots\).

Thus no union of incompatible pushed packets is ever taken.

The main theorem proved in Section 9 is the following corrected
existence form.  Its analytic and descriptive-set components are
separated in the dependency ledger, then recombined in Section 9.

### Theorem N1 (Borel leafwise-directed stationary continuation)

Fix \(b\geq1\), put \(N=b+3\), and let \(F\) be a KKL
parabolically \(b\)-bounded, periodically repelling,
primitively-renormalizable pseudo-quadratic-like relation.  Let \(A\)
be a proper Wave ending at \(BL_0\).  There are nested leaf
subfamilies

\[
 A_0\supset A_1\supset\cdots\supset A_{N-1},
 \qquad
 A_0=A^{N\text{-nbr}}\setminus A^{\rm sh},
\]

such that, with

\[
 S_n:=\Phi_n(A_n)=F_*^nA_n,
\]

the following hold for \(0\leq n<N\):

1. \(S_n\) is a Wave ending at \(BL_0\);
2. \(S_n=S_n^{(N-n)\text{-nbr}}\);
3. for every nonempty \(S_n\), \(n\geq1\), every leaf is individually
   directed above the same noncritical limb block \(BL_{k_n}\);
4. for one constant \(C_b<\infty\), independent of the rotation
   denominator \(q\), the Wave, and all analytic widths,
   \[
     \mathcal W(A_n\setminus A_{n+1})\leq C_b
     \qquad(0\leq n<N-1).
   \]

Each family is a union of disjoint proper paths with the stated Wave
base and ends, and its extremal width is defined in the literal
path-family sense.  The Borel realization theorem in Section 3 makes
every one of these families a proper Borel KKL subwave.

The sequence is constructed by full occurrence saturation over the
central output Wave.  It is not defined by the ambiguous phrase
“the maximal subwave” at KKL line 1548.  Any later use needs only this
explicit nested sequence and not maximality.

The descriptive-set construction and the Borel regularization of the
DL discard are proved independently in
`kkl_stationary_n1_borel_ordered_wave_realization_20260726.md` and
`kkl_stationary_n1_borel_width_envelope_20260726.md`.  Section 3
imports their exact conclusions and verifies that they apply to every
operation in this proof.  Thus the theorem below is the full
stationary relative continuation claimed by Gate N1, subject only to
the final frozen-snapshot audits recorded in Section 12.

Sections 11--12 audit the theorem against the known cyclic-cover
counterexamples and list the exact hypotheses used.  This note does
not prove the later alignment assertion at KKL line 1603 and makes no
claim about VAAPC-I, UPTCR, or MLC.

## 1. Frozen sources and notation

The source files are immutable local copies.

| source | role | SHA-256 |
|---|---|---|
| `.tmp_wave_audit/waves-with-Misha.tex` | KKL master, arXiv:2606.27272 v1 | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_wave_audit/dl23/Feigen.tex` | DL annular source-pruning proof | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_kl06_source/appendix.tex` | extremal width, Series/Parallel laws | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| `.tmp_kl06_source/wad.tex` | proper Borel laminations and pulled WADs | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |

The exact KKL clauses used are:

- 439--461: pseudo-quadratic-like relations and the typed iterate;
- 497--503: cyclically ordered limbs and rotation number \(1/q\);
- 512--543: the planar Hubbard tree, the preimage tree
  \(f^{-1}(\mathcal T)\), and the combinatorial model;
- 661--667: parabolic \(b\)-boundedness;
- 838--866: \(BL_j\) and \(\ell(BL_j)\leq6b\);
- 1225--1274: the complementary covering/immersion, pulled markings,
  combinatorial action, and
  \[
    F_*BL_j=BL_{j+1}\quad(j\ne0),\qquad
    F_*BL_0=\partial_{\rm C}\mathcal T;
  \]
- 1355--1358: sequential unbreakability;
- 1403--1411: the one-step part of controllability transport;
- 1429--1478: restriction of an unbreakable common-crest Wave,
  including
  \[
    B=\iota^*S\text{ is a Wave over }\iota^*I,\qquad
    \mathcal W(S)\leq\mathcal W(B);
  \]
- 1524--1532: the Shift bound for localized nonshort Waves away
  from \(BL_0\);
- 1547--1559: \(N=b+3\) and the stationary horizon;
- 1839--1875: ideal markings, paths, laminations, bases, ends, and
  crests;
- 2065--2142: covering pushforward, immersion restriction, both
  marking filters, domination, and the action \(F_*=f_*\iota^*\);
- 2161--2168: unbreakability and common-crest transport; and
- 2171--2178: the Shift lemma.

Only the *proof* of the inner DL lemma at `Feigen.tex` 2821--2842 is
used.  Its input is a degree-\(m\) covering of annuli and one Wave above
one fixed boundary interval.  Its output is a source subwave on which
the cover is injective.  No numerical or computational statement is
used.

The indexing \(F_*BL_j=BL_{j+1}\) is legitimate in this note because
parabolic \(b\)-boundedness includes the hypothesis that the
combinatorial rotation number is \(1/q\) (KKL 662--666).  In the
general \(p/q\) notation at KKL 497--503 the geometric action is
\(j\mapsto j+p\).  The directed-adjacent argument below is not asserted
outside the \(p=1\) stationary setting.

Write

\[
  V=\mathcal U\setminus\mathcal T,\qquad
  V'=\mathcal U'\setminus f^{-1}(\mathcal T).
\]

On these complements,

\[
 f:V'\to V
\]

is an unbranched degree-two cover and

\[
 \iota:V'\to V
\]

is a holomorphic immersion.  The fine source marking is
\(f^*\mathcal I\); the coarser immersion marking is
\(\iota^*\mathcal I\).  Every restriction occurrence below is required
to survive both filters at KKL 2096--2097.

For \(\alpha\in A^{N\text{-nbr}}\), define the unique untagged
successors

\[
 \Phi_0(\alpha)=\alpha,\qquad
 F_*\Phi_j(\alpha)=\{\Phi_{j+1}(\alpha)\}
 \quad(0\leq j<N).
\]

This does not choose a unique retained restriction occurrence.

## 2. Width facts used in the proof

### Lemma 2.1 (finite-cover full-lift identity)

If \(p:X\to Y\) is an unbranched conformal cover of finite degree
\(d\), and \(p^*\Gamma\) denotes all lifts of every interval-
parametrized path in \(\Gamma\), then

\[
  \mathcal W(p^*\Gamma)=d\,\mathcal W(\Gamma).
  \tag{2.1}
\]

#### Proof

If \(\rho\) is admissible for \(\Gamma\), then \(p^*\rho\) is
admissible for every lift and

\[
 \operatorname{area}_{p^*\rho}(X)
 =d\,\operatorname{area}_{\rho}(Y).
\]

This gives

\[
 \mathcal W(p^*\Gamma)\leq d\,\mathcal W(\Gamma).
 \tag{2.2}
\]

Conversely, let \(\sigma\) be admissible for \(p^*\Gamma\).  Locally
enumerate the inverse branches by \(s_1,\ldots,s_d\), and put

\[
 \rho(y)=
 \frac1{\sqrt d}
 \left(
   \sum_{r=1}^d
   \sigma(s_r(y))^2|s_r'(y)|^2
 \right)^{1/2}.
 \tag{2.3}
\]

The expression is independent of the local enumeration.  If the
\(d\) lifts of \(\gamma\in\Gamma\) have \(\sigma\)-lengths
\(L_r\geq1\), Minkowski's integral inequality gives

\[
 \ell_\rho(\gamma)
 \geq
 \frac1{\sqrt d}
 \left(\sum_{r=1}^dL_r^2\right)^{1/2}
 \geq1.
\]

Thus \(\rho\) is admissible and

\[
 \operatorname{area}_\rho(Y)
 =
 \frac1d\operatorname{area}_\sigma(X).
\]

Taking infima gives the reverse inequality in (2.2), proving (2.1).
\(\square\)

### Lemma 2.2 (sequential relative transfer)

Let \(D\subset A_n\) and suppose

\[
 \Phi_n(D)\subset E\subset S_n.
\]

Then

\[
  \mathcal W(D)\leq2^n\mathcal W(E).
  \tag{2.4}
\]

#### Proof

Set \(D_j=\Phi_j(D)\) for \(0\leq j\leq n\).  Because
\(D\subset A_n\subset A_j\),

\[
 D_j\subset S_j,
\]

so every \(D_j\) is a sublamination of the already constructed Wave
\(S_j\).  Let \(B_j\) be the full family of retained restrictions of
\(D_j\) at step \(j\).  Preimages of disjoint leaves under a local
homeomorphism are disjoint; after the two filters, \(B_j\) is still a
lamination.  Unbreakability says:

1. every leaf of \(D_j\) has at least one leaf in \(B_j\); and
2. every leaf of \(B_j\) maps under \(f\) into \(D_{j+1}\).

KKL domination, inclusion, and Lemma 2.1 therefore give

\[
\begin{aligned}
 \mathcal W(D_j)
 &\leq\mathcal W(B_j)\\
 &\leq\mathcal W(f^*D_{j+1})\\
 &=2\mathcal W(D_{j+1}).
\end{aligned}
\]

Multiplying these \(n\) inequalities and using
\(D_n\subset E\) proves (2.4).  All retained occurrences are counted;
no untagged collision is discarded. \(\square\)

### Lemma 2.3 (relative one-common-crest DL pruning)

There is an absolute \(c_{\rm DL}<\infty\) with the following
property.  Let

\[
 p:A'\to A
\]

be a degree-two cover of closed annuli, let \(J\) be a connected
interval of one ideal boundary component of \(A'\), and let
\(\mathscr B\) be a proof-used proper Borel Wave above \(J\).  There
is a proper Borel subwave

\[
 \mathscr B^\sharp\subset\mathscr B
\]

such that

\[
 p|_{\mathscr B^\sharp}\text{ is injective},\qquad
 \mathcal W(\mathscr B\setminus\mathscr B^\sharp)
 \leq c_{\rm DL}.
 \tag{2.5}
\]

Moreover, \(p(\mathscr B^\sharp)\) is a proper Borel lamination and
\(p\) is conformal on each leaf.  In the stationary N1 application
all its paths have both ends on the same target ideal-boundary
component, so it is a KKL Wave subordinate to that component; the
leafwise target direction is supplied separately by KKL Proposition
A.14 on each singleton source/output pair.  For every subwave
\(\mathscr E\subset p(\mathscr B^\sharp)\),

\[
 \mathcal W\!\left(
   \mathscr B^\sharp\cap p^{-1}(\mathscr E)
 \right)
 \leq
 2\mathcal W(\mathscr E).
 \tag{2.6}
\]

#### Proof

Let \(\mathscr B^\sharp_{\rm DL}\) be the set-theoretic injective
subwave constructed in DL 2827--2841 and put

\[
 D_{\rm DL}:=
 \mathscr B\setminus\mathscr B^\sharp_{\rm DL}.
\tag{2.7}
\]

The displayed retained-width inequality at DL 2823 does not, by
itself, bound \(\mathcal W(D_{\rm DL})\).  The required relative
bound comes from the discarded packets in the proof.  DL 2830--2838
decomposes \(\mathscr B\) into disjoint dyadic deck-span classes

\[
 \mathscr B
 =
 \mathscr B^0\dot\cup\mathscr B^1\dot\cup\cdots
 \dot\cup\mathscr B^T,
 \qquad
 T=O(\log2)=O(1).
\]

For \(t>0\), write the packet as the one-buffer core \(C_t\) and its
two unit buffers \(Q_t^-,Q_t^+\).  The Shift argument at DL 2839
gives

\[
 \mathcal W(C_t)\leq c_{\rm sh},
\]

while the buffer definition at DL 1791--1792 gives

\[
 \mathcal W(Q_t^-)+\mathcal W(Q_t^+)\leq2.
\]

The Parallel Law therefore bounds every discarded nonzero-span
packet by \(c_{\rm sh}+2\).  DL 2841 removes one final \(O(1)\)
outer family from \(\mathscr B^0\).  Applying the Parallel Law once
to these finitely many discarded packets gives an absolute
\(c_{\rm DL}^{\rm raw}\) with

\[
\mathcal W(D_{\rm DL})\leq c_{\rm DL}^{\rm raw}.
\tag{2.8}
\]

We record (2.8), with this proof-internal provenance, as the analytic
import `DL_RELATIVE_DISCARD_FAMILY_BOUND`.  In particular, it is not
inferred from the aggregate retained-width inequality.

The family \(D_{\rm DL}\) need not have a Borel leaf predicate.
Apply `BOREL_WIDTH_ENVELOPE_PRUNING` with \(\varepsilon=1\).  It
produces a Borel super-discard \(E_{\rm DL}\supset D_{\rm DL}\) such
that

\[
 \mathcal W(E_{\rm DL})\leq c_{\rm DL}^{\rm raw}+1.
\tag{2.9}
\]

Define

\[
 \mathscr B^\sharp:=
 \mathscr B\setminus E_{\rm DL},
\qquad
 c_{\rm DL}:=c_{\rm DL}^{\rm raw}+1.
\tag{2.10}
\]

Then
\(\mathscr B^\sharp\subset\mathscr B^\sharp_{\rm DL}\), so DL
2827--2841 makes \(p\) injective on its geometric union.  The Borel
ordered-Wave realization gives a standard-Borel leaf space and a
jointly Borel injective evaluation for \(\mathscr B^\sharp\).
Composition with \(p\) is Borel and remains injective; Lusin--Souslin
therefore makes the image a proper Borel lamination.

This set-theoretic injectivity does **not** say that one common open
neighborhood supports a univalent branch, so no coefficient-one
equality is inferred.  Instead

\[
 \mathscr B^\sharp\cap p^{-1}(\mathscr E)
 \subset p^*\mathscr E .
\]

Monotonicity and Lemma 2.1 with \(d=2\) give (2.6).  Under
Borel width-envelope pruning, no individual dyadic-span or
outer-buffer predicate is required to be Borel. \(\square\)

The additive envelope charge in (2.9) is universal and is paid once
per stationary step.  It is independent of the rotation denominator,
the number of arc packets, and the Wave width.

For later reference, the target typing in the stationary application
is as follows.  Let \(\beta\in\mathscr B^\sharp\) lie over a source
leaf \(\gamma\in S\), where \(S\uparrow I\).  The singleton
\(\{\gamma\}\) is a KKL Wave over \(I\), and unbreakability makes
\(\{p(\beta)\}\subset F_*\{\gamma\}^{\rm nbr}\).  KKL Proposition
A.14 therefore makes \(\{p(\beta)\}\) a Wave over \(F_*I\).
Its singleton base is contained in the target ideal-boundary
component \(C\) containing \(F_*I\), so \(p(\beta)\) is subordinate
to \(C\).  KKL 1853--1856 permits \(C\) itself as a multi-interval.
Since every target leaf is subordinate to the same \(C\), the proper
Borel target lamination is a KKL Wave by KKL 1874.  Proposition A.14
also gives the leafwise statement

\[
p(\mathscr B^\sharp)\uparrow F_*I.
\tag{2.11}
\]

This does **not** assert that the aggregate crest of the target family
contains \(F_*I\).

## 3. Exact measurable interface

KL06 `wad.tex` 142--143 defines a proper lamination as a Borel point
set in the surface explicitly realized as a union of disjoint proper
paths.  That definition does not itself make the quotient *space of
leaves* standard Borel, make the same-leaf equivalence relation Borel,
or make an outermost transverse buffer a Borel leaf set.  A countable
inverse-branch atlas can analyze already-coded leaves; it cannot create
the missing leaf code.  Accordingly, the earlier unconditional
Lusin--Novikov shortcut is rejected.

### Theorem 3.1 (standard-Borel ordered-Wave realization)

Every stationary proof-used KKL Wave admits a finite disjoint
decomposition into standard-Borel ordered arc packets.  On their
finite tagged union there are:

1. a standard-Borel leaf space \(L_S\);
2. a jointly Borel evaluation
   \(e_S:L_S\times(0,1)\to V\), with each fiber a proper embedded
   path and distinct leaf images disjoint;
3. Borel endpoint maps into the metrizable prime-end boundary; and
4. on each arc packet, a Borel numeric order agreeing, up to reversal,
   with planar nesting and annular deck order.

This realization is closed under every operation used below:

1. finite arc, endpoint, direction, short/nonshort, and
   central/over/away partitions;
2. both KKL immersion-marking filters;
3. full proper-component restriction;
4. finite-cover pushforward on an injective retained family;
5. the Borel width-envelope replacement of the DL discard; and
6. full terminal-output saturation through the finite Wave horizon.

#### Proof

This is `STANDARD_BOREL_ORDERED_WAVE_REALIZATION`, proved in
`kkl_stationary_n1_borel_ordered_wave_realization_20260726.md`.
The construction does not assume a Borel quotient of the original
lamination.  Within each native arc class it orders leaves by strict
nesting of their preferred-side domains and uses a finite full-support
area measure \(\mu\) to define the injective coordinate

\[
 t(\gamma)=\mu(O_\gamma).
\tag{3.1}
\]

Open sublevel saturations make \(t\) Borel on the original Borel
geometric support.  Arsenin--Kunugui then makes the realized set of
coordinates Borel, and a Borel field of compactified arcs supplies the
joint evaluation and endpoint maps.

For restriction, a countable inverse-branch atlas, rational seed
times, compactly contained chart exhaustions, and explicit two-ended
properness tests produce a Borel countable occurrence relation.
Lusin--Novikov removes duplicate continuation codes and supplies the
unique untagged successor on an already unbreakable family.
Lusin--Souslin turns every injectively evaluated Borel leaf set into a
Borel geometric union.

No claim is made that DL's informal outermost deletion is an initial
or terminal interval in every arc chart.  Instead,
`BOREL_WIDTH_ENVELOPE_PRUNING`, proved in
`kkl_stationary_n1_borel_width_envelope_20260726.md`, replaces the
entire proof-internal discard \(D_{\rm DL}\) by one Borel
super-discard \(E_{\rm DL}\) with

\[
 D_{\rm DL}\subset E_{\rm DL},
 \qquad
 \mathcal W(E_{\rm DL})
 \leq\mathcal W(D_{\rm DL})+1.
\tag{3.2}
\]

The retained family is a Borel subset of the actual DL injective
family.  All subsequent injectivity, pullback, direction, and
unbreakability statements are hereditary under this further pruning.
Full finite-horizon saturation is the inverse image of a Borel
terminal leaf set under the composed Borel successor maps. \(\square\)

### Corollary 3.2 (unconditional Borel occurrence calculus)

Every family and occurrence relation constructed in Sections 4--10
is Borel.  In particular:

1. the maximal proper-component relation surviving both KKL filters
   is Borel with countable source sections;
2. the unique untagged successor on every proof-used unbreakable
   family is Borel;
3. every finite direction and central/over/away predicate is Borel;
4. the metric-envelope retained/discarded predicate is Borel; and
5. every full saturation \(\Phi_h^{-1}(E)\) of a Borel terminal leaf
   set is a proper Borel sublamination.

No transverse width measure, Borel predicate for an individual DL
span class, or chartwise order-convexity of the DL discard is used.

## 4. Leafwise direction, restriction, and the critical estimate

### Definition 4.0 (leafwise direction)

For a KKL Wave \(S\) and a connected inner-boundary multi-interval
\(I\), write

\[
 S\uparrow I
\]

if the crest of the singleton Wave \(\{\gamma\}\) contains \(I\) for
every \(\gamma\in S\).  This is deliberately weaker than saying that
the crest computed from the *aggregate* ends of \(S\) contains \(I\).
The latter implication can fail when different leaves have different
end intervals and is never used below.

In DL terminology, \(S\uparrow I\) says leaf by leaf that the bounded
boundary-side component cut off by the path contains \(I\) on its
prime-end boundary.  Thus it is exactly DL's phrase “goes above
\(I\)” at `Feigen.tex` 2813.

### Lemma 4.1 (leafwise KKL-to-DL restriction)

Let \(S=S^{\rm nbr}\) be a KKL Wave in \(V\) and assume
\(S\uparrow I\) for one connected multi-interval \(I\).  Put
\(J=\iota^*I\), and let \(B_I(S)\) be the family of all proper
components \(\beta\) of \(\iota^{-1}(\gamma)\), \(\gamma\in S\), which

1. survive both filters at KKL 2096--2097; and
2. are individually DL-directed above \(J\).

Then:

1. \(J\) is a connected interval on the inner boundary of
   \(V'\);
2. every \(\gamma\in S\) has at least one occurrence in \(B_I(S)\);
3. \(B_I(S)\) is one DL annular Wave above the fixed interval \(J\);
4. \(B_I(S)\) is a lamination; and
5. \(\mathcal W(S)\leq\mathcal W(B_I(S))\).

#### Proof

The conformal disks \(\mathcal U,\mathcal U'\) and the full connected
trees \(\mathcal T,\mathcal T'=f^{-1}(\mathcal T)\) (KKL 517 and
524--525) give annular
complements \(V,V'\).  Their prime-end compactifications are closed
annuli, and \(f:V'\to V\) is the unbranched degree-two cover obtained
by removing the branch value in \(\mathcal T\).  KKL Proposition 1254
describes \(\iota^*I\) as the union of \(\iota^{-1}(I)\) with the
prime-end boundaries of the attached components meeting \(I\), and
proves that this union is one interval.  This proves clause 1 and
verifies the annular input required by DL.

Fix \(\gamma\in S\).  The singleton \(\{\gamma\}\) is a KKL Wave over
\(I\), and it is unbreakable.  Rerun the classification at KKL
1429--1478 with this fixed connected subinterval \(I\) of the
singleton crest.  Inspection of 1429--1430 shows that the argument
uses only (a) \(I\) lies in the crest and (b) \(F_*\) is end-proper on
\(I\); it never uses minimality of the full crest.  The unbreakable
case at 1477 therefore says that the complete filtered restriction
\(B_\gamma\) is a nonempty KKL Wave over
\(J=\iota^*I\).
This aggregate statement does not say that every leaf of
\(B_\gamma\) is DL-directed above \(J\); opposite-side lifts are
possible.  We need only the following elementary implication:

> **Marked-circle directionalization.** If a KKL Wave \(L\)
> has aggregate crest containing a connected multi-interval \(J\), then at
> least one leaf of \(L\) is individually DL-directed above \(J\).

Let \(E_-,E_+\) be the aggregate ends.  The two endpoint intervals of
each leaf \(\beta\) lie in \(E_-,E_+\), respectively, and hence avoid
\(J\).  Its boundary-side base follows one of the two cyclic routes
between those endpoint intervals.  Since \(J\) is connected and
avoids both endpoint intervals, that route either traverses all of
\(J\), in which case \(\beta\) is DL-directed above \(J\), or avoids
\(J\) completely.  There is no partial-overlap case.

Suppose every leaf were in the second case.  Choose one marking
interval \(Q\subset J\).  The singleton base of every leaf is then
disjoint from \(Q\).  Because that base is an open multi-interval made
from whole marking intervals and marking endpoints, it cannot contain
either endpoint of \(\overline Q\): openness there would force it to
contain an adjacent open part, hence the whole marking interval \(Q\).
Therefore every singleton base is contained in the proper connected
multi-interval

\[
 \partial_{\rm C}\mathcal T'\setminus\overline Q.
\]

Every leaf is consequently subordinate to that same multi-interval,
in the exact sense of KKL 1867--1868.  By the defining minimality of the
aggregate base at KKL 1874--1875,
the aggregate base is contained in this proper multi-interval.  This
contradicts \(Q\subset J\subset\operatorname{crest}(L)\).  The asserted
leaf therefore exists.  Notice that this proof does not require
finiteness.

For completeness, the singleton packet is finite for an independent
reason.  Every retained occurrence in \(B_\gamma\) maps by the
degree-two cover \(f\) to the unique actual output path
\(\delta=F_*\gamma\).  Evaluation at one interior point of \(\delta\)
injects its distinct lifts into the two-point covering fiber, so
\(|B_\gamma|\le2\).  If both lifts occur, path-lifting uniqueness makes
them the deck-involution pair.  Apply marked-circle directionalization
to \(L=B_\gamma\).  At least one
retained occurrence of
\(\gamma\) belongs to \(B_I(S)\), proving clause 2.  Clause 3 is true
by the definition of \(B_I(S)\).  This selection is by a leaf
predicate, not by choosing one occurrence.

The endpoint-route proof, the degree-two path-lifting argument, and
their adversarial audit are recorded separately in
`kkl_stationary_n1_degree_two_directionalization_audit_20260726.md`.

Two selected retained components cannot cross in \(V'\).  Components coming
from one \(\gamma\) are distinct components of its inverse image.
If components coming from distinct leaves met at an interior point,
their images under the local homeomorphism \(\iota\) would give an
intersection of those two leaves in \(V\).  Both alternatives
contradict the lamination property.  Hence \(B_I(S)\) is a lamination,
proving clause 4.

Finally every source leaf has a retained occurrence in this one
lamination.  KKL domination at 2086--2090 gives

\[
 \mathcal W(S)\leq\mathcal W(B_I(S)).
\]

This proves clause 5.  Multiple retained occurrences are kept; no
selector or untagged quotient appears. \(\square\)

### Lemma 4.2 (leafwise critical bound)

There is an absolute \(c_{\rm crit}<\infty\) such that every
one-step-unbreakable proper Wave \(S\) satisfying
\(S\uparrow BL_0\) obeys

\[
  \mathcal W(S)\leq c_{\rm crit}.
  \tag{4.1}
\]

#### Proof

Let \(B=B_{BL_0}(S)\).  Lemma 4.1 gives
\(\mathcal W(S)\leq\mathcal W(B)\).  Apply Lemma 2.3:

\[
 B=B^\sharp\mathbin{\dot\cup}B^{\rm bad},
 \qquad
 \mathcal W(B^{\rm bad})\leq c_{\rm DL},
\]

where \(B^{\rm bad}=E_{\rm DL}\) is the metric-envelope discard and
\(f\) is injective on \(B^\sharp\).  For every
\(\beta\in B^\sharp\), let \(\gamma\) be its source leaf.  Apply KKL
Proposition A.14 (2164--2168) to the singleton source and singleton
output \(f(\beta)\).  It is correctly typed because
\(\gamma\) is unbreakable and \(F_*\) acts combinatorially on
\(BL_0\).  The conclusion is

\[
 \{f(\beta)\}\uparrow F_*BL_0
 =\partial_{\rm C}\mathcal T.
\]

No proper path can go above its entire ideal-boundary component: in
DL's definition both of its ends must lie outside the interval, and
the complement of the entire component is empty.  Thus
\(B^\sharp=\varnothing\).  Consequently

\[
 \mathcal W(S)
 \leq\mathcal W(B)
 =\mathcal W(B^{\rm bad})
 \leq c_{\rm DL}.
\]

Take \(c_{\rm crit}=c_{\rm DL}\). \(\square\)

This proves the restricted form of KKL Proposition 1514 needed below
without the false broad wording of KKL Lemma A.13.

### Lemma 4.3 (leafwise precritical packet)

Let \(S=S^{2\text{-nbr}}\) be a Wave with
\(S\uparrow BL_{q-1}=BL_{-1}\).  Then

\[
 \mathcal W(S)\leq c_{\rm pre}:=3c_{\rm DL}.
 \tag{4.2}
\]

#### Proof

Let \(B=B_{BL_{q-1}}(S)\), and apply Lemma 2.3:

\[
 B=B^\sharp\mathbin{\dot\cup}B^{\rm bad},
 \qquad
 \mathcal W(B^{\rm bad})\leq c_{\rm DL}.
\]

Here again \(B^{\rm bad}\) is the metric-envelope discard.  Put
\(R=f(B^\sharp)\).  The stationary target-typing rule following
Lemma 2.3 makes \(R\) a proper Borel KKL Wave and gives the leafwise
direction \(R\uparrow BL_0\).  Since \(S\) is two-step unbreakable,
every leaf of \(R\) is one-step unbreakable.
Lemma 4.2 therefore gives

\[
 \mathcal W(R)\leq c_{\rm crit}=c_{\rm DL}.
\]

Set \(B_R=B^\sharp\cap f^{-1}(R)=B^\sharp\).  Lemma 2.1, monotonicity,
and the Parallel Law give

\[
\begin{aligned}
 \mathcal W(S)
 &\leq\mathcal W(B)\\
 &\leq\mathcal W(B^{\rm bad})+\mathcal W(B^\sharp)\\
 &\leq c_{\rm DL}+\mathcal W(f^*R)\\
 &=c_{\rm DL}+2\mathcal W(R)\\
 &\leq3c_{\rm DL}.
\end{aligned}
\]

No open univalent neighborhood of \(B^\sharp\) and no
coefficient-one conformal-invariance claim is used. \(\square\)

## 5. The leafwise directed adjacent-limb theorem

The next lemma is the only new planar-combinatorial input.

### Lemma 5.1 (ordered limb blocks)

The connected multi-intervals

\[
 BL_0,BL_1,\ldots,BL_{q-1}
\]

occur as noninterleaving blocks in the prime-end circle of
\(\mathcal T\), in the cyclic order of the limbs

\[
 \mathcal L_0,\mathcal L_1,\ldots,\mathcal L_{q-1}
\]

around \(\alpha_F\).

#### Proof

Let \(G_j\) be the actual lifted limb subtree used in KKL's proof of
the combinatorial size bound.  KKL 861 says that every marked interval
in \(BL_j\) is an actual side either of a vertex of \(G_j\) different
from \(\alpha_F\), or of an edge of \(G_j\).  For \(j\ne k\),

\[
 (G_j\setminus\{\alpha_F\})
 \cap
 (G_k\setminus\{\alpha_F\})
 =\varnothing .
\tag{5.1a}
\]

An open marked side cannot simultaneously be a side of two objects in
these disjoint subtrees.  Thus distinct \(BL_j\)'s have disjoint open
marked interiors (their closures may share marked endpoints).  KKL
838 says each \(BL_j\) is a connected multi-interval.  Two connected
open blocks with disjoint interiors on a circle cannot interleave.

To identify their order, take the first actual edge germ from
\(\alpha_F\) into each \(G_j\).  These germs inherit the ribbon order
of the oriented dynamical plane, and KKL 501 labels the limbs in
exactly that counterclockwise order.  The two sides of a small regular
neighborhood of the \(j\)-germ lie in \(BL_j\).  Since each \(BL_j\)
is connected and different blocks cannot interleave, enlarging the
germ to the full \(G_j\) cannot change the cyclic position of its
prime-end block.

This also treats the non-locally-connected case.  KKL 542--543
construct the combinatorial vertices and edges and then lift those
actual objects and their sides to the dynamical carrier; the argument
above uses only the lifted ribbon germs, KKL 861's side inventory, and
KKL 838's connectedness.  It does not assume an unstated monotone
projection from the filled Julia set to its model.
\(\square\)

### Lemma 5.2 (two leafwise directions)

Let \(S\) be a Wave ending at \(BL_0\), and suppose every leaf of
\(S\) is nonshort.  If \(q>2\), there is a disjoint partition

\[
 S=S^+\dot\cup S^-
 \tag{5.1}
\]

such that

\[
 S^+\uparrow BL_1,\qquad
 S^-\uparrow BL_{-1}.
 \tag{5.2}
\]

If \(q=2\), the whole family satisfies

\[
 S\uparrow BL_1=BL_{-1}.
 \tag{5.3}
\]

#### Proof

Consider one leaf \(\gamma\).  Its singleton Wave has a connected
boundary-side base \(B_\gamma\), possibly the whole inner boundary
component.  One singleton end interval \(E_\gamma\) lies in \(BL_0\).

Because \(E_\gamma\subset BL_0\), the individual crest cannot contain
all of \(BL_0\).  Since the leaf is nonshort, its crest contains
\(BL_j\) for some \(j\ne0\).

Follow within the connected base from the selected \(BL_0\)-end
toward that \(BL_j\)-block.  By Lemma 5.1, the route leaves \(BL_0\)
in exactly one of the two cyclic directions.  In the positive
direction it meets the complete block \(BL_1\) before a later limb
block; in the negative direction it meets \(BL_{-1}\) first.  Because
the complete \(BL_j\)-block lies in the singleton crest, the other end
cannot intervene before that block.  Hence the first adjacent block
is in the base interior rather than in either singleton end.  Thus

\[
 BL_1\subset\operatorname{crest}(\gamma)
 \quad\text{or}\quad
 BL_{-1}\subset\operatorname{crest}(\gamma).
 \tag{5.4}
\]

A winding base may satisfy both alternatives.

Define

\[
\begin{aligned}
 S^+
 &:=
 \{\gamma\in S:
 BL_1\subset\operatorname{crest}(\gamma)\},\\
 S^-
 &:=
 \{\gamma\in S:
 BL_1\not\subset\operatorname{crest}(\gamma)\}.
\end{aligned}
\]

Equation (5.4) makes this an exhaustive disjoint partition and makes
every \(S^-\)-leaf individually directed above \(BL_{-1}\).  The
predicate is a discrete endpoint/homotopy predicate and is Borel by
Corollary 3.2.  Each part is a sublamination
subordinate to the original
base, so it is a KKL Wave.  We do **not** infer that its aggregate
family crest contains the indicated block.  This proves
(5.1)--(5.2).

For \(q=2\), the two adjacent noncentral limb blocks coincide, so
(5.4) gives (5.3). \(\square\)

### Lemma 5.3 (the short part is leafwise)

If \(A^{\rm sh}\) is KKL's unique maximal short subwave, then it
contains exactly the individually short leaves of \(A\).  Consequently
every leaf of

\[
 A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}
 \tag{5.5}
\]

is nonshort.

#### Proof

The individually short leaves form a sublamination of \(A\).  It is
subordinate to the base of \(A\), and by definition none of its leaves
crests over a limb; hence it is a short subwave.  Conversely, every
leaf of a short subwave is individually short.  Maximality and
uniqueness therefore identify \(A^{\rm sh}\) with this leafwise
family. \(\square\)

Combining Lemmas 4.3, 5.2, and 5.3 gives, for \(q>2\),

\[
 \mathcal W(S_0^-)\leq c_{\rm pre},
 \tag{5.6}
\]

while \(S_0^+\uparrow BL_1\).  For \(q=2\),
Lemma 4.3 bounds all of \(S_0\).

## 6. Uniform central/noncentral output decomposition

### Lemma 6.1 (finite localization of a central-ending Wave)

If \(S\) is a proper Wave ending at \(BL_0\), then \(S\) is the
disjoint union of at most

\[
  \ell(BL_0)\leq6b
  \tag{6.1}
\]

localized subwaves.

#### Proof

List the marked intervals contained in \(BL_0\) in cyclic order.  For
each leaf choose the first interval in this fixed list which contains
one of its endpoints.  The corresponding leaf classes are disjoint,
Borel, and exhaustive.  Every class ends at its selected single marked
interval and is therefore localized.  There are at most
\(\ell(BL_0)\) classes. \(\square\)

### Lemma 6.2 (one-step bounded controllability)

There is an integer

\[
 \eta_b\leq 6b+4b(2b+1)
 \tag{6.2}
\]

such that the following holds.  Let \(S=S^{\rm nbr}\) be a Wave ending
at \(BL_0\), and let

\[
 R\subset F_*S
\]

be a Wave obtained from retained occurrences.  Then \(R\) is the union
of:

1. one Wave whose leaves are individually directed above \(BL_0\);
   and
2. at most \(\eta_b\) localized Waves.

The modules can be allocated as occurrence-disjoint
sublaminations.

#### Proof

Lemma 6.1 makes \(S=S^{\rm nbr}\) a \(6b\)-controllable Wave: it is a
union of at most \(6b\) localized Waves, with an empty over-\(BL_0\)
module if necessary.  Apply the \(n=1\) case of KKL Lemma 1399
(`lem:pushing controllable`) to \(S\) and the actual Wave
\(R\subset F_*S\).  Its proof at 1403--1411 uses only proper
translation, endpoint localization in \(BL_{[-b,b]}\), and the limb
length bound; it does not invoke the invalid broad Wave pushforward
lemma.  With \(k=6b\), the printed count becomes

\[
 k+4b(2b+1)=6b+4b(2b+1).
\]

The over-class in that proof is defined leaf by leaf, which is the
first module above.  All predicates are finite
endpoint/subordination predicates and are Borel by Corollary 3.2.
Order the finitely many modules and assign a leaf to the first
eligible module; this gives occurrence-disjoint modules without
increasing their number.
\(\square\)

### Lemma 6.3 (controlled trichotomy relative to \(BL_0\))

Suppose \(R\) is a Wave which:

1. is the disjoint union of one module directed leafwise above
   \(BL_0\) and at most \(\eta_b\) localized modules;
2. is one-step unbreakable; and
3. satisfies \(R\uparrow BL_k\) for one noncritical limb,
   \(k\ne0\).

Then there is a disjoint partition

\[
 R=C\dot\cup Y\dot\cup
 Z_1\dot\cup\cdots\dot\cup Z_s,
 \qquad s\leq\eta_b,
 \tag{6.3}
\]

where:

- \(C\) is a Wave ending at \(BL_0\);
- \(Y\uparrow BL_0\); and
- every \(Z_r\) is localized and subordinate to
  \(\partial_{\rm C}\mathcal T\setminus BL_0\).

Moreover,

\[
 \mathcal W(R\setminus C)\leq e_b
 \tag{6.4}
\]

for a constant \(e_b<\infty\) independent of \(q\) and of \(R\).
The central family still satisfies \(C\uparrow BL_k\).

#### Proof

Within each occurrence-disjoint module, assign leaves in this order:

1. to \(C\), if an endpoint lies in \(BL_0\);
2. to \(Y\), if the leaf crests over \(BL_0\);
3. otherwise to the residual \(Z_r\).

For one leaf, its singleton base and \(BL_0\) are connected unions of
whole marked intervals on a circle.  If neither singleton end lies in
\(BL_0\), then the base either avoids \(BL_0\) or contains all of
\(BL_0\): a proper nonempty intersection would force one end interval
of the base to lie in \(BL_0\).  The second alternative is exactly
the leafwise-over class already assigned to \(Y\).  Hence every
residual localized class is subordinate to
\(\partial_{\rm C}\mathcal T\setminus BL_0\).  The union of all
central classes is a sublamination ending at \(BL_0\), hence a Wave.
The finite leaf predicates are Borel.

Every subfamily inherits one-step unbreakability.  Lemma 4.2 gives

\[
 \mathcal W(Y)\leq c_{\rm crit}.
 \tag{6.5}
\]

Every leaf of \(R\), and hence of each \(Z_r\), is directed above the
noncritical limb \(BL_k\).  Therefore

\[
 Z_r^{\rm sh}=\varnothing.
\]

KKL Proposition 1524, whose proof is the Shift lemma and does not use
the broad Wave extraction statement, gives one absolute
\(c_{\rm away}\) such that

\[
 \mathcal W(Z_r)
 =
 \mathcal W(Z_r^{\rm nbr})
 \leq c_{\rm away}.
 \tag{6.6}
\]

The Parallel Law now gives

\[
\begin{aligned}
 \mathcal W(R\setminus C)
 &\leq
 \mathcal W(Y)+\sum_{r=1}^s\mathcal W(Z_r)\\
 &\leq c_{\rm crit}+\eta_b c_{\rm away}.
\end{aligned}
\]

Take

\[
 e_b:=c_{\rm crit}+\eta_b c_{\rm away}.
 \tag{6.7}
\]

Since \(C\subset R\), it retains the leafwise direction \(BL_k\).
\(\square\)

### Remark 6.4 (when the next crest is critical)

If \(R\uparrow BL_0\), do not apply Lemma 6.3.  Lemma 4.2
directly gives

\[
 \mathcal W(R)\leq c_{\rm crit}.
 \tag{6.8}
\]

The central continuation may then be taken empty, and the whole source
packet is charged as a bounded exceptional family.

## 7. One-packet relative central continuation

### Proposition 7.1 (one directed packet, one stationary step)

Let \(0\leq n<N-1\), and let \(S=S^{(N-n)\text{-nbr}}\) be a proper
Wave which:

1. ends at \(BL_0\); and
2. satisfies \(S\uparrow BL_k\) for one noncritical limb \(BL_k\).

Then there is a subwave \(P_C\subset S\) and a Wave \(C\)
ending at \(BL_0\) such that

\[
  \Phi_1(P_C)=C
  \tag{7.1}
\]

and

\[
  \mathcal W(S\setminus P_C)\leq c_b^{\rm step}
  \tag{7.2}
\]

for one \(b\)-dependent constant independent of \(q,k,n,S\).  Either
\(C=\varnothing\), or \(C\uparrow BL_{k+1}\), with indices read modulo
\(q\), and

\[
 C=C^{(N-n-1)\text{-nbr}}.
 \tag{7.3}
\]

#### Proof

Lemma 4.1 gives the actual retained occurrence Wave

\[
 B=B_{BL_k}(S)
\]

above \(\iota^*BL_k\), with

\[
 \mathcal W(S)\leq\mathcal W(B).
\]

Apply Lemma 2.3 and write

\[
 B^\sharp\subset B,\qquad
 R=f(B^\sharp)\subset F_*S.
\]

Define

\[
 S^\sharp
 :=
 \{\alpha\in S:
 \iota^*\alpha\text{ contains a leaf of }B^\sharp\}.
 \tag{7.4}
\]

If \(\alpha\notin S^\sharp\), every **directed occurrence in \(B\)**
lies in \(B\setminus B^\sharp\), and Lemma 4.1 guarantees that at
least one such occurrence exists.  KKL domination and (2.5) give

\[
 \mathcal W(S\setminus S^\sharp)
 \leq
 \mathcal W(B\setminus B^\sharp)
 \leq c_{\rm DL}.
 \tag{7.5}
\]

The stationary target-typing rule following Lemma 2.3 makes \(R\) a
proper Borel KKL Wave and gives

\[
 R\uparrow F_*BL_k=BL_{k+1}.
 \tag{7.6}
\]

It inherits \((N-n-1)\)-unbreakability.

If \(k+1=0\pmod q\), Lemma 4.2 gives

\[
 \mathcal W(R)\leq c_{\rm crit}.
\]

Every leaf of \(S^\sharp\) has a retained occurrence in
\(B^\sharp\), so domination, inclusion in the full lift of \(R\), and
Lemma 2.1 give

\[
 \mathcal W(S^\sharp)
 \leq\mathcal W(B^\sharp)
 \leq\mathcal W(f^*R)
 =2\mathcal W(R)
 \leq2c_{\rm crit}.
\]

Set \(P_C=C=\varnothing\).  The Parallel Law and (7.5) yield

\[
 \mathcal W(S)
 \leq c_{\rm DL}+2c_{\rm crit}.
 \tag{7.7}
\]

Now suppose \(k+1\ne0\pmod q\).  Lemma 6.1 and the one-step
controllability Lemma 6.2 apply to \(S\) and \(R\).  Lemma 6.3 gives

\[
 R=C\dot\cup E,\qquad
 E=R\setminus C,\qquad
 \mathcal W(E)\leq e_b,
 \tag{7.8}
\]

where \(C\) ends at \(BL_0\) and \(C\uparrow BL_{k+1}\).

Define the full untagged central saturation

\[
 P_C
 :=
 \{\alpha\in S:\Phi_1(\alpha)\in C\}.
 \tag{7.9}
\]

Corollary 3.2 makes this full saturation Borel.  It is not a
one-occurrence selector.

For every \(\alpha\in S^\sharp\setminus P_C\), its occurrence in
\(B^\sharp\) belongs to

\[
 B_E:=B^\sharp\cap f^{-1}(E).
\]

Domination, inclusion \(B_E\subset f^*E\), and Lemma 2.1 give

\[
 \mathcal W(S^\sharp\setminus P_C)
 \leq\mathcal W(B_E)
 \leq2\mathcal W(E)
 \leq2e_b.
 \tag{7.10}
\]

Equations (7.5), (7.10), and the Parallel Law prove

\[
 \mathcal W(S\setminus P_C)
 \leq c_{\rm DL}+2e_b.
 \tag{7.11}
\]

Every leaf of \(C\subset R\) has a source occurrence in
\(B^\sharp\), hence a source leaf in \(P_C\).  Conversely the
definition of \(P_C\) maps it into \(C\).  Therefore (7.1) is exact.
Residual unbreakability and leafwise direction are inherited from \(R\),
giving (7.3).

Take

\[
 c_b^{\rm step}
 :=
 c_{\rm DL}+2\max\{c_{\rm crit},e_b\}.
 \tag{7.12}
\]

This covers both cases. \(\square\)

## 8. The initial directed step

### Proposition 8.1 (initial extraction without packet conflict)

Let

\[
 S_0=A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}.
\]

There is a subwave \(P_{C,0}\subset S_0\) and a Wave \(C_1\)
ending at \(BL_0\) such that

\[
 \Phi_1(P_{C,0})=C_1,
 \qquad
 \mathcal W(S_0\setminus P_{C,0})
 \leq c_b^{\rm init},
 \tag{8.1}
\]

and either \(C_1=\varnothing\) or \(C_1\uparrow BL_2\).

#### Proof

Lemma 5.3 makes every leaf of \(S_0\) nonshort.

If \(q=2\), Lemma 5.2 gives \(S_0\uparrow BL_1=BL_{q-1}\).
Lemma 4.3 bounds all of \(S_0\).  Take
\(P_{C,0}=C_1=\varnothing\).

Assume \(q>2\).  Use

\[
 S_0=S_0^+\dot\cup S_0^-
\]

from Lemma 5.2.  Since \(S_0\) is \(N\)-unbreakable and \(N\geq4\),
Lemma 4.3 gives

\[
 \mathcal W(S_0^-)\leq c_{\rm pre}.
 \tag{8.2}
\]

Apply Proposition 7.1 to the directed packet \(S_0^+\) with
\(k=1\).  If \(2=0\pmod q\), which only occurs for \(q=2\) already
handled, that proposition takes the bounded case.  Otherwise it gives
a central packet \(P^+_C\) mapping exactly to a Wave
\(C_1\uparrow BL_2\), and

\[
 \mathcal W(S_0^+\setminus P^+_C)
 \leq c_b^{\rm step}.
\]

Define the saturation across all of \(S_0\),

\[
 P_{C,0}:=\Phi_1^{-1}(C_1)\cap S_0.
\]

It contains \(P^+_C\).  Hence

\[
\begin{aligned}
 S_0\setminus P_{C,0}
 &\subset
 S_0^-\cup(S_0^+\setminus P^+_C),\\
 \mathcal W(S_0\setminus P_{C,0})
 &\leq c_{\rm pre}+c_b^{\rm step}.
\end{aligned}
\]

Take

\[
 c_b^{\rm init}:=c_{\rm pre}+c_b^{\rm step}.
\]

Surjectivity onto \(C_1\) comes from \(P^+_C\), while the definition
gives the reverse inclusion. \(\square\)

The two packets are never pushed and unioned.  The negative packet is
charged before the positive directed packet is continued.  This is
why the many-scale cyclic-cover conflict in Section 11 does not apply.

## 9. Full stationary induction

We now construct the sequence in Theorem N1.  The construction is
explicit; no inclusion-maximal extension is taken.

Set

\[
 A_0:=A^{N\text{-nbr}}\setminus A^{\rm sh},
 \qquad S_0:=A_0.
 \tag{9.1}
\]

Apply Proposition 8.1 and define

\[
 A_1:=P_{C,0},
 \qquad
 S_1:=\Phi_1(A_1)=C_1.
 \tag{9.2}
\]

Suppose \(1\leq n<N-1\) and \(A_n,S_n\) have been constructed with

\[
 S_n=\Phi_n(A_n),\qquad
 S_n=S_n^{(N-n)\text{-nbr}},
 \tag{9.3}
\]

and either \(S_n=\varnothing\) or

\[
 S_n\uparrow BL_{n+1\pmod q},
 \qquad n+1\not\equiv0\pmod q.
 \tag{9.4}
\]

If \(S_n=\varnothing\), set \(A_{n+1}=S_{n+1}=\varnothing\).
Otherwise apply Proposition 7.1 to \(S_n\).  Let
\(P_{C,n}\subset S_n\) and \(C_{n+1}\) be its source packet and central
output, and define the full source saturation

\[
 A_{n+1}
 :=
 A_n\cap\Phi_n^{-1}(P_{C,n}).
 \tag{9.5}
\]

For \(\alpha\in A_n\), unbreakability gives

\[
 \Phi_{n+1}(\alpha)
 =
 \Phi_1(\Phi_n(\alpha)).
 \tag{9.6}
\]

Using (9.5), Proposition 7.1, and both inclusions separately,

\[
\begin{aligned}
 \Phi_{n+1}(A_{n+1})
 &=\Phi_1\!\left(\Phi_n(A_n)\cap P_{C,n}\right)\\
 &=\Phi_1(P_{C,n})\\
 &=C_{n+1}.
\end{aligned}
\tag{9.7}
\]

The first equality is legitimate because
\(P_{C,n}\subset\Phi_n(A_n)=S_n\), so the full saturation in (9.5)
maps *onto*, not merely into, \(P_{C,n}\).  Define

\[
 S_{n+1}:=C_{n+1}.
\tag{9.8}
\]

Every leaf of \(S_{n+1}\) has \(N-n-1\) unbreakable steps left.
If the new direction is \(BL_0\), Proposition 7.1 has already set
\(S_{n+1}=\varnothing\).  Otherwise it advances (9.4) by one.  This
proves the induction invariants without crossing a critical crest.

It remains to prove the source-relative loss.  At the initial step,
Proposition 8.1 gives

\[
 \mathcal W(A_0\setminus A_1)
 \leq c_b^{\rm init}.
\tag{9.9}
\]

For \(1\leq n<N-1\), put

\[
 D_n:=A_n\setminus A_{n+1}.
\]

Full saturation gives the exact implication

\[
 \Phi_n(D_n)\subset S_n\setminus P_{C,n}.
\tag{9.10}
\]

Apply the sequential relative transfer Lemma 2.2 and then
Proposition 7.1:

\[
\begin{aligned}
 \mathcal W(D_n)
 &\leq
 2^n\mathcal W(S_n\setminus P_{C,n})\\
 &\leq
 2^n c_b^{\rm step}\\
 &\leq
 2^{b+1}c_b^{\rm step},
\end{aligned}
\tag{9.11}
\]

because \(n\leq N-2=b+1\).  Therefore

\[
 C_b:=
 \max\left\{
 c_b^{\rm init},
 2^{b+1}c_b^{\rm step}
 \right\}
\tag{9.12}
\]

is independent of \(q,n,F,A\), and all analytic widths, and

\[
 \boxed{
 \mathcal W(A_n\setminus A_{n+1})\leq C_b
 \quad(0\leq n<N-1).
 }
\tag{9.13}
\]

This proves the analytic stationary continuation.  Theorem 3.1 and
Corollary 3.2 make (9.1), (9.2), and (9.5) Borel set operations and
make every \(A_n,S_n\) a proper Borel sublamination.
\(\square\)

### Horizon audit

The weakest input to Proposition 7.1 occurs at \(n=N-2\), where the
source has exactly two remaining unbreakable steps and the output has
one.  This is sufficient both for the precritical repair (Lemma 4.3)
and for the critical/away bounds on the output.  No step with
\(n=N-1\) is attempted.  Thus neither an undefined \(A_N\) nor the
later KKL line-1603 alignment assertion enters Gate N1.

## 10. Occurrence and charge ledger

The construction above can be audited before any width is measured.
At a one-step transition from \(S_n\), an occurrence record is

\[
 \omega=
 (\alpha,\beta,\delta,
   e_f^-,e_f^+,e_c^-,e_c^+,
   s,\pi,\varepsilon,\ell,\tau),
\tag{10.1}
\]

with the following meanings.

| field | exact content |
|---|---|
| \(\alpha\) | original source leaf in \(S_n\) |
| \(\beta\) | one proper component of \(\iota^{-1}(\alpha)\) |
| \(\delta=f(\beta)=\Phi_1(\alpha)\) | its unique untagged output |
| \(e_f^\pm\) | the two fine endpoint intervals in \(f^*\mathcal I\) |
| \(e_c^\pm\) | the containing coarse intervals in \(\iota^*\mathcal I\) |
| \(s\) | one of the at most two covering-lift sheets over \(\delta\) |
| \(\pi\) | the component/atlas-continuation code identifying the parent \(\alpha\) |
| \(\varepsilon\) | directed above \(J=\iota^*BL_k\), or opposite-side |
| \(\ell\) | Borel retained or `metric-envelope discard`; the latter may contain a proof-internal DL-retained leaf |
| \(\tau\) | central, over-critical, localized-away, or unused shadow |

The two KKL filters are imposed before \(\varepsilon\) is evaluated.
An occurrence rejected by either filter is not a KKL path and never
enters a domination family.  A surviving opposite-side occurrence is
recorded with \(\tau=\mathrm{shadow}\); it is not charged as lost
source mass because marked-circle directionalization supplies the
same parent leaf with at least one directed occurrence.  All directed
occurrences form \(B_I(S_n)\).

DL 2827--2841 first gives the set-theoretic partition

\[
 B_I(S_n)
 =
 B^\sharp_{\rm DL}\mathbin{\dot\cup}D_{\rm DL},
\tag{10.2}
\]

where the proof-internal discarded packets satisfy
\(\mathcal W(D_{\rm DL})\leq c_{\rm DL}^{\rm raw}\).  The Borel
width envelope produces

\[
 D_{\rm DL}\subset E_{\rm DL},
\qquad
\mathcal W(E_{\rm DL})\leq
c_{\rm DL}^{\rm raw}+1=c_{\rm DL}.
\tag{10.3}
\]

The actual proof partition is therefore

\[
B_I(S_n)
=
B^\sharp\mathbin{\dot\cup}B^{\rm bad},
\qquad
B^\sharp:=B_I(S_n)\setminus E_{\rm DL},
\quad
B^{\rm bad}:=E_{\rm DL}.
\tag{10.4}
\]

Every member of \(B^{\rm bad}\) receives the single Borel ledger
label `metric-envelope discard`.  It is forbidden to infer that every
such leaf has an original dyadic-span or outer-buffer label: the
envelope may deliberately delete additional leaves of
\(B^\sharp_{\rm DL}\).  What is retained from DL is precisely

\[
 \mathcal W(B^{\rm bad})\leq c_{\rm DL}.
\tag{10.5}
\]

The parent partition must be made from the **untagged output**, not
from the existence of one retained occurrence.  This distinction is
forced because a parent with no occurrence in \(B^\sharp\) can share a
central untagged output with another parent that does have a retained
occurrence.  Put

\[
 S^\sharp
 :=
 \{\alpha\in S_n:
   \alpha\text{ has an occurrence in }B^\sharp\},
\qquad
 P_C:=\Phi_1^{-1}(C)\cap S_n .
\tag{10.6}
\]

There are then exactly three mutually exclusive and exhaustive source
classes:

\[
\begin{array}{ll}
\mathsf K:
 &P_C;\\[2mm]
\mathsf D_{\rm bad}:
 &(S_n\setminus P_C)\setminus S^\sharp;\\[2mm]
\mathsf D_E:
 &(S_n\setminus P_C)\cap S^\sharp.
\end{array}
\tag{10.7}
\]

For \(\mathsf D_{\rm bad}\), every parent has a directed occurrence by
Lemma 4.1 and none is retained; hence every such directed occurrence
lies in \(B^{\rm bad}\).  Domination gives the first charge

\[
 \mathcal W(\mathsf D_{\rm bad})
 \leq\mathcal W(B^{\rm bad})
 \leq c_{\rm DL}.
\tag{10.8}
\]

For \(\mathsf D_E\), choose any retained occurrence.  Its untagged
output is \(\Phi_1(\alpha)\notin C\), hence lies in
\(E=R\setminus C\).  Thus the occurrence belongs to

\[
 B_E:=B^\sharp\cap f^{-1}(E)\subset f^*E,
\]

and the degree-two full-lift identity gives the second charge

\[
 \mathcal W(\mathsf D_E)
 \leq\mathcal W(B_E)
 \leq2\mathcal W(E).
\tag{10.9}
\]

Finally, two distinct \(B^\sharp\)-occurrences of one parent would
have the same output by unbreakability, contradicting injectivity of
\(f|_{B^\sharp}\).  Thus a kept parent contributes at most one
retained occurrence.  Conversely, different parents cannot share one
retained output: injectivity would identify their occurrences, and
the local immersion would then identify the source leaves.  Hence no
occurrence multiplicity creates an additional width charge in
(10.8)--(10.9).  A parent
in \(S_n\setminus S^\sharp\) whose output is central belongs to
\(\mathsf K\), not to a discarded class; this is the overlap that the
output-first partition (10.7) removes.

This ledger is the occurrence-resolved form of RSC-1 and RSC-2.  The
earlier cyclic-cover no-go allows an unbounded number of incompatible
target packets.  Here every charged source leaf is represented inside
one fixed pulled interval \(J\), and the only sheet multiplicity is
the explicit factor two in (10.9).

## 11. Adversarial audit

### 11.1 Aggregate KKL crest versus DL direction

The proof never identifies these notions.  KKL line 1477 is applied
to one source singleton to obtain a finite aggregate restriction Wave.
Marked-circle directionalization then selects *all* occurrences which
are individually DL-above the fixed \(J\).  Opposite-side occurrences
remain in the ledger as shadows.  This is necessary: two lifts can
have an aggregate KKL crest containing \(J\) while one lift runs on
the other side.

### 11.2 Static cyclic-cover counterexample

The fixed-degree counterexample in
`kkl_stationary_relative_wave_cyclic_cover_no_go_20260726.md` builds
arbitrarily many incompatible target packets whose pulled crests are
not one fixed source interval.  It refutes any degree-only
common-*target*-crest estimate.  In the present proof:

1. the \(BL_{-1}\) direction is charged and discarded before pushing;
2. every retained positive occurrence is DL-above the same
   \(J=\iota^*BL_k\);
3. one DL pruning acts on that single ordered packet; and
4. every later output loss is lifted with the explicit degree-two
   factor.

Thus the hypothesis missing from the counterexample is proved rather
than assumed.

### 11.3 Repeated outputs and sheets

No coefficient-one output pullback is used.  Equations (2.6), (4.2),
(7.7), and (7.10) use

\[
 \mathcal W(B_E)\leq\mathcal W(f^*E)=2\mathcal W(E).
\]

DL injectivity prevents two retained occurrences from one source leaf,
or from two different source leaves, from collapsing onto one output.
All omitted nonretained occurrences remain explicitly tagged.

### 11.4 Critical wrap and small \(q\)

For \(q=2\), the entire initial nonshort family is precritical and is
bounded by Lemma 4.3.  For \(q>2\), a packet directed above
\(BL_{q-1}\) is passed once through the relative pruning, its output is
directed above \(BL_0\), and Lemma 4.2 bounds that output.  The
continuation is then set empty.  No packet is propagated *through*
the critical crest.

### 11.5 Away module typing

The residual \(Z_r\)'s are not called away merely because they are
noncentral.  Each is:

1. a subfamily of one localized controllability module;
2. subordinate to
   \(\partial_{\rm C}\mathcal T\setminus BL_0\) by the connected-base
   trichotomy;
3. one-step unbreakable; and
4. leafwise directed above a noncritical limb, hence has empty short
   part.

These are exactly the hypotheses of KKL 1524--1532.

### 11.6 Non-local connectivity

Lemma 5.1 uses actual lifted ribbon-tree sides and the KKL side
inventory at 861.  It does not assume local connectivity of the Julia
set or an unstated monotone model projection.  All boundary language
is prime-end language.

### 11.7 Measurability

The analytic theorem uses literal path families, for which KL06
defines extremal width and the Parallel Law.  Theorem 3.1 constructs
the standard-Borel leaf space before any Lusin--Novikov occurrence
enumeration is used.  The Borel envelope is applied once to the whole
DL discard; no individual outer-buffer predicate is assumed Borel.

### 11.8 Circularity and scope

The repaired critical bound is proved directly from DL pruning and
the identity \(F_*BL_0=\partial_{\rm C}\mathcal T\).  The stationary
proposition under repair, the broad KKL Wave lemma, KKL line 1576, the
line-1603 alignment claim, and any MLC/rigidity conclusion are absent
from the dependency chain.

## 12. Exact Gate N1 status

The integrated conclusions of this pass are:

| statement | status in this frozen candidate | reason |
|---|---|---|
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION_ANALYTIC` | proved | explicit directed cores and (9.13) |
| `DL_RELATIVE_DISCARD_FAMILY_BOUND` | analytic import from DL 2830--2841 | proof-internal discarded packets, never inferred from aggregate retention |
| `BOREL_WIDTH_ENVELOPE_PRUNING` | proved and independently audited | pointwise l.s.c. metric envelope and Parallel Law |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | proved in the companion construction, pending exact integrated-snapshot audit | ordered arc packets, Borel occurrences, metric-envelope pruning, saturation |
| critical and precritical directed bounds | proved | Lemmas 4.2--4.3 |
| stationary occurrence and charge partition | proved | Section 10, with metric-envelope labels |
| ordered limb blocks, including non-LC case | proved | actual lifted ribbon sides |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | candidate proved, not yet promoted | promotion requires the frozen backward audit of this file and the BOWR file |
| Gate N2 and all later gates | open | outside this pass |
| VAAPC-I, UPTCR, MLC | open | no implication asserted |

The actual-Wave provenance is audited separately in
`kkl_stationary_n1_actual_wave_provenance_audit_20260726.md`.  That
audit rules out a shortcut through the canonical ancestry of the
trichotomy witness: KKL 1168 chooses a nearly maximal member of the
full controllable-Wave class, and KKL 1629--1631 applies the
stationary proposition to a subwave of the resulting arbitrary input.
Canonical-WAD maximality is only a coordinate inequality and supplies
neither a leafwise realization nor a period-independent replacement
error.  The Borel realization above therefore treats the actual
arbitrary proper Waves used by the stationary argument.

Promotion is deliberately deferred until independent auditors read
the exact hashes backward from (9.13) through the target-Wave typing,
metric-envelope parent partition, Borel occurrence relation, and the
sole analytic DL discard import.  Failure of any one of those checks
keeps Gate N1 open at that exact clause.  Passing them closes Gate N1
only; it does not promote N2, terminal alignment, VAAPC-I, UPTCR,
rigidity, parameter fibers, or MLC.
