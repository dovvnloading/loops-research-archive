# Gate N1 — adversarial audit of the Borel ordered-Wave draft

## 0. Scope, frozen target, and verdict

This audit concerns only

```text
kkl_stationary_n1_borel_ordered_wave_realization_20260726.md
```

at SHA-256

```text
EA561F51C64C6A5DC2593B42565F7CB3F436A822D33FF2A17AFD747A940CD964.
```

It does not edit the draft, the main N1 proof, or the machine ledger.

### Verdict

The area-coordinate idea in Sections 3--4 contains a real and useful
descriptive-set argument.  Conditional on:

1. a Borel geometric support for one oriented arc packet; and
2. a strict total nesting theorem for the chosen side domains,

the sublevel proof does show that the leaf-constant area coordinate is
Borel, and Arsenin--Kunugui then gives a standard-Borel realized
coordinate set.

The draft nevertheless does **not** prove BOWR.  There are three
blocking defects.

1. The Borel status of each arc-class support \(Z_\alpha\) is asserted,
   not proved or imported.
2. The assertion that every compactified leaf is an arc with two
   distinct prime-end endpoints is false for allowed proper embedded
   paths whose two ideal endpoints coincide.
3. The filtered-immersion restriction sketch does not construct the
   maximal proper lift components used by KKL.  In particular, those
   components generally project to proper subintervals of the source
   path parameter, not to the whole path.

There are additional repairable gaps in the nesting proof, the
hyperspace projection argument, endpoint ordering, DL-buffer
measurability, and successor coding.

Accordingly:

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION = open.
```

## 15. Direct DL reconstruction and the Borel-envelope bypass

This section continues the frozen-snapshot audit in Section 14.  It
addresses only DL-Feigen lines 2821--2842 and does not alter the live
BOWR proof.

### 15.1 What the frozen DL proof actually constructs

Let \(f:A\to B\) be the degree-\(m\) annular cover and let
\(\mathscr S\) be the source Wave.  In the common universal cover \(X\),
the source and target deck groups are \(m\mathbb Z\) and \(\mathbb Z\).
DL denote the integer translates by \(\mathscr S_k\).

The proof makes two set-theoretic deletions.

1. Lines 2830--2839 partition
   \[
   \mathscr S
   =
   \mathscr S^0\sqcup\mathscr S^1\sqcup\cdots\sqcup\mathscr S^T,
   \qquad T=O(\log m).
   \]
   It proves \(\mathcal W(\mathscr S^t)=O(1)\) for every \(t>0\)
   and discards their union.
2. Line 2841 deletes an additional family \(D_0\) of
   “\(O(1)\) outermost curves” from \(\mathscr S^0\), leaving a family
   whose full integer deck orbit is pairwise disjoint.

Thus the proof-internal discard is
\[
D
:=
\left(\bigcup_{t=1}^T\mathscr S^t\right)\cup D_0,
\qquad
\mathscr S^{\rm new}=\mathscr S\setminus D.
\tag{15.1}
\]

The finite dyadic part of (15.1) is descriptively harmless once the
endpoint/deck-span predicates are coded.  The final family \(D_0\) is
not defined beyond the word “outermost.”  In particular, the source
does not specify a collision relation, a choice between the two leaves
of a colliding pair, or a cut value in any leaf order.

### 15.2 Why no exact chart-downset theorem follows from the displayed
DL conclusion

The displayed conclusions
\[
f|_{\mathscr S^{\rm new}}\ \text{injective},
\qquad
\mathcal W(\mathscr S^{\rm new})
\geq
\mathcal W(\mathscr S)-C
\tag{15.2}
\]
do not determine \(D\).  Even in one ordered rectangle on which \(f\)
is already injective, deleting a middle Borel band of width \(<C\)
still satisfies (15.2), while that deleted band is neither initial nor
terminal in the leaf order.  This is a logical countermodel to deriving
a downset property from (15.2); it is not a counterexample to DL's
intended word “outermost.”

For the intended geometry, fix one arc chart and one translated
packet.  Jordan separation does prove the following limited fact.  If
the translated obstacle is connected to one fixed side of the chart
and two chart leaves avoid it, then every chart leaf between them also
avoids it.  Hence the leaves meeting that one-sided obstacle form an
initial or terminal interval.  Taking a connected obstacle meeting both
sides gives a union of two such intervals.  This is the topological
content of DL-neutral lines 8757--8767 for a vertical rectangle.

What remains absent from DL-Feigen 2821--2842 is an identification of
the actual \(D_0\) with those obstacle-intersection families for
arbitrary restricted Waves.  Nor do those frozen lines prove that a
minimal collision deletion, which is a vertex-cover choice in the
deck-collision graph, is unique.  Accordingly, the exact
`DL_BUFFER_CHART_DOWNSET_LEMMA` cannot be reconstructed from the frozen
text without adding a new selection rule.

### 15.3 Strength of the analytic discard estimate

There are two distinct source statements:

1. the displayed relative estimate in (15.2); and
2. the stronger proof-internal assertion
   \[
   \mathcal W(D)\leq C_{\rm DL}(1+\log m).
   \tag{15.3}
   \]

The first does **not** imply the second.  The Parallel Law gives
\(\mathcal W(\mathscr S)\leq
\mathcal W(\mathscr S^{\rm new})+\mathcal W(D)\), which has the wrong
direction for deriving an upper bound on \(\mathcal W(D)\).

The frozen proof does, however, state the ingredients of (15.3):

* line 2827 says the construction removes \(O(\log m)\) outermost
  curves;
* line 2839 states
  \(\mathcal W(\mathscr S^t)=O(1)\) for \(t>0\);
* line 2837 states \(T=O(\log m)\); and
* line 2841 describes the final deleted family as \(O(1)\) outermost
  curves.

In DL's width calculus, the last two occurrences of “\(O(\cdot)\)
curves” mean a subfamily of that extremal width, not a literal finite
number of individual leaves.  Subadditivity of width then gives
(15.3).  This is also the only evident route by which the authors
obtain their displayed relative estimate.

Therefore (15.3) is a defensible proof-internal source import, but it
must be ledgered explicitly as

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND.
```

Importing only the displayed theorem statement is insufficient for the
argument below.  The final \(O(1)\) assertion at line 2841 remains terse;
the bypass does not independently reprove that analytic estimate.

### 15.4 Borel low-width envelope lemma

The order-cut premise can be avoided.

> **Lemma 15.1 (Borel low-width envelope).**
> Let \(V\) be the stationary annulus, let \(L\) be a standard-Borel
> leaf space with a Borel map into compactified proper paths, and let
> \(D\subset L\) be any, not necessarily measurable, subfamily of
> locally rectifiable leaves.  If
> \(\mathcal W(D)\leq C<\infty\), then for every
> \(\epsilon>0\) there is a Borel leaf set \(B\subset L\) such that
> \[
> D\subset B,
> \qquad
> \mathcal W(B)\leq C+\epsilon.
> \tag{15.4}
> \]

#### Proof

Fix a smooth conformal background metric \(ds\) on \(V\), with area
\(dA\).  By the definition of extremal width, choose a nonnegative
Borel density \(\rho\), admissible for every leaf in \(D\), such that
\[
\int_V\rho^2\,dA
<
\mathcal W(D)+\epsilon/2.
\tag{15.5}
\]

The Vitali--Caratheodory theorem in \(L^2(V,dA)\) gives a nonnegative
lower-semicontinuous density \(\sigma\) satisfying, **pointwise**,
\[
\rho\leq\sigma,
\qquad
\int_V\sigma^2\,dA
<
\int_V\rho^2\,dA+\epsilon/2.
\tag{15.6}
\]
Pointwise majorization, rather than almost-everywhere majorization, is
important because admissibility is required on every discarded leaf.

Write
\[
\operatorname{Len}_\sigma(\gamma)
:=
\int_\gamma\sigma\,ds.
\tag{15.7}
\]
The functional \(\operatorname{Len}_\sigma\) is lower semicontinuous on
the compact-open space of compactified paths.  Here is the required
verification.  Use a conformal annular uniformization to choose the
background metric extending to the prime-end compactification and
extend \(\sigma\) by zero on the ideal boundary.  The extension is
lower semicontinuous because \(\sigma\geq0\).  Write
\(\sigma=\sup_n\sigma_n\) for an increasing sequence of nonnegative
continuous functions.  For continuous \(\sigma_n\), weighted path
length is lower semicontinuous under uniform convergence, by the usual
finite-partition proof of lower semicontinuity of metric length.
Monotone convergence along each path gives
\[
\operatorname{Len}_\sigma
=
\sup_n\operatorname{Len}_{\sigma_n},
\]
which is lower semicontinuous.

Define
\[
B
:=
\{\ell\in L:
  \operatorname{Len}_\sigma(\gamma_\ell)\geq1\}.
\tag{15.8}
\]
The compactified-path map is Borel, and the superlevel in (15.8) is
Borel for a lower-semicontinuous functional.  Hence \(B\) is Borel.
Since \(\sigma\geq\rho\) and \(\rho\) is admissible for \(D\), we have
\(D\subset B\).  Finally \(\sigma\) is itself admissible for \(B\), so
by (15.5)--(15.6),
\[
\mathcal W(B)
\leq
\int_V\sigma^2\,dA
<
\mathcal W(D)+\epsilon
\leq C+\epsilon.
\]
This proves (15.4). \(\square\)

The proof is invariant under reparameterization.  If a compactified
path has infinite background length, (15.7) is understood as the
standard extended weighted metric length; the lower-semicontinuity
argument still applies.

### 15.5 Borel regularization of the DL output

Assume the proof-internal source clause (15.3).  Apply Lemma 15.1 to
the actual, possibly non-Borel DL discard \(D\), and put
\[
\mathscr S^{\rm Bor}
:=
\mathscr S\setminus B.
\tag{15.9}
\]

Then:

1. \(\mathscr S^{\rm Bor}\) is a Borel sublamination: its leaf-code set
   is Borel, and the injective Borel leaf evaluation has Borel geometric
   image by Lusin--Souslin;
2. \(D\subset B\) implies
   \(\mathscr S^{\rm Bor}\subset\mathscr S^{\rm new}\), so
   \(f\) remains injective on the entire retained geometric family; and
3. the Parallel Law and (15.4) give
   \[
   \begin{aligned}
   \mathcal W(\mathscr S)
   &\leq
   \mathcal W(\mathscr S^{\rm Bor})+\mathcal W(B),\\
   \mathcal W(\mathscr S^{\rm Bor})
   &\geq
   \mathcal W(\mathscr S)
   -C_{\rm DL}(1+\log m)-\epsilon.
   \end{aligned}
   \tag{15.10}
   \]

Every retained leaf is still above the same Wave interval, so enlarging
the discard does not destroy the individual Wave-direction predicate.
No total leaf order, chartwise downset, measurable transverse width, or
measurable choice of the native DL buffer is used.

### 15.6 Result of the direct pass

The frozen DL text does not determine enough data to prove the proposed
chart-downset lemma.  It does provide, at proof level, the different
invariant actually needed by Lemma 15.1: a low-width discard family.
Consequently the viable replacement interface is

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND
        + BOREL_LOW_WIDTH_ENVELOPE
        => BOREL_INJECTIVE_DL_SUBWAVE.
```

This bypass is conditional only on importing (15.3), not on any
ordering of the full Wave.  If the project refuses the terse final
width assertion at DL 2841 as a source proof, then
`DL_RELATIVE_DISCARD_FAMILY_BOUND` remains the exact analytic blocker;
the descriptive-set part of the bypass is complete.

## 13. Addendum: second live repair and residual audit

The next live revision, audited through SHA-256

```text
D35EA70FC80DEC05DCA2C07C0C1CAEC69B52227DACED46C4AE15DF41FDE7362C,
```

materially repairs several earlier findings:

1. it indexes the decomposition by all nonempty arc classes and proves
   their finiteness using an auxiliary coefficient-one arc diagram, so
   zero-width classes are no longer omitted;
2. it defines the preferred domain on the coincident-endpoint locus,
   lifts a based circle to an ordinary strip crosscut with nonzero deck
   displacement, and adds a Borel based-circle parameterization;
3. it supplies an explicit rational-limit argument for joint lift
   evaluation and a path-space argument for the KKL subordination
   filters; and
4. it replaces the ill-typed hyperspace iteration by a parameterized
   path-space output and typed maps through the actual intermediate
   Waves.

These repairs retire the literal counterexample R5 as an obstruction
to the **revised** theorem: the based-circle case is now included rather
than incorrectly excluded.  The example remains the reason that the
new branch is necessary.

The following residual items still prevent a completed independent
audit.

### 13.1 Shared lifted endpoints

The revised nesting proof reduces coincident downstairs endpoints to
distinct lifted endpoints, which is correct when the deck displacement
is nonzero.  Two different lifted crosscuts can nevertheless share one
lifted ideal endpoint.  The sentence “nonnesting makes the endpoint
positions alternate” does not literally cover equality.

Add the standard shared-endpoint case: two disjoint Jordan crosscuts
with a common ideal endpoint and with preferred sides containing the
same lifted interval have nested preferred domains.  This follows by
Jordan separation after deleting a sufficiently small boundary collar,
or directly from the crosscut order theorem.  The area argument needs
only that explicit topological clause.

### 13.2 Borel ordering of two endpoints in one marked interval

The revised endpoint relation is Borel and finite, but the phrase “the
oriented arc-class tag orders the endpoints” is still not a Borel
construction.  On a same-interval two-endpoint packet, choose the fixed
lift(s) determined by the oriented arc tag, lift each Lusin--Novikov
endpoint through the homeomorphic marking-interval lift, and compare
the resulting boundary coordinates/deck displacement.  State that
comparison as the Borel selector.

### 13.3 Two details in the continuation code

The finite inverse-branch word should require the source image of each
closed parameter subinterval to be compactly contained in the
corresponding chart domain.  This positive-margin condition is Borel
and prevents a path value at an irrational time from lying on a chart
boundary even though the checked rational values lie inside.

After affine reparameterization, evaluation at a normalized rational
time is not evaluation at an original rational time when
\(a_\omega,b_\omega\) are irrational.  Use Borel functions

\[
 q_n(\omega,r)\in
 \mathbb Q\cap(a_\omega,b_\omega),
 \qquad
 q_n(\omega,r)\longrightarrow
 a_\omega+(b_\omega-a_\omega)r,
\]

and take the limit of the already Borel original-rational evaluations.

Finally, “lexicographically first” must mean first in the natural-number
Lusin--Novikov enumeration of \((q,z',\text{chart})\); it must not use
an arbitrary lexicographic order on the raw uncountable \(z'\)
coordinate.

### 13.4 Endpoint-moving homotopies

KKL 1868 phrases subordination using homotopy rel the exact endpoints.
The revised path-space proof uses small homotopies whose endpoints move
inside fixed marking intervals.  The intended conclusion is correct
provided the following stability statement is written:

> Joining two nearby endpoints by short paths inside the same marked
> intervals preserves subordination to a multi-interval containing
> those intervals, in both directions.

This converts the endpoint-moving local path-space class into the
exact-endpoint KKL predicate.  Without the sentence, the proof changes
the equivalence relation without explanation.

### 13.5 DL buffer extraction remains the largest residual source gap

The revised draft still infers from DL 2841 that the deleted
“outermost curves” are finitely many initial/terminal order intervals.
The conclusion is consistent with the rectangle-buffer definitions at
DL23 1768--1792, but the particular Wave Lemma proof must explicitly
identify:

1. the ordered parallel packet(s) to which each buffer belongs;
2. the left/right or inner/outer buffer in those packet coordinates;
3. the finite number of such buffers in each deck-span class; and
4. the correspondence between that rectangle order and the deck order
   established in Section 6.

Once this lift-level extraction is written, the area coordinate does
make every resulting cut Borel.  Until then,
`DL_OUTER_BUFFER_IS_ORDER_INTERVAL` is still asserted rather than
proved.

### 13.6 Residual verdict

No counterexample was found to the repaired nested-area sublevel
argument, its AK application, the \(\Theta\) parameterization of arc
fibers, or the new based-circle parameterization.  The remaining
obligations are localized and appear repairable, but they are proof
obligations, not editorial preferences.

Therefore the independent classification remains:

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION = open pending 13.1--13.5.
```

Nothing in this audit changes the open status of the ledger Gate N1,
N2, VAAPC-I, UPTCR, or MLC.

## 14. Fresh frozen-snapshot audit

This section supersedes the chronological findings above for the
current live draft.  The audited file is frozen at SHA-256

```text
C9F1C7BD37FD192E047B13B79023B3A88AC3148A5A11C5A79EC52B349114D318
```

and has 1,315 lines.  The live proof file and the machine ledger were
not edited during this audit.

### 14.1 Exact disposition of the five previous residuals

| item | current lines | disposition | reason |
|---|---:|---|---|
| A: shared lifted endpoints | 283--292 | passes, with a citation-quality improvement recommended | In the prime-end strip each compactified lift is a Jordan arc.  Two such arcs meeting only at a common boundary endpoint form a tame planar arc graph.  A boundary-preserving local Schoenflies isotopy in an arbitrarily small half-disk separates the landing points while fixing prescribed witnesses outside that half-disk.  The ordinary alternating-endpoint crosscut theorem then applies. |
| B: Borel ordering of two endpoints | 532--549 | passes | The draft no longer claims that an arbitrary Borel endpoint enumeration realizes the arc orientation.  It uses an arbitrary fixed Borel order only to parametrize the compact arc and retains arc orientation/winding as separate discrete tags.  KKL paths are unoriented up to reparameterization, and all later endpoint filters are symmetric membership predicates. |
| C: continuation code | 865--925 and 1022--1038 | passes | The chart word now requires the whole closed source subsegment to lie in \(\overline{W_{i,k}}\Subset W_i\).  Membership in the closed set is equivalent to membership at all rational times by continuity.  A nested relatively compact exhaustion of each \(W_i\) captures every compact continued segment.  The draft also evaluates normalized irrational source times by Borel rational approximants and selects representatives by natural-number Lusin--Novikov indices. |
| D: endpoint-moving homotopies | 984--1019 | passes mathematically; one explicit whisker sentence would improve traceability | If two endpoints move inside fixed marked intervals, join old and new endpoints by short collar paths in those intervals.  For every neighborhood of a candidate multi-interval, push these joins slightly into the surface inside that neighborhood.  Concatenation converts a representative subordinate with the old exact endpoints into one subordinate with the new exact endpoints, and reversal gives the converse.  Thus the KKL exact-endpoint predicate is constant on the relative classes used in lines 984--1009. |
| E: DL outer-buffer extraction | 736--772 and 1122--1164 | **fails; blocking** | The order-cut measurability lemma (7.6c) is correct once the deleted set is known to be an order cut.  The missing implication is precisely that premise.  DL 1791--1792 defines left/right buffers only for the vertical foliation of a specified rectangle.  DL 2827 and 2841 merely say “outermost curves”; they do not identify, for an arbitrary Wave and its deck-span pieces, a rectangle coordinate or prove that the selected deletion is downward/upward closed in every arc chart. |

The old open-chart counterexample no longer attacks item C.  It was:
for irrational \(a\in(0,1)\), the continuous function
\(x\mapsto(x-a)^2\) belongs to the open set \((0,\infty)\) at every
rational time but not at \(a\).  Lines 870--874 correctly avoid this
failure by testing a **closed**, compactly-contained chart core.

### 14.2 Source-semantic audit of
`ARC_CLASS_SUBLAMINATION_IS_PROPER_BOREL`

**Disposition: passes as an explicit source convention, not as a
derived closure theorem.**

KL06 `wad.tex` 142--143 defines a proper lamination as a Borel
geometric support decomposed into disjoint proper paths.  Its footnote
at line 144 says that every lamination subsequently considered is
proper.  Lines 145--150 then explicitly call
\(\mathcal F(\alpha)\) a *sublamination*.  KKL 1911 uses the same
word for the same arc-class object.  Read literally under the standing
convention, that object is therefore a proper, hence Borel,
lamination.  Frozen-draft lines 151--167 state exactly this limited
import and expressly reject the invalid inference that an arbitrary
leaf subfamily of a Borel lamination is Borel.

This import does not extend to a subset selected by a new analytic or
descriptive predicate.  Every such later selection still needs its own
Borel argument.

### 14.3 First fatal gap and exact repair

The first fatal gap in line order is the assertion at lines 765--768:

```text
An outermost buffer of the full planar family restricts in each chart
to an initial interval, a terminal interval, their union, or the empty
set.
```

Lines 1127--1139 repeat rather than prove this statement.  The sentence
“a leaf lying between a removed outer leaf and the corresponding end
is itself in the same buffer” is the desired monotonicity conclusion;
it does not follow merely from the Euclidean-rectangle definition
unless the DL Wave deletion has first been realized in that rectangle
coordinate.

The smallest sufficient repair is a source-level
`DL_BUFFER_CHART_DOWNSET_LEMMA` with the following data and proof:

1. choose the actual lifted deck-span packet
   \(\mathscr S^t_k\) used at DL 2830--2841;
2. for every nonempty arc chart \(\alpha\), identify its nested-domain
   order with the relevant lift order;
3. define the exact left and right conflict families removed by the DL
   construction, rather than an unspecified family of the same width;
4. prove by Jordan separation that, for every relevant deck shift,
   each conflict family intersected with \(L_\alpha\) is downward or
   upward closed;
5. prove that only the finitely many shifts/buffers occurring in the
   DL construction are used and that deleting their union makes
   \(\mathscr S^\new_0,\ldots,\mathscr S^\new_{m-1}\) pairwise
   disjoint; and
6. identify these exact deletions with the buffer families to which
   DL's \(O(\log m)\) width estimate applies.

Only after steps 1--6 does (7.6c) prove the deleted geometric family
Borel.  The finite arc atlas is the right measurable target, but
finiteness alone does not supply the missing monotonicity.

### 14.4 Corollary 3.2a and the opposite-side fan

The opposite-side fan correctly refutes the earlier assertion that a
common individually directed interval alone totally orders several arc
classes.  Corollary 3.2a adds the necessary common, disjoint collective
end blocks.  Under those hypotheses its conclusion survives audit.

The terse sentence at lines 339--343 can be expanded as follows.  A
simple strip lift is disjoint from each of its nontrivial deck
translates; alternating endpoints therefore prohibit a displacement
larger than one deck period.  With both collective end blocks connected
and disjoint from \(J\), there is a unique adjacent pair of their lifts
whose intervening boundary interval contains the fixed lift of \(J\).
Directedness forces every selected leaf lift to use that pair.  The
ordinary noncrossing-crosscut order then gives nested \(J\)-side
domains.  The opposite-side fan fails exactly this common-end-block
hypothesis.

Corollary 3.2a is no longer needed for the finite-atlas construction,
but this expansion should be included if the corollary remains in the
proof.

### 14.5 Other current clauses

No new counterexample was found to:

1. the Borel sublevel argument at lines 362--415;
2. the Arsenin--Kunugui construction of the realized coordinate set;
3. the Borel compactified-leaf field;
4. the ordered-arc parameterization;
5. the separately treated based-Jordan-circle parameterization;
6. properness and prime-end Cauchy tests for maximal occurrences;
7. the typed path-space successor; or
8. terminal saturation, conditional on the preceding Borel successor
   and on a Borel terminal leaf set.

The shared-endpoint collar step and the exact-endpoint whisker step are
true planar-topology facts, but spelling them out would make the proof
self-contained at the standard demanded by this project.

### 14.6 Frozen-snapshot verdict

The core nested-area construction and the KKL filtered-restriction
realization pass this audit.  The DL outer-buffer interface does not.
Therefore:

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION = open
    pending DL_BUFFER_CHART_DOWNSET_LEMMA.
```

The first fatal gap is frozen-draft lines 765--768.  Nothing in this
audit promotes Gate N1, N2, VAAPC-I, UPTCR, rigidity, parameter
fibers, or MLC.

## 1. Severity table

| ID | draft location | severity | finding |
|---|---:|---|---|
| R1 | 135--155 | blocking | \(Z_\alpha\) is declared Borel without a source theorem or proof |
| R2 | 164--210 | major | strict nesting proof omits equal endpoints, shared endpoints, and the lift-to-base descent |
| R3 | 248--301 | passes conditionally | the “at most one omitted leaf” sublevel argument is correct after R1--R2 |
| R4 | 319--338 | passes conditionally | the first AK use is valid after R1--R3 |
| R5 | 355--420 | blocking | compactified leaves can be based Jordan circles with a one-point endpoint section |
| R6 | 442--468 | major | projection over the hyperspace is not closed when \(s\mapsto K_s\) is only Borel |
| R7 | 413--419 | major | ordering equal-interval endpoints requires a proved Borel lift/deck rule |
| R8 | 524--539 | major | compatibility with deck order is asserted by a crossing slogan, not proved |
| R9 | 568--593 | blocking | the maximal proper-component restriction relation is not constructed |
| R10 | 597--611 | major | the target leaf code and injectivity needed for the successor map are not typed |
| R11 | 613--626 | major | DL “outermost curves” are not proved to be the claimed finite order intervals |
| R12 | 628--642 | conditional | saturation is correct only after a Borel, correctly typed successor map exists |

## 2. Arc-packet reduction: the first unsupported inference

### Finding R1

Draft lines 135--155 reason:

1. only finitely many arc classes occur; and
2. KL06/KKL call \(\mathcal F(\alpha)\) a sublamination;
3. therefore the geometric support \(Z_\alpha\) is Borel.

Step 3 is not present in the locked clauses.

KL06 `wad.tex` 142--150 says:

- the total geometric support \(Z\) of a proper lamination is Borel;
- its leaves decompose set-theoretically by arc class; and
- \(\mathcal F(\alpha)\) can be regarded as a path family for extremal
  width.

KKL 1911--1914 likewise defines the arc-class subfamily and its WAD
coefficient.  Neither quoted passage proves that the union of the leaves
in one arc class is a Borel subset of the surface.

A finite partition of a Borel set does not make its pieces Borel.  The
fact that the partition pieces come from planar arc classes may force
Borelness, but that is a new topological/descriptive-set lemma and is
exactly what must be proved.

The finite-number assertion also needs a slightly different
justification than the one in the draft.  The support of the WAD induced
by \(S\) can omit a nonempty zero-width arc family.  Finiteness follows
instead from the fact that all nonempty arc classes form an arc diagram
and a finite-type marked surface admits only finitely many pairwise
nonintersecting arc classes.  Equivalently, assign an auxiliary positive
weight to every nonempty class and apply the topological support bound.

### Required repair

Prove an `ARC_CLASS_SUPPORT_BOREL` lemma:

> If \(Z\) is the Borel support of a proper Wave in the finite-marked
> annulus and its leaves are explicitly decomposed into disjoint proper
> embedded paths, then the union \(Z_\alpha\) of the leaves in each
> marked arc class \(\alpha\) is Borel.

The proof must use the finite noncrossing arc diagram and actual
separating regions or a finite Borel topological invariant.  It cannot
assume a Borel leaf quotient, since construction of that quotient is
the purpose of BOWR.

Until this lemma is supplied, Lemma 3.3 cannot start: its domain
\(Z_\alpha\) is not known to be a standard Borel subset of \(V\).

## 3. Strict nesting and the area sublevel argument

### Finding R2: the conclusion is plausible, but the written proof is incomplete

For two leaves in a fixed marked arc class, the correct proof should
choose the pair of lifted marking intervals determined by that arc
class and compare the corresponding lifted oriented crosscuts.

Draft lines 195--205 instead say that nonnested side domains would make
“the four endpoints alternate.”  This does not cover:

1. two leaves sharing one ideal endpoint;
2. two leaves sharing both ideal endpoints;
3. a proper embedded path whose two ideal endpoints are the same prime
   end;
4. the case in which nesting is first proved in an annular lift and
   must then be descended to the selected side domains in \(V\); or
5. the assertion that the orientation selects the same topological side
   for all leaves when both endpoints lie in the same marking interval.

These are not cosmetic cases.  KKL allows arcs connecting an interval
to itself, and a proper embedded open path can have coincident ideal
endpoints.

### Required repair

State and prove a marked-annulus crosscut lemma with two cases.

1. **Distinct endpoint case.**  Lift the arc class to fixed boundary
   intervals \(\widetilde I,\widetilde J\).  Use the cyclic order on
   those intervals, including shared-endpoint limits, to prove that the
   oriented side domains are strictly nested.
2. **Coincident endpoint case.**  The compactified leaf is a based
   Jordan circle.  Use Jordan separation and the common winding/arc
   class to prove that the selected domains are strictly nested.

The lemma must also prove:

```text
if one interior point of gamma lies in O_eta, then the whole leaf gamma
lies in O_eta.
```

That fact is used at draft lines 264--275 but is not stated.

### Finding R3: the “at most one omitted leaf” argument passes

Assume R1 and the strengthened R2.  For rational \(r\), let

\[
 U_r=\bigcup_{t(\eta)<r}O_\eta .
\]

This is open.  Strict nesting implies

\[
 \gamma\cap U_r\ne\varnothing
 \quad\Longleftrightarrow\quad
 \exists\eta\quad
 t(\gamma)<t(\eta)<r.
\]

Thus every sublevel leaf is contained in \(U_r\), except possibly a
maximum of \(t(P)\cap(-\infty,r)\).  Injectivity of \(t\) makes that
maximum unique.  A proper embedded path has closed image in \(V\), so
adjoining that one leaf preserves Borelness.

No additional omitted leaves appear at a gap or a nonattained supremum:
if a leaf is not maximal in the sublevel order, there is, by definition,
a strictly larger leaf still in that sublevel.

This portion of the draft is sound once its two prerequisites are
proved.

## 4. Arsenin--Kunugui audit

### First use, draft lines 319--338

Conditional on \(Z_\alpha\) being Borel and \(t\) being Borel, the graph

\[
 G_\alpha=\{(s,x):x\in Z_\alpha,\ t(x)=s\}
\]

is Borel in \(\mathbb R\times V\).  Its nonempty vertical sections are
closed proper leaves, hence sigma-compact.  Since \(\mathbb R\) and
\(V\) are Polish, AK applies and \(t(P)\) is Borel.

This application is correct.

### Later uses

When the draft treats \(L_\alpha\) with its inherited topology, it
should not silently assume that an arbitrary Borel subset of
\(\mathbb R\) is Polish in that topology.  Either:

1. apply AK to the ambient Polish first coordinate \(\mathbb R\) and
   then restrict to \(L_\alpha\); or
2. equip the standard-Borel space \(L_\alpha\) with a compatible Polish
   realization.

This is a local repair, not an obstruction.

## 5. Prime-end endpoint failure

### Finding R5: “compact arc” and “exactly two endpoints” are false

Draft lines 355--364 assert that every prime-end compactification
\(K_s\) of a leaf is a compact arc.  Lines 403--415 then assert that
\(K_s\cap\partial^{\rm pe}V\) has exactly two points.

An allowed proper embedded path can have the same prime end at both
ends.  Here is an explicit model in the annulus

\[
 A=\{1<|z|<2\}.
\]

For \(0<t<1\), set

\[
 \gamma(t)=
 \bigl(1+\tfrac14\sin(\pi t)\bigr)e^{2\pi i t}.
\]

Then:

1. \(\gamma\) is an embedded proper path in \(A\);
2. both parameter ends converge to the same inner prime end \(1\);
3. its prime-end closure is a Jordan circle, not a compact arc; and
4. its ideal-boundary intersection is the singleton \(\{1\}\).

With a finite marking of the inner boundary having at least three
intervals and with \(1\) in the interior of one interval, the winding
path is subordinate to the whole inner boundary but not to any
multi-interval of combinatorial length at most two.  Thus it is of the
type allowed by the marked Wave definitions.  KKL also explicitly
allows arcs connecting an interval to itself.

Consequently, the two-point Lusin--Novikov enumeration and Lemma 5.2 do
not cover all proof-used Waves.

### Required repair

Partition the compactified-leaf field by endpoint cardinality, which is
Borel once the compact field is established:

1. **two-endpoint packet:** \(K_s\) is an arc and the current
   arc-parameterization strategy applies after R6 is repaired;
2. **one-endpoint packet:** \(K_s\) is a based Jordan circle and
   \(K_s\setminus\{a_s\}\) must be parameterized as an oriented open
   interval.

The second case requires a Borel field theorem for based oriented
Jordan circles.  One may construct oriented initial subarcs after
removing the Borel basepoint, but the orientation and the selected
one-sided approach to that basepoint must be part of the marked arc
tag.  Merely duplicating the endpoint map does not make the existing
\([0,1]\)-to-\(K_s\) homeomorphism possible.

## 6. Hyperspace parameterization

### Lemma 5.1, conditional assessment

The hit-set equivalence

\[
 K_s\cap W\ne\varnothing
 \Longleftrightarrow
 (G_\alpha)_s\cap(W\cap V)\ne\varnothing
\]

is valid: every prime-end neighborhood of an endpoint met by \(K_s\)
also meets the interior leaf.  The right-hand sections are relatively
open subsets of a proper embedded line and are sigma-compact.  AK
therefore gives the required hit predicates.

This proves a Borel compact-set field, but not that every compact set
is an arc; R5 remains.

### Finding R6: the order relation uses a false closed-projection step

At draft lines 453--457, the parameter \(s\mapsto K_s\) is only Borel.
Therefore the set of tuples satisfying \(C\subset K_s\) is Borel, not
generally closed in the \(s\)-variable.  Projection over a compact
hyperspace does not turn an arbitrary Borel set into a closed set.

The desired conclusion is nevertheless repairable.  For fixed
\((s,x,y)\), the family of continua

\[
 C\subset K_s\setminus B(x,1/m),\qquad a_s,y\in C
\]

is a closed subset of the compact hyperspace and hence compact.  The
total incidence relation is Borel.  AK with compact vertical sections
therefore makes its projection Borel.

A second explicit AK application is then needed to show that

\[
 (s,x)\longmapsto K_s[a_s,x]
\]

is a Borel compact-valued field.  This does not follow merely from the
word “consequently” at draft line 459.

After these repairs, the function

\[
 \Theta(C)=\sum_n2^{-n}(1+d(q_n,C))^{-1}
\]

is indeed continuous in the Hausdorff topology and strictly increasing
under proper compact inclusion.  The normalized function \(u_s\) then
parameterizes every genuine compact arc correctly.

### Endpoint ordering gap

Lusin--Novikov can enumerate a two-point endpoint section, but the
sentence “the oriented arc-class tag orders them” still needs a Borel
rule.  If the endpoints lie in distinct marking intervals, the rule is
finite and immediate.  If they lie in the same interval, one must:

1. choose a Borel lift of the endpoint pair to the fixed lifted marking
   interval(s);
2. include the deck displacement specified by the arc tag; and
3. prove that comparing the lifted endpoints is Borel.

The draft states this topological convention in Section 2 but does not
turn it into the Borel selector used in Section 5.

## 7. Compatibility with DL deck order

### Finding R8

Draft lines 531--536 say that two leaves can exchange deck order only
by crossing, so the nesting order is globally the deck order or its
reverse.

This is not a proof of a global order identity.  The repair should use
the fixed lift of the arc packet.  For each leaf, record the ordered
pair of endpoints on the lifted boundary line.  Noncrossing forces the
opposite endpoint monotonicities, and the chosen \(J\)-side identifies
which monotonicity equals domain inclusion.  This directly proves, for
every pair of leaves, that:

\[
 O_\gamma\subset O_\eta
 \quad\Longleftrightarrow\quad
 \widetilde\gamma<_{\rm deck}\widetilde\eta
\]

or the fixed reverse relation.

The sign cannot be chosen by “evaluate one pair” unless the
single-leaf and coincident-endpoint cases are separately declared.

## 8. Filtered immersion restriction

### Finding R9: maximal proper components are not whole-path lifts

KKL restriction takes **all maximal proper path components** contained
in \(\iota^{-1}(\gamma)\), subject to the two marking filters.

Such a component generally projects to a proper open subinterval

\[
 (a,b)\subsetneq(0,1)
\]

of the parameter interval of \(\gamma\).  This already occurs for a
holomorphic inclusion of one planar domain into another: a proper path
can enter the smaller domain, follow one component there, and leave it.
That intersection component is a proper path of the smaller domain,
but it is not a lift of the whole original path.

Draft lines 578--581 test continuation “over the whole path” and test
proper escape only near \(0\) and \(1\).  They therefore omit precisely
the components whose maximal parameter endpoints \(a,b\) are interior.

The proposed finite continuation word also does not itself code
continuation along the whole noncompact component.  A rational seed
and a starting inverse branch determine a unique maximal lift, but the
proof must construct its maximal interval and show that its endpoints
depend Borelly on the seed code.

### Additional missing steps

The following claims in lines 568--593 need separate proofs.

1. The relation “two rational seed codes generate the same maximal
   component” is Borel.
2. Each component contains a rational source parameter, so the
   components form countable source sections.
3. The left and right maximal continuation endpoints \(a,b\) are
   Borel functions of a canonical seed code.
4. The maximal lift admits a jointly Borel reparameterization from
   \((0,1)\).
5. Proper escape is checked at \(a,b\), including finite interior
   endpoints.
6. The two ideal endpoints in \(V'\) form a Borel finite field.
7. “Is a path in the fine marking” and “is not subordinate to one
   coarse interval” are Borel predicates on the actual lifted
   endpoint/deck/homotopy code.
8. Duplicate-seed deletion uses a Borel equality relation and a
   genuine well-order of the countable seed codes.

### Minimal viable construction

Let

\[
 R=\{(\ell,t,y):\iota(y)=e_S(\ell,t)\}.
\]

This is Borel, with countable \(y\)-sections.  Use Lusin--Novikov to
enumerate rational-time starting lifts.  A local inverse-branch atlas
and uniqueness of path lifting should then prove a Borel continuation
relation on rational compact parameter intervals.  Define the maximal
domain endpoints as the infimum and supremum of the rational intervals
on which continuation exists.  Only after proving those endpoint maps
Borel may one impose proper escape and the two KKL filters.

This is a plausible route, but it is a new lemma; the paragraph in
Section 7.2 does not establish it.

## 9. Pushforward, pruning, and saturation

### Finding R10: successor typing

On a DL-retained packet, point-set injectivity of \(f\) on the entire
geometric union is enough to push the source code forward.  The draft
should explicitly take the output leaf code to be the retained
occurrence code, with evaluation \(f\circ e\).  Lusin--Souslin then
makes the image Borel.

As written, \(L_{F_*S}\) appears before it is constructed, and
Lusin--Novikov is invoked on an “untagged output relation” whose Borel
target coding has not been specified.  Unbreakability gives
single-valuedness; it does not by itself provide the target
standard-Borel space.

### Finding R11: DL outer-buffer measurability

DL 2830--2838 gives a finite deck-span decomposition by endpoint
positions.  Once the endpoint/deck code is proved, those pieces are
Borel.

The further assertion at draft lines 618--621 is not yet source-locked:
the words “remove \(O(1)\) outermost curves” at DL 2841 must be expanded
to show that the deleted family is a finite union of initial or
terminal intervals **within the same ordered arc/occurrence packets**.
The phrase can refer to buffers of positive extremal width, not to a
finite number of individual leaves.

The area coordinate proves that every specified order interval is
Borel.  It does not prove that the analytic DL deletion has the
specified interval form.  A short lift-level lemma extracting the
actual outer packets from the DL proof is required.

### Finding R12: terminal saturation is conditionally correct

If \(\Phi_h\) is a Borel successor map between correctly typed
standard-Borel leaf spaces and \(E\) is Borel in the target code, then
\(\Phi_h^{-1}(E)\) is Borel.  Restricting an injective joint evaluation
to that source set and applying Lusin--Souslin makes its geometric union
Borel.

Thus Section 7.5 is sound after R9--R10.  It cannot repair those missing
inputs.

## 10. Exact minimum repair package

BOWR can be reconsidered only after the following lemmas are written
and audited.

1. `ARC_CLASS_SUPPORT_BOREL`.
2. `MARKED_ANNULUS_STRICT_NESTING`, including shared and coincident
   ideal endpoints.
3. `BOREL_COMPACTIFIED_LEAF_FIELD`, with a Borel split into compact
   arcs and based Jordan circles.
4. `BOREL_ARC_AND_BASED_CIRCLE_PARAMETERIZATION`.
5. `BOREL_LIFTED_ENDPOINT_ORDER`.
6. `BOREL_MAXIMAL_IMMERSION_COMPONENT_CALCULUS`, with variable
   parameter domains and both KKL filters.
7. `DL_OUTER_BUFFER_IS_ORDER_INTERVAL`.
8. `BOREL_INJECTIVE_PUSHFORWARD_AND_SUCCESSOR`.

The current area-sublevel lemma and the final saturation observation
can be retained as components of that repair.  They do not, by
themselves, close the Borel realization interface.

## 11. Promotion rule

The draft's status table at lines 738--745 overstates what has been
proved.  The defensible classification is:

| statement | audited status |
|---|---|
| area coordinate injective under strict nesting | proved conditionally |
| area-coordinate sublevels are Borel | proved conditionally |
| realized coordinate set is Borel by AK | proved conditionally |
| arbitrary KKL arc-class packet is Borel | open |
| all compactified leaves are arcs with two endpoints | refuted |
| filtered maximal-component restriction is Borel | open |
| DL deleted buffers are Borel order intervals | open |
| full saturation | proved conditionally |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | open |
| ledger Gate N1 and all later gates | open |

## 12. Addendum: audit of the live revision at SHA `AEFA7812...`

While this red-team pass was running, the target draft was expanded to
924 lines and SHA-256

```text
AEFA781244C0D7FF3CDC78F33FA2AB89CBB2CFB523CBA08F1ED9DD65C80BAD25.
```

The revision correctly repairs the compact-hyperspace projection step
identified in R6 by using AK with compact sections.  It also recognizes
that a maximal immersion lift has a variable interval
\((a_\omega,b_\omega)\), rather than necessarily all of \((0,1)\).
Those are material improvements.

The revision is still not promotable for the following exact reasons.

### 12.1 Equation (2.2) omits nonempty zero-width classes

Revised lines 140--163 still write

\[
 S=\mathop{\dot\bigcup}_{\alpha\in\operatorname{supp}W_S}S(\alpha).
\]

This is false when \(S(\alpha)\ne\varnothing\) but
\(\mathbb W(S(\alpha))=0\), for example for an isolated leaf.  The
support of the induced WAD contains the positive-weight classes, not
all nonempty classes.

Replace the index set by

\[
 \mathcal A(S)=\{\alpha:S(\alpha)\ne\varnothing\}.
\]

Finiteness of \(\mathcal A(S)\) follows from the finite arc-diagram
bound, not from positivity of induced extremal widths.

The semantic claim that KL06's word “sublamination” automatically
imports Borel support remains a source-interpretation issue.  Even if
that interpretation is accepted, the support-index equality above
must still be fixed.

### 12.2 The based-circle counterexample remains untouched

Revised lines 394--395 and 444 still assert “compact arc” and “exactly
two-point sections.”  The inner-boundary winding example in Section 5
of this audit directly refutes those assertions.  It also invalidates:

1. the crosscut-only nesting proof at revised lines 212--227;
2. the \([0,1]\)-onto-\(K_s\) homeomorphism at revised lines 456--555;
3. the “compact-arc hyperspace code” for successors at revised lines
   768--785.

A based-circle branch is mandatory unless an exact KKL hypothesis is
found that excludes coincident prime-end tails.  None of the cited
clauses does so.

### 12.3 The revised maximal-lift calculus is still a proof sketch

Revised lines 642--760 now record variable maximal intervals and give
the right general outline.  Four obligations remain.

1. A finite continuation word must use compactly contained chart
   ranges, or an equivalent positive-margin condition.  Checking that
   rational values lie in an open chart does not exclude an irrational
   parameter whose value lies on the chart boundary.
2. Borel evaluation at rational parameter values plus fiberwise
   continuity does not by the single sentence at lines 688--690 produce
   a jointly Borel evaluation at all real parameters.  Supply the
   rational-approximation limit construction explicitly.
3. The KKL tests “path in the fine marking” and “not subordinate to one
   coarse interval” are not merely endpoint predicates when two
   endpoints lie in the same interval.  The winding/deck/homotopy tag
   of the maximal component must be constructed Borelly.
4. Lexicographic deletion must be performed on a natural-number code
   obtained from the Lusin--Novikov enumeration.  The raw germ tuple
   contains \(z'\), and an arbitrary lexicographic order on an
   uncountable Polish coordinate need not give every duplicate class a
   least element.

These are plausible repair lemmas, but they are not derivations already
contained in the revision.

### 12.4 The hyperspace successor cannot be finitely composed as typed

Revised lines 768--786 map a source leaf to only the compact image of
its pushed path:

\[
 \Phi_1:L_S\longrightarrow\mathcal K(\overline V^{\rm pe}).
\]

That compact image is not a parameterized path code on which the next
filtered restriction operation is defined.  If an intermediate
pushforward is not a lamination, there is no target leaf space and no
next map having the displayed hyperspace as its domain.  Therefore the
sentence “finite composition gives every \(\Phi_h\)” does not follow.

A valid repair must carry a Borel **parameterized-path occurrence**
through all finitely many steps, or directly construct the finite
iterated occurrence relation on the original source code.  It must not
discard parametrization and orientation after one step.

Furthermore, a covering pushforward of a proper embedded input path
need not be embedded unless point-set injectivity on that occurrence is
proved.  Its compact image therefore need not be an arc even when the
input has distinct ideal endpoints.

### 12.5 Terminal saturation has a codomain mismatch

At revised lines 803--814, \(E\) is called a Borel target leaf set, but
\(\Phi_h\) has just been typed as a map into the compact hyperspace.
The expression \(\Phi_h^{-1}(E)\) is therefore undefined until \(E\)
is embedded as a Borel set of compact path images.  If the target image
map is Borel and injective, Lusin--Souslin can supply this embedding;
the draft must state and prove it.  In the based-circle case, the image
map must include that branch as well.

### 12.6 DL deletion is still asserted rather than extracted

Revised lines 793--801 repeat that DL's “outermost curves” are finitely
many initial or terminal order segments.  No lift-level derivation was
added.  The locked DL line supplies the analytic deletion but does not
spell out the exact Borel packet decomposition claimed here.

The required `DL_OUTER_BUFFER_IS_ORDER_INTERVAL` lemma therefore
remains open.

### 12.7 Updated verdict

The live revision fixes R6 and begins the correct repair of R9.  It does
not fix R1/R5/R8/R10/R11, and it introduces no complete iterated
parameterized-path calculus.  Thus the updated status is unchanged:

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION = open.
```
