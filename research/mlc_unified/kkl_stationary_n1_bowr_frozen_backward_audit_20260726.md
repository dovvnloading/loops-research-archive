# Frozen backward audit — stationary Borel ordered-Wave realization

## 0. Verdict

```text
AUDIT VERDICT: PASS
```

The audited object is exactly

```text
research/mlc_unified/
kkl_stationary_n1_borel_ordered_wave_realization_20260726.md

SHA-256
6F9B4085C914BD74DD5030C67F311334A4B4882594E111FF552429E4FCC9D118

line count
1368
```

No edit was made to that object during this audit.

Theorem BOWR is proved at this frozen snapshot, relative only to the
imports it explicitly declares:

1. the KL06/KKL meaning of a proof-used proper sublamination;
2. the source-locked KKL prime-end, restriction, covering, and
   unbreakable-Wave results; and
3. the analytic input
   `DL_RELATIVE_DISCARD_FAMILY_BOUND`.

The third item is not a measurable conclusion of BOWR.  It is the
explicit analytic statement extracted from the families discarded at
DL 2830--2841.  The independently audited Borel width-envelope theorem
then supplies the measurable replacement.

This verdict proves only the frozen measurable realization/pruning
interface.  It does not by itself prove the full analytic stationary
continuation theorem, Gate N2, VAAPC-I, UPTCR, rigidity, parameter
fibers, or MLC.

## 1. Identity and dependency checks

The hashes named by the frozen proof were recomputed:

| object | expected SHA-256 | result |
|---|---|---|
| KKL `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` | match |
| DL `Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` | match |
| KL06 `wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` | match |
| Borel width envelope | `9F2ABD1E8DDD0E0E1B4FFC3B55B8DAF3BA64B4BCBE4E9562454A850E5E8422BE` | match |
| audited BOWR file | `6F9B4085C914BD74DD5030C67F311334A4B4882594E111FF552429E4FCC9D118` | match |

The referenced main analytic note currently contains `Theorem N1` and
does not contain the stale label `Theorem N1-A`.  The references at
BOWR lines 72 and 774 are therefore correctly typed.

## 2. Backward map from the theorem statement

| BOWR clause | proof location | audit |
|---|---|---|
| finite Borel arc decomposition | 144--209 | pass |
| strict planar nesting | 249--321 | pass |
| injective Borel area coordinate | 323--412 | pass |
| standard-Borel leaf space | 418--460 | pass |
| Borel prime-end endpoints | 462--546 | pass |
| jointly Borel proper-path evaluation | 548--731 | pass |
| Borel order intervals | 733--762 | pass |
| finite/native subwave partitions | 776--823 | pass |
| both immersion-marking filters | 981--1036 | pass |
| full proper-component occurrence relation | 834--1059 | pass |
| injective covering pushforward | 1061--1065 and 1179--1197 | pass |
| unique untagged successor | 1067--1136 | pass |
| metric-envelope DL pruning | 1138--1202 | pass |
| full terminal saturation | 1204--1230 | pass |

The two definition-level inputs used at the start are kept visible:

- KL06 `wad.tex` 142--150 declares the proof-used proper lamination and
  its arc-class sublaminations in the standing proper sense; and
- KKL 1907--1914 gives the finite topological support bound and repeats
  the arc-class sublamination construction.

The proof does not infer that an arbitrary saturated subset of a Borel
support is Borel.

## 3. Shared-endpoint nesting

### 3.1 Lift and side selection

Lines 267--286 lift one oriented arc class to the closed annular strip.
The chosen lift of the complete crest interval \(Q_\alpha\) fixes the
preferred side.  A coincident-endpoint path downstairs has distinct
lifted endpoints: zero deck displacement would make it subordinate to
one endpoint marking interval, contrary to KKL 1869.

Thus the objects compared upstairs are genuine crosscuts.  The
preferred lifted components project to the domains \(O_\gamma\) used
downstairs.

### 3.2 Shared endpoints

Lines 291--310 include the previously missing shared-endpoint case.
For two planar crosscuts, their finite union near a common boundary
endpoint is a finite embedded planar arc graph.  The boundary-relative
Jordan--Schoenflies theorem straightens this finite graph in a
half-disk while preserving its local cyclic order.  Truncation on a
small half-circle therefore replaces a shared endpoint by two distinct
endpoints in the same cyclic order.

The truncation is disjoint from the fixed nondegenerate interval
\(Q_\alpha\), and it can also be chosen disjoint from a compact witness
to nonnesting.  Hence it changes neither selected side nor a hypothetical
nonnesting witness.  Nonnesting after truncation would give alternating
endpoint pairs, which the Jordan crosscut theorem forbids for disjoint
crosscuts.

The opposite-side fan in lines 1334--1344 is not a counterexample:
those leaves have different oriented arc tags.  The proof orders only
one arc packet at a time.

### 3.3 Strictness

Lines 315--321 correctly rule out equality and exhibit an open region
between distinct nested crosscuts.  A sufficiently small disk in that
region projects injectively, so full support of the finite measure
\(\mu\) makes the area coordinate strictly monotone.

No unproved endpoint injectivity and no local connectivity of the
geometric boundary is used.

## 4. Borel leaf code and proper-path evaluation

### 4.1 The sublevel argument

For rational \(r\), lines 365--411 form the open union

\[
U_r=\bigcup_{t(\eta)<r}O_\eta .
\]

A leaf of value below \(r\) meets this union exactly when a strictly
larger leaf of value below \(r\) exists.  Consequently the sublevel
support differs from \(Z_\alpha\cap U_r\) by at most the unique maximal
leaf below the cut.  A proper leaf is closed in \(V\).  The sublevel is
therefore Borel even when the realized order has gaps, jumps, or a
nonclosed support.

Arsenin--Kunugui applies at lines 430--449 because each nonempty
vertical section of the swapped graph is one closed proper leaf and is
sigma-compact.  This proves that the realized coordinate set
\(L_\alpha\) is Borel; no pre-existing measurable leaf quotient is
assumed.

### 4.2 Compactified leaf field and endpoints

Lines 496--517 reduce every hyperspace hit predicate for \(K_s\) to a
projection whose section is an open subset of one proper leaf, hence
sigma-compact.  This proves the Borel compact-valued field.

The boundary relation has one- or two-point sections.  Finite-section
Lusin--Novikov therefore gives Borel endpoint maps at lines 519--539.
The arbitrary endpoint sorting is kept separate from the oriented arc
and winding tags, so it cannot alter the nesting order.

### 4.3 Evaluation

The compactified image is a compact arc when the endpoint limits are
distinct and a Jordan circle when they coincide.  This follows from
the continuous compactification of the original embedded proper path,
not from endpoint cardinality alone.

For compact arcs, lines 576--609 give a Borel initial-subarc relation.
The connected-compact witness is coded in a compact hyperspace, so its
existential projection is Borel by Arsenin--Kunugui.  The functional

\[
\Theta(C)=\sum_n2^{-n}(1+d(q_n,C))^{-1}
\]

is continuous and strictly increases under proper compact inclusion.
It consequently gives a continuous strictly increasing coordinate on
each arc, and Lusin--Novikov gives its jointly Borel inverse.

For the one-endpoint case, lines 679--715 select a second point and the
two complementary compact arcs Borelly, parameterize them, and
concatenate them.  The evaluation is injective on the open parameter
interval even though its endpoint values coincide.

Thus lines 718--731 establish the exact theorem clause: the evaluation
is jointly Borel, each fiber is the original proper embedded path, and
the product evaluation is injective on leaf code times \((0,1)\).

### 4.4 Order intervals

Each packet leaf space is a Borel subset of \(\mathbb R\).  Any initial
segment is empty, the whole packet, or its intersection with
\((-\infty,a)\) or \((-\infty,a]\); terminal segments are analogous.
They are Borel.  This justifies lines 761--762 even when the realized
order has gaps.

## 5. Filtered proper-component occurrences

Lines 836--1059 do not infer a Borel restriction relation merely from
analyticity of the immersion.

1. A countable inverse-branch atlas and rational seed times give a
   countable Borel germ relation (836--849).
2. A nested compactly-contained chart exhaustion makes continuation
   over every compact rational interval a countable union of finite
   Borel word predicates (863--884).
3. The maximal source interval endpoints are Borel infima and suprema
   of rational reachability predicates (886--899).
4. Original rational-time evaluation is converted to a full jointly
   Borel normalized evaluation by Borel rational approximation
   (899--930).
5. The positive-distance tail test is equivalent to properness
   (932--957).  Mere rational nonmembership is correctly rejected.
6. Rational Cauchy tests in the compact prime-end annulus give Borel
   endpoint convergence and Borel limit maps (959--979).
7. The two KKL marking filters are Borel because relative homotopy
   classes with endpoints moving inside fixed marked intervals are
   open; the endpoint-whisker argument proves that KKL's
   exact-endpoint subordination predicate is invariant on those
   classes (981--1036).
8. Duplicate germs are removed only when their maximal intervals
   overlap and their evaluations agree at an interior rational time.
   Path-lifting uniqueness then identifies the maximal lifts.  Natural
   enumeration indices provide a genuine least code (1038--1049).

Every maximal proper component contains an original rational time, so
the germ enumeration is exhaustive.  Distinct retained components are
disjoint: components over one leaf are distinct inverse-image
components, while an intersection over two different source leaves
would project to an intersection of those leaves.  Lusin--Souslin
therefore makes the geometric union Borel.

The construction never equates unbreakability with raw occurrence
cardinality.

## 6. Pushforward, pruning, and exact target-Wave typing

### 6.1 The measurable discard

The frozen proof does not try to make DL's literal outermost deletion
an order cut.  Instead:

\[
D_{\rm DL}\subset E_{\rm DL},\qquad
\mathcal W(E_{\rm DL})\le C_{\rm DL}+1
\]

by the independently audited width-envelope theorem.  Therefore

\[
B^\sharp_{\rm Bor}=B\setminus E_{\rm DL}
\subset B^\sharp_{\rm DL}.
\]

The covering is injective on the retained geometric union.  Restricting
the jointly Borel source evaluation and composing with the finite
cover gives an injective Borel target evaluation; Lusin--Souslin gives
a proper Borel target lamination.

At lines 1180--1182, the pronoun in “their injective evaluation” must
be read as the evaluation of the retained family
\(B^\sharp_{\rm Bor}\), whose covering injectivity was established in
line 1179.  No assertion that the covering is injective on the
super-discard \(E_{\rm DL}\) is used anywhere.  This is an editorial
antecedent issue, not a missing proof dependency.

### 6.2 Singleton A.14 and the common whole component

The repaired lines 1183--1197 have the correct two-part typing.

Fix a retained occurrence \(\beta\) with source leaf \(\gamma\).
The N1 source hypothesis says that the singleton Wave
\(\{\gamma\}\) is over \(I\), and the leaf belongs to the declared
unbreakable packet.  The singleton output is a lamination contained in
\(F_*\{\gamma\}^{\rm nbr}\).  KKL Proposition A.14 therefore applies
to this singleton pair and makes the output singleton a Wave over the
same target interval \(F_*I\).

Let \(C\) be the target ideal-boundary component containing \(F_*I\).
The connected singleton base lies in \(C\), so the output path is
subordinate to \(C\).  KKL 1853--1856 permits a whole ideal-boundary
component as a multi-interval.  Since all retained output leaves are
subordinate to this one \(C\), KKL 1874 makes their already-proved
proper Borel lamination an aggregate target Wave.

The conclusions are correctly separated:

- common-component subordination proves the aggregate Wave type; and
- singleton Proposition A.14 proves the leafwise direction
  \(R\uparrow F_*I\).

Lines 1192--1194 explicitly reject the false stronger conclusion that
the aggregate crest of \(R\) must contain \(F_*I\).

## 7. Unique successor and terminal saturation

A general pushed family is not assumed to be a lamination.  Lines
1067--1096 work only on the imported unbreakable source packet, where
all retained occurrences represent one untagged path.  The least
Borel occurrence supplies a path-space value without discarding
traversal information.

When that output belongs to an actual Wave \(R\), the injective compact
leaf code

\[
j_R:L_R\longrightarrow\mathcal K(\overline V^{\,\rm pe})
\]

has a Borel inverse on its Borel range.  Hence lines 1098--1128 produce
a correctly typed Borel map to the target *leaf code*.  Finite
iteration composes these leaf-code maps through the actual intermediate
Waves; no compact set is fed into a path restriction operator.

For a Borel terminal leaf set \(E\subset L_R\), the full source
saturation is exactly

\[
\phi_h^{-1}(E),
\]

not the ill-typed inverse image of \(E\) under a path-space map.  It is
Borel, and restriction of the original injective source evaluation
makes its geometric support Borel by Lusin--Souslin.  This includes
every source leaf with the terminal untagged output; it is not a
selector.

## 8. Hidden-assumption search

The complete frozen file was searched for the chartwise claims rejected
by the earlier audits.

No proof step:

- identifies DL's “outermost curves” with an initial or terminal
  interval in every arc chart;
- treats extremal width as a countably additive transverse measure;
- assumes one global order on an opposite-side fan;
- assumes a common univalent neighborhood from point-set injectivity;
- counts restriction occurrences to decide unbreakability; or
- assumes the aggregate target crest contains the leafwise target
  interval.

The only deck-order statement is the harmless per-arc-packet comparison
at lines 741--748.  The actual DL pruning at lines 1138--1202 uses the
metric envelope and does not consume that order comparison.

## 9. Promotion consequence

For this exact frozen object:

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION = proved
```

The status line at frozen line 1364 said “candidate proved, pending
integrated-file re-audit.”  This report discharges that stated audit
condition for the exact hash above.

It does not discharge the independent analytic proof and integration
audit required for:

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION.
```

All later gates remain open until their own complete proofs and audits
are supplied.
