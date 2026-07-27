# KKL stationary marked fixed-end pair certificate: direct source pass

Date: 2026-07-26  
Status: exact negative source-derivability result; no global obligation
promoted

## 1. Question and verdict

This note attacks
`KKL_STATIONARY_MARKED_FIXED_END_PAIR_CERTIFICATE` directly.  For every
proof-used stationary depth \(h\), the requested certificate consists
of

\[
\mathfrak C_h=
\left(
C_h^-,X_h^-,C_h^+,X_h^+,P_h,M_h
\right),
\tag{1.1}
\]

where:

- \(C_h^-\) selects a fixed, or measurably partitioned, source end over
  the original \(BL_0\) access at which the immersion is proper of
  degree one;
- \(X_h^-\) proves that the maximal lift from that end first exits at
  the declared \(L_0^h\) occurrence;
- \(C_h^+\) supplies the corresponding proper-degree-one remote source
  end;
- \(X_h^+\) proves that the reverse maximal lift first exits at the
  same \(L_0^h\) occurrence;
- \(P_h\) couples the two lifts to the same target leaf, transverse
  parameter, occurrence window, immersion sheet, and marked access;
  and
- \(M_h\) proves that both source paths survive the native fine and
  coarse filters and have the two asserted, noncolliding Wave outputs.

The binary verdict is:

\[
\boxed{
\text{The locked sources prove none of the six clauses for one common
marked pair.}
}
\tag{1.2}
\]

The first failed invocation hypothesis is \(C_h^-\).  KKL's fixed-end
immersion theorem requires a previously selected **topological end** at
which the immersion is proper of degree one.  The Wave source gives
only a marked \(BL_0\) interval/access and an existential restriction
ending at \(L_0^h\).  It does not construct an access-splitting
localization in which the \(BL_0\) access is a separate topological end,
nor prove proper degree one on such an end.

Even if \(C_h^-\) and \(C_h^+\) are added as hypotheses, the theorem can
produce two marginal lift-until-exit WADs whose exits are different.
It does not establish \(X_h^-=X_h^+\) at the occurrence level, hence
does not establish \(P_h\) or \(M_h\).

This is a source-derivability verdict, not a quadratic-dynamical
counterexample.  The exact counterconfiguration in Section 9 shows
that the proposed inference is false for finite-topology holomorphic
immersions even when both starting ends are proper of degree one.

`KKL_STATIONARY_MARKED_FIXED_END_PAIR_CERTIFICATE`,
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR`, VAAPC-I, UPTCR, and MLC
remain open.

## 2. Locked sources

All line numbers below are one-based physical line numbers in the
following local files.

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5

.tmp_wave_audit/not-all-good2.tex
SHA-256 B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01

.tmp_kl06_source/wad.tex
SHA-256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580

.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228

.tmp_kl06_source/appendix.tex
SHA-256 EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3
```

For reproducibility, the LF-normalized hashes of the two decisive
source excerpts, with one final LF included, are:

```text
waves-with-Misha.tex lines 1536--1605
ef9163d82e45aa89d77aa2c488de94b0cd09825eb322f541dfb095bb2b81d1d6

not-all-good2.tex lines 514--545
1948d540c52bc267368fede4e127dcf6b6f8433abb442b615709e102b0cf45cb
```

The controlling ranges are:

| source | lines | content used |
|---|---:|---|
| `waves-with-Misha.tex` | 439--461 | pseudo-quadratic-like maps and finite pullback iterates |
| same | 512--544 | Hubbard tree and the non-locally-connected combinatorial-model paragraph |
| same | 838--866 | \(BL_j\) as marked Carathéodory multi-intervals |
| same | 1225--1274 | tree-complement covering/immersion and combinatorial action |
| same | 1355--1358 | native singleton-path definition of unbreakability |
| same | 1423--1494 | one-step breaking decomposition |
| same | 1534--1605 | critical-end stationary argument and disputed alignment |
| same | 1844--1875 | ideal boundary, marked intervals, proper paths, and Waves |
| same | 1901--1914 | WAD norm and validity |
| same | 2065--2108 | covering pushforward, immersion restriction, filters, and itineraries |
| same | 2128--2168 | \(F_*=f_*\iota^*\), Wave pushforward, and breaking |
| `not-all-good2.tex` | 310--347 | subsurface localization and an actual proper-end statement |
| same | 514--545 | fixed-end immersion decomposition |
| `wad.tex` | 8--46 | finite topology and topological ends |
| same | 141--160 | valid WADs as Borel proper laminations |
| `psiql2.tex` | 60--78, 140--178 | embedded neighborhood of the filled set and degree-one annular boundary |
| same | 216--301, 350--416 | pullback properties and iterated pseudo-polynomial-like maps |
| `appendix.tex` | 12--68 | extremal width and overflow laws; no marked-pair construction |

## 3. Frozen source objects and the type distinction

Put

\[
N=b+3,\qquad m=N-1=b+2.
\tag{3.1}
\]

The Wave proof defines \(A_n\) only for \(0\le n<N\) at master lines
1547--1548.  For the line-1603 use, put

\[
h=n+1,\qquad n\ge b.
\tag{3.2}
\]

Thus the source's two-portion assertion is a late-horizon assertion.
It is not a theorem for every \(1\le h\le b+2\).  At the terminal
alignment the two relevant values are \(h=b+1\) and \(h=b+2\).

Let

\[
T^h=F^{-h}(T),\qquad
V_h=U^h\setminus T^h,\qquad
V=U\setminus T,\qquad
i_h=\iota_h:V_h\longrightarrow V.
\tag{3.3}
\]

Only the associated inclusion identification used by the source is
intended in (3.3).  No inverse branch of \(i_h\) is assumed.

There are two different boundary objects:

1. KL06 `wad.tex` lines 35--46 use the finite set
   \(\mathcal E(V_h)\) of **topological ends** of the finite-topology
   surface; and
2. the Wave source lines 1844--1875 refines an ideal boundary component
   into marked intervals, multi-intervals, endpoints, and accesses.
   In particular, \(BL_0\) is a marked multi-interval, not by definition
   a separate element of \(\mathcal E(V)\).

The fixed-end theorem in `not-all-good2.tex` lines 514--545 is typed by
the first object.  It assumes a set \(E'\subset\mathcal E(V_h)\) on
which \(i_h\) is already proper of degree one.  It has no hypothesis or
conclusion phrased for one marked subinterval of a nonproper
topological end.

The Wave source's “end-proper on an interval” at master lines
2157--2159 is a different, marking-relative notion: it means
properness on the end-intervals of a pulled multi-interval.  It does
not convert that interval into a KL06 topological end and does not
state degree one there.

This type distinction is essential in the clause audit.

## 4. What the decisive source lines actually say

### 4.1 The Wave passage

Master line 1600 has the logical form

\[
\forall\alpha\in A_h\quad
\exists\theta_\alpha\in i_h^*\alpha
\quad
\left[
\theta_\alpha\text{ has an endpoint at the marked }L_0^h
\text{ locus}
\right].
\tag{4.1}
\]

Accepting line 1600 as written, (4.1) supplies one existential
restriction.  It does not state:

- one source topological end from which \(\theta_\alpha\) begins;
- properness or end degree of \(i_h\) there;
- a prime-end access, sheet, or occurrence window;
- that \(\theta_\alpha\) is the maximal lift from a prescribed end;
- that the first exit of that maximal lift is the declared occurrence;
- a Borel choice \(\alpha\mapsto\theta_\alpha\); or
- survival under master lines 2096--2097.

Master line 1601 adds only that the other target endpoint is somewhere
in

\[
\partial_{\rm C}T\setminus BL_0.
\tag{4.2}
\]

It does not select a remote source end over that set.

Master line 1603 is not a proof of the missing data.  It asserts that,
if the leaf avoids \(K_0^n\), then the two topological portions

\[
BL_0\rightsquigarrow L_0^{n+1},
\qquad
L_0^{n+1}\rightsquigarrow
\partial_{\rm C}T\setminus BL_0
\tag{4.3}
\]

“would both pushforward to waves,” and then invokes breaking.  But
native breaking is defined at lines 1355 and 2161 by the complete
**filtered** \(F_*\)-image not being one path.  Before that
contradiction is available, (4.3) must already have been realized by
two full retained paths with two distinct path outputs.  That is
precisely part of \(X_h^\pm,P_h,M_h\); line 1603 assumes rather than
derives it.

### 4.2 The fixed-end theorem

`not-all-good2.tex` lines 514--518 assume:

\[
\begin{array}{l}
i:V'\to V\text{ is a finite-topology holomorphic immersion},\\
E'\subset\mathcal E(V')\text{ is already selected},\\
i\text{ is proper of degree one at every }e'\in E',\\
Y\text{ is a valid target WAD, and every target arc meets }i(E').
\end{array}
\tag{4.4}
\]

Only after (4.4) does the theorem lift a realizing target foliation
from the prescribed source ends until exit.  The output is the
alternative:

\[
\begin{array}{ll}
\text{full:}&
\text{both source endpoints lie in }E'
\text{ and the source arc maps to the complete target arc};\\
\text{exit:}&
\text{one source endpoint lies in }E'
\text{ and the other source endpoint does not.}
\end{array}
\tag{4.5}
\]

The proof at lines 535--544 subdivides the target foliation first by
target homotopy class and then by source homotopy class.  It does not
label the other source end by a prescribed tree access.  It does not
couple two applications made with opposite orientations.

The theorem is therefore useful only after \(C_h^\pm\) have been
constructed.  It cannot prove its own proper-degree-one starting-end
hypothesis.

### 4.3 The source contains the missing kind of localization elsewhere

`not-all-good2.tex` lines 310--347 localize a different component
surface and explicitly state that the resulting immersion is proper
on ends corresponding to selected components of \(\widehat{\mathcal
K}_I\).  This confirms the required proof pattern:

1. construct the localization;
2. identify its actual topological ends; and
3. prove properness there.

No analogous localization of the \(BL_0\) and remote marked accesses
is constructed in master lines 1534--1605.

## 5. The deep \(L_0^h\) occurrence cannot be the starting end

For \(h\ge b\), master lines 1598 and 1602 place the proof-used deep
\(L_0^h\) locus away from the original tree \(T\).  Under the
associated inclusion identification it is a compact locus in

\[
V=U\setminus T.
\tag{5.1}
\]

Take the proper restriction supplied by line 1600 and a sequence on
its tail converging to the declared \(L_0^h\) occurrence.  The sequence
leaves every compact subset of \(V_h\), while its \(i_h\)-image
accumulates on the compact locus \(L_0^h\Subset V\).  A compact
neighborhood of that locus in \(V\) therefore contains the image of a
tail.  Hence

\[
i_h\text{ is not proper at the declared deep occurrence.}
\tag{5.2}
\]

This sequence criterion uses no local connectivity of the carrier.
The proof-used path itself supplies the access sequence.

Consequently the reverse-oriented fixed-end theorem may not be started
at \(L_0^h\).  It must start at an independently certified remote end,
which is exactly why \(C_h^+\) and \(X_h^+\) are separate clauses.

There is a second consequence.  On the unlocalized tree-complement,
the source does not assert that the original \(BL_0\) access is a
different KL06 topological end from the nonproper deep accesses.
Thus local embedding near the filled set does not by itself supply
\(C_h^-\).  The missing object is an access-separated localization or
collar surface on which the selected access becomes an actual end and
the induced map is proved proper of degree one.

## 6. Clause-by-clause audit

### 6.1 \(C_h^-\): not proved; first failed hypothesis

The potentially relevant positive source statements are:

1. master line 1241: the one-step immersion is injective near the
   filled set;
2. lines 1263--1271: the one-step action is combinatorial/end-proper
   in the marked-interval sense; and
3. `psiql2.tex` lines 60--78 and 140--178: a pseudo-polynomial-like
   immersion has an embedded filled-set neighborhood and degree one
   on the associated annular filled-set boundary.

None proves \(C_h^-\).  The required surface is
\(V_h=U^h\setminus T^h\), not the filled-set annulus.  The original
\(BL_0\) object is a marked access inside the tree-side ideal boundary,
not a selected KL06 topological end.  The tree pullback contains
additional branches; approaching one of those branches may leave
compacta in \(V_h\) while the immersion image remains in a compact
subset of \(V\).  Thus properness at a local \(BL_0\) collar cannot be
promoted to properness of the entire unlocalized tree end.

What is missing is the theorem:

> Construct a finite-topology access localization \(V_{h,-}\) and an
> induced immersion \(i_{h,-}:V_{h,-}\to V_-\) for which the selected
> \(BL_0\) access is one topological end \(e^-_h\), prove
> \(i_{h,-}\) proper of degree one at \(e^-_h\), and prove that the
> proof-used Wave restricts width-faithfully to this localization.

No locked line proves this statement.  Therefore the hypotheses of
`thm:immer-decomp` fail before its lift construction begins.

### 6.2 \(X_h^-\): not proved

Grant \(C_h^-\) temporarily.  Line 1600 gives

\[
\exists\theta_\alpha
\quad
\partial\theta_\alpha\cap L_0^h\ne\varnothing.
\tag{6.1}
\]

The desired assertion is stronger:

\[
\operatorname{Exit}
\left(
\operatorname{MaxLift}_{i_{h,-}}
(\alpha,e^-_h)
\right)
=\xi_h(\alpha),
\tag{6.2}
\]

where \(\xi_h(\alpha)\) is the complete declared occurrence, including
the access, sheet, and nested window.

Existence (6.1) does not imply equality (6.2).  The existential
restriction may:

- begin at another source access;
- lie on another immersion sheet;
- reach another occurrence of the same coarse component;
- be a strict subpath of a different maximal lift; or
- coexist with an earlier exit at another attached branch.

Master itinerary lines 2099--2108 expressly allow nonproper
intermediate intervals, adjacent intervals, and two fine intervals in
one pulled coarse interval.  They do not exclude any of these
possibilities.  Hence \(X_h^-\) is not proved.

### 6.3 \(C_h^+\): not proved

The remote target endpoint is only localized to the set (4.2).
Neither line 1600 nor line 1601 supplies:

- a source topological end over that endpoint;
- a proper-degree-one extension there;
- a fixed finite list or Borel candidate relation of eligible ends;
- its marked access and immersion sheet; or
- a width-faithful measurable leaf partition.

Master Proposition `improper intervals`, lines 1279--1286, proves
properness only on the specified translation-region multi-interval
\(BL_{[b,q-b-2]}\).  The remote endpoint in (4.2) is not asserted to
lie there.  The general combinatorial-action statement again gives
only marked end-interval properness, not a KL06 topological end of
degree one.

Thus \(C_h^+\) is not proved.

### 6.4 \(X_h^+\): not proved

Grant \(C_h^+\).  Reverse the target orientation and apply the
fixed-end theorem from the certified remote end.  The theorem follows
the lift until its first source exit, but it does not identify that
exit.  It may be another attached component or another access of the
same component.

By Section 5, one cannot instead start the theorem at the deep
\(L_0^h\) occurrence.  Therefore an independent equality

\[
\operatorname{Exit}
\left(
\operatorname{MaxLift}_{i_{h,+}}
(\alpha,e^+_h(\alpha))
\right)
=\xi_h(\alpha)
\tag{6.3}
\]

is required.  No locked source line proves (6.3), so \(X_h^+\) is not
proved.

### 6.5 \(P_h\): not proved

Suppose, beyond the source, that separate applications produce
\(\theta^-_\alpha\) and \(\theta^+_\alpha\).  The required diagonal
coupling is

\[
\begin{aligned}
\operatorname{target}(\theta^-_\alpha)
&=\operatorname{target}(\theta^+_\alpha)=\alpha,\\
\operatorname{exitcode}(\theta^-_\alpha)
&=\operatorname{exitcode}(\theta^+_\alpha)=\xi_h(\alpha),
\end{aligned}
\tag{6.4}
\]

with equality of transverse parameter, actual occurrence window,
sheet, access, and all future-compatibility data.

Two marginal WAD decompositions do not imply (6.4).  The fixed-end
proof records target and source homotopy classes, but it does not
retain a joint occurrence variable for two independent orientations.
Even a common Borel partition by starting-end pair proves only that
both constructions use the same target leaf.  It does not prove that
their exit codes agree.

Coarse equality of the \(L_0^h\) component label is insufficient:
different prime-end accesses or repeated occurrences of that component
remain different marked exits.  Thus \(P_h\) is not proved.

### 6.6 \(M_h\): not proved

For each of the two source portions, \(M_h\) requires:

1. a full proper path in the exact stage surface;
2. endpoints in the proof-used fine marking;
3. non-subordination to one pulled coarse interval;
4. the declared covering endpoint degree;
5. a complete covering image which is a Wave with the stated base and
   crest; and
6. distinct retained path outputs when the source invokes breaking.

Master lines 2096--2097 explicitly discard restrictions which fail
items 2 or 3.  Proposition `itineraries`, lines 2099--2108, is an
alternative list and does not prove survival.  The covering statement
at lines 2065--2072 says that an already proper source path has a
proper image; it does not prove items 1--3 or Wave typing.

Finally, native \(F_*\) is set-valued before taking its untagged path
image.  Two distinct retained source paths can have the same covering
image.  Without a marked noncollision theorem, two source portions do
not force the complete \(F_*^h\)-image to contain two distinct paths.
Line 1603 supplies no such theorem.

Therefore the phrase “would both pushforward to waves” is exactly the
unsupported \(M_h\) step, and \(M_h\) is not proved.

## 7. Quantifier and indexing audit

The source implication needed for one incoming role is

\[
\begin{split}
&\forall\alpha\in\Lambda_h\quad
\exists e^-_h(\alpha),\theta^-_\alpha\\
&\quad
\left[
e^-_h(\alpha)\text{ is eligible},\
\theta^-_\alpha=
\operatorname{MaxLift}(\alpha,e^-_h(\alpha)),\
\operatorname{Exit}(\theta^-_\alpha)=\xi_h(\alpha)
\right].
\end{split}
\tag{7.1}
\]

The pair theorem needs the same statement for \(+\), together with the
diagonal equality of exit variables and a Borel, width-faithful joint
selection.  Line 1600 gives only the projection

\[
\forall\alpha\quad\exists\theta_\alpha
\left[
\partial\theta_\alpha\cap L_0^h\ne\varnothing
\right].
\tag{7.2}
\]

Projection (7.2) contains no selected end or diagonal coupling and
cannot imply (7.1).

There are also two literal indexing defects:

1. \(A_n\) is defined at line 1548 only for \(0<n<N\), but line 1605
   invokes undefined \(A_N\), while Lemma 1591 concerns \(A_{N-1}\).
   Replacing \(A_N\) by \(A_{N-1}\) is the evident index repair, but
   does not prove any clause of (1.1).
2. Line 1603 applies only when \(n\ge b\).  It cannot by itself prove
   an all-route-horizon certificate for \(1\le h\le b+2\).

## 8. No-local-connectivity audit

Master lines 516--520 first define the physical Hubbard tree under a
local-connectivity assumption.  Lines 542--543 then state that in the
non-locally-connected case the combinatorial model has analogous
objects and that these can be lifted by the model projection.

Those two lines do not prove:

- a prime-end extension of the physical iterated immersion;
- injectivity on the complete marked access set;
- preservation of cyclic order for the two selected accesses;
- equality of physical and combinatorial occurrence windows; or
- proper/end-proper relative-cover behavior at those accesses.

Accordingly no clause above is inferred from local connectivity.
More strongly, the counterconfiguration below is made from annuli and
Jordan obstacles, so the failure of the abstract inference already
occurs in a locally connected finite-topology setting.

## 9. Exact counterconfiguration to the two-orientation inference

This is a countermodel to the logical inference

\[
C_h^-\wedge C_h^+
\Longrightarrow
X_h^-\wedge X_h^+\wedge P_h.
\tag{9.1}
\]

It is not claimed to be an actual KKL dynamical block.

Let

\[
V=\{1<|z|<4\}.
\tag{9.2}
\]

Choose a narrow radial product rectangle

\[
R=\{1<|z|<4,\ |\arg z|<\varepsilon\}\Subset_{\rm sides} V
\tag{9.3}
\]

and two disjoint closed Jordan disks \(Q_1,Q_2\Subset V\) which cross
the full angular width of \(R\), in that radial order.  Put

\[
V'=V\setminus(Q_1\cup Q_2),
\qquad
i:V'\hookrightarrow V.
\tag{9.4}
\]

Then:

1. \(V'\) and \(V\) have finite topology.
2. \(i\) is a holomorphic immersion.
3. Near the inner and outer annular ends, \(i\) is the identity.
   Hence it is proper of degree one at both starting ends.
4. The radial product foliation of \(R\) is a Borel proper lamination
   and induces a valid target WAD \(Y\).

Orient a target leaf from the inner annular end.  Its maximal
\(i\)-lift exits at the first obstacle \(Q_1\).  Orient the same leaf
from the outer annular end.  Its reverse maximal lift exits at \(Q_2\).
Thus both fixed-end hypotheses hold, and `thm:immer-decomp` applies in
both orientations, but

\[
\operatorname{Exit}(\theta^-)=Q_1
\ne
Q_2=\operatorname{Exit}(\theta^+).
\tag{9.5}
\]

There is no common occurrence and no concatenated source pair.

If a coarse quotient assigns \(Q_1\) and \(Q_2\) the same “deep
attachment” label, (9.5) also proves that coarse label equality does
not establish \(P_h\).  Alternatively, using one Jordan obstacle,
the two orientations meet its two different boundary accesses.  They
then have the same component label but different marked access codes.

This counterconfiguration satisfies every abstract hypothesis of the
fixed-end theorem.  The missing same-exit conclusion must therefore be
an additional geometric incidence theorem; it cannot be extracted from
the WAD theorem by formal manipulation.

## 10. Additional source defect: the later degree-one sentence

Master lines 1592--1593 also state that \(f^{N-1}\) has degree one on
the selected component \(K\), but lines 1596--1605 do not derive this
claim.  Under the canonical graph realization \(K=K_0^b\), the selected
pullback arrows \(K_0^s\to K_0^{s-1}\) are univalent, while the later
itinerary crosses the central restriction

\[
K_0^0\longrightarrow F(K_0^0)
\tag{10.1}
\]

containing the unique critical point.  The resulting total degree is
two, not one.  This is the independently proved project correction
`KKL_STATIONARY_DEGREE_TWO_CORRECTION`.

The degree error occurs after the pair-construction gap and is not the
first obstruction to (1.1), but it prevents treating the rest of the
printed alignment lemma as a completed substitute.

## 11. Exact replacement hypothesis

The first missing theorem is not another width estimate.  It is the
following access-localized, jointly marked lift theorem.

> **Marked fixed-end diagonal lift theorem.**  
> For each proof-used depth \(h\), construct access localizations
> \(V_{h,-},V_{h,+}\) and a conull standard Borel target transversal
> \((\Lambda_h,\nu_h)\) such that:
>
> 1. the selected \(BL_0\) and remote accesses become actual source
>    topological ends;
> 2. the induced immersions are proper of degree one at those ends;
> 3. the two oriented maximal lifts exist measurably;
> 4. both first-exit maps equal one common complete occurrence code
>    \(\xi_h:\Lambda_h\to\Xi_h\);
> 5. the two paths survive every fine/coarse marking filter;
> 6. their covering images are the asserted distinct Wave paths; and
> 7. the localized transverse measure is the native width measure used
>    later in the stationary argument.

The fixed-end immersion theorem may then be applied on the joint
partition.  It supplies the paired unmarked WAD full/exit split, but
not items 1--7.

If the diagonal equality in item 4 fails, the first countercertificate
must record

\[
\left(
\alpha,\ e_h^-,e_h^+,\ 
\xi_h^-(\alpha),\xi_h^+(\alpha),\
\text{both sheets, accesses, windows, filters, and outputs}
\right)
\tag{11.1}
\]

at the first leaf with
\(\xi_h^-(\alpha)\ne\xi_h^+(\alpha)\).  The replacement response state
must retain the two-occurrence relation; it may not quotient the exits
to one coarse component label.

## 12. Final result

The direct source pass ends at the first invocation boundary:

\[
\boxed{
\begin{array}{c}
\text{line 1600 supplies an existential marked restriction;}\\
\text{the fixed-end theorem requires a supplied proper-degree-one
topological end;}\\
\text{no access localization identifies the former with the latter.}
\end{array}
}
\tag{12.1}
\]

Conditionally adding the starting ends still leaves two independent
exit maps, and the annular two-obstacle example proves they need not
agree.  Therefore no source-checkable proof of
\(\mathfrak C_h\) exists in the locked passages.

`KKL_STATIONARY_MARKED_FIXED_END_PAIR_CERTIFICATE` must remain open.
The next analytic action is to prove the marked fixed-end diagonal
lift theorem above or instantiate the first unequal-exit certificate
(11.1) on an actual stationary KKL block.
