# Gate N1 audit: degree-two singleton directionalization

Date: 2026-07-26

Scope: only the finite-circle step used in Lemma 4.1 of
`kkl_stationary_relative_wave_continuation.md`.

## 1. Verdict

The required existential statement is valid:

> If the complete retained restriction of one unbreakable source leaf is
> an aggregate KKL Wave whose crest contains a connected marked interval
> \(J\), then at least one retained restriction leaf is individually
> above \(J\) in the sense of Dudko--Lyubich.

In the native stationary setting there are at most two retained
restriction leaves.  If there are two, they are the two lifts of the same
actual output path under the degree-two annular covering.  This special
fact is compatible with, but is not needed for, the cyclic-order
existence argument.

The stronger assertion that *every* retained restriction leaf is above
\(J\) is false in general.  The proof below establishes exactly the
existential assertion required for domination; it does not make that
stronger claim.

The conclusion is conditional on the preceding KKL input that the
complete retained restriction really is an aggregate Wave over \(J\).
This audit does not re-prove that separate input and does not promote
Gate N1, VAAPC-I, UPTCR, or MLC.

## 2. Source-locked definitions

The locked KKL source is
`research/mlc_unified/.tmp_wave_audit/waves-with-Misha.tex`, SHA-256

```text
AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The proof uses:

- lines 406: paths are considered up to reparameterization;
- 1850--1859: ideal intervals and connected open multi-intervals;
- 1867--1875: subordination, Wave base, aggregate ends, and aggregate
  crest;
- 2065--2072: covering pushforward;
- 2081--2097: immersion restriction and the two retained-path filters;
- 2128--2142: \(F_*=f_*\iota^*\);
- 1355--1358 and 2161--2162: an unbreakable path has a single
  \(F_*\)-output path.

The locked DL source is
`research/mlc_unified/.tmp_wave_audit/dl23/Feigen.tex`, SHA-256

```text
EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF
```

DL line 2813 says that a leaf is above \(J\) when its endpoints are
outside \(J\) and the bounded component cut off by the leaf contains
\(J\) on its Carathéodory boundary.

All circle statements below take place on the inner prime-end boundary
of the closed-annulus compactification.  They do not use local
connectivity of the underlying planar carrier.

## 3. The marked-circle lemma

### Lemma 3.1 (aggregate crest has a witnessing leaf)

Let \(A\) be a closed annulus with an ideal marking on one boundary
circle \(C\).  Let \(L\) be a nonempty lamination of boundary-parallel
proper paths with both endpoints on \(C\).  Let

\[
 B_L,\qquad E_L^0,\qquad E_L^1,\qquad
 K_L=B_L\setminus(E_L^0\cup E_L^1)
\]

be its KKL base, two aggregate ends, and crest.  If a connected
multi-interval \(J\) satisfies \(J\subset K_L\), then some
\(\beta\in L\) is individually DL-above \(J\).

#### Proof

For a leaf \(\beta\), write \(P_\beta,Q_\beta\) for the two marked
intervals containing its endpoints.  Since \(E_L^0,E_L^1\) are
aggregate ends, label the endpoints so that

\[
 P_\beta\subset E_L^0,\qquad Q_\beta\subset E_L^1.
\tag{3.1}
\]

In particular,

\[
 (P_\beta\cup Q_\beta)\cap J=\varnothing
\tag{3.2}
\]

because \(J\subset K_L\).

The prime-end compactification is a closed annulus.  A simple proper
path with both endpoints on the same boundary circle cuts off one disk.
The intersection of the Carathéodory boundary of that disk with \(C\)
is one of the two cyclic boundary arcs from the first endpoint to the
second.  Denote that boundary-side arc by \(a_\beta\).  The singleton
KKL base \(B_\beta\) is the least marked multi-interval containing
\(a_\beta\), including the two endpoint intervals.

Remove the two endpoint intervals \(P_\beta,Q_\beta\) from \(C\).
Their complement has at most two cyclic between-end components.
Because \(J\) is connected and satisfies (3.2), it lies in one such
component.  The boundary-side arc \(a_\beta\) uses exactly one of the
two cyclic routes between \(P_\beta\) and \(Q_\beta\).  Consequently
there is a dichotomy:

\[
 J\subset B_\beta\setminus(P_\beta\cup Q_\beta)
 \quad\text{or}\quad
 B_\beta\cap J=\varnothing.
\tag{3.3}
\]

There is no partial-overlap case.  Indeed, a connected route between
the two endpoint intervals either traverses the entire between-end
component containing \(J\), or traverses the other component.

The first alternative in (3.3) says exactly that the bounded component
cut off by \(\beta\) has every prime end of \(J\) on its Carathéodory
boundary.  Together with (3.2), this is the DL-above condition.

Assume for contradiction that no leaf is DL-above \(J\).  Then (3.3)
gives

\[
 B_\beta\cap J=\varnothing
 \qquad(\beta\in L).
\tag{3.4}
\]

Choose one ideal-marking interval \(Q\) contained in \(J\).  Such a
\(Q\) exists because a nonempty open multi-interval is a union of
marking intervals and marking endpoints.  Equation (3.4) says that
every singleton base is disjoint from \(Q\).  A singleton base is an
open multi-interval made from whole marking intervals and marking
endpoints.  It cannot contain either endpoint of \(\overline Q\):
openness at such an endpoint would force the base to contain an
adjacent open part and hence the whole marking interval \(Q\).
Therefore

\[
 B_\beta\subset C\setminus\overline Q
 \qquad(\beta\in L).
\tag{3.5}
\]

The set \(C\setminus\overline Q\) is a proper connected open
multi-interval made from the remaining marking intervals and endpoints.
Since each leaf is subordinate to its singleton base, (3.5) and KKL's
definition at 1867--1868 make every leaf subordinate to this one
proper multi-interval.  By the defining minimality of the aggregate
base at KKL 1874--1875,

\[
 B_L\subset C\setminus\overline Q.
\tag{3.6}
\]

But \(Q\subset J\subset K_L\subset B_L\), contradicting (3.6).
Therefore at least one leaf is DL-above \(J\). \(\square\)

### Audit note 3.2

Finiteness is not needed in Lemma 3.1.  In particular, the sentence
“finiteness rules out an accumulating sequence” in the previous draft
is unnecessary.  The proper common base
\(C\setminus\overline Q\) gives a direct contradiction even for an
infinite family.

## 4. Why the singleton packet has at most two leaves

### Lemma 4.1 (two-sheet bound and deck pairing)

Let

\[
 f:A'\longrightarrow A
\]

be the connected unbranched degree-two annular cover in the stationary
KKL complement.  Fix a source path \(\gamma\) that is unbreakable for
one step, and let \(L_\gamma\) be its complete restriction by
\(\iota\), after the two filters at KKL 2096--2097.  Then:

1. every \(\beta\in L_\gamma\) is a lift under \(f\) of the same actual
   proper path \(\delta=F_*\gamma\);
2. \(|L_\gamma|\le 2\);
3. if equality holds, the two leaves are exchanged by the nontrivial
   deck involution of \(f\).

#### Proof

By KKL 2128--2142,

\[
 F_*\gamma=f_*(\iota^*\gamma),
\tag{4.1}
\]

where \(\iota^*\gamma\) already means the retained path family after
the filters at 2096--2097.  By unbreakability at KKL 1355 or
2161--2162, the right side of (4.1) is a single path; call it
\(\delta\).  Thus

\[
 f\circ\beta=\delta
\tag{4.2}
\]

up to the path reparameterization convention at KKL line 406, for
every retained \(\beta\).

Choose one interior parameter value \(t_0\in(0,1)\).  A lift of
\(\delta\) is uniquely determined by its value over
\(\delta(t_0)\).  The fiber \(f^{-1}(\delta(t_0))\) has exactly two
points.  Therefore evaluation at \(t_0\) injects the set of distinct
lift paths into a two-point set, proving \(|L_\gamma|\le2\).

A connected two-sheeted cover is regular.  Its nonidentity deck
transformation \(\tau\) exchanges the two points of every fiber.
Path-lifting uniqueness then gives

\[
 \beta_1=\tau\circ\beta_0
\]

when both lifts occur. \(\square\)

## 5. Application to the disputed step

Assume the input used in the main Lemma 4.1:

\[
 J=\iota^*I
 \subset\operatorname{crest}_{\rm KKL}(L_\gamma),
\tag{5.1}
\]

where \(L_\gamma\) is the complete filtered restriction of the
singleton unbreakable source leaf \(\gamma\).

Lemma 4.1 shows that \(L_\gamma\) contains one or two paths.  Lemma 3.1
then supplies

\[
 \beta\in L_\gamma
 \quad\text{with}\quad
 \beta\text{ DL-above }J.
\tag{5.2}
\]

Thus the family obtained by retaining *all* occurrences satisfying the
leafwise predicate “DL-above \(J\)” has at least one occurrence over
each source leaf.  This is the exact fact needed to invoke KKL
domination at 2086--2090.

If two deck-paired lifts occur, they may take different cyclic routes.
That only shows why one must not claim that the whole restriction is
leafwise directed.  It does not defeat (5.2): if neither lift used the
route containing \(J\), both would be subordinate to the same proper
multi-interval \(C\setminus\overline Q\), contradicting (5.1).

## 6. Adversarial checks

1. **Two opposite cyclic routes.** If the two lifts use opposite
   routes, an aggregate full-circle base can occur.  Each nonempty
   aggregate crest component is nevertheless traversed by at least one
   lift.  The claim is existential, not universal.
2. **Both lifts use the route away from \(J\).** Then
   \(C\setminus\overline Q\), for one marking interval
   \(Q\subset J\), is a common proper base.  This contradicts the
   aggregate-crest hypothesis.
3. **Partial intersection with \(J\).** This would require one of the
   two endpoint intervals to enter \(J\).  Aggregate-end disjointness
   forbids it.
4. **Whole-circle singleton base.** Its singleton crest contains every
   marked interval disjoint from its two endpoint intervals, so it is
   already a witnessing leaf.
5. **Non-locally-connected carrier.** The proof is entirely on the
   prime-end circle of the annular compactification.
6. **Filtered subset of the two lifts.** One retained lift is the
   singleton case.  Two retained lifts are deck-paired.  Rejected
   topological lifts are not counted.
7. **More than two immersion components.** They cannot all survive
   unbreakability with the same exact output path: evaluation in a
   degree-two covering fiber bounds the surviving lifts by two.
8. **Infinite-family accumulation.** It is irrelevant; Lemma 3.1
   produces a proper common marked base directly.

## 7. Exact status

| assertion | result |
|---|---|
| aggregate crest over \(J\) implies at least one leafwise witness | proved |
| one unbreakable singleton has at most two retained output lifts | proved |
| two retained lifts are deck-paired | proved |
| every retained lift is above \(J\) | false in general and not used |
| KKL 1477 supplies the aggregate premise for the chosen \(J\) | outside this audit |
| full Gate N1 | not promoted here |
| VAAPC-I / UPTCR / MLC | open |
