# Gate N1: two-direction common-crest repair of the stationary continuation

> **Superseded working note (2026-07-26).**  Do not cite this file as
> the final N1 argument.  The source-locked corrected proof is
> `kkl_stationary_relative_wave_continuation.md`.  In particular, the
> full KKL restriction Wave need not be leafwise DL-directed above its
> aggregate crest, coefficient-one width transfer is unavailable, and
> unconditional Borel maximality is not proved.  The corrected proof
> uses the leafwise-directed occurrence subpacket \(B_I(S)\), the
> degree-two full-lift charge, explicit saturated cores, and records
> `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` as the remaining formal
> interface.

## 1. Scope and exact verdict

This note addresses only the stationary KKL subproblem

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION
```

for the native Hubbard-tree complement in KKL's Wave section.  It does
not use the false broad coefficient-one Wave assertion.

There are two logically distinct conclusions.

1. **Native analytic conclusion.**  In the KL06 category of arbitrary
   path families, the two-direction construction below proves an
   additive stationary continuation
   \[
      \mathcal W(A_n\setminus A_{n+1})\le C_b,
      \qquad 0\le n<N-1,\qquad N=b+3,                    \tag{1.1}
   \]
   for a legitimate choice of the inclusion-maximal source families
   \(A_{n+1}\).  The construction uses a protected common-crest core
   inside each \(A_n\).  The core, rather than arbitrary leaves added by
   maximal extension, is propagated to the next stage.
2. **Extra formal-interface caveat.**  KL06 defines extremal width for
   an arbitrary path family and KKL does not assume that an arbitrary
   input Wave has a standard-Borel leaf set.  A Zorn maximal extension
   also need not be Borel.  Therefore the project-added requirement
   that every \(A_n\) be a Borel maximal family does not follow from the
   locked sources.  One may either:

   - use the explicitly constructed protected cores as the stationary
     sequence (maximality is not used in the N1 width argument);
     or
   - add a separate Borel regularization/maximal-extension theorem.

Thus (1.1) is proved as a source-valid extremal-width statement,
subject to the ordered prime-end limb fact proved in Lemma 4.0.  A
ledger entry whose statement additionally insists on Borel maximality
must retain that presentational clause as open until it is separately
discharged.

Nothing in this note addresses VAAPC-I, UPTCR, rigidity, parameter
fibers, or MLC.  Those obligations remain open.

## 2. Locked sources and source clauses

The source files and SHA-256 values are:

```text
KKL, waves-with-Misha.tex:
AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5

Dudko--Lyubich, Feigen.tex:
EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF

KL06, appendix.tex:
EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3
```

The imported clauses are:

| clause | locked location |
|---|---|
| limbs \(BL_j\) and \(\ell(BL_j)\le 6b\) | KKL 838--842 |
| \(F_*BL_j=BL_{j+1}\) for \(j\ne0\), and \(F_*BL_0=\partial_{\rm C}T\) | KKL 1274 |
| \(F_*\) acts combinatorially | KKL 1254--1271 |
| definition of \(r\)-unbreakability | KKL 1355--1358 |
| pushing controllability | KKL 1399--1417 |
| full restriction of an unbreakable Wave over a pulled crest, with domination | KKL 1477--1478, 2081--2090 |
| away-from-critical Shift estimate | KKL 1524--1532 and 2171--2178 |
| stationary horizon \(N=b+3\) | KKL 1547--1559 |
| Wave, base, ends, and crest | KKL 1844--1875 |
| degree-two covering on complements and filtered immersion restriction | KKL 2062--2142 |
| nonbreaking transports a Wave crest | KKL 2161--2168 |
| relative one-common-crest annular pruning | DL 2821--2842 |
| Parallel Law and arbitrary-family definition of width | KL06 13--36, 59--68 |

The proof-level relative content of DL 2821--2842 is important.  The
displayed lemma only states
\[
   \mathcal W(B^+)\ge \mathcal W(B)-O(\log d),
\]
but its proof constructs a disjoint decomposition
\[
   B=B^0\mathbin{\dot\cup}B^1\mathbin{\dot\cup}\cdots
        \mathbin{\dot\cup}B^T,\qquad T=O(\log d),
\]
bounds every \(B^t\), \(t>0\), by \(O(1)\) using Shift, and removes one
final \(O(1)\) outer buffer from \(B^0\).  The Parallel Law therefore
gives the genuinely relative conclusion
\[
   \mathcal W(B\setminus B^+)\le c_{\rm DL}(d).           \tag{2.1}
\]
We use (2.1) with \(d=2\).  We never obtain (2.1) by subtracting two
aggregate inequalities.

## 3. Typed stationary data

Fix \(b\), put \(N=b+3\), and let
\[
   A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}.
\]
Every leaf of \(A_0\) is \(N\)-unbreakable.  Moreover, every leaf of
\(A_0\) is individually nonshort: if a leaf \(\gamma\notin A^{\rm sh}\)
were short, then the union of \(A^{\rm sh}\) with the singleton
subwave \(\{\gamma\}\) would be a larger short subwave, contradicting
the defining maximality of \(A^{\rm sh}\).

For an \(N\)-unbreakable source leaf \(\alpha\), denote its unique
untagged \(n\)-step successor by
\[
   \Phi_n(\alpha).
\]
This notation does not select a restriction occurrence.  At every
one-step restriction we use the full KKL family of all components
surviving both the fine and coarse marking filters.

We will construct:

- an admissible inclusion-maximal source family \(A_n\);
- a protected core \(C_n\subset A_n\);
- its actual \(n\)-step image
  \[
     P_n:=\Phi_n(C_n);
  \]
- a number \(e_n\) with
  \[
     \mathcal W(A_n\setminus C_n)\le e_n.                \tag{3.1}
  \]

The protected image \(P_n\), not the uncontrolled maximal extension
\(\Phi_n(A_n)\), carries the common-crest invariant.

## 4. The two-direction prime-end lemma

### Definition 4.0 (leafwise-\(J\) Wave)

A KKL subwave \(S\) is a **leafwise-\(J\) Wave** if every singleton
subwave \(\{\gamma\}\), \(\gamma\in S\), crests over the fixed connected
prime-end interval \(J\).  This is the exact common-crest condition used
below.  It avoids inferring a family-level crest from a collection of
singleton crests.

In the annular language of DL 2813, a leafwise-\(J\) lamination is one
Wave above \(J\): every leaf goes above that same boundary interval.

### Lemma 4.0 (ordered limb access blocks)

The multi-intervals
\[
   BL_0,BL_1,\ldots,BL_{q-1}
\]
occur on the inner prime-end circle in the circular order of the planar
limbs \(\mathcal L_0,\ldots,\mathcal L_{q-1}\), with disjoint
interiors.

#### Source audit and proof

KKL 500--503 fixes the counter-clockwise circular order of the planar
limbs.  KKL 516--543 constructs the tree in the locally connected
model and then transports the tree data from the rational-lamination
quotient in the non-locally-connected case.  KKL 838 asserts, without
a local-connectivity restriction, that
\[
   BL_j=\partial_{\rm C}\mathcal L_j
\]
is one connected multi-interval.  Thus the only point not written as a
separate KKL lemma is preservation of the planar cyclic order by these
connected access blocks.

That point is a prime-end crosscut fact.  If the interiors of the
access blocks of two distinct limb components alternated on the
prime-end circle, choose two prime ends from each block in alternating
order and crosscuts sufficiently far down their defining chains, in
disjoint neighborhoods of the two limb components away from their
common attachment at \(\alpha_F\).  Crosscuts with alternating
prime-end endpoints in an annulus must intersect by Jordan separation,
contradicting the disjoint limb neighborhoods.  Hence two connected
limb access blocks cannot interleave.  Their order is therefore the
planar order fixed at KKL 500--503.

The argument takes place in the prime-end compactification.  It does
not identify prime ends with points of \(T\), and therefore does not
assume local connectivity. \(\square\)

### Lemma 4.1 (two adjacent noncritical crests)

Let \(S\) be a Wave in \(U\setminus T\) ending at \(BL_0\), and assume
that every leaf of \(S\) is individually nonshort.  Then there is a
disjoint partition
\[
   S=S^+\mathbin{\dot\cup}S^-                            \tag{4.1}
\]
such that every leaf of \(S^+\) crests over \(BL_1\), and every leaf of
\(S^-\) crests over \(BL_{-1}\).  When \(q=2\), the two limb
multi-intervals coincide and one may take \(S^-= \varnothing\).
Equivalently, \(S^\pm\) are leafwise-\(BL_{\pm1}\) Waves.

#### Proof

The inner prime-end boundary of \(U\setminus T\) is a circle.  The
multi-intervals \(BL_j\) occur in the cyclic order of the planar limbs
\(\mathcal L_j\); each is one connected block on that circle.

Fix a leaf \(\gamma\) and choose one of its endpoints lying in
\(BL_0\).  Since \(\gamma\) is nonshort, the singleton Wave
\(\{\gamma\}\) crests over some full limb \(BL_j\).

It cannot crest over \(BL_0\): the chosen endpoint lies in an ideal
interval contained in \(BL_0\), while every end interval is removed
when the crest is formed.  Hence \(j\ne0\).

The base of \(\{\gamma\}\) is a connected arc of the prime-end circle
(or the whole circle).  Starting at the chosen end in \(BL_0\), the
part of that connected base leading to the full block \(BL_j\) leaves
\(BL_0\) in one of the two cyclic directions.  In the positive
direction it contains the first complete noncritical limb \(BL_1\);
in the negative direction it contains the first complete noncritical
limb \(BL_{-1}\).  The selected endpoint is in \(BL_0\), and the other
endpoint lies beyond the full limb that \(\gamma\) crests over.
Consequently the adjacent full limb is in the interior part of the
base, not in an end, and is contained in the crest.  If the base is
the whole circle, both adjacent limbs are contained.

Assign \(\gamma\) to \(S^+\) whenever it crests over \(BL_1\), and to
\(S^-\) otherwise.  The preceding paragraph proves that every leaf in
the second class crests over \(BL_{-1}\).  Both classes are
sublaminations of \(S\), hence are Waves subordinate to the original
base.  This proves (4.1). \(\square\)

No packet count involving \(q\) or the total marking cardinality occurs:
there are exactly two possible directional classes.

## 5. One common crest: relative pruning and inheritance

### Lemma 5.1 (one-packet successor)

Let \(P\) be a one-step unbreakable leafwise-\(I\) Wave for a fixed
limb \(I=BL_k\), \(k\ne0\).  Let
\[
   B:=\iota^*P
\]
be the full KKL restriction after both endpoint filters.  Then there
are subfamilies \(P^{\rm good}\subset P\) and a Wave
\[
   R=F_*P^{\rm good}
\]
with:

\[
\begin{aligned}
  \mathcal W(P\setminus P^{\rm good})&\le c_{\rm DL},    \tag{5.1}\\
  \text{every leaf of }R
     &\text{ crests over }F_*I=BL_{k+1}.                 \tag{5.2}
\end{aligned}
\]

Every leaf of \(R\) has one fewer remaining unbreakable step than its
predecessor.

#### Proof

For a singleton source leaf \(\{\gamma\}\), its full crest contains
\(I\).  The pullback description at KKL 1254--1260 is monotone for
connected boundary subsets: every inverse access and every attached
component included for \(I\) is also included for a connected
multi-interval containing \(I\).  Hence
\[
   \iota^*I\subset \iota^*(\operatorname{crest}\{\gamma\}).
\]
KKL's full-restriction statement at 1477, applied to each singleton and
then united, gives:

1. every retained leaf of \(B\) goes above the same connected
   prime-end interval
   \(J=\iota^*I\);
2. every leaf of \(P\) has at least one retained occurrence in \(B\);
3. by domination,
   \[
      \mathcal W(P)\le\mathcal W(B).                     \tag{5.3}
   \]

Restrictions of distinct leaves cannot cross under the local
homeomorphism \(\iota\), and distinct restriction components of one
leaf are disjoint.  Thus \(B\) is a lamination.  Since the DL definition
at 2813 is leafwise, the preceding common-\(J\) property makes \(B\)
one DL Wave above \(J\).  No assertion about an aggregate KKL crest is
being substituted for this leafwise statement.

The complement map
\[
   f:U'\setminus T'\longrightarrow U\setminus T
\]
is an unbranched degree-two annular covering.  Apply the proof-level
relative DL pruning (2.1) to \(B\).  It gives a genuine subwave
\(B^+\subset B\) such that
\[
   \mathcal W(B\setminus B^+)\le c_{\rm DL},             \tag{5.4}
\]
and \(f\) is injective on the retained Wave.  Hence
\[
   R:=f(B^+)
\]
is an actual lamination and Wave.

Define \(P^{\rm good}\) to be the source leaves having at least one
restriction occurrence in \(B^+\).  A leaf outside
\(P^{\rm good}\) has a retained restriction in \(B\setminus B^+\).
KKL domination and (5.4) give (5.1).

Because \(P\) is unbreakable, all retained occurrences of one source
leaf have the same untagged output.  It follows directly that
\[
   F_*P^{\rm good}=f(B^+)=R.                             \tag{5.5}
\]
There is no choice or quotient of repeated occurrences in (5.5).

Finally apply KKL Proposition `prop:nonbreaking` to each singleton
source leaf and its output singleton.  Since \(F_*\) acts
combinatorially and the source leaf crests over \(I\), its successor
crests over \(F_*I=BL_{k+1}\).  This proves (5.2) leafwise.  The
remaining-unbreakability assertion follows immediately from the
definition at KKL 1355--1358. \(\square\)

### Corollary 5.2 (no-short inheritance)

If \(F_*I\) is a limb multi-interval, every leaf of \(R\) is
individually nonshort.  The same is true for every subfamily of \(R\),
in particular its central subfamily.

This is stronger than merely saying that the aggregate Wave has a
crest: (5.2) was proved for every singleton leaf.

## 6. Repair of the over-critical estimate

The printed proof of KKL `prop:over critical` invokes the invalid broad
coefficient-one Wave lemma.  The following proof does not.

### Proposition 6.1 (relative-DL over-critical bound)

There is an absolute constant \(c_{\rm over}<\infty\) such that, for
every leafwise-\(BL_0\) Wave \(Q\),
\[
   \mathcal W(Q^{\rm nbr})\le c_{\rm over}.              \tag{6.1}
\]

#### Proof

Put \(Q_0=Q^{\rm nbr}\).  Its full filtered restriction
\[
   D=\iota^*Q_0
\]
is one DL Wave above \(\iota^*BL_0\), by the singleton argument and
pullback monotonicity in Lemma 5.1, and domination gives
\[
   \mathcal W(Q_0)\le\mathcal W(D).                      \tag{6.2}
\]

Apply (2.1) to obtain \(D^+\subset D\) with
\[
   \mathcal W(D\setminus D^+)\le c_{\rm DL}
\]
and injective Wave image \(f(D^+)\).  KKL nonbreaking transport gives
that \(f(D^+)\) is a Wave over
\[
   F_*BL_0=\partial_{\rm C}T.
\]
There is no nonempty Wave over the entire prime-end boundary; this is
exactly the terminal observation used at KKL 1520.  Hence \(D^+\) is
empty.  The Parallel Law and (6.2) now give
\[
   \mathcal W(Q_0)
   \le\mathcal W(D)
   =\mathcal W(D\setminus D^+)
   \le c_{\rm DL}.
\]
Thus (6.1) holds with \(c_{\rm over}=c_{\rm DL}\). \(\square\)

This proof is neither circular nor an aggregate subtraction.  It uses
the explicit relative discarded family in the DL proof.

### Corollary 6.2 (backward directional packet)

Let \(P\) be **two-step unbreakable** and leafwise-\(BL_{-1}\).  Then
\[
   \mathcal W(P)\le c_{\rm back}                         \tag{6.3}
\]
for an absolute constant \(c_{\rm back}\).

#### Proof

Apply Lemma 5.1 before its final width conclusion.  The pruned image
\(R\) is leafwise-\(BL_0\).  The second unbreakable step of \(P\)
makes \(R\) one-step unbreakable, so Proposition 6.1 gives
\(\mathcal W(R)\le c_{\rm over}\).  Moreover
\[
\begin{aligned}
 \mathcal W(P)
 &\le \mathcal W(B)\\
 &\le \mathcal W(B\setminus B^+)+\mathcal W(B^+)\\
 &\le c_{\rm DL}+\mathcal W(f^*R)\\
 &=c_{\rm DL}+2\mathcal W(R).
\end{aligned}
\]
The last identity is the degree-two full-lift identity; the weaker
general degree-two covering estimate would also suffice.  This proves
(6.3). \(\square\)

The same proof applies whenever a propagated common crest is
\(BL_{q-1}\) and two unbreakable steps remain.  Every N1 transition has
two remaining steps because \(n\le N-2\).  Therefore wrap-around at
small \(q\) creates a bounded terminal packet, not a missing case.

## 7. Bounded noncentral output

### Lemma 7.1 (central extraction from a common-crest output)

Let \(R\subset F_*P\) be the Wave produced by Lemma 5.1.  Assume:

1. every leaf of \(R\) is one-step unbreakable;
2. \(R\) is leafwise-\(BL_k\) for a full limb \(BL_k\ne BL_0\);
3. \(P=P^{\rm nbr}\) is \(k_b\)-controllable.

Let \(R^{\rm cen}\) be the subfamily of leaves with an endpoint in
\(BL_0\).  Then
\[
   \mathcal W(R\setminus R^{\rm cen})\le c_{\rm nc}(b).
                                                               \tag{7.1}
\]
Moreover \(R^{\rm cen}\) is a Wave ending at \(BL_0\), every leaf
retains the common crest, and every leaf is individually nonshort.

#### Proof

Because \(P\) ends at \(BL_0\), it is \(k_b\)-controllable with
\[
   k_b\le\ell(BL_0)\le6b:
\]
partition by the ideal interval of a chosen endpoint in \(BL_0\).
KKL `lem:pushing controllable` therefore gives a number
\(\eta_b<\infty\), independent of \(q\), such that \(R\) is
\(\eta_b\)-controllable.

Start from one controllability cover
\[
   R=R^{\rm over}_0\cup L_1\cup\cdots\cup L_{\eta_b},
                                                               \tag{7.2}
\]
where \(R^{\rm over}_0\) is over \(BL_0\) and every \(L_j\) is
localized.  We refine (7.2) without double charging:

1. first remove \(R^{\rm cen}\);
2. among the remaining leaves, put every leaf whose singleton crest
   contains all of \(BL_0\) into \(R^{\rm over}\);
3. assign each remaining leaf to the first localized \(L_j\) containing
   it, and call the assigned family \(Z_j\).

The family \(R^{\rm over}\) is leafwise-\(BL_0\).  Every \(Z_j\) is
localized.  It is also subordinate to
\(\partial_{\rm C}T\setminus BL_0\): a connected base on a circle,
with neither endpoint in \(BL_0\), either avoids \(BL_0\) or contains
the whole block \(BL_0\) in its crest.  The latter leaves were assigned
to \(R^{\rm over}\).

All these families are one-step unbreakable.  By Proposition 6.1,
\[
   \mathcal W(R^{\rm over})\le c_{\rm over}.
\]
Every leaf of every \(Z_j\) crests over the inherited full limb, so
\((Z_j)^{\rm sh}=\varnothing\).  KKL `prop:away from critical` gives
\[
   \mathcal W(Z_j)
   =\mathcal W(Z_j^{\rm nbr})
   \le \mathcal W(Z_j^{\rm sh})+O_b(1)
   =O_b(1).
\]
The Parallel Law and the bound \(\eta_b\) prove (7.1).

The final assertions follow because \(R^{\rm cen}\) is a sublamination
of \(R\), every leaf ends at \(BL_0\), and common-crest/no-shortness
were established leafwise in Lemma 5.1. \(\square\)

If the inherited crest is \(BL_0\), Proposition 6.1 bounds all of
\(R\).  In that case we set \(R^{\rm cen}=\varnothing\) and terminate
the protected core.  This is the wrap-around rule.

## 8. One protected-core transition

Assume \(C_n\subset A_n\) has protected image
\[
   P_n=\Phi_n(C_n)
\]
which is a Wave ending at \(BL_0\), has at least one remaining
unbreakable step, and, for \(n\ge1\), has the leafwise common crest
\[
   BL_{n+1}\quad\text{(indices modulo \(q\), until the first wrap).}
                                                               \tag{8.1}
\]

### Initial stage

For \(n=0\), apply Lemma 4.1:
\[
   P_0=P_0^+\mathbin{\dot\cup}P_0^-.
\]
Corollary 6.2 gives
\[
   \mathcal W(P_0^-)\le c_{\rm back}.                    \tag{8.2}
\]
It applies because every leaf of \(P_0\subset A^{N\text{-nbr}}\) has
at least \(N\ge2\) remaining unbreakable steps.
Use \(P_0^+\), whose common crest is \(BL_1\), as the forward packet.

### General forward packet

Let \(P\) denote \(P_0^+\) at the initial stage and \(P_n\) thereafter.
At every transition \(n\le N-2\), the leaves of \(P\) have at least
\(N-n\ge2\) remaining unbreakable steps.  If its common crest is
\(BL_{q-1}\), Corollary 6.2 bounds \(P\).  In this wrap case define
\[
   P^{\rm cen}:=\varnothing,
   \qquad
   \mathcal W(P\setminus P^{\rm cen})\le c_{\rm back}.   \tag{8.2a}
\]

In the nonwrap case apply Lemma 5.1.  Let \(P^{\rm good}\) be the surviving
source family, let \(R=F_*P^{\rm good}\), and let
\(R^{\rm cen}\) be supplied by Lemma 7.1.  Define
\[
   P^{\rm cen}
   :=
   \{p\in P^{\rm good}:F_*p\in R^{\rm cen}\}.             \tag{8.3}
\]

The DL-discarded source family satisfies
\[
   \mathcal W(P\setminus P^{\rm good})\le c_{\rm DL}.
                                                               \tag{8.4}
\]
For the noncentral survivors, the full-restriction degree-two transfer
gives
\[
   \mathcal W(P^{\rm good}\setminus P^{\rm cen})
   \le2\mathcal W(R\setminus R^{\rm cen})
   \le2c_{\rm nc}(b).                                    \tag{8.5}
\]
This inequality retains every occurrence and counts both covering
sheets.  It does not infer coefficient one from unbreakability.

Combining (8.2)--(8.5), using (8.2a) in the wrap case and (8.2) only
at \(n=0\), yields
\[
   \mathcal W(P_n\setminus P^{\rm cen})\le c_*(b),
   \qquad
   c_*(b):=
   c_{\rm back}+c_{\rm DL}+2c_{\rm nc}(b).               \tag{8.6}
\]

Define the next protected source core by the actual untagged preimage
\[
   C_{n+1}
   :=
   C_n\cap\Phi_n^{-1}(P^{\rm cen}).                       \tag{8.7}
\]
Then
\[
   \Phi_{n+1}(C_{n+1})=R^{\rm cen}.                      \tag{8.8}
\]
Thus (8.1) advances from \(BL_{n+1}\) to \(BL_{n+2}\), unless the
wrap rule terminated the core.

The sequential multiplicity-aware transfer through the first \(n\)
degree-two stages gives
\[
\begin{aligned}
 \mathcal W(C_n\setminus C_{n+1})
 &\le 2^n\mathcal W(P_n\setminus P^{\rm cen})\\
 &\le2^{b+1}c_*(b)
 =:L_b,                                                   \tag{8.9}
\end{aligned}
\]
because \(0\le n<N-1=b+2\).  All intermediate images lie in the
already declared stationary Waves: \(C_n\subset A_n\subset A_j\) for
\(j\le n\).  Hence the transfer is correctly typed at every stage.

## 9. Maximal extension without corrupting the crest induction

Set \(C_0=A_0\).  After constructing \(C_{n+1}\), consider all
subwaves \(B\) satisfying
\[
   C_{n+1}\subset B\subset A_n,
   \qquad
   \Phi_{n+1}(B)\text{ is a Wave ending at }BL_0.         \tag{9.1}
\]
The collection is nonempty because \(C_{n+1}\) satisfies (9.1).
A union of a chain still satisfies (9.1): the images are nested
pairwise-disjoint path families, so their union is pairwise disjoint,
ends at \(BL_0\), and is subordinate to the union of their nested
connected bases.  In the operational KKL/KL path-family category used
for extremal width, this is a Wave.  Zorn's lemma therefore gives an
inclusion-maximal member; choose it as \(A_{n+1}\).

If “lamination” is strengthened to require a closed subset of the path
space, the locked source does not state the additional chain-closure
theorem.  One would then have to close the chain union inside \(A_n\)
and verify continuity of the untagged image.  This topological
maximal-extension issue is avoided completely by the explicit-core
formulation in Section 11.2.

This member is inclusion-maximal in the full admissible poset, not only
among families containing the core: any strict admissible extension of
it would still contain \(C_{n+1}\), contradicting its Zorn maximality.
It is not asserted to be a **greatest** admissible family, and it need
not be unique.  The distinction matters because two incomparable
maximal Waves can exist.

This realizes the only source-valid reading of the printed word
“maximal” without requiring the maximal extension itself to carry the
common crest.  Only the protected core is propagated.

Let
\[
   e_n:=\mathcal W(A_n\setminus C_n).
\]
Since \(A_{n+1}\subset A_n\) and \(C_{n+1}\subset A_{n+1}\), the
Parallel Law and (8.9) give
\[
\begin{aligned}
 e_{n+1}
 &\le e_n+L_b,                                           \tag{9.2}\\
 \mathcal W(A_n\setminus A_{n+1})
 &\le e_n+L_b.                                           \tag{9.3}
\end{aligned}
\]
Indeed, the two set containments used here are
\[
\begin{aligned}
 A_{n+1}\setminus C_{n+1}
 &\subset A_n\setminus C_{n+1},\\
 A_n\setminus A_{n+1}
 &\subset A_n\setminus C_{n+1},
\end{aligned}
\]
and, because \(C_{n+1}\subset C_n\),
\[
 A_n\setminus C_{n+1}
 =
 (A_n\setminus C_n)\mathbin{\dot\cup}
 (C_n\setminus C_{n+1}).
\]
Thus arbitrary maximal extras are charged to \(e_n\) exactly once.
No greatestness or compatibility between different maximal choices is
used.
As \(e_0=0\), induction yields
\[
   e_n\le nL_b
\]
and therefore
\[
 \boxed{
   \mathcal W(A_n\setminus A_{n+1})
   \le(n+1)L_b
   \le(b+2)L_b=:C_b.
 }                                                        \tag{9.4}
\]

The constant depends only on the fixed parabolic bound \(b\).  It is
independent of the satellite period \(q\), the rotation denominator,
the corridor length, and the total marking cardinality.

Equation (9.4) is the desired additive stationary continuation.

## 10. N1 telescope boundary

There are \(N-1=b+2\) transitions.  The Parallel Law and (9.4) give
\[
   \mathcal W(A_0)
   \le\mathcal W(A_{N-1})+(N-1)C_b.                      \tag{10.1}
\]

Equation (10.1) is the entire consequence claimed in this N1 note.  It
reduces the stationary estimate to a bound for the terminal family
\(A_{N-1}\).

The component-alignment and degree-one terminal argument at KKL
1591--1621 is a separate dependency (Gate N2 in
`qa_native_kkl_stationary_2026-07-26.md`).  It contains the printed
\(A_N/A_{N-1}\) indexing defect and has not been re-proved here.
Accordingly this note does **not** promote terminal alignment or the
full stationary proposition.

## 11. Measurability audit

### 11.1 What the analytic proof needs

KL06 13--36 defines extremal width for an arbitrary family of paths.
The Parallel Law also applies to arbitrary families.  Consequently:

- the two-direction partition is a literal set partition;
- the DL discarded and retained families are literal subwaves;
- the full occurrence preimages in (8.3) and (8.7) are legitimate path
  families;
- all displayed widths are defined without a measurable leaf-index
  space.

No unproved Borel selector is used in (9.4).

### 11.2 What a stronger Borel interface would need

The clean measurable formulation deliberately avoids maximal
extension.

Let \(\mathscr P(V)\) be the standard-Borel space of parametrized
proper simple paths in the prime-end compactification of the marked
annulus \(V\), with the compact-open Borel structure.  Assume:

1. \(A_0\subset\mathscr P(V)\) is Borel;
2. the endpoint interval, singleton base, cyclic direction, and
   central-end predicates are Borel on every proof-used stage path
   space;
3. the filtered retained-occurrence relation
   \[
      \mathscr E
      \subset
      \mathscr P(V^{\rm out})\times\mathscr P(V^{\rm res})
   \]
   is Borel and has countable vertical sections;
4. the native DL deck-span classes and final outer-buffer cut are
   represented by Borel subfamilies.

These assumptions are enough.  The two-direction classes are inverse
images of finite Borel labels.  If \(B^+\) is the Borel retained DL
family, then
\[
   \{p:\exists\beta\in B^+,\ (p,\beta)\in\mathscr E\}
\]
is Borel by the Lusin--Novikov theorem, because
\(\mathscr E\cap(\mathscr P(V^{\rm out})\times B^+)\) is Borel with
countable vertical sections.

The graph of the untagged successor relation is
\[
 \{(p,q):\exists\beta,\ (p,\beta)\in\mathscr E,\ q=f(\beta)\}.
\]
It is Borel by the same countable-section projection theorem, since
\(\beta\mapsto f(\beta)\) is Borel.  On the unbreakable family its
vertical sections are singletons, so it is the graph of a Borel
successor map.  Central preimages and the recursion (8.7) are therefore
Borel as well.

Under clauses 1--4, define the stationary sequence explicitly by
\[
   A_n^{\rm exp}:=C_n
\]
and do not apply Zorn.  Equation (8.9) directly gives
\[
   \mathcal W(A_n^{\rm exp}\setminus A_{n+1}^{\rm exp})
   \le L_b.
\]
This is the cleanest measurable N1 statement: it is Borel, explicit,
and occurrence-saturated, and maximality is absent because it is not
used in the N1 estimate.

The locked sources do not prove clauses 1--4 for every arbitrary KKL
Wave.  In particular, KKL permits an arbitrary path family and does
not specify a standard-Borel leaf presentation.  Nor do the sources
give a Borel inclusion-maximal extension of (9.1).  Therefore:

- the arbitrary-family analytic proof (9.4) is unconditional in the
  source category;
- the explicit-core Borel proof is conditional on clauses 1--4; and
- the conjunction “arbitrary input + Borel + inclusion-maximal” remains
  an independent formal-interface obligation.

## 12. Adversarial checks

1. **Cyclic-cover collision.**  The two directional images are never
   united.  The backward packet has bounded total source width and is
   discarded.  The forward packet is made injective by native DL
   pruning.  Hence the known two-packet crossing counterexample does
   not apply.
2. **Repeated untagged outputs.**  The full restriction is retained
   before pruning, and all losses are transferred with the degree-two
   full-lift inequality.  No repeated occurrence is collapsed to one
   conductance coordinate.
3. **Aggregate subtraction.**  The only relative DL estimate is derived
   from the explicit disjoint classes in DL 2830--2841.  No inequality
   of the form “large total minus large survivor” is used.
4. **Short-output birth.**  Common-crest inheritance is proved for each
   singleton leaf.  Every propagated leaf crests over a full limb, so
   its short part is empty.
5. **Small \(q\) and wrap-around.**  A crest \(BL_{q-1}\) is bounded
   before it can be propagated through \(BL_0\).  The bound uses two
   remaining unbreakable steps, which every N1 transition has.  No
   lower bound on \(q\) is needed.
6. **Away/localized mismatch.**  The away families are refined
   leafwise so that they are both localized and subordinate to
   \(\partial_{\rm C}T\setminus BL_0\), exactly as required by KKL
   1524--1528.
7. **Maximal-extension contamination.**  Arbitrary extra leaves are
   charged in \(e_n\); they never enter the common-crest induction.
8. **Fine/coarse marking filters.**  Every restriction family is the
   full KKL filtered restriction.  A topological lift rejected by
   either filter is not used for domination.
9. **Prime-end local connectivity.**  The proof uses the prime-end
   circle, KKL's connected limb multi-intervals, and the crosscut
   noninterleaving argument in Lemma 4.0, not pointwise local
   connectivity of \(T\).
10. **Period dependence.**  The packet count is two, the covering
    degree is two, the horizon is \(b+3\), and controllability uses
    \(\ell(BL_0)\le6b\).  Every constant is independent of \(q\).
11. **Circularity.**  Proposition 6.1 is re-proved directly from native
    DL pruning.  Neither the stationary proposition nor the false broad
    KKL Wave lemma is invoked.
12. **Terminal overreach.**  No use is made of KKL 1591--1621.  That
    separate Gate N2 remains open in this note.

## 13. Status table

| item | status in this note |
|---|---|
| ordered limb access blocks in the prime-end model | proved from KKL's connected blocks plus crosscut noninterleaving |
| two-direction adjacent-crest lemma | proved |
| proof-level relative DL pruning for degree two | imported from the explicit DL proof |
| common-crest inheritance | proved |
| over-critical estimate without broad KKL Wave lemma | proved |
| bounded noncentral output | proved |
| protected-core additive transition | proved |
| inclusion-maximal continuation containing the core | proved by Zorn in the operational path-family category; closed/Borel maximality remains separate |
| additive stationary estimate (9.4), source-native category | proved |
| Borel explicit-core transition | proved conditional on clauses 1--4 of Section 11.2 |
| Borel maximal continuation for an arbitrary KKL Wave | open formal-interface clause |
| terminal alignment / Gate N2 | open |
| VAAPC-I | open |
| UPTCR | open |
| MLC | open |
