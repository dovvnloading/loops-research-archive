# Gate N1 source reconstruction: stationary relative Wave continuation

## Status and scope

This document reconstructs, from the locked source, the exact objects and
quantifiers used in the stationary paragraph of KKL and isolates the
smallest analytically meaningful form of
`KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` (Gate N1).

It is **not** a proof of Gate N1.  It proves only the set-theoretic and
indexing statements explicitly identified below.  The source-relative
analytic estimate remains open.  No conclusion about VAAPC-I, UPTCR, or
MLC is made.

No ledger or manuscript status was changed during this pass.

## 1. Source custody

The line references in this document are to the following immutable local
files.

| source | role | SHA-256 |
|---|---|---|
| `.tmp_wave_audit/waves-with-Misha.tex` | KKL master source; arXiv 2606.27272 v1 | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_wave_audit/not-all-good2.tex` | KKL included stationary/tame-case source | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` |
| `.tmp_wave_audit/kkl.tar` | frozen KKL source archive | `7FFDCDC90C0785AE55DE23F0AB64F63178E1F2C661FAB1FCC5C95768D8F53AF8` |
| `.tmp_wave_audit/dl23/Feigen.tex` | Dudko--Lyubich source for the annular source-pruning lemma cited by KKL | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |

The KKL master identifies itself as the top-level source in
`.tmp_wave_audit/00README.json`.  It includes `not-all-good2.tex` at
master line 1140.  The present reconstruction uses the KKL master at
lines 394--461, 495--543, 661--713, 838--866, 1142--1280,
1354--1358, 1513--1622, and 1838--2162.  The DL source is used only to
state the exact scope of its source-side annular pruning lemma, at lines
2813--2842.

## 2. Ambient analytic and combinatorial data

### 2.1 The pseudo-quadratic-like relation

KKL define

\[
 F=(f,\iota):(\mathcal U',\mathcal K')
 \rightrightarrows(\mathcal U,\mathcal K),
\]

where \(\mathcal U',\mathcal U\) are conformal disks,

1. \(f:\mathcal U'\to\mathcal U\) is a double branched covering;
2. \(\iota:\mathcal U'\to\mathcal U\) is a holomorphic immersion; and
3. \(f^{-1}(\mathcal K)=\iota^{-1}(\mathcal K)=\mathcal K'\).

This is exactly master lines 439--445.  Global iterates are fiber-product
objects \(\mathcal U^m\), not literal iterated inverse images inside one
fixed copy of \(\mathcal U\); see lines 457--461.

For the Wave section, \(b\geq1\) and \(F\) are fixed in advance, the
renormalization is parabolically \(b\)-bounded, and all constants in that
section are allowed to depend on \(b\); see lines 698--713 and
1142--1149.  Thus the word “universal” in Proposition
`prop:into the critical limb` means:

\[
 \text{independent of }q,\ A,\ \mathcal W(A),\text{ and }
 \mathcal W(\mathcal RF),\quad\text{after }b\text{ is fixed}.
\]

It does not mean independent of \(b\).

### 2.2 Hubbard tree and central limb marking

For a primitively renormalizable, periodically repelling relation, KKL
construct the cycle \(\mathcal K\) of small filled Julia sets and the
Hubbard tree \(\mathcal T\); see lines 486--490 and 512--543.  The limb
\(\mathcal F L_0\) contains the critical point (line 501), and

\[
 \mathcal L_j=\mathcal F L_j\cap\mathcal T
\]

at line 518.

The Wave surface is

\[
 V:=\mathcal U\setminus\mathcal T.
\]

It is equipped with the ideal marking \(\mathcal I\) induced by the
sides of \(\widehat{\mathcal K}\) in the Carathéodory boundary of
\(\mathcal T\); see lines 1145--1147.  The central marked limb is the
multi-interval

\[
 BL_0:=\partial_{\rm C}\mathcal L_0.
\]

More generally, \(BL_j=\partial_{\rm C}\mathcal L_j\), and
\(\ell(BL_j)\leq6b\); see lines 838--842.  In particular, \(BL_0\) is
not asserted to be one interval.

### 2.3 The one-step complement relation

Set

\[
 \mathcal T'=f^{-1}(\mathcal T),\qquad
 V'=\mathcal U'\setminus\mathcal T'.
\]

After removing the trees, the same symbols denote a covering and an
immersion

\[
 f:V'\to V,\qquad \iota:V'\to V;
\]

see line 1225.  The target marking is \(\mathcal I\), the fine source
marking is

\[
 \mathcal I'=f^*\mathcal I,
\]

and the immersion marking is

\[
 \widetilde{\mathcal I}=\iota^*\mathcal I.
\]

KKL prove that \(\mathcal I'\) refines
\(\widetilde{\mathcal I}\) and that the action is combinatorial; see
lines 1254--1274.

The interval action satisfies

\[
 F_*BL_j=BL_{j+1}\quad(j\ne0),\qquad
 F_*BL_0=\partial_{\rm C}\mathcal T
\]

at line 1274.

## 3. Exact path, restriction, and Wave semantics

### 3.1 Ideal markings and Waves

An ideal marking is a countable collection of pairwise-disjoint open
connected subsets of the ideal boundary whose union is dense; its
elements are intervals (lines 1844--1853).  A multi-interval is a
connected open union of marked intervals and endpoints (lines
1855--1859).

A path in \((V,\mathcal I)\) is a proper path with endpoints in marked
intervals which is not subordinate to a multi-interval of combinatorial
length at most two (lines 1867--1870).  A lamination “ends at” a
multi-interval \(I\) when every leaf has an endpoint in \(I\); it is
localized only when it ends at one interval of \(\mathcal I\) (lines
1871--1872).

A Wave is a lamination subordinate to a connected multi-interval.  Its
base, two ends, and crest are defined at lines 1874--1875.  Consequently:

- “ends at \(BL_0\)” does not choose a particular interval of \(BL_0\);
- it does not distinguish which endpoint is the central endpoint;
- it does not assert a common lifted rectangle, a common deck-span
  class, or a common restriction branch; and
- “localized to \(BL_0\)” can only mean localized at a single marked
  interval contained in \(BL_0\), unless an additional nonstandard
  meaning is supplied.

### 3.2 Retained restrictions

For a proper target path \(\gamma\), \(\iota^*\gamma\) is initially the
set of proper components of \(\iota^{-1}(\gamma)\); see lines
2081--2084.  Once the fine marking \(\mathcal I'\) is fixed, KKL delete
from this set:

1. restrictions that are not paths in \((V',\mathcal I')\); and
2. restrictions subordinate to one interval of the coarser marking
   \(\iota^*\mathcal I\).

These filters are explicit at lines 2096--2097.

The one-step action is then the set-valued operation

\[
 F_*\gamma=f_*(\iota^*\gamma)
\]

on the retained restrictions; see lines 2128--2142.  Path families are
ordinary sets, not occurrence-tagged multisets.  Thus two different
retained restrictions, or two different source paths, may produce the
same untagged output path.

A path breaks exactly when \(F_*\gamma\) is not a singleton (lines
2161--2162).  Hence “unbreakable” guarantees one untagged output path;
it does **not** guarantee one retained restriction occurrence.

It is useful to record the omitted occurrence layer explicitly:

\[
 \operatorname{Occ}_F(\gamma,\delta)
 :=
 \left\{
 \widetilde\gamma:
 \begin{array}{l}
 \widetilde\gamma\text{ is retained in }\iota^*\gamma,\\
 f(\widetilde\gamma)=\delta
 \end{array}
 \right\}.
\]

If \(\gamma\) is unbreakable and \(F_*\gamma=\{\delta\}\), this set is
nonempty but need not be a singleton.

### 3.3 Sequential versus one-shot iteration

KKL later construct the fiber-product iterate
\((f^n,\iota_n):\mathcal U^n\setminus\mathcal T^n\to
\mathcal U\setminus\mathcal T\) and prove

\[
 f_*^n\iota_n^*I=F_*^nI
\]

for multi-intervals \(I\); see lines 1707--1709.  They do not state the
analogous equality for path families.  Intermediate fine/coarse filters
make that equality a separate theorem.  Gate N1 must therefore be
formulated using the sequential \(F_*\)-action unless a one-shot
path-occurrence equivalence is independently proved.

### 3.4 Source typing defects in the generic covering paragraph

The generic covering paragraph has three literal symbol/type slips:

- line 2067 defines \(f_*I\) while the source interval was named \(I'\);
- line 2071 writes \(f(\gamma)\) while the source path was named
  \(\gamma'\); and
- line 2076 puts the source ending set \(X'\) in
  \(\partial_iV\), although the degree of \(f\) on \(X'\) requires
  \(X'\subset\partial_iV'\).

The intended corrections are unambiguous, but they should be corrected
before these statements are used as typed interfaces.  The later Wave
lemma at lines 2149--2152 is correctly typed with a source Wave in
\((V',f^*\mathcal I)\) ending at a source multi-interval \(I'\).

## 4. Exact stationary quantifiers and objects

### 4.1 Proposition-level quantifiers

After fixing \(b\) and \(F\) as above, Proposition
`prop:into the critical limb` quantifies over every Wave
\(A\subset\mathcal U\setminus\mathcal T\) ending at \(BL_0\) and claims
the existence of a section-universal integer \(N\); see lines
1534--1537.  The proof sets

\[
 N=b+3
\]

at line 1547.

The preliminary continuation lemma is asserted for every integer

\[
 0\leq n<N-1=b+2,
\]

equivalently \(0\leq n\leq b+1\); see lines 1550--1555.

### 4.2 Short and unbreakable source family

At lines 1355--1358, KKL define

\[
 A^{r\text{-nbr}}
 =
 \left\{
 \alpha\in A:
 F_*^m\alpha\text{ does not break for every }0\leq m<r
 \right\}.
\]

The short part \(A^{\rm sh}\) is the unique maximal short subwave
(lines 1180--1183).  The stationary source is

\[
 A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}.
\]

For \(0<n<N\), KKL then say:

\[
 A_n\subset A_{n-1}
\quad\text{is “the maximal subwave” such that}\quad
 F_*^nA_n\text{ is a Wave ending at }BL_0.
\]

This is line 1548.  The declared list is exactly

\[
 A_0,A_1,\ldots,A_{N-1}=A_{b+2}.
\]

There is no declared \(A_N\).

“The maximal subwave” has two inequivalent readings:

1. a **greatest** eligible subwave, containing every eligible subwave;
2. an arbitrary **inclusion-maximal** eligible subwave.

Only the first reading licenses the containment inference used at line
1572.  The source does not prove existence or uniqueness under either
reading.  This is not merely linguistic: the pushforward of a
lamination need not be a lamination (line 2072), so unions of eligible
source subfamilies need not have eligible output.

### 4.3 The unique untagged path maps

There is nevertheless a canonical untagged path map on the
\(N\)-unbreakable source.  For \(\alpha\in A^{N\text{-nbr}}\), define
recursively

\[
 \Phi_0(\alpha)=\alpha,\qquad
 F_*\Phi_r(\alpha)=\{\Phi_{r+1}(\alpha)\}
 \quad(0\leq r<N).
\]

The recursion is valid because the defining predicate for
\(A^{N\text{-nbr}}\) says that each displayed \(F_*\)-image is a
singleton.  It gives a function on untagged paths, not a unique chain of
retained restrictions.

For every \(A_n\), line 1559 defines

\[
 S_n=F_*^nA_n=\Phi_n(A_n).
\]

By the selection predicate, \(S_n\) is a Wave ending at \(BL_0\).
Nestedness gives

\[
 A_n\subset A_r\subset A^{N\text{-nbr}}
\quad(0\leq r\leq n),
\]

and direct substitution in the unbreakability definition gives

\[
 S_n=S_n^{(N-n)\text{-nbr}}.
\]

This last equality is valid at the untagged path level: if
\(\beta=\Phi_n(\alpha)\), then for \(0\leq j<N-n\),

\[
 F_*^j\beta=\{\Phi_{n+j}(\alpha)\}
\]

and \(\Phi_{n+j}(\alpha)\) does not break.

For \(0\leq n<N-1\), define the complete one-step terminal set

\[
 G_{n+1}:=\Phi_{n+1}(A_n)=F_*S_n.
\]

This is a path family, but the source does not prove it is a
lamination.  Since \(A_{n+1}\subset A_n\), the strongest unconditional
set inclusion is

\[
 S_{n+1}=\Phi_{n+1}(A_{n+1})\subset G_{n+1}.
\]

## 5. The four printed output symbols and their time types

Fix \(0\leq n<N-1\).  The printed proof uses \(X_n\) in two
incompatible time roles:

1. line 1560 chooses a Wave \(X_n\subset F_*S_n=G_{n+1}\);
2. line 1564 decomposes that \(X_n\) into
   \(X_{n+1},Y_{n+1},Z_{n+1}\); but
3. when the same argument is invoked with index \(n+1\), line 1560
   again defines \(X_{n+1}\), now as a Wave in \(F_*S_{n+1}\).

The first \(X_{n+1}\) is a time-\((n+1)\) central part of an output from
\(S_n\).  The second is a time-\((n+2)\) extraction from
\(S_{n+1}\).  No equality between them is stated or implied.  Thus the
symbols do not define one globally consistent sequence.

The only type-safe local alpha-renaming is:

\[
 R_{n+1}\subset G_{n+1}
\]

for the Wave chosen at line 1560, and

\[
 R_{n+1}
 =
 C_{n+1}\,\dot\cup\,Y_{n+1}\,\dot\cup\,Z_{n+1}
\]

for the intended decomposition at line 1564, where:

- \(C_{n+1}\) is localized at a marked interval contained in \(BL_0\);
- \(Y_{n+1}\) is a Wave over \(BL_0\); and
- \(Z_{n+1}\) is subordinate to
  \(\partial_{\rm C}\mathcal T\setminus BL_0\).

The dotted union is what the width argument needs.  The printed word
“decompose” does not explicitly state disjointness modulo a
width-zero boundary family, so this is a proof obligation rather than
a verbatim theorem.

There is a second family mismatch here.  Proposition
`prop:away from critical` at lines 1524--1528 applies to a
**localized** Wave subordinate to
\(\partial_{\rm C}\mathcal T\setminus BL_0\).  Line 1564 says only that
\(Z_{n+1}\) is subordinate to that complement.  Therefore the later
appeal to the proposition additionally requires either:

1. \(Z_{n+1}\) itself to be localized; or
2. a decomposition of \(Z_{n+1}\) into at most \(c_b\) localized
   subwaves, with a width accounting statement.

Neither clause is printed in the stationary paragraph.

For completeness, the other possible readings do not repair the
argument:

1. **Identify \(C_{n+1}\) with \(S_{n+1}\).**  
   This would make the line-1565 unbreakability appeal relevant, but
   makes \(S_{n+1}\setminus C_{n+1}\) empty at line 1576 and leaves
   \(A'_{n+1}\) in line 1572 unexplained.
2. **Treat \(X_n\) as one recursive sequence.**  
   Then line 1560 places \(X_n\) at time \(n+1\), while the previous
   stage placed the same symbol at time \(n\).  A separate stationary
   identification theorem would be required and none is stated.
3. **Change line 1560 to \(X_{n+1}\).**  
   This fixes the time index of the raw output but leaves line 1564
   trying to decompose \(X_{n+1}\) into another object also named
   \(X_{n+1}\).
4. **Delete the prime from \(A'_{n+1}\).**  
   This makes the line-1569 equality define \(S_{n+1}=C_{n+1}\), but
   then \(A'_{n+1}\) is undefined in lines 1572 and 1576.  Correcting
   the displayed equality to use \(A'_{n+1}\) is the only reading
   compatible with the next two displays.

The residual unbreakability which can control these three families is

\[
 R_{n+1}=R_{n+1}^{(N-n-1)\text{-nbr}},
\]

provided \(R_{n+1}\subset G_{n+1}\) retains the actual terminal paths.
The printed appeal at line 1565 to
\(S_{n+1}=S_{n+1}^{(N-n-1)\text{-nbr}}\) is a family mismatch:
\(Y_{n+1}\) and \(Z_{n+1}\) are subfamilies of \(R_{n+1}\), not of
\(S_{n+1}\).

The Wave lemma at lines 2149--2152 does not give the further line-1560
property that \(R_{n+1}\) has no short leaves.  That is a separate
shortness-transport or source-pruning obligation.

## 6. Strongest correct source/output identities

This section separates pure set theory from analytic regularity.

Assume for one stage that a typed central subwave

\[
 C_{n+1}\subset R_{n+1}\subset G_{n+1}
\]

has been constructed.  Define its **full untagged source preimage**

\[
 A'_{n+1}
 :=
 \Phi_{n+1}^{-1}(C_{n+1})\cap A_n.
\]

Then, without choosing one source leaf per output leaf,

\[
 \Phi_{n+1}(A'_{n+1})=C_{n+1}.
\]

The proof is elementary but important:

1. the forward inclusion follows from the definition of the preimage;
2. for every \(\gamma\in C_{n+1}\subset G_{n+1}\), the definition
   \(G_{n+1}=\Phi_{n+1}(A_n)\) supplies at least one
   \(\alpha\in A_n\) with \(\Phi_{n+1}(\alpha)=\gamma\); and
3. every such \(\alpha\) belongs to \(A'_{n+1}\).

Thus the line-1569 equality can be realized canonically at the level of
sets.  The symbol in that equality must be \(A'_{n+1}\), not
\(A_{n+1}\), because line 1572 compares the two families.

This set-level observation sharpens the previous “arbitrary selector”
diagnosis: a selector is not needed to obtain surjectivity onto
\(C_{n+1}\).  What remains unproved is:

- that the full preimage has the regularity required of a
  sublamination in the authors' analytic category;
- that its intermediate images satisfy all fine/coarse marking
  conditions;
- that “maximal” means greatest, so that
  \(A'_{n+1}\subset A_{n+1}\); and
- the relative width control on its complement.

The full-preimage reading is also the one most consistent with KKL's
nearby proof style.  At line 1411 they assert a source subwave \(A'\)
with \(B'=F_*A'\), and at lines 1356, 1442, 1454, 1754, and 1772 they
form subwaves by leaf predicates.  None of those passages introduces a
one-leaf-per-output selector.  They do not, however, supply the missing
measurability or closed-lamination lemma for the present full preimage.

If these regularity and greatestness clauses hold, then

\[
 A'_{n+1}\subset A_{n+1}
\]

and hence

\[
 A_n\setminus A_{n+1}
 \subset
 A_n\setminus A'_{n+1}.
\]

There is also an exact two-charge partition:

\[
\begin{aligned}
 A_n\setminus A'_{n+1}
 &=
 \Phi_{n+1}^{-1}(G_{n+1}\setminus R_{n+1})
 \\
 &\qquad\dot\cup\
 \Phi_{n+1}^{-1}(R_{n+1}\setminus C_{n+1}),
\end{aligned}
\]

where every preimage is taken inside \(A_n\).  If the output
decomposition is genuine, then

\[
 R_{n+1}\setminus C_{n+1}
 =
 Y_{n+1}\dot\cup Z_{n+1}.
\]

These are the strongest useful exact set identities.  They expose two
different analytic charges:

1. **extraction/collision charge**
   \(\Phi_{n+1}^{-1}(G_{n+1}\setminus R_{n+1})\);
2. **noncentral-output charge**
   \(\Phi_{n+1}^{-1}(Y_{n+1}\cup Z_{n+1})\).

By contrast, for an arbitrary noninjective map \(\Phi\) and
\(B\subset A\), only

\[
 \Phi(A)\setminus\Phi(B)
 \subset
 \Phi(A\setminus B)
\]

is automatic.  The reverse inclusion fails whenever a discarded and a
retained source leaf have the same untagged image.  Therefore no
untagged output difference can by itself upper-bound the discarded
source width.

If source occurrences are tagged, the exact difference identity is
restored.  With

\[
 \widehat\Phi_{n+1}(\alpha)
 :=
 (\alpha,\Phi_{n+1}(\alpha)),
\]

one has

\[
 \widehat\Phi_{n+1}(A_n\setminus A_{n+1})
 =
 \widehat\Phi_{n+1}(A_n)
 \setminus
 \widehat\Phi_{n+1}(A_{n+1}).
\]

This is only a set identity.  A proof still has to put the correct
analytic width on the tagged family and compare it with source width.

### 6.1 Why the printed line-1576 difference has the wrong support

Assume all favorable regularity and greatestness clauses, so that
\(A'_{n+1}\subset A_{n+1}\) and hence
\(C_{n+1}\subset S_{n+1}\).  Then

\[
 S_{n+1}\setminus C_{n+1}
\]

consists only of terminal paths supplied by source leaves retained in
\(A_{n+1}\) but not represented by the selected central subfamily.
It contains no record of a source leaf in
\(A_n\setminus A_{n+1}\) whose terminal path lies outside
\(S_{n+1}\), and it also loses any discarded occurrence which collides
with a retained untagged path.

The defect is already visible in finite set theory.  Let
\(A_n=B\dot\cup D\), let \(A_{n+1}=A'_{n+1}=B\), and let the terminal
map send \(B\) onto \(C_{n+1}=S_{n+1}\).  Give the leaves of \(D\)
terminal images outside \(S_{n+1}\).  Then

\[
 S_{n+1}\setminus C_{n+1}=\varnothing,
\qquad
 A_n\setminus A'_{n+1}=D,
\]

and \(D\) can carry arbitrary source width.  This countermodel uses
only the printed set relations.  It shows that line 1576 cannot be a
formal consequence of those relations.

Replacing its right side by
\(R_{n+1}\setminus C_{n+1}\) still omits the extraction/collision
charge
\(\Phi_{n+1}^{-1}(G_{n+1}\setminus R_{n+1})\).  The exact two-charge
partition above, rather than either untagged output difference alone,
is therefore necessary.

## 7. Exact form of the missing relative continuation theorem

### 7.1 Minimal sufficient theorem

The logically minimal Gate N1 statement is:

> **Relative stationary continuation, minimal form.**  
> For every \(b\geq1\) there is \(C_b<\infty\) such that, for every KKL
> stationary datum \(F,\mathcal T,\mathcal I,BL_0\) satisfying the
> hypotheses in Sections 2--3 above and every Wave \(A\) ending at
> \(BL_0\), there exist nested subwaves
> \[
> A_0,A_1,\ldots,A_{N-1},\qquad N=b+3,
> \]
> with
> \[
> A_0=A^{N\text{-nbr}}\setminus A^{\rm sh},
> \quad
> F_*^nA_n\text{ a Wave ending at }BL_0,
> \]
> and, for every \(0\leq n<N-1\),
> \[
> \mathcal W(A_n\setminus A_{n+1})\leq C_b.
> \]
> The constant is independent of \(q,n,F,A\), and all analytic widths.

This statement is exactly sufficient for the telescope at lines
1586--1589.  It avoids the undefined \(A_N\) and does not require a
globally consistent printed \(X_n\)-sequence.

It is not sufficiently explanatory to count as a completed analytic
proof.  The following occurrence-resolved form records the mechanism
which must be established.

### 7.2 Occurrence-resolved and counterexample-sensitive form

For every stage \(0\leq n<N-1\), a complete proof must construct:

1. the untagged terminal map
   \(\Phi_{n+1}:A_n\to G_{n+1}\);
2. a standard measurable model of the source lamination and a Borel
   terminal map, or an equivalent foliation-level construction;
3. a distinguished \(BL_0\)-endpoint and a retained restriction
   occurrence at every intermediate step, including both marking
   filters from lines 2096--2097;
4. a typed output Wave
   \(R_{n+1}\subset G_{n+1}\);
5. a disjoint output decomposition
   \[
   R_{n+1}
   =
   C_{n+1}\dot\cup Y_{n+1}\dot\cup Z_{n+1}
   \]
   with the three geometric types in Section 5, strengthened so that
   \(Z_{n+1}\) is localized or is a union of at most \(c_b\) localized
   subwaves with additive width accounting;
6. the full source continuation
   \[
   A'_{n+1}
   =
   \Phi_{n+1}^{-1}(C_{n+1})\cap A_n,
   \]
   proved to be an admissible subwave and contained in the chosen
   \(A_{n+1}\); and
7. constants \(C_b,D_b<\infty\), independent of \(q,n,F,A\), satisfying
   the two **source-relative** estimates
   \[
   \mathcal W\!\left(
     \Phi_{n+1}^{-1}(G_{n+1}\setminus R_{n+1})
   \right)
   \leq C_b
   \tag{RSC-1}
   \]
   and
   \[
   \mathcal W\!\left(
     \Phi_{n+1}^{-1}(Y_{n+1}\cup Z_{n+1})
   \right)
   \leq
   D_b\bigl(
     \mathcal W(Y_{n+1})+\mathcal W(Z_{n+1})
   \bigr)+C_b.
   \tag{RSC-2}
   \]

The theorem must additionally prove:

\[
 R_{n+1}=R_{n+1}^{(N-n-1)\text{-nbr}},
\]

and either

\[
 R_{n+1}^{\rm sh}=\varnothing
\]

or a replacement estimate charging every short output birth to the
source-relative buffer in (RSC-1).

Under these clauses, Propositions `prop:over critical` and
`prop:away from critical` give

\[
 \mathcal W(Y_{n+1})+\mathcal W(Z_{n+1})=O_b(1).
\]

The exact partition in Section 6, monotonicity, (RSC-1), and (RSC-2)
then give

\[
\begin{aligned}
 \mathcal W(A_n\setminus A_{n+1})
 &\leq
 \mathcal W(A_n\setminus A'_{n+1})\\
 &\leq
 \mathcal W\!\left(
   \Phi_{n+1}^{-1}(G_{n+1}\setminus R_{n+1})
 \right)\\
 &\quad+
 \mathcal W\!\left(
   \Phi_{n+1}^{-1}(Y_{n+1}\cup Z_{n+1})
 \right)\\
 &\leq C'_b.
\end{aligned}
\]

This derivation does not infer a relative estimate from an aggregate
one.

### 7.3 Why the published aggregate Wave lemma is insufficient

KKL Lemma `lem:wave` at lines 2149--2152 gives, under its own source
ending-degree hypothesis, only an extracted Wave \(R\) satisfying

\[
 \mathcal W(Q)\leq\mathcal W(R)+O(1+\log d).
\]

It does not state:

- a source subwave whose complement has bounded width;
- (RSC-1) for the preimage of the omitted output paths;
- (RSC-2) for arbitrary output subfamilies;
- preservation of nonshortness; or
- compatibility with sequential occurrence choices.

An aggregate inequality permits a large discarded source family to be
compensated by a large retained output family.  It cannot prove Gate
N1.

### 7.4 The strongest directly relevant imported precedent

Dudko--Lyubich's annular buffer lemma, `Feigen.tex` lines 2821--2842,
does make a source-side statement.  For a degree-\(m\) covering of
closed annuli and a genuine Wave above one boundary interval \(J\), it
constructs a source subwave on which the covering is injective and
loses only \(O(\log m)\) source width.

That lemma has the right **relative direction** for (RSC-1), but the
KKL input \(S_n\) is only a Wave ending at the multi-interval \(BL_0\),
whose length is at most \(6b\).  The locked source does not reduce
\(S_n\) to one DL annular Wave above one fixed interval.  A viable proof
must therefore establish a finite coherent-packet reduction:

1. split the retained restrictions by distinguished central interval,
   sheet, and deck-span class;
2. apply the source-side annular buffer lemma within each admissible
   packet;
3. prove that inter-packet output collisions have total source width
   \(O_b(1)\), rather than retaining only the widest packet; and
4. prove that the union of the surviving packet images is a
   lamination with the required central/over/away decomposition.

Choosing only one of finitely many packets and losing a fixed fraction
of the source width would not prove an additive \(O_b(1)\) estimate.

## 8. Ambiguity ledger

| source phrase or symbol | viable readings | consequence |
|---|---|---|
| “the maximal subwave” at line 1548 | greatest eligible subwave; arbitrary inclusion-maximal subwave | only the greatest reading implies every eligible \(A'_{n+1}\) is contained in \(A_{n+1}\) |
| \(X_n\) at line 1560 and \(X_{n+1}\) at line 1564 | local raw/central variables; one global sequence | the global-sequence reading is time-inconsistent; local alpha-renaming \(R_{n+1},C_{n+1}\) is safe |
| \(S_{n+1}\) at line 1565 | literal \(S_{n+1}\); intended raw output \(R_{n+1}\) | only the latter controls the actual \(Y,Z\) subfamilies |
| \(A_{n+1}\) in the line-1569 equality | literal; intended \(A'_{n+1}\) | the following inequality forces the primed reading |
| “decompose” at line 1564 | literal disjoint partition; cover by three subwaves | the width calculation needs disjointness modulo a width-zero boundary set |
| “localized to \(BL_0\)” | ends at one interval contained in \(BL_0\); ends somewhere in the whole multi-interval | only the first agrees with the formal definition of localized |
| \(Z_{n+1}\) “subordinate to” the complement | one localized Wave; an arbitrary Wave with a longer end | Proposition `prop:away from critical` requires the first, or a separately bounded localized decomposition |
| unbreakable path | one untagged output; one retained restriction occurrence | only the first follows from lines 2161--2162 |
| \(F_*^n\) versus \(f_*^n\iota_n^*\) on paths | sequential equality; equality only on multi-intervals | the source proves only the latter interval statement |
| Wave output “with no short leaves” at line 1560 | consequence of Lemma `lem:wave`; additional pruning/transport theorem | the lemma supplies no such conclusion |
| \(S_{n+1}\setminus C_{n+1}\) in line 1576 | charge for discarded source; extra central output occurrences | it records the latter and can be empty while the discarded source is large |

The most conservative coherent reading makes the following corrections:

\[
\begin{array}{rcl}
\text{printed }X_n\text{ at stage }n&\rightsquigarrow&R_{n+1},\\
\text{printed decomposed }X_{n+1}&\rightsquigarrow&C_{n+1},\\
\text{printed }S_{n+1}\text{ in the unbreakability appeal}
&\rightsquigarrow&R_{n+1},\\
\text{printed }A_{n+1}\text{ in line 1569}
&\rightsquigarrow&A'_{n+1}.
\end{array}
\]

These repairs make the objects typeable.  They do not prove
(RSC-1), (RSC-2), shortness transport, or greatestness.

## 9. Adversarial failure certificates for Gate N1

A claimed proof of Gate N1 fails if any one of the following occurs.

1. **Hidden occurrence multiplicity.**  
   \(F_*\gamma\) is one untagged path but two retained restrictions
   realize it, and the proof silently treats the restriction as unique.

2. **Cross-leaf output collision.**  
   Distinct leaves of \(S_n\) have unique individual outputs, but those
   outputs cross, so \(G_{n+1}\) is not a lamination.

3. **Incomparable continuations.**  
   Two eligible central source subwaves have crossing output unions.
   There is no greatest eligible \(A_{n+1}\), only different maximal
   choices.

4. **Aggregate compensation.**  
   \(\mathcal W(S_n)\leq\mathcal W(R_{n+1})+C_b\) holds while
   \(\mathcal W(\Phi_{n+1}^{-1}
   (G_{n+1}\setminus R_{n+1}))\) is unbounded.

5. **Output short birth.**  
   A nonshort \(N\)-unbreakable source leaf has a short terminal image,
   leaving \(Z_{n+1}^{\rm sh}\) uncontrolled.

6. **Central endpoint swap.**  
   Different retained restrictions exchange which endpoint lies in
   \(BL_0\), destroying one coherent localized central packet.

7. **Sequential/one-shot filter mismatch.**  
   A path survives the one-shot \((f^{n+1},\iota_{n+1})\) restriction
   but is removed by an intermediate fine/coarse filter, or conversely.

8. **Packet selection by proportion.**  
   A proof retains the widest of \(O_b(1)\) packets and thereby loses a
   fixed fraction, rather than \(O_b(1)\) additive width.

A valid failure record must identify the first stage \(n\), source
leaves or positive-width source subfamily, retained restriction
occurrences, fine/coarse marked intervals, output paths, and the exact
failure among (RSC-1), (RSC-2), shortness transport, or greatestness.

## 10. Source-locked verdict and immediate frontier target

The following statements are established directly from the locked
source and elementary set theory:

1. the only declared stationary families are
   \(A_0,\ldots,A_{N-1}\), with \(N=b+3\);
2. the untagged terminal maps \(\Phi_r\) are functions on
   \(A^{N\text{-nbr}}\);
3. \(S_n=\Phi_n(A_n)\) has residual
   \((N-n)\)-unbreakability;
4. \(S_{n+1}\subset G_{n+1}=F_*S_n\);
5. once a central output \(C_{n+1}\) exists, its full source preimage is
   a canonical set mapping exactly onto it; and
6. the discarded source has the exact two-charge partition in
   Section 6.

The following are not established:

1. a globally consistent printed \(X_n\)-sequence;
2. source-lamination regularity of the full central preimage;
3. existence of a greatest central continuation;
4. a coherent retained-restriction packet for the actual \(S_n\);
5. bounded source width of output-collision/extraction loss;
6. relative transfer of the over/away output charge;
7. a localized or uniformly finitely localized decomposition of the
   away family \(Z_{n+1}\);
8. preservation of nonshortness; and
9. the resulting bound
   \(\mathcal W(A_n\setminus A_{n+1})\leq C_b\).

Accordingly, Gate N1 remains **open**.

The immediate frontier theorem is not another aggregate Wave estimate.
It is the following packet-level statement:

> **Coherent-packet source-pruning target.**  
> For the actual stationary \(S_n\), construct a finite
> \(b\)-controlled partition of retained restriction occurrences such
> that source-side annular pruning loses \(O_b(1)\) total width,
> every positive-width inter-packet collision is either retained in
> one common output lamination or charged \(O_b(1)\) by a proved shift
> estimate, and the surviving full central preimage is an admissible
> continuation subwave.  The construction must imply (RSC-1) and
> (RSC-2), not merely an aggregate output-width inequality.

This is the precise point at which a new analytic argument, or an exact
counterexample in the stationary KKL geometry, is required.
