# KKL stationary retained-realization: exact source audit

## 1. Result and status

This note audits the earliest unresolved predicate in
`kkl_stationary_tsnc_source_reduction.md`, namely

\[
 \operatorname{RR}(n,\alpha),
\tag{1.1}
\]

for the two portions named at line 1603 of the locked
Kahn--Koropecki--Lyubich (KKL) source.

The audit proves one strictly weaker statement.

> **One-chain theorem.**
> For every proof-used \(n\) and every
> \(\alpha\in A_{n+1}\), the definitions of \(A_0,\ldots,A_{n+1}\)
> and \(N\)-unbreakability supply at least one retained proper
> restriction component at every stage.  All retained components at
> one stage have the same untagged proper image, and that image is the
> leaf selected by the next \(A_r\)-Wave.

This theorem neither constructs nor identifies the two separator-side
occurrences used in line 1603.  The first missing assertion is:

\[
\begin{split}
 \operatorname{TB}(n,\alpha):\quad&
 \text{the two topological portions named at line 1603 bind to two}\\
 &\text{specified, distinct, retained proper components of the actual}\\
 &\text{iterated immersion restriction, with compatible stagewise}\\
 &\text{factorizations and complete pulled-interval records.}
\end{split}
\tag{1.2}
\]

Here `TB` means **two-occurrence binder**.  The locked source does not
prove (1.2).  Its ideal-marking results prove that the KKL action is
defined, but they do not bind either topological portion to a retained
path.  Its itinerary proposition expressly permits adjacency and
same-pulled-interval transitions in place of actual restriction paths.
Moreover, the proof-used \(BL_0\)-end is outside the source's
proper-action range and satisfies

\[
 F_*BL_0=\partial_{\mathrm C}T.
\tag{1.3}
\]

Thus neither proper interval transport nor a terminal interval label
recovers the missing occurrence.

Consequently `RR`, two-sided noncollision, and the stationary Wave
repair remain open.  Nothing in this note promotes VAAPC-I, UPTCR, or
MLC.

## 2. Locked sources

The locked KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The source occurrences used below are:

- lines 757--761: the ideal marking on
  \(U\setminus T\) and the definition of controllable Waves;
- lines 838--866: \(BL_j\) as the Carathéodory-boundary
  multi-interval of the Hubbard-tree limb \(L_j\);
- lines 1241--1274: the actual pulled-tree description,
  existence of \(\iota^*\mathcal I\), refinement by
  \(f^*\mathcal I\), combinatorial action, and
  \(F_*BL_0=\partial_{\mathrm C}T\);
- lines 1279--1286: proper action only on
  \(BL_{[b,q-b-2]}\);
- lines 1292--1307: the unique stretching multi-interval and the
  absorption of every new \(T'\setminus T\) component at one attachment
  point;
- lines 1354--1358: breaking and \(N\)-unbreakability;
- lines 1547--1548: \(N=b+3\), \(A_0\), and the nested
  \(A_r\);
- lines 1597--1603: the selected pulls, the one-path sentence at
  line 1600, the separator statement, and the two portions;
- lines 2065--2078: proper covering pushforward;
- lines 2081--2108: immersion restriction, the retention filter, and
  the three-way itinerary alternative;
- lines 2128--2167: the set-valued action \(F_*=f_*\iota^*\),
  breaking, and combinatorial end transport.

The locked Kahn source is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

It supplies the fiber-product iterates and their stage maps.  This
audit does not replace a geometric restriction component by a
parameterized fiber-product path: the former is KKL's set of every
retained proper component.

## 3. Typed stage notation

Put

\[
 \mathcal V=U\setminus T,
 \qquad
 \mathcal V'=U'\setminus T',
 \qquad
 T'=f^{-1}(T).
\tag{3.1}
\]

The one-step correspondence consists of

\[
 f,\iota:\mathcal V'\longrightarrow\mathcal V.
\tag{3.2}
\]

Its two source markings are

\[
 \mathcal I^{f}=f^*\mathcal I,
 \qquad
 \mathcal I^{\iota}=\iota^*\mathcal I.
\tag{3.3}
\]

KKL retain from \(\iota^{-1}(\beta)\) only components which

1. are proper paths in
   \((\mathcal V',\mathcal I^{f})\); and
2. are not subordinate to one interval in
   \(\mathcal I^{\iota}\).

Denote this one-step retained set by

\[
 \mathscr R(\beta).
\tag{3.4}
\]

With KKL's untagged convention,

\[
 F_*\beta
 =
 \left\{
    f(\gamma):\gamma\in\mathscr R(\beta)
 \right\}.
\tag{3.5}
\]

Repeated equal images in (3.5) occur only once as a set element.
The output is again a path in \(\mathcal V\), so every successive
application of \(F_*\) uses the same one-step correspondence (3.2).

Separately, Kahn's fiber product packages a simultaneous depth-\(r\)
restriction as

\[
 P_r,\ I_r:
 \mathcal V^{[r]}
 =
 U^r\setminus P_r^{-1}(T)
 \longrightarrow
 \mathcal V,
\tag{3.6}
\]

where \(P_r=f^r\) is proper and \(I_r=\iota_r\) is the iterated
immersion.  A sequence of independently chosen members of
\(\mathscr R(\beta_j)\) need not be the sequence of projections of one
component of \(I_r^{-1}(\alpha)\).  That compatibility is part of the
missing binder.

For line 1603, \(A_{n+1}\) must be defined.  Since
\(N=b+3\), its actual proof-used range is

\[
 b\le n\le N-2=b+1.
\tag{3.7}
\]

No assertion below uses the undefined \(A_N\).

## 4. What the actual ideal-marking results prove

### Proposition 4.1 (the KKL action is defined)

For the native KKL one-step correspondence used by \(F_*\), the source
proves that \(\iota^*\mathcal I\) is defined and that

\[
 f^*\mathcal I
 \quad\text{refines}\quad
 \iota^*\mathcal I.
\tag{4.1}
\]

Thus the retention rule (3.4) and the action (3.5) are well typed.

#### Proof

KKL Proposition 6.5, at lines 1254--1261, describes the pullback of a
multi-interval \(I\) as the union of its direct immersion inverse and
the Carathéodory boundaries of components of \(T'\setminus T\) attached
at \(I\).  Lines 1267--1271 then state that these pulled intervals form
a partial ideal marking and that \(f^*\mathcal I\) refines the induced
\(\iota^*\mathcal I\).  This is precisely (4.1).  Since \(F_*\) maps
path families back to the base surface, the same well-typed action can
be applied successively. \(\square\)

Proposition 4.1 is important negatively as well as positively.  The
failure of `RR` is not a failure to define the native KKL marking.
Rather, it is a failure to prove that the two particular portions in
line 1603 survive the already defined marking and filter.

### Proposition 4.2 (proper versus end-proper at the critical end)

KKL prove combinatorial, hence end-proper, action on the complete
Hubbard-tree ideal boundary.  They prove proper action only on

\[
 BL_{[b,q-b-2]}.
\tag{4.2}
\]

The proof-used interval \(BL_0\) is not in (4.2), and the source gives

\[
 F_*BL_0=\partial_{\mathrm C}T.
\tag{4.3}
\]

#### Proof

The end-proper conclusion is at lines 1263--1271.  The proper range is
Proposition 6.7, lines 1279--1286.  Since \(b\ge1\), index \(0\) is
outside that range.  Equation (4.3) is stated at line 1274.
\(\square\)

End-properness controls the end-intervals of a pulled multi-interval.
It does not remove the attached Carathéodory-boundary pieces in
Proposition 6.5, prove that a prescribed inverse trace is a proper
path, or prove that it is not subordinate to one pulled interval.
Those are exactly the decisions made by the filter at lines
2096--2097.

### Proposition 4.3 (native attachment absorption)

At one native pull, all components of \(T'\setminus T\) meet \(T\) at
one point \(x\), and Proposition 6.5 absorbs their Carathéodory
boundaries into \(\iota^*x\).  For the particular selected extra pull
used in KKL's stretching-interval proof, its boundary multi-interval is
contained in the interior of one interval

\[
 \widetilde I_{\mathrm{str}}\in\iota^*\mathcal I
\tag{4.4}
\]

associated to KKL's stretching multi-interval.  Consequently a proper
restriction component that is subordinate to this absorbed boundary
region is removed by the line-2097 filter.

#### Proof

KKL lines 1302--1304 state that every component of
\(T'\setminus T\) meets \(T\) at a single point \(x\).  Proposition
6.5 puts the attached Carathéodory boundaries in \(\iota^*x\).
Lines 1303--1304 additionally put the boundary multi-interval
\(BL_{[b,q-b-2]}'\) of the selected extra pull inside
\(\operatorname{Int}\iota^*x\).  If \(x\) belongs to an interval of
\(\mathcal I\), line 1304 takes its immersion pullback as
\(\widetilde I_{\mathrm{str}}\).  If \(x\) is an endpoint, line 1305
takes \(\operatorname{Int}\iota^*x\) itself as that interval.  Thus this
selected absorbed boundary lies in the single interval (4.4).  KKL
line 2097 then discards any restriction path subordinate to it.
\(\square\)

Proposition 4.3 is a genuine filter hazard, but it is not by itself an
`RR` counterexample.  To prove actual removal of
\(P^-_{n,\alpha}\) or \(P^+_{n,\alpha}\), one would still have to prove
all of the following:

1. which iterated attachment component contains \(L_0^{n+1}\), and
   whether it belongs to the selected absorbed region in Proposition
   4.3;
2. its complete predecessor chain down to the one-step point \(x\);
3. the actual pulled interval containing each end of the candidate
   portion; and
4. that the complete candidate path is subordinate to
   \(\widetilde I_{\mathrm{str}}\), rather than merely having one end
   in its absorbed boundary.

The locked source records none of these four occurrence-level facts.
Endpoint membership in an absorbed interval does not imply
subordination of the whole path.  Therefore the present evidence is an
exact missing attachment identification, not a proved failure of
`RR`.

## 5. The exact consequence of \(A_r\) and unbreakability

### Theorem 5.1 (one retained chain, with possible collisions)

Fix \(n\) in (3.7) and \(\alpha\in A_{n+1}\).  Put

\[
 \beta_0=\alpha,
 \qquad
 \beta_r=F_*^r\alpha
 \quad(1\le r\le n+1).
\tag{5.1}
\]

Then:

1. every \(\beta_r\) is a single retained marked path;
2. for every \(0\le r\le n\),
   \(\mathscr R(\beta_r)\ne\varnothing\);
3. for every
   \(\gamma\in\mathscr R(\beta_r)\),
   \[
     f(\gamma)=\beta_{r+1};
   \tag{5.2}
   \]
4. at least one sequence
   \[
     \gamma_{r+1}\in\mathscr R(\beta_r),
     \qquad
     f(\gamma_{r+1})=\beta_{r+1},
   \tag{5.3}
   \]
   can be chosen through the finite horizon;
5. for each \(r\le n+1\), \(\beta_r\) belongs to the Wave
   \(F_*^rA_r\) ending at \(BL_0\).

The theorem does not assert uniqueness of \(\gamma_{r+1}\), coherence
of independently chosen components in the complete fiber product, or
that either \(\gamma_{r+1}\) represents one of the two portions in
line 1603.

#### Proof

The subwaves are nested, so

\[
 \alpha\in A_{n+1}\subset A_r
 \qquad(0\le r\le n+1).
\tag{5.4}
\]

Also

\[
 A_{n+1}\subset A_0
 \subset A^{N\text{-nbr}}.
\tag{5.5}
\]

Since \(n+1<N\), Definition 7.1 at lines 1354--1358 says that
\(\beta_r\) does not break at any stage \(0\le r\le n\).  By the
definition at line 2161,

\[
 F_*\beta_r
 \quad\text{is a single path}.
\tag{5.6}
\]

It cannot be empty, since the empty set is not a single path.
Equations (3.4)--(3.5) and (5.6) prove assertions 1--3.  Finite choice
gives (5.3), proving assertion 4.

Finally, the definition at lines 1547--1548 says that
\(F_*^rA_r\) is a Wave ending at \(BL_0\).  Equations
(5.1) and (5.4) put \(\beta_r\) in that Wave, proving assertion 5.
\(\square\)

### Corollary 5.2 (what unbreakability does not remember)

If two or more members of \(\mathscr R(\beta_r)\) have the same
\(f\)-image, Theorem 5.1 records only the common path
\(\beta_{r+1}\).  Neither \(A_r\) nor \(F_*^rA_r\) records which
restriction component, sheet, attached interval, or parent access
produced that occurrence.

#### Proof

This is immediate from the set definition (3.5) and equation (5.2).
\(\square\)

## 6. Why the two portions do not follow

KKL line 1603 names the portions

\[
\begin{aligned}
 P^-_{n,\alpha}&:
 BL_0\longrightarrow L_0^{n+1},\\
 P^+_{n,\alpha}&:
 L_0^{n+1}\longrightarrow
 \partial_{\mathrm C}T\setminus BL_0.
\end{aligned}
\tag{6.1}
\]

These arrows are not typed in the locked source as elements of any
\(\mathscr R_r(\beta_r)\).  In particular:

1. \(L_0^{n+1}\) belongs to a pulled tree, whereas
   \(\alpha\) is initially a path in the base complementary surface;
2. immersion restriction is set-valued and can split;
3. the filter can remove a component even when its endpoint labels
   occur in an interval itinerary;
4. different retained components can have one untagged covering image;
5. independently selected one-stage components need not form one
   component of the full fiber-product restriction.

Line 1600 asserts that a leaf of \(A_r\) restricts to *a* path having
one endpoint in \(L_0^r\).  The source gives no stagewise proof of that
sentence in the stationary lemma, does not type the endpoint as a
specific interval or prime end, and does not obtain two paths from it.
Even if line 1600 is accepted as a source-local assertion, it supplies
only one unspecified path and therefore does not imply (1.2).

### Proposition 6.1 (the itinerary proposition stops before `RR`)

KKL Proposition 2099 cannot promote the two routes in (6.1) to retained
proper paths.

#### Proof

For two consecutive intervals in its itinerary, Proposition 2099
allows exactly three alternatives:

1. an actual restriction path;
2. adjacency of the intervals; or
3. containment of both intervals in one pulled target interval.

`RR` requires the first alternative for each proof-used transition of
each of the two portions, together with survival of the line-2097
filter.  No source result excludes alternatives 2 and 3 for the
critical-limb route.  Proposition 4.2 shows why the available proper
interval theorem cannot do so: the route has a \(BL_0\)-end, while
\(BL_0\) is outside the proper range (4.2) and expands as in (4.3).
Proposition 4.3 gives the complementary obstruction: a new deep-tree
boundary can be absorbed into one coarse immersion-pulled interval and
is then subject to the single-interval filter.
Therefore the conclusion of Proposition 2099 is strictly weaker than
`RR`. \(\square\)

This is the first exact source obstruction.  Deck phase and endpoint
noncollision arise only after two retained occurrences have been
constructed.  The locked source does not reach that antecedent.

## 7. The missing two-occurrence binder

For a source-checkable replacement, define a binder record

\[
 \mathfrak B^\epsilon_{n,\alpha}
 =
 \left(
   \Gamma^\epsilon;
  \{\gamma^\epsilon_{r}\}_{r=1}^{n+1};
   \{J^\epsilon_{r,\mathrm{in}},
     J^\epsilon_{r,\mathrm{out}}\}_{r=1}^{n+1};
   \{s^\epsilon_r,p^\epsilon_r,\phi^\epsilon_r\}_{r=1}^{n+1}
 \right),
 \qquad \epsilon\in\{-,+\},
\tag{7.1}
\]

where:

- \(\Gamma^\epsilon\) is one connected component of the complete
  iterated immersion restriction
  \(I_{n+1}^{-1}(\alpha)\);
- \(\gamma^\epsilon_r\in\mathscr R(\beta_{r-1})\) is its
  \(r\)-th one-step projection;
- \(J^\epsilon_{r,\mathrm{in/out}}\) are its actual endpoint intervals
  in \(f^*\mathcal I\);
- \(s^\epsilon_r\) is its sheet;
- \(p^\epsilon_r\) is its Hubbard-tree parent component and access;
- \(\phi^\epsilon_r\) records the filter decision and, when retained,
  certifies that the path is not subordinate to one interval in
  \(\iota^*\mathcal I\).

The binder theorem needed before `RR` is:

> **Stationary two-occurrence binder.**
> If \(\alpha\in A_{n+1}\) fails the source's pass-through predicate at
> \(K_0^n\), there exist two records
> \(\mathfrak B^-_{n,\alpha}\) and
> \(\mathfrak B^+_{n,\alpha}\) such that:
>
> 1. their complete components are distinct;
> 2. their routes realize the two portions in (6.1);
> 3. every stage projection is a proper marked path;
> 4. every filter flag is retained;
> 5. the stage projections commute with the fiber-product maps;
> 6. each terminal image is a Wave with its actual terminal interval
>    pair recorded.

This theorem implies `RR`.  It does not imply that the two terminal
Waves are geometrically distinct; that is the later selected-corridor
and deck-noncollision problem.

## 8. Failure certificate and proof strategy

An attempted proof should inspect the two records simultaneously.  At
the first failed stage \(r\), record

\[
\begin{split}
(&n,\alpha,\epsilon,r,
  \text{source and target pulled intervals},
  \text{parent access},\text{sheet},\\
 &\text{one of: no proper component, non-path, single-interval
 subordination, adjacency-only transition, same-pullback transition,
 split component, or incompatible fiber-product predecessor}).
\end{split}
\tag{8.1}
\]

The correct proof order is:

1. construct the two complete fiber-product components;
2. project them to every stage;
3. compute \(f^*\mathcal I\) and \(\iota^*\mathcal I\) using
   KKL Proposition 6.5;
4. identify every \(T'\setminus T\) attachment point and determine
   whether the candidate route enters
   \(\widetilde I_{\mathrm{str}}\);
5. discharge the path, subordination, and filter tests at each stage;
6. prove the two routes realize (6.1);
7. only then compute selected-corridor confinement, access flags, and
   deck noncollision.

Starting with a coarse interval itinerary reverses this order: the
itinerary may use adjacency or same-pullback containment at precisely
the stage where an actual occurrence is required.

## 9. Skeptic audit

1. The actual KKL ideal marking is not declared missing; Proposition
   4.1 records that it exists.
2. End-properness is not upgraded to properness at \(BL_0\).
3. The source's one-path sentence is not promoted to two paths.
4. A set-valued restriction is not replaced by a chosen parameterized
   lift.
5. Untagged equality does not supply occurrence uniqueness.
6. Adjacency in Proposition 2099 is not relabeled as a physical path.
7. A same-pulled-interval transition is not relabeled as a retained
   path.
8. The proof-used range is \(n=b,b+1\), not every unrestricted
   \(n\ge b\).
9. Attachment absorption is recorded as a possible filter mechanism,
   not promoted to an actual discarded portion without a complete
   itinerary and subordination proof.
10. No deck predicate is invoked before two retained occurrences exist.
11. The note proves no stationary alignment, Wave amplification,
    VAAPC-I, UPTCR, or MLC theorem.

## 10. Conclusion

The native source proves the marked action and guarantees at least one
retained chain for every unbreakable selected leaf.  It does not bind
the two separator-side portions to two retained chains.  The first
unresolved analytic statement is the stationary two-occurrence binder,
not deck separation.

Until that binder is proved on the actual pulled Hubbard-tree surfaces,
`RR(n,\alpha)` and every later TSNC predicate remain open.
