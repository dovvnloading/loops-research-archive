# KKL stationary survivors force a marked route switch

## 1. Result and status

The exact survivor reduction leaves one new family:

\[
 E_A^{\rm surv}
 =
 E_A\cap A^{N\text{-nbr}}\setminus A^{\rm sh},
 \qquad N=b+3.
\tag{1.1}
\]

Every leaf in this family loses its selected marked route, although
the complete ambient KKL path remains a single path at every stage
through \(N\).

This note proves the next source-typed fact:

\[
\boxed{
\begin{minipage}{0.88\linewidth}
At the first named-route failure, ambient unbreakability supplies a
full retained restriction witnessing the same unique next ambient
path.  Either this is a geometrically different replacement path, or
the named path survives geometrically and only its declared marked
state fails.  Repeating the singleton-witness argument constructs,
pointwise, a complete alternative segmented restriction chain through
the remaining horizon.
\end{minipage}}
\tag{1.2}
\]

Thus a survivor is not an unstructured inverse-branch failure.  It
has a finite **marked route-switch certificate**.

The theorem is pointwise.  It does not provide:

- a Borel choice of replacement paths;
- a uniformly bounded number of replacement occurrences;
- proper ideal landing of a failed partial named lift;
- width control for the switch family; or
- a terminal-Wave response.

No stationary obligation, `VAAPC-I`, `UPTCR`, or `MLC` is promoted.

## 2. Locked source and semantics

The locked KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The exact clauses used are:

- lines 1355--1358: a path is \(N\)-unbreakable precisely when its
  successive ambient images do not break at any of the first \(N\)
  stages;
- lines 2081--2084: \(\iota^*\delta\) is the collection of proper
  source paths contained in \(\iota^{-1}(\delta)\);
- lines 2096--2097: only fine-marked paths which are not subordinate
  to one pulled coarse interval are retained;
- lines 2128--2142: \(F_*=f_*\iota^*\) acts on paths and path
  families; and
- line 2161: a path breaks when its complete filtered \(F_*\)-image
  is not a single path.

For a source-native ambient path \(\delta\), define its set of retained
one-step restrictions by

\[
\mathcal R(\delta)
=
\left\{
 \gamma:
 \begin{array}{l}
 \gamma\text{ is a proper path in the fine-marked source surface},\\
 |\gamma|\subset\iota^{-1}(|\delta|),\\
 \gamma\text{ is not removed by KKL's subordinate filter}
 \end{array}
\right\}.
\tag{2.1}
\]

With paths understood up to the source's reparameterization
equivalence, the set-theoretic action is

\[
 F_*\delta
 =
 \{\,f_*\gamma:\gamma\in\mathcal R(\delta)\,\}.
\tag{2.2}
\]

If several restriction paths have the same untagged covering image,
the right side of (2.2) may be a singleton even though
\(\mathcal R(\delta)\) contains several paths.  This is precisely why
ambient singleton continuation does not imply marked-route
uniqueness.

Equation (2.2) is the only interpretation used below.  No global
inverse branch of \(\iota\) is assumed.

## 3. The singleton-witness lemma

### Lemma 3.1 (retained witness)

Suppose \(F_*\delta\) is the single proper path \(\delta^+\).  Then:

\[
 \mathcal R(\delta)\ne\varnothing,
\tag{3.1}
\]

and every \(\gamma\in\mathcal R(\delta)\) satisfies

\[
 f_*\gamma=\delta^+.
\tag{3.2}
\]

#### Proof

By (2.2),

\[
 \{\,f_*\gamma:\gamma\in\mathcal R(\delta)\,\}
 =
 \{\delta^+\}.
\tag{3.3}
\]

The right side is nonempty, so the indexing set
\(\mathcal R(\delta)\) is nonempty.  Every member of the image set on
the left equals the unique member \(\delta^+\), proving (3.2).
\(\square\)

The nonemptiness in (3.1) would fail if \(F_*\delta\) were empty.
But an empty family is not the single proper path \(\delta^+\), so
that case is excluded by the hypothesis rather than silently treated
as unbreakable.

## 4. Ambient singleton chain

Put

\[
 N=b+3,\qquad m=N-1=b+2.
\tag{4.0}
\]

The stationary named route uses pullback levels through \(m\), while
ambient unbreakability supplies one further singleton image through
\(N\).  Fix \(\alpha\in A^{N\text{-nbr}}\).  Define

\[
 \delta_0=\alpha.
\tag{4.1}
\]

Because \(\alpha\) is \(N\)-unbreakable, there are unique untagged
proper paths \(\delta_1,\ldots,\delta_N\) satisfying

\[
 F_*\delta_{j-1}=\{\delta_j\}
 \qquad(1\leq j\leq N).
\tag{4.2}
\]

The braces in (4.2) emphasize singleton path-family equality.  They
do not assert that there is only one restriction witness.

Applying Lemma 3.1 at every stage gives nonempty witness sets

\[
 \mathcal R_j(\alpha)
 :=
 \left\{
   \gamma\in\mathcal R(\delta_{j-1}):
   f_*\gamma=\delta_j
 \right\}
 =
 \mathcal R(\delta_{j-1})
 \ne\varnothing.
\tag{4.3}
\]

Every \(\gamma_j\in\mathcal R_j(\alpha)\) obeys

\[
 \iota(|\gamma_j|)\subset|\delta_{j-1}|,
 \qquad
 f(|\gamma_j|)=|\delta_j|.
\tag{4.4}
\]

The first relation can be strict.  Sequential KKL occurrence
therefore uses an occurrence window, not equality of full
parameterized paths.

## 5. First marked-route failure

Let \(\alpha\in E_A^{\rm surv}\), and let
\(s_A(\alpha)\) be the complete single-valued first-exit record from
`kkl_stationary_route_exit_survivor_reduction.md`.  Let

\[
 1\leq r\leq m=N-1
\tag{5.1}
\]

be its globally first failure stage.

For \(j<r\), the named route supplies full retained paths
\(\gamma_j^{\rm nam}\in\mathcal R_j(\alpha)\), together with their
occurrence windows and declared states.  At stage \(r\), exactly one
of the following two cases occurs after the failure codes have been
made exhaustive.

### Case P: strict path replacement

The named stage-\(r\) occurrence is not a full retained member of
\(\mathcal R_r(\alpha)\).  This includes:

1. a maximal named partial lift which escapes before becoming a full
   proper path;
2. a full topological pullback which has no proper marked endpoints;
   or
3. a full proper pullback discarded by KKL's subordinate filter.

Lemma 3.1 supplies

\[
 \widehat\gamma_r\in\mathcal R_r(\alpha).
\tag{5.2}
\]

This is a strict replacement:

\[
 \widehat\gamma_r
 \ne
 \gamma_r^{\rm nam}
\tag{5.3}
\]

as an occurrence-tagged retained path.  In the partial-lift
subcase, it is also geometrically different from the named initial
germ.  Indeed, if a full replacement lift shared that germ, uniqueness
of local lifts for the immersion would extend the named maximal lift
past its failure time, a contradiction.

In the filtered-full-path subcase, the same occurrence-tagged path
cannot be both removed and retained by the fixed filter.  Hence (5.3)
again holds.  The untagged images may nevertheless coincide:

\[
 f_*\widehat\gamma_r=\delta_r.
\tag{5.4}
\]

### Case S: retained-path state mismatch

The named geometric path survives as a full retained restriction:

\[
 \gamma_r^{\rm nam}\in\mathcal R_r(\alpha),
\tag{5.5}
\]

but it fails the declared marked route state.  Examples of state data
which may fail are:

- the named access or side;
- obstacle absorption/separation status;
- the declared sheet or root ancestry;
- route-role orientation;
- an occurrence-window compatibility flag; or
- a protected marking-survival flag not used by the coarse KKL
  filter.

In this case the singleton witness can be taken to be the same
geometric path,

\[
 \widehat\gamma_r=\gamma_r^{\rm nam},
\tag{5.6}
\]

but the ambient transition carries only the untagged path
\(\delta_r\), not the failed declared state.  The switch is therefore
in the state coordinate rather than in the geometric restriction
path.

Cases P and S are disjoint by (5.5) and exhaustive once every
first-failure code specifies whether the named occurrence was a full
retained KKL path.  A vague code such as “route lost” is not enough
to apply this dichotomy.

In particular, a branch stopped only because it crossed a declared
access/state boundary must first be continued geometrically on the
full immersion domain.  If that continuation is a full retained path,
the failure is Case S.  It may be placed in Case P only if maximal
geometric continuation or the native KKL filter actually prevents a
full retained named occurrence.

## 6. Full alternative chain

### Theorem 6.1 (pointwise route-switch chain)

Let \(\alpha\in E_A^{\rm surv}\) and let \(r\) be its first marked
route-failure stage.  Then there exist full retained proper paths

\[
 \widehat\gamma_r,\widehat\gamma_{r+1},
 \ldots,\widehat\gamma_N
\tag{6.1}
\]

such that, for every \(r\leq j\leq N\),

\[
\begin{aligned}
 \iota(|\widehat\gamma_j|)
 &\subset|\delta_{j-1}|,\\
 f_*\widehat\gamma_j
 &=\delta_j.
\end{aligned}
\tag{6.2}
\]

Together with the successful named prefix

\[
 \gamma_1^{\rm nam},\ldots,\gamma_{r-1}^{\rm nam},
\tag{6.3}
\]

these paths form a complete alternative segmented sequential
occurrence through horizon \(N\).  At stage \(r\) the alternative has
exactly one of the two switch types:

\[
 \mathsf{switch}(\alpha)
 \in\{\mathsf P,\mathsf S\},
\tag{6.4}
\]

where \(\mathsf P\) is strict path replacement and \(\mathsf S\) is
retained-path state mismatch.

#### Proof

At the first failed stage, choose \(\widehat\gamma_r\) as in Case P
or Case S.  For each \(j>r\), the set
\(\mathcal R_j(\alpha)\) is nonempty by (4.3).  Since the horizon is
finite, choose one

\[
 \widehat\gamma_j\in\mathcal R_j(\alpha)
\tag{6.5}
\]

for every \(r<j\leq N\).  Equations (6.2) follow from (4.4).

For \(j<r\), the definition of first failure supplies the successful
named full restriction \(\gamma_j^{\rm nam}\).  Its covering image is
\(\delta_j\), and the next selected restriction is contained in the
immersion preimage of that ambient path.  At the switch stage,

\[
 \iota(|\widehat\gamma_r|)
 \subset|\delta_{r-1}|
 =
 |f_*\gamma_{r-1}^{\rm nam}|.
\tag{6.6}
\]

For \(j>r\),

\[
 \iota(|\widehat\gamma_j|)
 \subset|\delta_{j-1}|
 =
 |f_*\widehat\gamma_{j-1}|.
\tag{6.7}
\]

Thus every successive source path occupies an occurrence window in
the preceding covering image.  For simple oriented path
representatives, Lemma 4.2 of
`kkl_stationary_segmented_occurrence_binder.md` extracts the unique
occurrence map on that window.  The prefix and replacement paths,
together with those maps, satisfy the definition of a segmented
sequential occurrence.

The stage-\(r\) dichotomy is proved in Section 5. \(\square\)

### Qualification 6.2 (pointwise does not mean measurable)

The finite choices in (6.5) prove pointwise existence only.  They do
not prove that the set-valued fields

\[
 \alpha\longmapsto\mathcal R_j(\alpha)
\tag{6.8}
\]

have Borel graphs, compact values, or Borel selectors.  Nor do they
bound

\[
 \#\mathcal R_j(\alpha)
\tag{6.9}
\]

uniformly in the period, rotation denominator, stage, or block.

Consequently Theorem 6.1 cannot by itself define a measurable
replacement lamination or transfer extremal width to the alternative
chain.

### Qualification 6.3 (segmented flag is not a deepest proper path)

Theorem 6.1 constructs the linked stage paths and their occurrence
windows.  By the reconstruction theorem in
`kkl_stationary_segmented_occurrence_binder.md`, this gives compatible
truncated paths at every finite prefix of the Kahn relation.  It does
not imply that the untruncated stage paths are the coordinates of one
full proper path in the deepest fiber product.  The reconstructed
prefix coordinates can be truncated and nonproper, and ideal-endpoint
survival remains a separate obligation.

## 7. Exact uniqueness gate

For a declared stage state \(\sigma_j^{\rm nam}\), let

\[
 \mathcal R_j^{\rm nam}(\alpha)
 =
 \left\{
 \gamma\in\mathcal R_j(\alpha):
 \gamma\text{ realizes }\sigma_j^{\rm nam}
 \right\}.
\tag{7.1}
\]

At the first survivor failure,

\[
 \mathcal R_r(\alpha)\ne\varnothing,
\tag{7.2}
\]

while either:

\[
\begin{array}{ll}
\mathsf P:&
\text{the named occurrence is not a member of }
\mathcal R_r(\alpha);\\[1mm]
\mathsf S:&
\text{the named path belongs to }\mathcal R_r(\alpha)
\text{ but not to }\mathcal R_r^{\rm nam}(\alpha)
\text{ as a state-realizing occurrence.}
\end{array}
\tag{7.3}
\]

This identifies the exact continuation theorem which would eliminate
the survivor family.

### Proposition 7.1 (marked witness completeness implies no survivors)

Assume that for every proof-used ambient singleton chain and every
declared route stage \(j\leq N\):

1. the named route occurrence is a full retained member of
   \(\mathcal R_j(\alpha)\); and
2. every such named occurrence realizes the complete declared marked
   state, equivalently
   \[
     \gamma_j^{\rm nam}\in
     \mathcal R_j^{\rm nam}(\alpha).
   \tag{7.4}
   \]

Then

\[
 E_A^{\rm surv}=\varnothing.
\tag{7.5}
\]

#### Proof

If a survivor existed, take its first failure stage \(r\).  Case P
would contradict clause 1, while Case S would contradict clause 2.
The exhaustive dichotomy leaves no case. \(\square\)

Proposition 7.1 is intentionally stated as a strong sufficient
condition.  It is not imported from KKL.  A weaker theorem could allow
several retained witnesses, provided at least one canonical witness
preserves the declared state coherently through all later occurrence
windows.

## 8. Replacement state if uniqueness fails

If survivor switches occur, the least route-switch record is

\[
\mathfrak W(\alpha)
=
\left(
\begin{array}{c}
r,\ \mathsf{switch}(\alpha),\
\gamma_{<r}^{\rm nam},\
\widetilde\gamma_r^{\rm nam},\
\widehat\gamma_{\ge r},\\
\delta_0,\ldots,\delta_N,\
\text{occurrence windows},\
\text{access/sheet/obstacle/filter states}
\end{array}
\right).
\tag{8.1}
\]

For a quantitative proof, this record must be upgraded to:

1. a Borel field of replacement chains;
2. a uniformly bounded or summably charged replacement multiplicity;
3. proper/end-proper ideal access data;
4. a collision code distinguishing
   - outer-boundary overflow,
   - small-Julia component incidence,
   - critical-end switching,
   - marking/filter state loss, and
   - nonlanding; and
5. a width theorem which either charges the switch or turns a large
   switch family into a terminal Wave.

Without these upgrades, the replacement chain is a pointwise
certificate, not an analytic solution.

## 9. Adversarial audit

1. **Empty image.**  It is not treated as a singleton proper path;
   Lemma 3.1 uses nonemptiness explicitly.
2. **Duplicate covering image.**  Several source paths may map to the
   same \(\delta_j\); ambient unbreakability does not remove this
   multiplicity.
3. **Artificial embedding boundary.**  A named lift is called partial
   only after maximal continuation on the full immersion domain, not
   after hitting an arbitrary collar boundary.
4. **Filtered full path.**  A path removed by the fixed KKL filter is
   not reused as its own retained replacement.
5. **State-only failure.**  A geometrically surviving path can still
   fail a protected access or obstacle state; Case S retains this
   possibility.
6. **No common full parameter path is assumed.**  Successive
   restrictions occupy occurrence windows, as required by the
   segmented-occurrence semantics.
7. **No measurable choice is inferred from finite choice.**
   Qualification 6.2 keeps that obligation open.
8. **No multiplicity bound is inferred from finite horizon.**
9. **No width is inferred from the number of labels.**
10. **No breakable-family argument is applied.**
    Every leaf under study is ambient \(N\)-unbreakable.
11. **No local connectivity is assumed.**
12. **No MLC-level status is changed.**

## 10. Immediate next analytic theorem

The next theorem should be the **Marked Replacement Exclusion or
Charge Theorem**:

> For the actual stationary critical-end route, every route-switch
> certificate in (8.1) is either impossible by marked witness
> completeness, or belongs measurably to a proper vertical,
> small-Julia-incidence, or independently terminal-response packet,
> with constants and multiplicities bounded only by \(b\).

The first countercertificate, if the theorem fails, must name:

- the ambient leaf and first switch stage;
- the dying named partial path or failed marked state;
- the full retained replacement path;
- both occurrence windows and source sheets;
- the access, obstacle, and filter discrepancy;
- the complete replacement itinerary through \(N\); and
- the first class for which no vertical, renormalization, or response
  charge applies.

Until this theorem is proved, the stationary route survivor,
`VAAPC-I`, `UPTCR`, and `MLC` remain open.
