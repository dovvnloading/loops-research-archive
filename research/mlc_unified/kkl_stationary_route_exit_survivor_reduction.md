# KKL stationary route exits: exact survivor reduction

## 1. Status and purpose

This note proves a source-typed reduction for the unresolved stationary
route defect.  It does **not** prove that the defect is empty or
bounded.

The reduction separates three logically different kinds of selected
route exit:

1. the ambient KKL leaf breaks within the proof-used horizon;
2. the ambient leaf remains unbreakable but is already short; and
3. the ambient leaf remains unbreakable, is not absorbed by the
   maximal short subwave, and nevertheless loses the selected marked
   route.

The first two classes are already represented in

\[
 B_A=A^{H\text{-br}}\cup A^{\rm sh}.
\]

Only the third class is a new residual.  In particular, KKL's
one-step breaking argument cannot be applied to that residual: its
defining leaves are unbreakable.

The locked source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The source clauses used here are:

- lines 1355--1358: breaking and the \(H\)-breakable/unbreakable
  partition;
- lines 1375--1392: the auxiliary family
  \(B_A=A^{H\text{-br}}\cup A^{\rm sh}\);
- lines 1423--1494: KKL's one-step breaking response;
- lines 2083--2097: actual immersion restrictions and the marking
  filter; and
- lines 2128--2162: the \(F_*=f_*\iota^*\) action and the definition
  of a breaking path.

The marked whole-route continuation problem is source-audited in
`kkl_stationary_two_occurrence_source_attack.md`.  The collar
conductance obstruction is source-audited in
`kkl_stationary_uniform_collar_charge_attack.md`.

VAAPC-I, UPTCR, and MLC remain open.

## 2. Frozen occurrence space

Fix a source-native Wave \(A\) and a finite proof-used horizon
\(H\geq1\).  The set identities below hold for every such \(H\).
Applications of KKL's later controllability and `small breaking'
properties require the specific source-selected horizon \(H=N\);
finite horizon alone does not supply those properties.  In the
stationary application this selected \(N\) is bounded in terms of the
fixed parabolic bound \(b\).

Let \(\Lambda_A\) be a leaf-indexed parameter space for the actual
native Wave lamination.  A usable occurrence construction must supply
a standard Borel structure, the native transverse measure or
equivalent marked-lamination width typing, and a projection which does
not duplicate one target leaf under several occurrence tags.  These
analytic and measurable data are hypotheses below, not consequences
of the finite record format.
A **segmented marked route record** over a leaf \(\alpha\in\Lambda_A\)
contains:

\[
 \mathfrak r(\alpha)=
 \left(
  \alpha;\,
  h,r,\epsilon;\,
  \{\gamma_j,\delta_j,J_j,a_j,\phi_j\}_{j<r};\,
  (\widetilde\gamma_r,J_r,\tau_r);\,
  \mathcal I,\mathcal O,\mathcal S,\mathcal F;\,
  \mathsf q
 \right).
\tag{2.1}
\]

Here:

- \(1\le h\le H\) is the declared horizon;
- \(1\le r\le h\) is the first route-failure stage;
- \(\epsilon\) is the oriented route role;
- \(\gamma_j\) is the full proper stage restriction for \(j<r\);
- \(\delta_j\) is the corresponding ambient stage path;
- \(J_j\) and \(a_j\) are the nested occurrence window and
  reparameterization;
- \(\phi_j\) is the common truncated trace at a completed earlier
  stage;
- \(\widetilde\gamma_r\) is the maximal partial lift at the first
  failure stage, \(J_r\) is its continuation window, and \(\tau_r\)
  is its failure endpoint;
- \(\mathcal I,\mathcal O,\mathcal S,\mathcal F\) retain the complete
  access, obstacle, sheet, and marking-filter records; and
- \(\mathsf q\) is a first-failure code.

For a post-path marking or filter failure, the record may additionally
contain a full proper \(\gamma_r\).  For a continuation failure it
must not: the absence of that full path is the failure being recorded.
Definition (2.1) records data; it does not assert that such a record
exists.

### Definition 2.1 (single-valued first-exit selector)

A **first-exit selector** is a partial Borel map

\[
 s_A:\Lambda_A\dashrightarrow\mathfrak R_{\le H}
\tag{2.2}
\]

such that:

1. the record \(s_A(\alpha)\) lies over \(\alpha\);
2. \(s_A(\alpha)\) is defined if and only if at least one proof-used
   route role over \(\alpha\) has a first failure through the declared
   horizon;
3. at most one record is selected over each leaf;
4. its failure stage is the globally earliest stage among all failed
   proof-used route roles over \(\alpha\); and
5. ties between route roles at that stage are resolved by one fixed
   priority order.

Write

\[
 E_A=\operatorname{dom}s_A\subset\Lambda_A
\tag{2.3}
\]

for the selected route-exit family.

The single-valued condition is essential.  Without it, one leaf with
several failed presentations could be charged several times, and
neither a leaf-family width nor the KKL breakable/unbreakable
partition would be correctly typed.

No existence, completeness, or Borelness theorem for (2.2) is claimed
here.  The propositions below apply to every selector satisfying
Definition 2.1; constructing such a selector on the actual KKL family
is part of the open analytic route-exit obligation.

## 3. Ambient breaking time

For \(\alpha\in\Lambda_A\), define its first ambient breaking time
through horizon \(H\) by

\[
 \beta_H(\alpha)=
 \min\left\{
  0\le m<H:
  F_*^m\alpha\text{ is a single path and breaks under }F_*
 \right\},
\tag{3.1}
\]

with \(\beta_H(\alpha)=\infty\) if every iterated image required before
time \(H\) remains a single path.

This is an inductive definition.  Once a path breaks, later symbols
\(F_*^j\alpha\) need not denote a single path and are not used to
define an additional breaking time.

By KKL lines 1355--1358,

\[
\begin{aligned}
 A^{H\text{-br}}
 &=\{\alpha\in A:\beta_H(\alpha)<\infty\},\\
 A^{H\text{-nbr}}
 &=\{\alpha\in A:\beta_H(\alpha)=\infty\}.
\end{aligned}
\tag{3.2}
\]

These are complementary source-native subfamilies of \(A\).
For every quantitative use below, the occurrence construction must
also prove that \(A^{H\text{-br}}\),
\(A^{H\text{-nbr}}\), and \(A^{\rm sh}\) are measurable in the
chosen target-leaf parameter space and carry the same native
transverse-width typing.  KKL use their widths as subfamilies; the
marked occurrence refinement must preserve that measurability rather
than merely preserve their set-theoretic labels.

The selected route failure in (2.2) and ambient breaking in (3.1) are
different predicates.  The first follows one named restriction,
sheet, access, and filter record.  The second asks whether the complete
filtered image \(F_*\) of the ambient path is a single path.  A
selected restriction may fail while another retained restriction
keeps the ambient image single.

## 4. The exact three-way partition

Let \(A^{\rm sh}\) be KKL's maximal short subwave.  Define

\[
\begin{aligned}
 E_A^{\rm br}
   &=E_A\cap A^{H\text{-br}},\\
 E_A^{\rm sh}
   &=E_A\cap A^{H\text{-nbr}}\cap A^{\rm sh},\\
 E_A^{\rm surv}
   &=E_A\cap A^{H\text{-nbr}}\setminus A^{\rm sh}.
\end{aligned}
\tag{4.1}
\]

The superscript `surv' means that the ambient path survives as one
path through the full horizon even though its selected marked route
does not survive.

### Proposition 4.1 (route-exit survivor reduction)

The families in (4.1) are pairwise disjoint and exhaust \(E_A\).
Moreover, for

\[
 B_A=A^{H\text{-br}}\cup A^{\rm sh},
\tag{4.2}
\]

one has

\[
\begin{aligned}
 E_A^{\rm br}\cup E_A^{\rm sh}&\subset B_A,\\
 E_A^{\rm surv}\cap B_A&=\varnothing.
\end{aligned}
\tag{4.3}
\]

Thus \(E_A^{\rm surv}\) is the unique selected route-exit class not
already represented by the two native terms in \(B_A\).

#### Proof

Equation (3.2) gives the disjoint exhaustive partition

\[
 A=A^{H\text{-br}}\sqcup A^{H\text{-nbr}}.
\tag{4.4}
\]

Intersect (4.4) with \(E_A\).  Then partition
\(E_A\cap A^{H\text{-nbr}}\) by membership in \(A^{\rm sh}\).  This
gives the disjoint union

\[
 E_A=
 E_A^{\rm br}\sqcup E_A^{\rm sh}\sqcup E_A^{\rm surv}.
\tag{4.5}
\]

The first line of (4.3) follows from the definitions of
\(E_A^{\rm br}\), \(E_A^{\rm sh}\), and \(B_A\).

For the second line, every member of \(E_A^{\rm surv}\) lies in
\(A^{H\text{-nbr}}\) and outside \(A^{\rm sh}\).  By (4.4) it also
lies outside \(A^{H\text{-br}}\).  Hence it lies outside their union
\(B_A\). \(\square\)

### Corollary 4.2 (correct relabelling rule)

Suppose a stationary leaf decomposition is constructed on one native
transverse occurrence space, with each leaf assigned to exactly one
class.  Any selected route-exit leaf in \(E_A^{\rm br}\) must be
relabelled as \(A^{H\text{-br}}\), and any leaf in \(E_A^{\rm sh}\)
must be relabelled as \(A^{\rm sh}\).  After this relabelling, the only
route-exit residual is \(E_A^{\rm surv}\).

#### Proof

The relabellings are the two inclusions in the first line of (4.3).
Because the occurrence decomposition assigns each leaf once, moving
a leaf to its already valid \(B_A\)-class neither deletes nor
duplicates its transverse mass.  Proposition 4.1 shows that exactly
the survivor class remains outside \(B_A\). \(\square\)

### Qualification 4.3

Corollary 4.2 is a rule for rebuilding the underlying disjoint
proof-use partition.  It does not follow merely by manipulating a
previous coarse inequality

\[
 \mathcal W(A)\le
 \mathcal W(B_A)+\cdots+\mathcal W(E_A),
\]

because that inequality may have forgotten whether a leaf was counted
twice.  The relabelling must occur before widths are summed, on the
single-valued occurrence space of Definition 2.1.

## 5. Why KKL one-step breaking does not discharge the survivor

### Proposition 5.1 (source-scope exclusion)

No leaf of \(E_A^{\rm surv}\) belongs to the \(H\)-breakable part of
\(A\).  Consequently KKL lines 1423--1494 cannot be applied to
\(E_A^{\rm surv}\) merely on the ground that the selected route
exited.

#### Proof

By (4.1),

\[
 E_A^{\rm surv}\subset A^{H\text{-nbr}}.
\tag{5.1}
\]

KKL's proof at lines 1423--1494 begins with leaves of the one-step
breakable family \(A^{\rm br}\), after assuming that family has a
definite width fraction.  Every member of (5.1), in contrast, remains
unbroken at each of the first \(H\) ambient stages.  Therefore the
source hypothesis for the three-case breaking partition is absent.
\(\square\)

This is not a semantic subtlety.  KKL line 2083 takes **all** proper
restriction paths, line 2097 applies the marking filter, and line 2161
calls the ambient path broken only when the resulting \(F_*\)-image is
not a single path.  Failure of one selected restriction does not imply
failure of every retained restriction.

### Corollary 5.2 (correction to the response program)

A theorem of the form

\[
 \text{every marked route exit is an actual KKL break}
\tag{5.2}
\]

would absorb the route-exit family into \(A^{H\text{-br}}\); it would
not create a genuinely separate responsive residual.

For the actual residual \(E_A^{\rm surv}\), the needed theorem is
instead one of:

\[
\begin{array}{ll}
\text{continuation:}
 &E_A^{\rm surv}=\varnothing;\\[1mm]
\text{charge:}
 &\mathcal W(E_A^{\rm surv})
   \le C_b\bigl(V(F)+R(F)+1\bigr);\\[1mm]
\text{response:}
 &\mathcal W(E_A^{\rm surv})>\epsilon\mathcal W(A)
   \Longrightarrow A\text{ is terminal},
\end{array}
\tag{5.3}
\]

where the response alternative requires a new source-typed
construction and cannot cite the one-step breakable-family proof
circularly.

### Proposition 5.3 (pointwise survivor route-switch certificate)

Let \(\alpha\in E_A^{\rm surv}\).  In this proposition only,
transition stages are numbered
\(j=0,\ldots,H-1\); a stage numbered \(r+1\) in the record convention
of Section 2 is numbered \(r\) below.  Write

\[
 \delta_0=\alpha,\qquad
 \delta_{j+1}=F_{j*}\delta_j
 \quad(0\le j<H),
\tag{5.4}
\]

where the stage index is written explicitly when the pulled
immersion, covering, or marking changes.  Each \(F_{j*}\) is the
actual native stage action used in the definition of
\(H\)-unbreakability; an independently changed marking is not
substituted.  Every \(\delta_j\) in (5.4) is one nonempty proper
retained path.

For a proper ambient path \(\delta_j\), define its retained predecessor
fiber over \(\delta_{j+1}\) by

\[
\begin{split}
 \operatorname{Ret}_j(\delta_j,\delta_{j+1})
 =
 \{\,\gamma:\;&
 \gamma\in\iota_j^*\delta_j,\quad
 \gamma\text{ is a path in the fine pulled marking},\\
 &\gamma\text{ is not discarded as subordinate to one coarse
 interval},\quad
 f_{j*}\gamma=\delta_{j+1}\,\}.
\end{split}
\tag{5.5}
\]

Then

\[
 \operatorname{Ret}_j(\delta_j,\delta_{j+1})\ne\varnothing
 \qquad(0\le j<H).
\tag{5.6}
\]

Let \(r\) be the first failed stage of the selected marked route.
There is a pointwise full alternative stagewise retained predecessor
flag

\[
 \widehat{\mathfrak S}_\alpha
 =
 \left(
  \delta_0;\,
  \widehat\gamma_0,\delta_1,\ldots,
  \widehat\gamma_{H-1},\delta_H
 \right),
\qquad
 \widehat\gamma_j\in
 \operatorname{Ret}_j(\delta_j,\delta_{j+1}),
\tag{5.7}
\]

which agrees with the selected valid chain before \(r\) and has one
of the following two first-switch certificates at \(r\):

1. **strict path replacement:** the named stage-\(r\) occurrence is
   not an element of the retained predecessor fiber (for example it
   is nonproper, discarded by the marking filter, or has the wrong
   covering image), and \(\widehat\gamma_r\) is a different full
   retained restriction; or
2. **marked-state switch:** the named full retained restriction exists
   geometrically but fails the declared access, obstacle, occurrence,
   sheet, remote-end, complete-target-portion, or
   future-compatibility state.  A proper KKL restriction may map by
   the immersion to only a strict subpath of the target leaf.  The
   same underlying curve may therefore serve as
   \(\widehat\gamma_r\), while its actual route state differs from the
   prescribed state.

#### Proof

Because \(\alpha\in A^{H\text{-nbr}}\), KKL's definition of
\(H\)-unbreakability says inductively that each \(F_{j*}\delta_j\) is
a single path.  The word “single” includes existence: it is not the
empty set.

By KKL lines 2083 and 2096--2097, \(\iota_j^*\delta_j\) is first
restricted to full proper source paths and then filtered to the paths
in the fine marking which are not subordinate to one coarse pulled
interval.  By line 2141, \(F_{j*}=f_{j*}\iota_j^*\) is formed from
exactly those retained restrictions.  Since its value is the
nonempty singleton \(\{\delta_{j+1}\}\), at least one retained
\(\gamma\) maps to \(\delta_{j+1}\).  This proves (5.6).

Choose one element of each of the finitely many nonempty sets (5.6).
Every chosen \(\widehat\gamma_j\) is full, proper, survives both
marking filters, satisfies

\[
 \iota_j(|\widehat\gamma_j|)\subset|\delta_j|,
 \qquad
 f_{j*}\widehat\gamma_j=\delta_{j+1},
\tag{5.8}
\]

and hence gives the pointwise stagewise flag (5.7).  Before the first
failed stage, use the already valid selected occurrence.

At stage \(r\), either the named occurrence is not an element of
\(\operatorname{Ret}_r(\delta_r,\delta_{r+1})\), in which case the
chosen retained path is a strict replacement, or it is such an
element.  In the latter case the occurrence is a full proper **source
restriction** and the native filter has succeeded; this does not say
that its immersion image covers the complete declared target portion.
The declared route can therefore first fail only in one of its
additional marked-state or complete-portion predicates.  This is the
second case.  The cases are exhaustive. \(\square\)

If, as in the proof-used Wave setting, every \(\delta_j\) is given by
a simple oriented Wave-leaf representative, then every
\(\widehat\gamma_j\) is an embedded covering lift and the containment
in (5.8) satisfies Lemma 4.2 of
`kkl_stationary_segmented_occurrence_binder.md`.  That lemma supplies
the unique occurrence window and reparameterization at every stage.
Under this additional verified simple-Wave typing, (5.7) is therefore
a segmented retained prefix flag.  It is not one full proper path in
the deepest fiber product, and it gives no endpoint-survival theorem
for the truncated earlier coordinates.

### Qualification 5.4

Proposition 5.3 is pointwise.  Finite choice proves (5.7) for one
leaf; it proves neither:

1. a Borel choice
   \(\alpha\mapsto\widehat{\mathfrak S}_\alpha\);
2. a uniform bound on the number of retained predecessor paths or
   marked states;
3. preservation of transverse width under that choice; nor
4. a terminal or numerical response to a large switch family.

Those are the analytic tasks.  The proposition removes a weaker,
incorrect picture in which an ambient survivor has no full
continuation at all.

### Corollary 5.5 (marked witness completeness suffices)

The survivor family is empty if, at every proof-used stage, the
following marked witness-completeness property holds:

> whenever \(F_{j*}\delta\) is a singleton along a declared route, the
> named occurrence is a full member of its retained predecessor fiber
> and realizes the declared access, sheet, obstacle, occurrence,
> remote-end, complete-target-portion, localization, attachment and
> parent-routing, cyclic-order and monodromy, relative-cover, filter,
> and future-compatibility state—in other words, every predicate in
> the frozen first-failure code universe.

Other retained predecessor classes are allowed; uniqueness is not
needed for this sufficient condition.

#### Proof

If a survivor existed, take its first failed stage.  Strict path
replacement would contradict full retained membership of the named
occurrence, while marked-state switch would contradict realization of
the declared state.  The exhaustive dichotomy leaves no case.
\(\square\)

Thus the continuation alternative in (5.3) has been reduced to a
falsifiable marked witness-completeness theorem.  If that theorem
fails, the first switch record in Proposition 5.3, rather than an
untyped “lost route,” is the replacement invariant.

## 6. Finite first-failure extraction

The survivor reduction also identifies the smallest measurable
subproblem on which a new response theorem must act.

Raw access, obstacle, component, sheet, and marking identifiers need
not have cardinality bounded by \(b\); finite horizon does not prove
otherwise.  Assume, as a separate hypothesis, a **uniform finite
response-type quotient**

\[
 q_A:\{\text{raw first-failure records for }A\}
 \longrightarrow\mathcal L_b
\tag{6.1}
\]

such that:

1. \(|\mathcal L_b|\le L(b)<\infty\);
2. every distinction used by a classwise analytic response theorem
   survives \(q_A\); and
3. the quotient is Borel on the selected occurrence space.

Put

\[
 L_b=|\mathcal L_b|\le L(b).
\tag{6.2}
\]

For \(\ell\in\mathcal L_b\), let

\[
 E_{A,\ell}^{\rm surv}
 =
 \{\alpha\in E_A^{\rm surv}:
   q_A(s_A(\alpha))=\ell\}.
\tag{6.3}
\]

The Borel properties in Definition 2.1 and (6.1) are required so that
(6.3) is a measurable subfamily.  Without a uniformly bounded quotient
one may repeat the arguments below with a block-dependent label count,
but the factor \(1/L_b\) and the resulting terminal constants are not
uniform and cannot promote a global obligation.

### Proposition 6.1 (finite priority extraction)

Assume the response-type quotient above and extremal-width
subadditivity on the finitely many marked families (6.3).  If

\[
 \mathcal W(E_A^{\rm surv})
 >
 \epsilon\mathcal W(A),
\tag{6.4}
\]

then some \(\ell\in\mathcal L_b\) satisfies

\[
 \mathcal W(E_{A,\ell}^{\rm surv})
 >
 \frac{\epsilon}{L_b}\mathcal W(A).
\tag{6.5}
\]

#### Proof

The single-valued priority selector gives

\[
 E_A^{\rm surv}
 =
 \bigcup_{\ell\in\mathcal L_b}E_{A,\ell}^{\rm surv}.
\tag{6.6}
\]

Finite subadditivity gives

\[
 \mathcal W(E_A^{\rm surv})
 \le
 \sum_{\ell\in\mathcal L_b}
 \mathcal W(E_{A,\ell}^{\rm surv}).
\tag{6.7}
\]

If every summand were at most
\(\epsilon\mathcal W(A)/L_b\), the right side of (6.7) would be at
most \(\epsilon\mathcal W(A)\), contradicting (6.4). \(\square\)

No additivity of arbitrary extremal-width families is used.

### Corollary 6.2 (classwise response suffices)

Suppose that for every \(\epsilon>0\) and every
\(\ell\in\mathcal L_b\), there are constants
\(0<\delta_{b,\epsilon,\ell}<1\) and
\(\eta_{b,\epsilon,\ell}<\infty\), independent of the individual
block and input controllability, such that

\[
 \mathcal W(E_{A,\ell}^{\rm surv})
 >
 \frac{\epsilon}{L_b}\mathcal W(A)
 \Longrightarrow
 A\text{ is }
 (\delta_{b,\epsilon,\ell},\eta_{b,\epsilon,\ell})
 \text{-terminal}.
\tag{6.8}
\]

Then the survivor family satisfies the response alternative in (5.3)
with

\[
\begin{aligned}
 \delta_{b,\epsilon}
 &=\min_{\ell\in\mathcal L_b}
   \delta_{b,\epsilon,\ell}>0,\\
 \eta_{b,\epsilon}
 &=\max_{\ell\in\mathcal L_b}
   \eta_{b,\epsilon,\ell}<\infty.
\end{aligned}
\tag{6.9}
\]

#### Proof

Apply Proposition 6.1 and then (6.8) to the selected label.  A Wave
which is \((\delta_\ell,\eta_\ell)\)-terminal is also
\((\delta,\eta)\)-terminal whenever
\(\delta\le\delta_\ell\) and \(\eta\ge\eta_\ell\): the vertical
inequality weakens as \(\delta\) decreases, and an
\(\eta_\ell\)-controllable response Wave is also
\(\eta\)-controllable after adding empty localized pieces.  Therefore
the finite minimum and maximum in (6.9) give constants valid for every
possible selected label. \(\square\)

Corollary 6.2 reduces the analytic response problem to finitely many
single first-failure types only after the uniform quotient (6.1) is
constructed.  It does not prove (6.8) for any type.

## 7. Exact unresolved survivor certificate

After Proposition 4.1, the first genuinely uncharged record has the
following complete certificate:

\[
 \mathfrak o=
 \left(
  \alpha,\,
  s_A(\alpha),\,
  \beta_H(\alpha)=\infty,\,
  \alpha\notin A^{\rm sh}
 \right).
\tag{7.1}
\]

Expanded, (7.1) says:

1. \(\alpha\) is an actual proof-used leaf;
2. one single-valued marked route record has a first failed stage,
   route role, access, sheet, obstacle, and filter code;
3. the complete ambient \(F_*\)-image remains one retained path at
   every stage through \(H\); and
4. \(\alpha\) is not in the maximal short subwave.

The obstruction is not yet an actual native counterexample.  To
produce one, all four clauses must be instantiated on a source-native
stationary KKL block.  Conversely, a proof that no such record exists
would establish the continuation alternative in (5.3).

If the uniform response-type quotient (6.1) exists, the least
quotient-level replacement state is the finite vector

\[
 \mathbf S_A=
 \left(
  \mathcal W(E_{A,\ell}^{\rm surv})
 \right)_{\ell\in\mathcal L_b},
\tag{7.2}
\]

with the complete marked occurrence data retained behind every
coordinate.  A single scalar total can be used only after a theorem
shows that all labels have the same transport and response behavior.
If (6.1) does not exist, (7.2) must be replaced by the raw
block-dependent label family together with its label-count or end
compactification; it is then an uncontrolled discrete factor, not a
uniform finite state.

## 8. Adversarial audit

1. **Route failure is not ambient breaking.**  The two predicates are
   defined separately in (2.2) and (3.1).
2. **No double counting.**  The selector is single-valued; a leaf with
   several presentations receives one priority record.
3. **Early ambient breaks are absorbed.**  They lie in
   \(A^{H\text{-br}}\) by definition, irrespective of which selected
   route failed.
4. **Short survivors are absorbed.**  They lie in \(A^{\rm sh}\).
5. **The true residual is unbreakable and is not absorbed by the
   maximal short subwave.**  This is \(E_A^{\rm surv}\), not all route
   exits.  No stronger leafwise notion of “nonshort” is inferred.
6. **KKL's breaking proof is not used outside its scope.**
   Proposition 5.1 blocks that circular shortcut.
7. **A coarse inequality is not silently repartitioned.**
   Qualification 4.3 requires reconstruction on the occurrence space.
8. **No arbitrary additivity is assumed.**  Proposition 6.1 uses only
   finite subadditivity.
9. **Measurability is not inferred from pointwise continuation.**
   Definition 2.1 states it as an open construction requirement.
10. **Finite horizon is not a quantitative estimate.**  It yields a
    finite factor only after the uniformly bounded
    response-type quotient (6.1) is proved; it is not a width bound.
11. **The survivor vector is not declared uniformly bounded.**
    Equation (7.2) is a replacement state if continuation and response
    both fail.
12. **No diagnostic promotes an analytic clause.**

## 9. Result

The proved conclusion of this note is:

\[
\boxed{
\begin{array}{c}
\text{all selected stationary route exits reduce to}\\
\text{the native breakable term, the native short term, or}\\
\text{one precisely typed ambient-survivor family outside the short term.}
\end{array}}
\tag{9.1}
\]

The immediate analytic target is no longer a bound for all local
collar exits.  It is the finite family of classwise statements (6.7)
for the survivor records (7.1), or a proof that those records cannot
occur on the actual stationary KKL block.
