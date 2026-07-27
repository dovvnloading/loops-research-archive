# Independent audit of the KKL stationary two-occurrence binder pass

> **Subsequent semantic correction.**  This audit correctly verifies
> the relation-chain map formulas and the common-parameter equalizer
> theorem, but its original verdict treated that strict theorem as the
> minimal model of KKL's sequential \(F_*\)-action.  That inference is
> false: KKL requires
> \(\iota(\gamma_{r+1})\subset f(\gamma_r)\), not equality of the two
> whole proper paths.  The corresponding fiber-product coordinates
> are cumulative truncations and may be nonproper.  Thus Sections 4
> and 9 below apply only to strict synchronized occurrences.  The
> corrected necessary invariant is the segmented nested-window record
> in `kkl_stationary_segmented_occurrence_binder.md`.  No ledger
> promotion may rely on the stronger record.

## 1. Scope and binary verdict

This audit independently checks

```text
kkl_stationary_two_occurrence_binder_design.md
audit_stationary_two_occurrence_binder_schema.py
kkl_stationary_two_occurrence_source_attack.md
```

against the locked Kahn and Kahn--Koropecki--Lyubich sources.

The binary verdict is:

1. the finite relation-chain coordinate calculus, coordinate formulas,
   synchronization lemma, and interior reconstruction theorem are
   **proved**;
2. the retained-chain consequence is **proved after repair** of one
   missing base marked-path hypothesis;
3. the certificate soundness theorem is **proved after repair** of its
   breaking-time conclusion;
4. the local-homeomorphism raw-component lemma, finite iterated
   embedded-neighborhood lemma, conditional local-seed corollary, and
   upper-half-disk countermodel are **proved under their explicitly
   stated hypotheses**;
5. the actual KKL bilateral route realization, complete path
   continuation, ideal-end landing, coordinate properness, marking,
   filter survival, terminal family membership, and terminal
   noncollision are **not proved**.

In particular, this audit does not promote

```text
KKL_STATIONARY_TWO_OCCURRENCE_BINDER
KKL_STATIONARY_RETAINED_PORTION_REALIZATION
KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION
VAAPC-I
UPTCR
MLC
```

All remain open.

## 2. Source integrity

The files were hashed directly during this audit.

The locked KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The locked Kahn source is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The audited source dependencies are:

- Kahn lines 188--214: the pullback universal property and
  set-theoretic/topological equalizer;
- Kahn lines 259--265: the analytic pullback has that underlying
  topological pullback when one leg is an immersion;
- Kahn lines 350--399: the first pseudo-polynomial-like pullback and
  its map orientation;
- Kahn lines 410--421: the finite tower, commuting square, and relation
  iteration;
- Kahn lines 60--77 and 155--178: an immersion is an embedding on a
  neighborhood of the filled set;
- KKL lines 439--461: the pseudo-quadratic-like map and its global
  pullback iteration;
- KKL lines 1241--1274: the pulled Hubbard-tree marking and action;
- KKL lines 1354--1358: breaking and finite unbreakability;
- KKL lines 1547--1603: the stationary Wave construction and the two
  proposed portions;
- KKL lines 1844--1875: ideal markings, proper paths,
  subordination, and Waves; and
- KKL lines 2081--2167: immersion restriction, retention, the
  itinerary alternatives, and breaking.

No claim below uses the undefined \(A_N\) appearing at KKL line 1605.
For line 1603, the valid range is

\[
 b\leq n\leq N-2=b+1,\qquad h=n+1<N.
\]

## 3. Map-type and orientation audit

Put

\[
 i_0=\iota:X_1\to X_0,\qquad f_0=f:X_1\to X_0.
\]

Kahn's first pullback is represented by pairs \((x,y)\) with

\[
 i_0(x)=f_0(y),\qquad i_1(x,y)=y,\qquad f_1(x,y)=x.
\]

Therefore the chronological one-step coordinate order is
\((y,x)\), and the relation-chain condition is

\[
 f_0(z_r)=i_0(z_{r+1}).
\]

This confirms the orientation used in the design note.  It is not the
opposite relation \(i_0(z_r)=f_0(z_{r+1})\).

For the tower maps

\[
 i_r,f_r:X_{r+1}\to X_r,\qquad
 i_r f_{r+1}=f_r i_{r+1},
\]

the proposed coordinate

\[
 q_{h,r}
 =
 f_1\circ\cdots\circ f_{r-1}
 \circ
 i_r\circ\cdots\circ i_{h-1}:X_h\to X_1
\]

is correctly typed.  The rightmost immersion string maps \(X_h\) to
\(X_r\), and the covering string then maps \(X_r\) to \(X_1\).
The endpoint cases are

\[
 q_{h,1}=i_1\cdots i_{h-1},\qquad
 q_{h,h}=f_1\cdots f_{h-1}.
\]

Using

\[
 f_{r-1}i_r=i_{r-1}f_r
\]

successively gives

\[
 f_0q_{h,r}=i_0q_{h,r+1}.
\]

The complete projections are correspondingly

\[
 I_h=i_0q_{h,1},\qquad P_h=f_0q_{h,h}.
\]

Thus the design note's Lemma 3.1 is correct.

The safe relation domain

\[
 X_h=
 \{(z_1,\ldots,z_h):f_0(z_r)=i_0(z_{r+1}),\
 z_r\in X_1\}
\]

is an open part of the ambient pullback surface, and dropping an
initial or terminal relation coordinate preserves the safe condition.
The note correctly does not infer all KKL obstacle and marking
identifications merely from this point-set description.  Those remain
part of the analytic realization certificate.

## 4. Theorem-by-theorem verdict for the binder design

### 4.1 Lemma 3.1

**Verdict: proved.**

All compositions are typed, their order agrees with the first Kahn
pullback, and the commuting-square calculation has the correct
orientation.

### 4.2 Theorem 6.1

**Verdict: proved as an interior categorical theorem.**

Given commonly parameterized paths \(\gamma_r\) satisfying

\[
 f_0\gamma_r=i_0\gamma_{r+1},
\]

the tuple

\[
 \Theta(t)=(\gamma_1(t),\ldots,\gamma_h(t))
\]

lies pointwise in the relation equalizer.  The equalizer carries the
subspace topology, so \(\Theta\) is continuous.  Under the canonical
identification with the recursively constructed Kahn pullback, the
coordinate projections are exactly \(q_{h,r}\).  Equality of all
coordinates gives uniqueness.

This theorem proves no ideal-boundary extension, properness, marking,
retention, component surjectivity, or component separation.  The
qualification in the design note is necessary and correct.

### 4.3 Corollary 6.3

**Verdict: proved.**

Orientation-compatible common parameterizations satisfying all
pointwise equalizer identities are necessary and sufficient for one
interior full-tower occurrence.  Equality of unparameterized images or
unmarked homotopy classes is strictly weaker.

### 4.4 Proposition 6.4

**Verdict before repair: not proved as stated.**

The former semantic core required every lifted coordinate
\(\gamma_r\) to be a retained fine-marked path, but required the
initial trace

\[
 \delta_0=i_0\gamma_1
\]

only to be proper and subordinate to the selected leaf.  The KKL
action \(F_*\delta_0\) is typed only when \(\delta_0\) is a path in
\((X_0,\mathcal I)\).  Properness does not imply the marked-path
non-subordination predicate.

**Repair implemented:** semantic-core clause 5 now requires that
\(\delta_0\) be a proper path in \((X_0,\mathcal I)\) and separately
certifies its image containment in the selected leaf.  The audit
expansion now includes

\[
 \phi^{\rm base}_0
 =
 (\mathrm{Prop}_0,\mathrm{Marked}_0,
 \delta_0((0,1))\subset|\alpha|;\mathsf w_0).
\]

**Verdict after repair: proved.**

At each stage, \(\gamma_r\) is a retained member of
\(\iota^*\delta_{r-1}\), and its covering image is \(\delta_r\).
Induction gives the retained chain.  Containment of the first lifted
path over \(\alpha\) gives the separately stated membership in
\(F_*^h\alpha\).

### 4.5 Proposition 6.5

**Verdict: proved as a non-implication from the abstract map types.**

The complete proper projection \(P_h\) need not be injective on two
different immersion-restriction components.  The explicit quadratic
pseudo-quadratic-like collision model supplies two different proper
source components with one untagged \(z^2\)-image.  The proposition
correctly does not represent that model as an actual KKL Wave block.

### 4.6 Theorem 7.1

**Verdict before repair: conclusion imprecise.**

The previous wording said that two terminal paths imply that the
"source leaf breaks."  KKL line 2161 defines one-step breaking.  Two
paths in \(F_*^h\alpha\) prove instead that \(\alpha\) is not
\(h\)-unbreakable.

**Repair implemented:** let \(m\leq h\) be the first nonsingleton
iterate.  Because the final iterate is nonempty and
\(F_*(\varnothing)=\varnothing\), every earlier iterate is nonempty.
Thus

\[
 F_*^{m-1}\alpha=\{\beta\},\qquad |F_*\beta|\geq2,
\]

so \(\beta\) breaks at a stage strictly before \(h\).

**Verdict after repair: proved as certificate soundness.**

The theorem remains conditional on a supplied analytic certificate and
does not construct one.

### 4.7 Lemma 7.2

**Verdict: proved.**

It is the standard unique-simple-path decomposition in a finite tree.
It supplies no analytic path, access, properness, or retention.

## 5. Executable-schema audit

The script is diagnostic only; string equality cannot prove an
analytic map equality or component statement.  Within that declared
scope, four definite schema defects were repaired:

1. a horizon \(h=0\) was previously accepted;
2. no field required the common full-tower core to be proper;
3. no field required the initial trace to be a marked path contained
   in the selected leaf; and
4. route validation compared the first two labels rather than the
   first and last labels, so it rejected legitimate expanded hit words
   and did not require intervening subarc witnesses.

The repaired schema records a core token, full-core properness, the
base trace, its marked-path and leaf-containment predicates, and route
edge witnesses.  It uses route endpoint semantics.

The former phrase "choose \(t_*\) outside the finite proof-used crossing
set" in the design note also assumed unproved finiteness.  It was
removed.  The record may choose any \(t_*\in(0,1)\); any later cut
avoidance must name a forbidden set and prove that an admissible
parameter exists.

## 6. Source-attack topology audit

### 6.1 Lemma 5.1

**Verdict: proved under the standard KKL ideal-closure convention.**

The exact hypotheses used are:

1. \(X,Y\) are Hausdorff, second-countable surfaces;
2. \(I:X\to Y\) is a local homeomorphism;
3. \(\alpha:(0,1)\to Y\) is a topological embedding;
4. each proposed inverse germ is a continuous lift on its one-sided
   parameter interval; and
5. "approaches an ideal-boundary point" means convergence in an ideal
   closure that separates interior points from ideal ends
   (equivalently for the proof, the germ cannot converge to an
   interior point of \(X\)).

The inverse trace is locally a one-manifold.  On a connected component
\(C\), the parameter map

\[
 t_C=\alpha^{-1}\circ I|_C:C\to(0,1)
\]

is a local homeomorphism.  A circle component is impossible because
its image would be nonempty, compact, and open in \((0,1)\).  On an
oriented interval-type component, the local orientation sign is
locally constant and hence constant; \(t_C\) is therefore strictly
monotone and injective.  Its image is an open interval.

If one component contained germs on both sides of \(t_0\), its
parameter image would contain \(t_0\), and the inverse of \(t_C\)
would force both germs to converge to the same interior point.  This
contradicts ideal-end landing.  The stronger alternative
\(\alpha(t_0)\notin I(X)\) gives the contradiction without using an
ideal compactification.

The lemma does not prove that a maximal component lands at either of
its remote ends.

### 6.2 Lemma 5.3

**Verdict: proved for every fixed finite horizon.**

The exact hypotheses used are:

1. every pullback stage is the Kahn pullback of a
   pseudo-polynomial-like map;
2. every \(K^r\) is compact;
3. \(i_r|_{K^{r+1}}\) is a homeomorphism onto \(K^r\); and
4. Kahn's polynomial-like restriction theorem supplies an open
   neighborhood of \(K^{r+1}\) on which \(i_r\) is an embedding.

At stage \(r\), compactness permits shrinking the embedding
neighborhood so its image lies in the already chosen neighborhood at
stage \(r-1\).  A finite induction makes

\[
 I_h=i_0\cdots i_{h-1}
\]

injective on an open neighborhood \(O_h\) of \(K^h\).  Holomorphic
injectivity makes its image open, and
\(I_h(K^h)=K^0\), so the image is a neighborhood of \(K^0\).

This is an ambient near-filled-set statement.  It does not make
\(I_h:X_h\to X_0\) proper or a covering, and it does not control a
route after the route leaves \(I_h(O_h)\).

### 6.3 Corollary 5.4 and BILI

**Verdict: proved conditionally, with no hidden global extension.**

The corollary requires more than a verbal "passes through" statement:

1. an actual parameter \(t_0\) and encounter point;
2. a short two-sided target subarc contained in \(I_h(O_h)\);
3. isolated incidence with the embedded pulled tree at that point;
4. two specified ideal accesses; and
5. actual one-sided landing at those accesses.

The ambient inverse embedding supplies the two local germs in
\(O_h\setminus T^h\); Lemma 5.1 places them in different raw
components.  No maximal component, remote endpoint, coordinate
properness, marking, or filter survival follows.

Consequently the implication

\[
 \mathrm{BILI}\Longrightarrow
 \text{two distinct raw inverse-trace components}
\]

is sound only with "BILI" read as actual one-sided inverse germs plus
specified ideal-access landing, not as two interval labels.

### 6.4 Upper-half-disk model

**Verdict: valid for its narrow stated purpose.**

For

\[
 \Omega=\mathbb D\cap\{\operatorname{Im}z>0\},
\qquad
 I:\mathbb D\xrightarrow{\phi}\Omega\hookrightarrow\mathbb D,
\]

and the vertical diameter

\[
 \alpha(t)=i(1-2t),
\]

the upper one-sided portion lies in \(I(\mathbb D)\), the lower portion
does not, and the midpoint lies on \(\partial\Omega\).  Carathéodory
extension for the Jordan domain makes the sole inverse component a
proper path in the source disk.  There is no inverse germ over the
lower portion.

The example correctly refutes only

\[
 \text{immersion + Jordan extension + one proper inverse + two target
 portions}
 \Longrightarrow
 \text{two raw inverse components}.
\]

It is not a KKL Hubbard-tree block and is not presented as one.

## 7. Exact first missing full-route theorem

The embedded neighborhood and Wave subordination do not extend the two
local seeds through the complete line-1603 portions.

Fix one local germ and let \(J^\epsilon\) be its maximal continuation
interval along the corresponding parameterized portion of \(\alpha\).
The first missing extension statement is:

\[
 J^-=\text{the full }BL_0\text{-to-}L_0^h\text{ parameter interval},
\qquad
 J^+=\text{the full }L_0^h\text{-to-non-}BL_0\text{ interval}.
\tag{7.1}
\]

Proving (7.1) requires ruling out every finite interior failure:

1. escape of the lift from every compact subset of \(X_h\);
2. exit of the target path from \(I_h(X_h)\);
3. collision with a pulled obstacle or tree component;
4. loss of the selected inverse branch; and
5. sheet or access switching.

A local homeomorphism has local path lifting but need not have the
global path-lifting property of a covering.  Lemma 5.3 controls only a
short subarc inside \(I_h(O_h)\).

Wave subordination, as defined at KKL lines 1867--1875, is a
relative-homotopy and endpoint condition.  It does not imply that a
chosen representative lies in \(I_h(X_h)\), remains in one lift
branch, or has a complete lift.

Even after (7.1), one needs a separate ideal-landing theorem:

\[
 \Theta^\epsilon(t)\longrightarrow
 a^\epsilon_{\rm far}
 \quad\text{at the remote endpoint,}
\tag{7.2}
\]

with a unique specified ideal access.  Existence on the full open
interval does not imply (7.2).  Only then is the full route proper.

After (7.1)--(7.2), the following remain independent:

- properness of every coordinate \(q_{h,r}\Theta^\epsilon\);
- membership in \(f^*\mathcal I\);
- non-subordination to one interval of \(\iota^*\mathcal I\);
- complete parent/attachment provenance;
- terminal Wave-family membership; and
- noncollision of the two terminal images.

This confirms both repair-route verdicts in the source-attack note:
line 1600 plus the separator reaches, at most, conditional local
seeds, and the imported width estimates cannot directly charge bad
leaves before an actual retained sublamination has been constructed.

## 8. Commands and results

The focused schema was executed after repair:

```text
python research\mlc_unified\audit_stationary_two_occurrence_binder_schema.py
stationary binder schema regressions: 12 passed
diagnostic only; no analytic KKL obligation promoted
```

The file compiles:

```text
python -m py_compile \
  research\mlc_unified\audit_stationary_two_occurrence_binder_schema.py
exit code 0
```

The central transfer suite was executed:

```text
python research\mlc_unified\audit_transfer_regressions.py
diagnostic transfer regressions: all passed
```

The proof ledger was audited:

```text
python research\mlc_unified\audit_proof.py
ledger: valid (407 obligations)
statuses: imported=25, proved=283, open=99
target: MLC [open]
```

The atomic source manifest was checked:

```text
python research\mlc_unified\
  generate_kkl_wave_atomic_source_manifest.py --check
PASS ... sha256=
C0A26652B383730E454DCC1FA0CFBD9EEA0DC0FEB45B8F2E92BB4150EDC657D2
```

## 9. Final status boundary

The finite coherence question is closed:

\[
 \text{pointwise Cartesian synchronization}
 \Longleftrightarrow
 \text{one interior full-horizon occurrence}.
\]

The local separation question is conditionally closed:

\[
 \text{two genuine one-sided lift germs with ideal landing}
 \Longrightarrow
 \text{two raw host components}.
\]

The actual KKL problem begins before deck noncollision.  It must first
construct the bilateral local incidence from the native stationary
geometry, continue both germs through their full target portions, and
prove their specified ideal landing and all one-step retention
predicates.  None of those analytic statements follows from the
finite schema or from the current locked source.
