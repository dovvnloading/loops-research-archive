# Hostile audit: fixed-end WAD decomposition and stationary route-exit charge

Date: 2026-07-26  
Status: source-locked audit; no global obligation promoted

## 1. Scope and verdict

This audit checks:

1. `kkl_fixed_end_immersion_switch_wad.md`;
2. `kkl_stationary_route_exit_conductance_reduction.md`; and
3. the pointwise chain used from
   `kkl_stationary_survivor_route_switch_reduction.md`.

The audit focuses on:

- the distinction between leaves, proper paths, arcs, laminations, and
  WAD coefficients;
- validity of restricted WADs;
- the exact meaning of coefficient-norm equality;
- Borel and transverse-measure requirements;
- endpoint degree versus interior total degree;
- the two horizons
  \[
  H=N=b+3,\qquad m=N-1=b+2;
  \]
- the scope of the KKL small-Julia incidence estimate; and
- whether any theorem is stronger than its stated hypotheses.

The verdict is:

\[
\boxed{
\begin{minipage}{0.88\linewidth}
The fixed-end full/exit WAD split is a valid local consequence of
KKL's immersion-decomposition theorem, provided it is understood as
the simultaneous subdivision of the particular target and source
foliations constructed in that theorem.  Its equality is an equality
of paired WAD coefficient norms, not an isometry of arbitrary
extremal-width families.

The vertical route-exit inequality and the charged/response
decomposition are correct conditional reductions after the
measurable packet, ideal-end degree, incidence, and packet-count
hypotheses are stated explicitly.  The locked sources do not construct
those packets for the proposed survivor exits.

Neither note proves the marked stationary repair.  In particular,
neither supplies a Borel replacement lamination, a period-independent
multiplicity bound, the critical-end pass-through theorem, or a
comparison \(R(F)\leq C_b(V(F)+1)\).
\end{minipage}}
\]

Thus `KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR`, `VAAPC-I`,
`UPTCR`, and `MLC` remain open.

## 2. Locked sources

The audited source files and recomputed hashes are:

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5

.tmp_wave_audit/not-all-good2.tex
SHA-256 B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01

.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The controlling source clauses are:

- `not-all-good2.tex`, lines 514--545:
  `thm:immer-decomp`;
- `waves-with-Misha.tex`, lines 1901--1914:
  WAD, coefficient norm, and validity;
- lines 2065--2078:
  covering and pushforward-lamination estimate;
- lines 2080--2097:
  immersion restriction, domination, and native marking filters;
- lines 2141 and 2161--2162:
  \(F_*=f_*\iota^*\) and singleton-path unbreakability;
- lines 2149--2152:
  Wave pushforward;
- lines 2171--2178:
  Shift;
- lines 1513--1532:
  the two independently bounded unbreakable-Wave cases; and
- lines 1591--1617:
  the final stationary alignment and its component-incidence
  consequence.

## 3. Fixed-end WAD audit

### 3.1 Type ledger

The source theorem begins with:

\[
i:V'\longrightarrow V,
\]

a finite-topology holomorphic immersion; a set \(E'\) of source ends
on which \(i\) is proper of degree one; and a valid target WAD \(Y\)
whose arcs have at least one endpoint in \(E=i(E')\).

The proof chooses a partial proper target foliation \(\mathcal F\)
realizing \(Y\).  It orients each leaf from an end in \(E\), lifts it
from the prescribed degree-one source end until it leaves \(V'\), and
assembles the lifted leaves into a partial proper source foliation
\(\mathcal F'\).  It then subdivides:

1. \(\mathcal F\) by target homotopy class; and
2. each target class by the homotopy class of its lifted source leaf.

Consequently the indices in

\[
Y=\sum_a v_a\beta_a,\qquad
Y'\geq\sum_a v_a\beta'_a
\]

refer to paired pieces of those two particular foliations.  They are
not arbitrary labels attached later to a formal WAD expression.

### 3.2 Why the restricted pieces are valid

Let

\[
\mathcal A=\mathcal A_{\rm full}\sqcup\mathcal A_{\rm exit}
\]

be the endpoint alternative supplied by the theorem.  The union of
the source foliation pieces indexed by either class is again a partial
proper foliation: every leaf was already a leaf of \(\mathcal F'\),
and the classification only removes foliation pieces.  The paired
target pieces are likewise subfoliations of \(\mathcal F\).

Therefore the four induced WADs

\[
Y_{\rm full},\quad Y_{\rm exit},\quad
Z'_{\rm full},\quad Z'_{\rm exit}
\]

are valid.  This conclusion depends on the foliation subdivision in
the source proof.  The formally stronger rule

> every subset of the indices in an arbitrary WAD presentation is
> automatically a valid WAD

was rejected: a coefficient presentation alone does not exhibit a
realizing partial proper foliation.

### 3.3 Coefficient-norm calculation

The WAD norm is defined at source line 1906 by

\[
\|W\|=\sum_{\alpha}W(\alpha).
\]

All coefficients are nonnegative.  Hence, even if several paired
indices represent the same arc and their weights combine in the WAD,

\[
\left\|\sum_{a\in\mathcal A_\star}v_a\beta_a\right\|
=
\sum_{a\in\mathcal A_\star}v_a
=
\left\|\sum_{a\in\mathcal A_\star}v_a\beta'_a\right\|,
\qquad
\star\in\{\mathrm{full},\mathrm{exit}\}.
\]

This proves the two paired coefficient-norm equalities.  It does not
prove:

- \(\|Y'\|=\|Y\|\), because the source theorem gives only
  \(Y'\geq\sum_a v_a\beta'_a\);
- equality of the moduli of arbitrary independently selected
  target/source curve families; or
- a canonical full/exit split independent of the realizing foliation,
  orientation, and selected source end.

### 3.4 Survivor-switch corollary

For a target leaf \(\delta\), ambient unbreakability states that the
native filtered image is one nonempty path:

\[
F_*\delta=f_*\iota^*\delta=\{\delta^+\}.
\]

Because \(\iota^*\delta\) in this formula is already restricted to
proper fine-marked paths not discarded by the coarse subordinate
filter, the retained predecessor fiber over \(\delta^+\) is nonempty.
This is a pointwise set-theoretic consequence.

The fixed-end exit leaf and a member of that retained fiber are linked
only after all of the following are identified with the same
stationary stage:

1. the abstract immersion \(i\) and the native \(\iota_j\);
2. the source and target ideal markings;
3. the proper degree-one starting end;
4. the target realizing subfoliation;
5. the native fine/coarse filtering convention; and
6. the complete occurrence, access, sheet, window, and obstacle state.

Even under this identification, the result is only a
witness-relative relation

\[
\{\ell'_{\rm exit}(\delta)\}
\times\operatorname{Ret}(\delta,\delta^+).
\]

The source does not select a Borel member of the second factor or
show that those replacements form a valid WAD.  The quantifier is
“almost every leaf in the stated subfoliation,” relative to its native
transverse measure; “every leaf” would exceed the hypothesis.

### 3.5 Audit of the finite-end selector

Kahn's source fixes the meaning of finite topology at
`.tmp_kl06_source/wad.tex`, lines 10--20:

\[
\text{finite topology}
\quad\Longleftrightarrow\quad
\text{finite genus and finitely many topological ends}.
\]

Thus a proof-used subset of the topological end set is finite for each
individual source surface.  If \(E'=\{e_1,\ldots,e_q\}\) is given the
discrete order and

\[
\mathcal C\subset\Lambda\times E'
\]

is Borel with nonempty fibers, then the first-priority selector is
Borel because

\[
\{\delta:e(\delta)=e_r\}
=
\{\delta:(\delta,e_r)\in\mathcal C\}
\setminus
\bigcup_{t<r}\{\delta:(\delta,e_t)\in\mathcal C\}.
\]

This finite-selection calculation is correct.

Three extra hypotheses or qualifications are indispensable:

1. **Fixed-end eligibility.**  The bare statement
   “\(\mathcal C\) is a Borel candidate relation” does not imply that
   \(i(e)\) is the relevant oriented endpoint of \(\delta\).  It must
   be assumed explicitly that every \((\delta,e)\in\mathcal C\)
   satisfies the target-end equality and every fixed-end hypothesis
   needed in the application.
2. **Borel saturation.**  A standard Borel set of leaf labels does not,
   by that phrase alone, prove that its saturated union in \(V\) is
   Borel.  One must supply a Borel quotient/parametrization
   \(p:Z\to\Lambda\) of the realizing proper lamination, so that
   \(p^{-1}(B)\) is a Borel union of proper leaves for every Borel set
   \(B\) used in the proof.  Kahn's definition at `wad.tex`, lines
   142--160, then shows that this restricted proper sublamination
   induces a valid WAD.
3. **No uniform bound.**  Finite topology gives finite \(q\) for one
   surface, not a period-independent bound \(q\leq q_b\) over all
   stationary blocks.  It also does not make the proof-used access,
   ideal-interval, sheet, or occurrence set finite: KKL's ideal
   markings are allowed to be countable at master-source lines
   1850--1852.  A partition by topological end pairs is therefore
   blockwise finite but need not be a uniform response-state
   partition.

After the first two hypotheses are added, two opposite orientations
can be handled on the same finite end-pair partition.  This proves
only the fixed-end selection and witness-relative WAD bookkeeping.
The assertion that both lifted leaves exit at the same proof-used
occurrence remains a separate geometric hypothesis, and any use of
the resulting partition in a uniform theorem still needs the third
bound or a summable replacement charge.

## 4. Route-exit audit

### 4.1 Horizon and degree bookkeeping

The stationary conventions are:

\[
N=b+3,\qquad H=N,\qquad m=N-1=b+2.
\]

Ambient breakability is tested through \(H\).  The named route
pullbacks being charged have horizons \(1\leq h\leq m\).  For

\[
P_h=f^h:X_h\longrightarrow X_0
\]

the safe total covering degree is

\[
D_h\leq2^h.
\]

Thus

\[
\sum_{h=1}^{m}D_h
\leq\sum_{h=1}^{m}2^h
=2^{m+1}-2
=2^{b+3}-2.
\]

No route is called degree one merely because it has a single
combinatorial label.

The KKL pushforward-lamination lemma is typed by the degree on the
ideal ending set, not just by an interior-degree slogan.  Every packet
to which it is applied must therefore certify:

1. extension of \(P_h\) to the proof-used ideal-end locus; and
2. end degree at most \(D_h\) there.

### 4.2 Vertical packet

Suppose the target survivor sublamination
\(\mathscr S_h^{\rm ver}\) is dominated by a genuine proper source
lamination \(\mathscr B_h^{\rm ver}\), every leaf of which connects
the pulled-tree ideal boundary to the outer ideal boundary.  Suppose
also that the endpoint-degree and marking hypotheses hold.

KKL domination gives

\[
\mathcal W(\mathscr S_h^{\rm ver})
\leq\mathcal W(\mathscr B_h^{\rm ver}).
\]

The pushforward-lamination lemma then produces
\(\mathscr C_h^{\rm ver}\subset P_{h*}\mathscr B_h^{\rm ver}\) with

\[
\mathcal W(\mathscr B_h^{\rm ver})
\leq
D_h\mathcal W(\mathscr C_h^{\rm ver})+2D_h.
\]

Every leaf of the output joins the two boundary components of
\(X_0\), so monotonicity gives

\[
\mathcal W(\mathscr C_h^{\rm ver})\leq V(F).
\]

Consequently

\[
\mathcal W(\mathscr S_h^{\rm ver})
\leq D_h(V(F)+2)
\leq2^h(V(F)+2).
\]

Summing only through \(m=b+2\),

\[
\begin{aligned}
\sum_{h=1}^{b+2}\mathcal W(\mathscr S_h^{\rm ver})
&\leq(2^{b+3}-2)(V(F)+2)\\
&\leq(2^{b+4}-4)(V(F)+1).
\end{aligned}
\]

The second line uses only \(V(F)\geq0\), since
\(V+2\leq2(V+1)\).  The arithmetic is correct.  The existence and
measurability of the proper packet are not supplied by the source and
remain hypotheses.

### 4.3 Small-Julia incidence packet

For one packet having exactly the final component incidence used at
KKL lines 1613--1617, domination and pushforward give

\[
\mathcal W(\mathscr S_h^{\rm ren})
\leq
D_h\mathcal W(\mathscr C_h^{\rm ren})+2D_h.
\]

The cited source comparison then gives

\[
\mathcal W(\mathscr C_h^{\rm ren})\leq2R(F),
\]

and hence

\[
\mathcal W(\mathscr S_h^{\rm ren})
\leq2D_h(R(F)+1)
\leq2^{h+1}(R(F)+1).
\]

If at most \(q_b\) disjoint certified incidence packets occur at each
horizon, then

\[
\sum_{h=1}^{b+2}\mathcal W(\mathscr S_h^{\rm ren})
\leq
q_b(2^{b+4}-4)(R(F)+1).
\]

Two proposed shortcuts were rejected:

1. KKL line 1617 is not a classification theorem for every earlier
   route horizon or arbitrary attached small-Julia component.  Its use
   is conditional on the exact component incidence.
2. “There are finitely many packets in each block” does not produce a
   bound \(q_b\) independent of period.  Such a theorem must be proved
   from the actual component and marking inventory.

There is no locked comparison

\[
R(F)\leq C_b(V(F)+1).
\]

The \(R\)-charge therefore cannot be absorbed into the vertical term.

### 4.4 Failure-code exhaustion

A maximal lift can fail geometrically only by escaping every compact
subset of the full immersion domain.  Collision of two image sheets,
or contact with an auxiliary collar boundary, is not by itself a
maximal-lift failure.

That topological alternative does not classify every declared route
failure.  A full retained KKL restriction may survive while its named
access, sheet, obstacle, occurrence window, or another protected state
coordinate fails.  The complete code therefore needs two top-level
cases:

1. no full retained named path, followed by a landing/nonlanding code;
2. a full retained path with a marked-state mismatch.

Without the second case, the asserted landing partition is not
exhaustive.  The route-exit note was corrected to record it as
\(\mathsf Q_h\).

### 4.5 Conditional charged/response theorem

The charged/response theorem is valid after, and only after, assuming:

1. RLS\(_h\) and a measurable first-horizon survivor partition;
2. exact vertical packets;
3. at most \(q_b\) exact small-Julia incidence packets;
4. at most \(q_b\) bounded Wave packets whose projected outputs are
   actually empty, actually lie in the unbreakable part of a Wave over
   \(BL_0\), or actually satisfy the Shift lemma;
5. an independently constructed survivor-response theorem for any
   response class; and
6. retention on the right of every critical-end, stage-output-short,
   marking, and nonlanding residual not otherwise controlled.

The theorem must partition every survivor exit, not only uniquely
landed exits, because its displayed partition contains a nonlanding
class.  That quantifier was corrected.

Under these hypotheses, subadditivity plus the estimates above gives

\[
\begin{aligned}
\sum_{h=1}^{b+2}\mathcal W(\mathscr S_h)
\leq{}&
A_b(V(F)+1)+B_b(R(F)+1)\\
&+\sum_h\left[
\mathcal W(\mathscr S_h^{\rm newresp})
+\mathcal W(\mathscr S_h^{\rm crit})
+\mathcal W(\mathscr S_h^{\rm out\text{-}sh})
+\mathcal W(\mathscr S_h^{\rm mark})
+\mathcal W(\mathscr S_h^{\rm nl})
\right].
\end{aligned}
\]

This is a conditional bookkeeping reduction, not the desired pure
\(V\)-bound.

## 5. Safe claims and promotion boundary

The following local claims are source-safe:

1. **Fixed-end WAD split.**  The KKL witness has valid full and
   other-end sub-WADs with paired coefficient-norm equality.
2. **Pointwise retained predecessor.**  A native singleton
   \(F_*\)-image has at least one full retained predecessor.
3. **Pointwise route switch.**  Under verified simple oriented
   Wave-leaf representatives, a first named-route failure has a
   strict-path or marked-state switch and admits a pointwise segmented
   alternative through the finite horizon.
4. **Conditional vertical charge.**  A certified proper vertical
   packet obeys the displayed \(2^h(V+2)\) estimate.
5. **Conditional incidence charge.**  One certified packet with the
   exact KKL final incidence obeys the displayed
   \(2^{h+1}(R+1)\) estimate.
6. **Conditional global reduction.**  Once the full measurable packet
   partition and uniform packet counts are independently proved, the
   charged/residual inequality follows.

The following claims are not promotable:

1. a canonical or Borel fixed-end replacement selector;
2. a valid replacement WAD assembled from the retained predecessor
   fibers;
3. a period-independent bound on fiber or packet multiplicity;
4. unique prime-end landing for every selected exit;
5. zero width of the nonlanding, marking, stage-output-short, or
   critical-end residuals;
6. the line-1603 pass-through/component-exhaustion statement;
7. \(R(F)\leq C_b(V(F)+1)\);
8. the stationary repair, VAAPC-I, UPTCR, or MLC.

## 6. Corrections made during this audit

The route-exit note was changed to:

1. distinguish geometric failure from retained-path state mismatch in
   RLS\(_h\);
2. remove “failure of Borel selection” from a class defined only after
   the complete Borel selector is assumed;
3. require ideal-end degree explicitly in the vertical and incidence
   packets;
4. label the vertical estimate as conditional on packet construction;
5. avoid claiming an unstated numerical universal Wave constant;
6. confine the \(2R(F)\) estimate to exact final stationary incidence;
7. partition every survivor exit, including nonlanding exits;
8. state the exact hypotheses of every bounded packet; and
9. qualify the horizon-\(N\) alternative chain as pointwise and
   dependent on the simple-path occurrence-window lemma.

The fixed-end note was changed to:

1. derive validity from the source-constructed paired foliation
   subdivision, not arbitrary WAD-index restriction;
2. make the stage-surface and marking identification explicit;
3. correct “every” to “almost every” in the survivor corollary;
4. record \(H=N=b+3\) versus \(m=N-1=b+2\); and
5. state that the relation is witness-relative and noncanonical.

## 7. Verification

Post-correction file hashes:

```text
kkl_stationary_route_exit_conductance_reduction.md
SHA-256 FF6FA617900A00853177A2CDF10ED4EA995EE88A2089BD30206FEB5FFD4B5C63

kkl_fixed_end_immersion_switch_wad.md
SHA-256 04024C9DEA82CB32F479D45905A069FD7A20020014D7BA5A45BF00A3E87D036A

kkl_stationary_survivor_route_switch_reduction.md
SHA-256 3A93B1FBC722042A35F43A2ACB4E3D7AE8AFF5AAF3971C8627DB085757F3E2E8
```

Diagnostics run:

```text
python audit_stationary_route_exit_schema.py
stationary route-exit schema regressions: 36 passed
diagnostic only; no analytic or ledger obligation promoted

python audit_stationary_segmented_binder_schema.py
8 segmented-binder schema regressions passed

python audit_proof.py
ledger: valid (407 obligations)
statuses: imported=25, proved=283, open=99
target: MLC [open]
```

These finite checks validate only schema consistency, arithmetic
bookkeeping, and ledger status.  They do not prove the analytic packet
construction or any global theorem.

## 8. Immediate analytic gate

The next theorem is not another scalar conductance bound.  It is a
**marked fixed-end survivor partition and response theorem**:

1. partition the actual target Wave measurably by degree-one starting
   end and proof-used occurrence;
2. apply the KKL fixed-end construction on the exact stage surfaces;
3. prove the full/exit split preserves all native markings and filters;
4. construct a Borel retained-predecessor selector with uniformly
   bounded or summably charged multiplicity;
5. classify each selected replacement as vertical, exact
   small-Julia incident, independently responsive, or a retained
   explicit residual; and
6. prove the critical-end residual without citing the KKL proposition
   whose proof uses line 1603.

Failure must be recorded by the first actual leaf, source end, exit
access, retained-predecessor fiber, marked-state mismatch, and projected
output type.  No global status changes until this theorem is proved.
