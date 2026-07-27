# Gate N1 — final integration and promotion audit

## 0. Verdict and boundary

This audit concerns only

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION.
```

The verdict is:

```text
GATE N1: PROVED
```

in the exact scope of Theorem N1 in
`kkl_stationary_relative_wave_continuation.md`: for fixed
parabolic bound \(b\), \(N=b+3\), and every proof-used KKL stationary
input Wave \(A\), there are nested proper Borel subwaves

\[
 A_0\supset A_1\supset\cdots\supset A_{N-1}
\]

with the prescribed one-step unbreakability, direction, and occurrence
data, and one constant \(C_b<\infty\), independent of the rotation
denominator \(q\), such that

\[
 \mathcal W(A_n\setminus A_{n+1})\le C_b
 \qquad(0\le n<N-1).
\tag{0.1}
\]

The proof does **not** establish the pointwise two-path break at KKL
line 1603, the final fixed-component exit lamination, the final
bounded-degree pushforward, the complete stationary repair, VAAPC-I,
UPTCR, rigidity, parameter-fiber shrinking, or MLC.  Gate N2 and every
later gate remain open.

The promotion is based on the native Dudko--Lyubich proof-internal
discard estimate.  It does not use the separate
measurable-support/additivity route, whose source-semantic bridge
remains unproved.

## 1. Immutable proof objects

The exact proof and audit snapshots are:

| object | SHA-256 | role |
|---|---|---|
| `kkl_stationary_relative_wave_continuation.md` | `ADFC7BCD5A73CE7E7ABE12C11C3E2C4D778826B995BF9114C6F8B431EF38094F` | integrated analytic and Borel Gate-N1 theorem |
| `kkl_stationary_n1_borel_ordered_wave_realization_20260726.md` | `6F9B4085C914BD74DD5030C67F311334A4B4882594E111FF552429E4FCC9D118` | standard-Borel ordered-Wave realization, occurrence code, and saturation |
| `kkl_stationary_n1_borel_width_envelope_20260726.md` | `9F2ABD1E8DDD0E0E1B4FFC3B55B8DAF3BA64B4BCBE4E9562454A850E5E8422BE` | Borel super-discard with arbitrarily small width overhead |
| `kkl_stationary_n1_dl_relative_discard_bound_20260726.md` | `80ABC64278889469F1B95508A378D30F7DE003B5D6CECF05D64A6C84F6F419E9` | Borel rectifiable-core reduction used by the promotion route; its separate additivity route is not used |
| `kkl_stationary_n1_bowr_frozen_backward_audit_20260726.md` | `F9A6BA1C1C9875CDCF1DE1506D3540DB21400FDCAC42B7EDCC3CAD9A574FF0F3` | independent frozen BOWR audit |
| `kkl_stationary_n1_frozen_backward_audit_20260726.md` | `0E44712DC835004B12A72D4856EEB1AB996ACE2D492E0FDD664523668F1A057E` | independent backward audit from (0.1) |
| `kkl_stationary_n1_dl_relative_discard_bound_frozen_audit_20260726.md` | `841DF0993F7C731E772D3333CC758B1C5CDF69B1DD35D008BD66D7EBEE6FE697` | independent A/B source-semantic audit |
| `kkl_stationary_n1_dl_relative_discard_ab_audit_20260726.md` | `4CD2DEE7BC16FEDF4385CA475B1CC67AE160396304FC2CB08DF3CECCABC69C2C` | second independent A/B audit |

The locked analytic sources used at the disputed interface are:

| source | SHA-256 |
|---|---|
| `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| `.tmp_kl06_source/appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |

Every hash in this table was recomputed from the local frozen file
before promotion.

## 2. Exact backward dependency chain

The proof of (0.1) has the following branching dependency graph:

\[
\begin{gathered}
\text{pre-pruning Borel Wave atlas and filtered occurrence code}
\Longrightarrow
\text{Borel rectifiable-core reduction},\\
\text{Borel rectifiable-core reduction}
+
\text{native DL rectifiable discarded-width bound}\\
\Downarrow\\
\text{relative discard bound for the complete KKL packet}\\
\Downarrow\\
\text{Borel width-envelope pruning}\\
\Downarrow\\
\text{full Borel ordered-Wave realization and saturation}\\
\Downarrow\\
\text{one-packet stationary continuation}\\
\Downarrow\\
\text{full source saturation and degree-two relative transfer}\\
\Downarrow\\
\mathcal W(A_n\setminus A_{n+1})\le C_b.
\end{gathered}
\tag{2.1}
\]

The pre-pruning atlas includes Sections 2--5 **and Section 7.2** of
the BOWR note.  Section 7.2 supplies the filtered immersion
restriction used to form the actual occurrence packet \(B_I(S)\).
This corrects a nonfatal omission in an earlier prose dependency
summary.  It introduces no cycle: the atlas and filtered occurrence
code are constructed before any DL pruning, while Sections 7.4--7.5
consume the independently proved Borel envelope only afterward.

No node in (2.1) depends on Gate N2, KKL line 1603, the stationary
proposition being repaired, or a global MLC statement.

## 3. Native relative discard bound

### 3.1 What must be proved

Let \(p:A'\to A\) be the proof-used degree-\(m\) annular covering and
let \(\mathscr S\) be one Wave above one connected source boundary
interval.  Dudko--Lyubich construct an injective retained subwave
\(\mathscr S^{\rm new}\).  Gate N1 needs the stronger relative
statement

\[
 \mathcal W(\mathscr S\setminus\mathscr S^{\rm new})
 \le C(1+\log m),
\tag{3.1}
\]

not merely

\[
 \mathcal W(\mathscr S^{\rm new})
 \ge \mathcal W(\mathscr S)-C(1+\log m).
\tag{3.2}
\]

Equation (3.2) alone does not imply (3.1), because the Parallel Law
has only the inequality

\[
 \mathcal W(\Gamma_1\cup\Gamma_2)
 \le \mathcal W(\Gamma_1)+\mathcal W(\Gamma_2).
\]

We use only the rectifiable sub-scope of the native DL Wave lemma,
whereas the KKL Borel proper-path family supplied to Gate N1 may
contain nonrectifiable leaves.  Before applying that sub-scope, uniformize
the source annulus conformally to a finite-area round annulus and use
the pre-pruning BOWR parameterization.  Euclidean total variation is a
Borel leaf function because rational partitions compute it as a
countable supremum of Borel functions.  Hence

\[
 \mathscr S
 =
 \mathscr S_{\rm rec}\mathbin{\dot\cup}\mathscr N_\infty
\tag{3.3}
\]

is a Borel decomposition into the finite-length core and the
infinite-length family.  Every constant density
\(\rho_\varepsilon=\varepsilon\) is admissible for
\(\mathscr N_\infty\), while its area tends to zero.  Therefore

\[
 \mathcal W(\mathscr N_\infty)=0.
\tag{3.4}
\]

Uniformizing the target annulus as well conjugates the cover to a
degree-\(m\) holomorphic annular cover.  Thus the native DL theorem is
applied only to \(\mathscr S_{\rm rec}\); no unproved preservation of
rectifiability at a rough physical boundary is used.

### 3.2 Proof-internal derivation

The proof at Feigen 2830--2838 partitions the rectifiable core into disjoint
deck-span packets

\[
 \mathscr S_{\rm rec}
 =
 \mathscr S^0\mathbin{\dot\cup}
 \mathscr S^1\mathbin{\dot\cup}\cdots
 \mathbin{\dot\cup}\mathscr S^T,
 \qquad T=O(\log m).
\tag{3.5}
\]

For every \(t>0\), Feigen 2839 applies the DL Shift Argument after
removing unit buffers and obtains

\[
 \mathcal W(\mathscr S^t)\le C_{\rm sh},
\tag{3.6}
\]

where \(C_{\rm sh}\) is absolute.  Feigen 1791--1792 defines a unit
buffer as a width-one rectangle.  The same author terminology is
quantitative elsewhere: Feigen 2601 explicitly says that the
``width of removed curves'' is bounded by the buffer charge, and
DL2 2348--2355 turns removal of \(O(1)\)-curves into unit-buffer
deletion with an explicit retained loss at most \(8\).

For source custody, the estimate used here is the direct printed
statement \(\mathcal W(\mathscr S^t)=O(1)\) at Feigen 2839.  The
core-and-two-buffer notation in the frozen main proof is explanatory
bookkeeping, not an additional source assertion and not a dependency
of (3.6).

After discarding the \(T\) nonzero-span packets, Feigen 2841 removes
one additional \(O(1)\) outer buffer from \(\mathscr S^0\).  Therefore
the Parallel Law gives

\[
\begin{aligned}
 \mathcal W(\mathscr S\setminus\mathscr S^{\rm new})
 &\le
 \mathcal W(\mathscr N_\infty)
   +
 \sum_{t=1}^{T}\mathcal W(\mathscr S^t)
   +C_{\rm out}\\
 &\le
 T C_{\rm sh}+C_{\rm out}\\
 &\le C(1+\log m).
\end{aligned}
\tag{3.7}
\]

This derivation uses only upper bounds for explicitly deleted
families.  It uses neither subtraction of extremal widths nor
measurability of the retained support.  In Gate N1, \(m=2\), so

\[
 c_{\rm DL}:=C(1+\log 2)<\infty
\tag{3.8}
\]

is universal.

### 3.3 Rejected additivity shortcut

For path families with disjoint **measurable geometric supports**, the
auxiliary note proves exact width additivity directly from admissible
metrics.  That lemma is mathematically valid.  However, Feigen 2823
calls the retained object a ``genuine subwave'' without explicitly
stating that its geometric support is measurable in the precise
Appendix-A.1 sense used by the separate DL2 source.  An arbitrary
subfamily of a measurable lamination need not have measurable support.

Consequently the implication

```text
Feigen genuine subwave
    => measurable retained support
    => exact support additivity
    => relative discard bound
```

is **not** admitted to the proof dependency graph.  Its missing
source-semantic premise is

```text
DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT.
```

The native proof-internal estimate (3.5) bypasses that premise
entirely.

## 4. Borel regularization

The native deleted family in (3.5) need not have a Borel predicate in
the project leaf code.  The Borel width-envelope theorem solves
exactly this problem.

Let \(D\) be any, possibly non-Borel, subfamily of a proper Borel
lamination \(S\), with \(\mathcal W(D)\le C\).  Choose a finite-area
admissible density \(\rho\) for \(D\).  Pointwise
Vitali--Carathéodory regularization produces a strictly positive
lower-semicontinuous density \(\sigma\ge\rho\) with

\[
 \int \sigma^2\le C+\varepsilon.
\tag{4.1}
\]

Weighted path length is lower semicontinuous in the compact-open path
topology.  Hence

\[
 E_\varepsilon
 :=
 \{\ell\in L_S:\ell_\sigma(e_S(\ell,\cdot))\ge1\}
\tag{4.2}
\]

is Borel, contains \(D\), and satisfies

\[
 \mathcal W(E_\varepsilon)\le C+\varepsilon.
\tag{4.3}
\]

Injectivity of the joint leaf evaluation and Lusin--Souslin make both
geometric supports, \(E_\varepsilon\) and its complement, Borel.  If
the annular map is injective on \(S\setminus D\), it remains injective
on the smaller retained Borel family

\[
 S^\sharp=S\setminus E_\varepsilon.
\tag{4.4}
\]

Taking \(\varepsilon=1\) makes the extra charge universal and paid
once per stationary step.  No chartwise measurable selection and no
factor equal to the number of arc charts occurs.

## 5. Ordered-Wave realization and target typing

The BOWR construction starts from finitely many native KKL arc
packets.  Strict planar nesting is encoded by the area of the region
on the marked side of a leaf.  Full support of the auxiliary finite
area measure makes this coordinate injective.  The Borel sublevel
argument and Arsenin--Kunugui uniformization then provide:

1. a standard-Borel leaf space;
2. a jointly Borel injective proper-path evaluation;
3. Borel prime-end endpoint and cyclic-order markings;
4. the filtered occurrence relation of BOWR Section 7.2;
5. closure under covering pushforward, Borel envelope pruning, and
   full source saturation.

The target of a retained occurrence is not typed by transporting a
source base through a cover.  For each singleton source/output pair,
KKL Proposition A.14 gives the leafwise direction

\[
 R\uparrow F_*I.
\tag{5.1}
\]

It does **not** give an aggregate target crest.  Instead, all retained
target leaves are subordinate to the same whole target ideal-boundary
component, which KKL permits as a multi-interval.  Since the target
family is already a proper Borel lamination, the KKL Wave definition
types the union as a Wave.  This distinction is essential and was
checked independently in the two frozen backward audits.

## 6. Relative induction and constants

Write \(S_n=\Phi_n(A_n)=F_*^nA_n\).  At a nonempty stage, the
one-packet theorem supplies a central source packet
\(P_{C,n}\subset S_n\) and central target Wave \(C_{n+1}\).  Define
the successor by **full source saturation**

\[
 A_{n+1}
 =
 A_n\cap\Phi_n^{-1}(P_{C,n}).
\tag{6.1}
\]

Because \(P_{C,n}\subset\Phi_n(A_n)\), this gives the exact image
identity

\[
 \Phi_{n+1}(A_{n+1})=C_{n+1}.
\tag{6.2}
\]

For the discarded source family

\[
 D_n:=A_n\setminus A_{n+1},
\]

full saturation gives

\[
 \Phi_n(D_n)\subset S_n\setminus P_{C,n}.
\tag{6.3}
\]

The exact full-lift formula for a degree-\(d\) annular cover is

\[
 \mathcal W(p^*\Gamma)=d\,\mathcal W(\Gamma).
\tag{6.4}
\]

Applying (6.4) successively to (6.3), without deleting colliding
source occurrences, yields

\[
\begin{aligned}
 \mathcal W(D_n)
 &\le 2^n\mathcal W(S_n\setminus P_{C,n})\\
 &\le 2^n c_b^{\rm step}\\
 &\le 2^{b+1}c_b^{\rm step},
\end{aligned}
\tag{6.5}
\]

because \(n\le N-2=b+1\).  The initial step has

\[
 \mathcal W(A_0\setminus A_1)\le c_b^{\rm init}.
\tag{6.6}
\]

Thus

\[
 C_b
 :=
 \max\{c_b^{\rm init},\,2^{b+1}c_b^{\rm step}\}
\tag{6.7}
\]

proves (0.1).  Every constituent of
\(c_b^{\rm init}\) and \(c_b^{\rm step}\) is either absolute or
depends only on the fixed parabolic bound \(b\).  None depends on
\(q\), the Wave width, the number of represented arc packets, or a
selector history.

The final attempted transition is \(n=N-2\), whose source retains two
unbreakable steps and whose output retains one.  No transition at
\(n=N-1\) is used.  Hence no undefined \(A_N\), final alignment, or
Gate-N2 assertion enters the proof.

## 7. Hostile tests

The promotion chain survives the following checks.

1. **Repeated-sheet cyclic cover.**  The known counterexample to the
   broad coefficient-one KKL Wave claim is irrelevant: the proof
   prunes one common-interval packet and uses the degree-two full-lift
   identity for relative transfer.  It never merges several
   independent positive-width source coordinates into one
   coefficient-one target estimate.
2. **Aggregate crest fallacy.**  Target Wave typing uses singleton
   A.14 direction plus common whole-component subordination, not an
   aggregate crest assertion.
3. **Non-Borel outer-buffer predicate.**  The Borel envelope is
   applied once to the complete metric-bounded discard.  Individual
   deck-span and outermost predicates need not be Borel.
4. **Nonmeasurable retained support.**  Exact support additivity is
   excluded from the proof.  The only use of the native retained
   family before Borel regularization is its set-theoretic
   injectivity.
5. **Nonrectifiable KKL leaves.**  The Borel total-variation
   decomposition removes a zero-width nonrectifiable family before
   the native rectifiable DL theorem is invoked.
6. **Non-local connectivity.**  Endpoints and sides are carried in
   prime-end compactifications; no Julia-set local-connectivity
   assumption is used.
7. **Occurrence collision.**  Source saturation keeps every
   occurrence.  Equation (6.4), rather than coefficient-one
   pushforward, pays the complete degree-two multiplicity.
8. **Critical wrap.**  The leafwise direction and the critical,
   precritical, adjacent-limb, and away estimates are applied before
   the next crest can become critical; a crest reaching \(BL_0\)
   terminates the successor.
9. **Horizon edge.**  The last source has exactly the two remaining
   steps required by the precritical repair.  No unproved extra step
   is silently consumed.
10. **Period growth.**  The only cover degree used in a stationary
   transition is \(2\); the number of transitions is \(b+2\).
   Therefore \(q\to\infty\) introduces no constant.
11. **Circularity.**  KKL line 1576, line 1603, the broad KKL Wave
    lemma, the stationary proposition under repair, Gate N2, and
    every global closure statement are absent from (2.1).

## 8. Promotion map

The machine ledger is to record the following acyclic package:

```text
N1_PREPRUNING_BOREL_WAVE_ATLAS                    proved
N1_BOREL_RECTIFIABLE_CORE_REDUCTION               proved
DL_NATIVE_RECTIFIABLE_RELATIVE_DISCARD_BOUND      imported
DL_RELATIVE_DISCARD_FAMILY_BOUND                  proved
BOREL_WIDTH_ENVELOPE_PRUNING                      proved
STANDARD_BOREL_ORDERED_WAVE_REALIZATION           proved
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION_ANALYTIC proved
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION          proved
```

The last node depends on the preceding analytic node.  The complete
relative-discard node depends on the Borel rectifiable-core reduction
and the native rectifiable DL import.  The analytic node depends on
that complete discard theorem, the Borel envelope, the ordered-Wave
realization, and `KKL_STATIONARY_ONE_RETAINED_CHAIN`.  The BOWR node
depends on its pre-pruning atlas, the Borel envelope, the complete
relative-discard theorem, and the retained-chain input.  No open node
is a proof dependency.

The condition

```text
DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT
```

is intentionally absent from this dependency chain.  It remains an
unproved premise only for the rejected optional additivity
rederivation.

## 9. Final classification

Gate N1 is closed in its stated stationary relative-continuation
scope.  This is a real analytic and descriptive-set repair of the
false printed relative-complement step: it constructs the nested
Borel source families and proves the uniform relative loss rather than
restating an aggregate retained-width inequality.

The current frontier immediately after this promotion is:

```text
KKL_STATIONARY_POINTWISE_TWO_PATH_BREAK             open
KKL_STATIONARY_FINAL_FIXED_COMPONENT_EXIT           open
KKL_STATIONARY_TYPED_BOUNDED_DEGREE_PUSHFORWARD     open
KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR          open
VAAPC-I                                             open
UPTCR                                               open
MLC                                                 open
```

No conclusion beyond Gate N1 is promoted by this audit.
