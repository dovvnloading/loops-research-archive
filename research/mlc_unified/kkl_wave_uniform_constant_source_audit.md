# KKL Wave pushforward: source audit of the uniform packet constant

## Post-audit correction (2026-07-26)

The later independent audit
`qa_extremal_wave_2026-07-26.md` invalidates the candidate bridge proposed
after this source audit and sharpens the conclusion here.

The distinction is now:

- it is a verified documentary fact that KKL master lines 2149--2152
  *print* an unscripted \(O(1+\log d)\) assertion;
- the assertion is not a usable imported theorem in that broad scope;
  a finite cyclic-cover pullback gives a counterexample under the printed
  definitions;
- Dudko--Lyubich's cited native result remains valid in its narrower
  one-common-boundary-interval annular setting; and
- neither local-end degree nor full-base degree alone supplies the missing
  coefficient-one reduction.

Accordingly, every “conditional on the literal KKL statement” conclusion
below is only a statement-level parsing exercise.  It may not license a
width inequality.  `KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT` remains
open and must be replaced by a restricted coherent-packet theorem or a
multiplicity-aware estimate.  The historical audit text is retained below
to document how the missing source bridge was originally isolated.

## 1. Binary verdict

The statement-level constant scope is clear, but the stronger
source-proof obligation is **not closed**.

> **Conditional uniformity conclusion.**  If KKL Lemma `lem:wave` is
> accepted with its ordinary quantified meaning, it has one absolute
> constant \(c_{\rm W}<\infty\) such that every instance satisfying the
> lemma's stated hypotheses obeys
> \[
>   \mathcal W(A')
>   \leq
>   \mathcal W(A)+c_{\rm W}(1+\log d).
>   \tag{1.1}
> \]
> The constant does not depend on the Riemann surfaces, the ideal
> marking or its cardinality, the combinatorial length of the ending
> multi-interval, the Wave, the branch, the stationary horizon,
> satellite period, or rotation number.  All instance dependence in
> (1.1) is displayed through \(d\).

The locked Dudko--Lyubich proof verifies an absolute
\(O(1+\log m)\) constant for its **native annular/global-degree
lemma**.  It does not prove the exact KKL generalization: KKL allow a
general ideal-marked hyperbolic surface, assume degree only on the
ending multi-interval, and use a Wave *ending at* that multi-interval;
the cited DL lemma assumes a degree-\(m\) annulus covering and a Wave
*above* a boundary interval.  No checked source constructs the
width-preserving, marking-compatible reduction between these two
statements.

For a parabolically \(b\)-bounded stationary response packet at
horizon \(h\leq b+2\), once the packet has supplied an **actual** source
Wave \(B^i\) and a degree bound on its **whole** ending multi-interval,
\[
 d_i\leq \deg(f^h)\leq 2^h\leq 2^{b+2},
\]
the same \(c_{\rm W}\) gives
\[
 \mathcal W(B^i)
 \leq
 \mathcal W(C^i)+
 c_{\rm W}\bigl(1+(b+2)\log 2\bigr).
\tag{1.2}
\]
Conditional on a separately supplied theorem with the displayed
coefficient-one form, no finite-packet maximum and no marking-dependent
constant are needed.  Under the ledger node's
stronger requirement---"verify from a complete source proof"---the
exact source mismatch prevents promotion.  Consequently:

* the project may use (1.1) only as a **conditional constant-scope
  unpacking** of the already imported KKL Wave-pushforward statement;
* a complete proof requires the precise local-end collision reduction
  isolated in Section 8 below;
* an intended source portion that has not been proved to be a genuine
  Wave ending at a marked multi-interval cannot use (1.1);
* a degree known only at one access or endpoint cannot replace the
  degree on the whole ending multi-interval.

Accordingly, the status recommendation is:

```text
KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT:
    open.

Historical missing dependency (subsequently retracted):
    KKL_WAVE_LOCAL_END_COLLISION_REDUCTION.

Documentary fact retained:
    KKL_WAVE_PUSHFORWARD_STATED records that the printed formula uses
    one unscripted constant; it does not license the formula.
```

This result does **not** promote the typed paired-Wave realization,
the uniform \(BL_0\)-survivor response, the stationary repair,
VAAPC-I, UPTCR, or MLC.  All of those remain open.

## 2. Locked sources

All line numbers below refer to the following local files.

| role | file | SHA-256 |
|---|---|---|
| KKL master source | `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| KKL source archive | `.tmp_wave_audit/kkl.tar` | `7FFDCDC90C0785AE55DE23F0AB64F63178E1F2C661FAB1FCC5C95768D8F53AF8` |
| Dudko--Lyubich Feigenbaum source | `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| Dudko--Lyubich Feigenbaum archive | `.tmp_wave_audit/dl23.tar` | `126CAAD9C5847EBB7918C305752783ECCE1B47541C7903D30D59A65485FB5702` |
| Dudko--Lyubich neutral source | `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| Dudko--Lyubich neutral archive | `.tmp_wave_audit/dlneutral.tar` | `1D84BFA8216A657CA8E99140BFA3423364BE047BD2051F6C349F552A9C3FBE55` |
| KL06 extremal-width appendix | `.tmp_kl06_source/appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| KL06 source archive | `.tmp_kl06_source.tar` | `3A63FC9773DB8B60ED4A0EB9A1C551E6F66C08E66AB92C36F4E2B482570AB817` |

No conclusion below is inferred from a title, abstract, or numerical
experiment.

## 3. Exact KKL statement and its quantifiers

### 3.1 Ambient definitions

KKL fix a hyperbolic Riemann surface without cusps and define its ideal
boundary in master lines 1844--1847.  An ideal marking is a countable
collection of pairwise disjoint open connected ideal-boundary sets
(lines 1850--1853).  A multi-interval is itself connected (lines
1855--1857).  Proper marked paths, laminations, and Waves are defined
in lines 1867--1875.

For the dynamical operation, KKL take a holomorphic covering
\[
 f:\mathcal V'\longrightarrow\mathcal V
\]
in lines 2062--2066.  The target marking pulls back to \(f^*\mathcal I\)
(line 2066), and path-family pushforward is defined in lines
2070--2072.

### 3.2 Wave pushforward

The complete active statement is master lines 2147--2152:

* \(A'\) is a Wave in \((\mathcal V',f^*\mathcal I)\);
* \(A'\) ends at a multi-interval \(I'\);
* \(f\) has degree at most \(d\) on \(I'\);
* there is a Wave \(A\subset f_*A'\) satisfying the
  \(O(1+\log d)\) loss.

There is no marking-cardinality, topology, multi-interval-length,
period, or horizon parameter in this statement.  In particular, the
lemma does not say \(O_{\lvert\mathcal I\rvert}(1+\log d)\),
\(O_{\ell(I')}(1+\log d)\), or \(O_b(1+\log d)\).

There is also a source-definition gap: an exhaustive search of the
locked KKL TeX finds uses of “degree on” a compact component or ideal
interval (master lines 1593, 1742--1743, 2076, and 2150), but no
definition of degree on an ideal-boundary subset or multi-interval.
The intended meaning is evidently a sheet bound for the covering
extension over that set, but a complete proof must state that meaning
and connect it to the annular deck multiplicity.  The packet convention
“uniformly over the whole ending multi-interval” is a safe project
interpretation; it is not a definition quoted from the checked KKL
source.

### 3.3 Formal meaning of the unscripted \(O\)

The KKL notation paragraph distinguishes constants whose dependence is
displayed from unscripted big-\(O\): master lines 394--404, especially
lines 400--401.  The cited Dudko--Lyubich convention is completely
explicit: neutral-source lines 1747--1750 define
\(\preceq\) using an **absolute** constant, define
\(\preceq_\kappa\) using a constant depending on \(\kappa\), and say
that unscripted \(O\) is controlled by the former while
\(O_\kappa\) is controlled by the latter.

Therefore the only nonvacuous **statement-level** quantified reading
of KKL's lemma is
\[
\begin{split}
 \exists c_{\rm W}<\infty\ \forall
 (\mathcal V',\mathcal V,\mathcal I,f,A',I',d)
 \text{ satisfying the displayed hypotheses},\\
 \exists A\subset f_*A'\text{ a Wave}:
 \quad
 \mathcal W(A')
 \leq
 \mathcal W(A)+c_{\rm W}(1+\log d).
\end{split}
\tag{3.1}
\]
Allowing the hidden constant to depend on the tuple being quantified
would reduce the asserted estimate to a tautology and would be
inconsistent with the source's explicit subscript convention.

This quantifier extraction determines what KKL assert.  It does not
replace the complete proof demanded by the present ledger obligation.

The logarithm base is immaterial.  Changing bases multiplies
\(\log d\) by one absolute number, which is absorbed by \(c_{\rm W}\).
We use the natural logarithm below.

## 4. The cited native proof and every source of loss

KKL master line 2148 points to Dudko--Lyubich's Lemma 5.2 in *MLC at
Feigenbaum points*.  In the locked TeX this is the nested lemma at
Feigenbaum-source lines 2821--2842.  It is logically separate from the
surrounding global Wave Lemma at lines 2815--2864.  This section proves
uniformity for exactly that native nested lemma; Section 8 audits the
unproved transfer to KKL's statement.

### 4.1 Local annular lemma

The local lemma assumes:

1. a degree-\(m\) covering \(f:A\to B\) of closed annuli;
2. an interval \(J\) in one boundary component of \(A\); and
3. a Wave \(\mathcal S\) above \(J\).

It produces a genuine subwave \(\mathcal S^{\rm new}\) on which \(f\)
is injective and asserts
\[
 \mathcal W(\mathcal S^{\rm new})
 \geq
 \mathcal W(\mathcal S)-O(\log m).
\tag{4.1}
\]
No side-count \(M\), marking cardinality, modulus, or ambient topology
appears in the lemma.

### 4.2 Universal-cover/deck-group step

Feigenbaum-source lines 2826--2828 lift the two annuli to their
universal cover.  The source and target deck groups are identified
with \(m\mathbb Z\) and \(\mathbb Z\).  The desired injectivity follows
once the \(m\) translates
\[
 \mathcal S^{\rm new}_0,\ldots,\mathcal S^{\rm new}_{m-1}
\]
are pairwise disjoint.

This step is conformal and topological.  It introduces no numerical
constant.

### 4.3 Dyadic span classes

Feigenbaum-source lines 2830--2838 split the Wave into pairwise
disjoint sublaminations
\[
 \mathcal S=\mathcal S^0\sqcup\mathcal S^1\sqcup\cdots
 \sqcup\mathcal S^T
\tag{4.2}
\]
according to dyadic endpoint span in fundamental intervals for the
\(\mathbb Z/m\)-action.  The source records
\[
 T=O(\log m)
\tag{4.3}
\]
with no subscript.

Equivalently, there is an absolute \(a_0<\infty\) such that
\[
 T\leq a_0(1+\log m).
\tag{4.4}
\]
The additive \(1\) covers \(m=1\), integer rounding, and the choice of
logarithm base.

### 4.4 Shift loss in each nonfundamental class

For every \(t>0\), Feigenbaum-source line 2839 says that after removing
one buffer, \(\mathcal S^t\) crosses its nontrivial deck shift.
Consequently
\[
 \mathcal W(\mathcal S^t)=O(1)
\tag{4.5}
\]
with no subscript.

The cited Shift Argument is quantitatively absolute.  In the locked
neutral source:

* lines 8849--8867 define linked conformal shifts;
* lines 8873--8876 state the bound
  \(\mathcal W(\mathcal R)\leq2\);
* lines 8877--8880 prove it by removing unit buffers and using
  noncrossing.

Thus there is one absolute \(a_1<\infty\), independent of \(t,m\), the
annulus modulus, and all markings, for which
\[
 \mathcal W(\mathcal S^t)\leq a_1,\qquad t>0.
\tag{4.6}
\]
The locked proof does not provide a fully normalized numerical value
for \(a_1\), because “one buffer” and the passage from a Wave family to
its canonical rectangle are not numerically normalized in the local
lemma.  It does prove that \(a_1\) is absolute.  A numerical value is
not required by (3.1).

### 4.5 Final separation buffer

After retaining \(\mathcal S^0\), Feigenbaum-source lines 2840--2841
remove one additional \(O(1)\) outermost portion so that all
\(\mathbb Z\)-translates are pairwise disjoint.  Hence there is an
absolute \(a_2<\infty\) for this last loss.

KL06 `appendix.tex`, lines 59--68, supplies the Parallel Law used to
sum widths of separated subfamilies; its coefficient is exactly one.
Even without equality, its upper inequality is sufficient to bound
the discarded union by the sum of the discarded widths.

Combining (4.2), (4.4), (4.6), and the final buffer gives
\[
\begin{aligned}
 \mathcal W(\mathcal S)-\mathcal W(\mathcal S^{\rm new})
 &\leq
   \sum_{t=1}^{T}\mathcal W(\mathcal S^t)+a_2\\
 &\leq a_1T+a_2\\
 &\leq
   \bigl(a_0a_1+a_2\bigr)(1+\log m).
\end{aligned}
\tag{4.7}
\]
Thus for the native DL lemma one may take
\[
 c_{\rm DL}:=a_0a_1+a_2,
\tag{4.8}
\]
an absolute constant.

### 4.6 No contamination from the global Wave Lemma

The global Dudko--Lyubich Wave Lemma begins at Feigenbaum-source line
2815 and concludes only
\[
 \mathcal W(U\setminus T)\succeq_M\mathcal W(\mathcal S),
\]
where \(M\) is the total number of sides defined at line 2807.  Its
later iteration uses \(n\) bounded in terms of \(M\) (lines
2844--2849).

That \(M\)-dependence is **not** part of the local injective-pushforward
lemma (lines 2821--2842), and KKL cites the latter for master
`lem:wave`.  Importing the \(M\)-dependence into \(c_{\rm W}\) would
conflate two different lemmas.

## 5. Independent KKL evidence for intended uniformity

KKL use their lemma in ways that require the hidden coefficient to be
uniform.  These uses confirm the intended scope of the statement; they
are not a proof of the missing reduction.

There is a relevant scope warning.  Master lines 1144--1149 say that
constants in the main Wave section are implicitly allowed to depend on
the fixed parabolic bound denoted `\bound`.  Consequently,
the \(O(1)\) and \(O(M)\) expressions at the applications below cannot,
by themselves, prove that the appendix lemma's coefficient is
absolute.  They do show independence from the unbounded variables
\(N,q\) once `\bound` is fixed.  Absoluteness for
the native local lemma comes instead from the DL convention and proof
in Section 4.

1. At master lines 1513--1521 they apply it in a degree-bounded
   one-step situation and write one \(O(1)\) loss.
2. At lines 1559--1563 they apply it at each stage of the stationary
   telescope and again write \(O(1)\), with no stage or marking
   subscript.
3. At lines 1740--1743 they establish a degree bound
   \(2^{M+1}\) for an unbounded iterate.
4. At lines 1769--1770 and 1776--1781 they apply the Wave lemma and
   convert \(\log(2^{M+1})\) into \(O(M)\), with no dependence on the
   iterate \(N\), the translation length \(q\), or the varying marked
   limb.

The last use is decisive for the **intended** scope with the parabolic
bound fixed.  If the hidden coefficient could vary with the marking,
\(N\), or \(q\), the displayed \(O(M)\) at lines 1770 and 1781 would
not follow from the lemma.

## 6. Conditional stationary packet specialization

Fix a realized response-packet branch \(i\) at horizon \(h\).  The
Wave lemma can be invoked only after the packet proves:

\[
\begin{array}{ll}
\text{(W1)}&
B^i\text{ is a genuine Wave in }(X_h,P_h^*\mathcal I),\\
\text{(W2)}&
B^i\text{ ends at a marked multi-interval }J_h^i,\\
\text{(W3)}&
P_h=f^h\text{ extends to all of }J_h^i,\\
\text{(W4)}&
\deg_{J_h^i}(P_h)\leq d_i .
\end{array}
\tag{6.1}
\]

These are precisely family/type/degree hypotheses, not constant
parameters.  If a new valid restricted theorem is separately supplied,
once they hold, (3.1) gives one Wave
\(C^i\subset P_{h*}B^i\) satisfying
\[
 \mathcal W(B^i)
 \leq
 \mathcal W(C^i)+c_{\rm W}(1+\log d_i).
\tag{6.2}
\]

Because a quadratic iterate has total degree \(2^h\),
\[
 d_i\leq2^h.
\tag{6.3}
\]
For the stationary critical-end horizon \(h\leq b+2\),
\[
\begin{aligned}
 c_{\rm W}(1+\log d_i)
 &\leq c_{\rm W}(1+h\log2)\\
 &\leq c_{\rm W}\bigl(1+(b+2)\log2\bigr)
 =:C_b.
\end{aligned}
\tag{6.4}
\]

On that conditional reading, every branch and every admissible packet
uses the same \(c_{\rm W}\).  Only the displayed degree ceiling
contributes to \(C_b\).

If \(b\) is allowed to tend to infinity, (6.4) does **not** give a
\(b\)-independent additive loss.  It gives the exact linear-in-\(b\)
charge forced by the logarithm of the safe global degree.  Obtaining a
universal \(C\) over unbounded \(b\) would require an independent
uniform bound on the degree over each actual ending multi-interval.
That is a different obligation and must not be hidden inside
\(c_{\rm W}\).

## 7. Dependency and hidden-constant ledger

| step | source | quantitative contribution | permitted dependence |
|---|---|---:|---|
| ideal marking / Wave definition | KKL 1844--1875 | none | none |
| covering and marking pullback | KKL 2062--2072 | none | none |
| Wave pushforward statement | KKL 2147--2152 | asserted \(c_{\rm W}(1+\log d)\) | \(d\) only through displayed factor |
| main Wave-section convention | KKL 1144--1149 | application-level constants may absorb `\bound` | fixed parabolic bound |
| annular universal cover | DL-Feigen 2826--2828 | none | none |
| dyadic span count | DL-Feigen 2830--2838 | \(a_0(1+\log m)\) classes | absolute \(a_0\) |
| shifted class | DL-Feigen 2839 | \(a_1\) per class | absolute \(a_1\) |
| linked-shift estimate | DL-neutral 8849--8880 | rectangle width \(\leq2\) before normalization buffers | absolute |
| final translate separation | DL-Feigen 2840--2841 | \(a_2\) | absolute \(a_2\) |
| sum of discarded families | KL06 appendix 59--68 | coefficient \(1\) | none |
| stationary degree | quadratic \(f^h\) | \(d_i\leq2^h\) | \(h\) |
| horizon ceiling | packet hypothesis | \(h\leq b+2\) | \(b\) |

There is no unlisted marking or topology term in the **native DL
constant calculation** or in the literal KKL statement.  The missing
item is not another numerical term; it is the theorem identifying the
DL dyadic collision count and Wave geometry with KKL's localized
degree \(d\) and marked Wave.

## 8. Exact source-proof obstruction

**Post-audit verdict.**  The proposed local-end collision reduction in
this section is false and is retained only as the historical candidate
that the independent cyclic-cover audit disproved.  Full-base degree
does not control collapse among distinct positive-width source
coordinates.

The KKL master source states `lem:wave` but does not include a proof
between lines 2149 and 2152.  The cited DL local lemma differs in three
typed inputs:

| datum | KKL 2149--2152 | DL-Feigen 2821--2842 |
|---|---|---|
| surface | general ideal-marked hyperbolic surface | closed annulus |
| Wave incidence | ends at \(I'\) | lies above \(J\) |
| degree | degree at most \(d\) on \(I'\) | global annulus-cover degree \(m\) |

Neither KKL nor DL identify the collision multiplicity of the retained
Wave with the local degree \(d\), nor do they state that the two Wave
notions identify without width loss.  Therefore the complete-source
obligation requires the following precise bridge.

> **KKL local-end collision reduction
> (`KKL_WAVE_LOCAL_END_COLLISION_REDUCTION`).**  Given the hypotheses of
> KKL `lem:wave`, construct a cyclic/strip ideal-boundary localization
> containing the full Wave and its ending multi-interval, or work
> directly in the universal cover, such that:
>
> 1. restriction to the localization loses no extremal width;
> 2. a KKL Wave ending at \(I'\) becomes a DL-type Wave above a
>    specified boundary interval, or the DL deck argument is reproved
>    directly for the ending-at-\(I'\) convention;
> 3. the number \(m_{\rm col}\) of deck translates that can collide
>    with the retained Wave satisfies \(m_{\rm col}\leq d\), where
>    \(d\) is the degree on the whole KKL ending multi-interval, after
>    explicitly defining boundary degree and proving this collision
>    bound;
> 4. the DL annular deck-group argument applies with the same absolute
>    buffer constants;
> 5. the injective retained image projects to a genuine Wave in the
>    original pulled marking; and
> 6. no complementary ideal interval, coarse-subordination filter, or
>    projection identifies retained leaves or introduces another
>    discarded family.

No such reduction is written in the checked KKL, DL, or KL06 sources.
KL06 supplies extremal-width circuit and holomorphic transformation
rules, but not this boundary localization or local-degree/deck-degree
identification.

Using the safe global degree \(2^h\) does not by itself remove the
obstruction: one must still prove that the proof-used ideal Wave admits
the DL annular realization with no width or marking loss.

A naive demand that the **global** annulus degree satisfy \(m\leq d\)
would be wrong.  For the boundary map of \(z\mapsto z^m\), a sufficiently
short source boundary interval maps injectively, so its local sheet
count is \(d=1\), while the annulus covering still has global degree
\(m\).  This is not a counterexample to KKL's lemma; it shows that the
replacement invariant must be the collision multiplicity
\(m_{\rm col}\) seen by Waves ending at \(I'\), not the global annulus
degree.  The missing theorem must prove \(m_{\rm col}\leq d\) or reprove
the dyadic pruning estimate directly from the local ending interval.

At the time of this preliminary audit, this was classified only as a
source-proof boundary.  The later positive-width cyclic-cover model
shows that the literal broad lemma is false under the printed
definitions.

## 9. Adversarial checks

### 9.1 Marking cardinality tends to infinity

The KKL statement contains no \(\lvert\mathcal I\rvert\), and the DL
local proof sees only the cyclic deck action at the ending interval.
Conditionally, the constant remains \(c_{\rm W}\).  Complete
verification still requires the reduction in Section 8, and
applicability can fail if
the proposed source family is not a Wave in the pulled marking.

### 9.2 Ending multi-interval length tends to infinity

The same conditional conclusion holds.  Combinatorial length is not a
constant parameter in the lemma.  The required degree is nevertheless
the degree on the **whole** multi-interval, so a large interval can
increase \(d\); that increase is already charged by \(\log d\).

### 9.3 Degree one

For \(d=1\), (1.1) permits an absolute \(O(1)\) loss.  It does not claim
zero loss.  Any argument demanding exact width preservation needs a
separate univalent/full-family theorem.

### 9.4 Rapidly growing degree

The dyadic decomposition gives \(O(\log d)\), not \(O(d)\).  No step in
the cited local proof multiplies the width by \(d\).

### 9.5 Infinitely many admissible packets

Taking a maximum over packetwise constants would be invalid for an
infinite class.  It is unnecessary once the theorem in Section 8 is
proved: (3.1) then supplies one constant before any packet is selected.

### 9.6 Global DL Wave Lemma side count

The global conclusion depends on \(M\); the local injective
pushforward does not.  This audit uses only the latter to determine
\(c_{\rm W}\).

### 9.7 Packet realization failure

A formal path portion, a finite ribbon-tree edge, an access germ, or a
locally lifted segment is not automatically a genuine source Wave.
The uniform constant cannot repair a failed (W1)--(W4) certificate.

### 9.8 Unbounded stationary horizon

On the literal KKL reading, the absolute coefficient \(c_{\rm W}\)
remains uniform, but the safe loss \(c_{\rm W}(1+h\log2)\) grows with
\(h\).  A claim of a horizon-free additive constant would require a
new sheet-degree theorem.

## 10. Historical status recommendation (superseded)

The following was the recommendation at the end of the original source
audit.  It is retained for provenance only and is superseded by the
post-audit correction at the start of this file:

```text
KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT
status: open
reason:
  the complete checked proof is for the DL annular/global-degree
  lemma, not the KKL marked/local-degree statement
dependencies:
  - KKL_WAVE_PUSHFORWARD_STATED
  - KKL_WAVE_LOCAL_END_COLLISION_REDUCTION
    (retracted historical candidate; not a live gate)
hypotheses at every application:
  - actual source Wave in the pulled ideal marking
  - actual whole ending multi-interval
  - covering extension and degree bound on that whole multi-interval
conclusion:
  - after the missing reduction, one absolute c_W works for all
    admissible instances
excluded conclusions:
  - actual typed paired-Wave realization
  - b-independent charge when b is unbounded
  - output controllability
  - BL_0 survivor exclusion or charge
```

No ledger or manuscript file was edited in this audit.  The stationary
repair, VAAPC-I, UPTCR, and MLC remain open.
