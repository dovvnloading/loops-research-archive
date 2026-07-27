# Phase QA-3 — extremal width and Wave arguments

Date: 2026-07-26

## 1. Scope and stop rule

This is an independent falsification audit of:

- `kkl_stationary_bl0_survivor_analysis.md`;
- `kkl_wave_uniform_constant_source_audit.md`;
- `kkl_stationary_typed_paired_wave_realization.md`;
- `kkl_stationary_bl0_uniform_response_closure_audit.md`; and
- the unreviewed candidate
  `kkl_wave_local_end_collision_reduction.md`.

The checked analytic sources are the locked KL06, Dudko--Lyubich, and
KKL TeX files listed in Section 2.  The audit checks Series and Parallel
inequalities, holomorphic transformation, Borel and countability
claims, Wave validity, dyadic Shift arguments, deck collisions,
constant dependencies, and conversion of packet estimates into ambient
terminality.

No ledger or manuscript file is edited by this pass.  In particular,
MLC, UPTCR, VAAPC-I, the KKL stationary repair, the typed paired-Wave
realization, and the uniform \(BL_0\)-survivor response remain open.

The main negative conclusion is:

\[
\boxed{
\begin{minipage}{0.90\linewidth}
The candidate local-end collision note is not correct.  Lemma 6.1 is
false under its own closed-hull convention, Lemma 6.2 is false because
its per-leaf translate span does not control collisions between
different leaves or different rectangular components, and Theorem 7.1
therefore fails.  A finite pulled-marking annulus model gives
\[
  \mathcal W(A')=Nw,\qquad
  \sup\{\mathcal W(A):A\subset f_*A'\text{ is a Wave}\}\leq w,
\]
while the full-base degree is at most the fixed annulus degree
\(M=N+2\).  Taking \(N=2\) and \(w\to\infty\) rules out every asserted
\(O(1+\log M)\) loss.

The same construction, in its still simpler full-pullback form in
Section 7.1, is a counterexample to the literal broad wording of KKL
Lemma A.13 under the printed definitions.  It does not contradict the narrower
Dudko--Lyubich annular lemma, whose input is a Wave above one fixed
boundary interval.  KKL's undefined phrase ``degree on \(I'\)'', or an
unstated single-rectangle/common-crest restriction on its Wave, is now
the only possible source-level escape.  No such restriction occurs in
the checked statement or definitions.  The KKL lemma cannot be used as
a complete proved bridge until the statement is corrected or clarified.
\end{minipage}}
\tag{1.1}
\]

The packet-level Series algebra and the conditional ambient-assembly
algebra survive this audit.  They remain conditional on actual source
Waves and on a valid Wave pushforward theorem.

## 2. Immutable evidence used

| file | lines | SHA-256 |
|---|---:|---|
| `kkl_stationary_bl0_survivor_analysis.md` | 1262 | `5F94E965B612B710DF24B643ACDFB79FC3FC216BE0127FFA4D9C4176CB544C48` |
| `kkl_wave_uniform_constant_source_audit.md` | 585 | `160106F9B02917FA5B3399C8D528DFEAE98510C150313AF23F295DEEB72D1A0F` |
| `kkl_stationary_typed_paired_wave_realization.md` | 1314 | `FDF5C152B721D300FE2D590D47416E081B22DFA3E2BC56632131F1BFE15BD025` |
| `kkl_stationary_bl0_uniform_response_closure_audit.md` | 1278 | `9A03A882B4FE234390DDA2DF74C6F17DA62028763C2AB4B4512F4D609F4E8564` |
| `kkl_wave_local_end_collision_reduction.md` | 744 | `323CBD280303B2F6D6B9E3629A5C5EC640B27E497A13C94EA70FF54261FF88EA` |
| `.tmp_wave_audit/waves-with-Misha.tex` | 2420 | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_wave_audit/dl23/Feigen.tex` | 3447 | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | 9112 | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| `.tmp_kl06_source/appendix.tex` | 181 | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| `.tmp_kl06_source/wad.tex` | 588 | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |

The decisive source clauses are:

- KL06 `appendix.tex` 39--68: Series and Parallel Laws;
- KL06 `appendix.tex` 72--114: holomorphic transformation and its
  one-sided direction;
- KL06 `wad.tex` 141--160: a valid WAD is realized by a Borel proper
  lamination;
- KL06 `wad.tex` 404--443: restriction, itinerary partition, and the
  finite-approximation step needed for an infinite itinerary set;
- KKL master 1844--1875: ideal markings, marked paths, laminations,
  Wave base, ends, and crest;
- KKL master 2065--2078: covering pushforward and its general
  degree-loss estimate;
- KKL master 2147--2152: the stated Wave pushforward estimate;
- DL Feigenbaum 2821--2842: the native annular Wave pruning proof; and
- DL neutral 8849--8880: the linked-rectangle Shift argument.

## 3. Classification summary

The classifications in this table use exactly the QA vocabulary fixed
at the freeze.

| statement | classification | reason |
|---|---|---|
| Exact occurrence Series inequality in `kkl_stationary_bl0_survivor_analysis.md`, Lemma 5.1 | **verified only under the explicitly stated exact-occurrence hypotheses** | Every target leaf contains pairwise disjoint source-image portions; KL06 Series has the stated direction; holomorphic transformation gives \(\mathcal W(I_hB^i)\leq\mathcal W(B^i)\). |
| Paired-Wave response, Theorem 6.1 of that note | **downgraded to conditional** | Its algebra is correct, but it requires actual source Waves and a valid coefficient-one Wave pushforward theorem with common \(c_{\rm W}\).  The candidate proof of that theorem fails. |
| Degree-surplus fallback, Section 7 of that note | **verified only under the displayed hypotheses** | Reciprocal inequalities and harmonic-sum algebra have the correct directions.  It uses the general KKL \(dW+2d\) pushforward statement as an imported input. |
| Packet collision response, Corollary 6.2 | **verified only under actual common-output containment** | Monotonicity yields a maximum bound; collision alone does not construct the common Wave. |
| Packet-to-ambient terminality, Corollary 6.4 | **verified only under the displayed ambient fraction, scale, and controllability hypotheses** | The strict inequality and threshold calculation are correct. |
| Uniform-constant audit's statement-level reading of KKL A.13 | **verified as a reading of the printed statement** | KKL print an unscripted \(O(1+\log d)\) with no marking or topology subscript. |
| Uniform-constant audit's complete-proof gate | **verified: still open** | DL prove only the narrower annular/global-degree, Wave-above-\(J\) theorem.  The candidate bridge is false. |
| Typed realization Lemma 4.1, closed-hit Borelness | **verified** | Projection is closed because the second factor is compact and the first factor is metric. |
| Typed realization Lemma 4.2, Borel unique-hit time | **verified**, with one path-space qualification | Rational sublevel sets are \(F_\sigma\).  Joint Borelness of the displayed fields follows.  Calling the path-space formulation “equivalent” needs a standard-Borel/Polish path-space hypothesis stronger than an arbitrary second-countable metric target. |
| Typed realization Corollary 4.3 | **verified only under its supplied product, unique-hit, partition, and width-faithfulness assumptions** | It is not instantiated on the KKL survivor. |
| Typed realization global-ending degree Lemma 6.1 | **source mismatch / conditional** | It is true for the natural boundary-fiber or collar sheet-count definition, but KKL never define “degree on” an ideal multi-interval. |
| Slit-domain and two-obstacle bridge countermodels | **verified as abstract countermodels** | They refute the proposed general implications, not a KKL dynamical block. |
| Uniform-response finite-packet and dominant-packet algebra | **verified** | Parallel/subfamily directions and strict terminality thresholds are correct. |
| Uniform-response ambient assembly Theorem 6.2 | **verified only under Definition 6.1** | The proof is an exact algebraic consequence of the very strong assembly inequality (6.4); that inequality is an open analytic certificate, not a consequence of packet response. |
| Countable Parallel use in the response ledger | **verified after supplying the standard countable-subadditivity proof** | The cited KL06 paragraph states the binary law only, but the countable version follows directly from the metric definition; see Section 4.3 below. |
| Candidate Proposition 5.1 | **verified only as a topological collision example; not a width counterexample** | The curve computation is correct.  As written it does not supply a pulled marking proving KKL path/Wave status, and a one-leaf family has width zero. |
| Candidate Lemma 6.1 | **false as stated** | Closed endpoint hulls give an off-by-one failure at integral span. |
| Candidate Lemma 6.2 | **false as stated, with positive-width counterexample** | Per-leaf self-span does not control mutual collisions among different source components; a dyadic class need not be one rectangle and its total width is not Shift-bounded. |
| Candidate Theorem 7.1 | **false as stated** | The translated-rectangle Wave has \(Nw\) source width and at most \(w\) target-Wave width at fixed logarithmic degree cost. |
| Candidate stationary repair (9.3) | **false / unavailable** | It depends on false Lemma 6.2 and Theorem 7.1 and still lacks actual packet instantiation. |
| Literal broad KKL Lemma A.13 | **false under the printed definitions; source clarification required** | The full pullback of one arbitrarily wide valid Wave is a marked source Wave ending at the entire source boundary component, has degree \(M\), and has width \(Mw\), while its set-theoretic pushforward is the original width-\(w\) Wave.  No printed single-rectangle/common-crest restriction excludes it. |

## 4. Width-law audit

### 4.1 Monotonicity and sign conventions

If \(\Gamma_1\subset\Gamma_2\), every metric admissible for
\(\Gamma_2\) is admissible for \(\Gamma_1\), so

\[
 \mathcal W(\Gamma_1)\leq\mathcal W(\Gamma_2).
\tag{4.1}
\]

This direction is used correctly when a pushed Wave \(C^i\) is placed
inside a common Wave \(T\):

\[
 C^i\subset T
 \quad\Longrightarrow\quad
 \mathcal W(C^i)\leq\mathcal W(T).
\tag{4.2}
\]

KL06's holomorphic transformation rule says

\[
 \mathcal L(f\Gamma)\geq\mathcal L(\Gamma),
\qquad
 \mathcal W(f\Gamma)\leq\mathcal W(\Gamma).
\tag{4.3}
\]

The exact-occurrence calculation uses (4.3) in the correct direction:

\[
 \Gamma^i=I_h(B^i)
 \quad\Longrightarrow\quad
 \mathcal W(\Gamma^i)\leq\mathcal W(B^i).
\tag{4.4}
\]

By contrast, the candidate collision note's equality

\[
 \mathcal W(f_*A^{\rm new})
 =
 \mathcal W(A^{\rm new})
\tag{4.5}
\]

does not follow from (4.3).  KL06 give equality for a conformal
isomorphism on the relevant ambient carrier.  “Injective on the
lamination” is not the same statement.  One needs either:

1. a univalent open neighborhood containing a modulus-realizing
   carrier for the retained family; or
2. an independently proved invariance theorem for the particular
   measured foliation/lamination.

The candidate proves neither.  Theorem 7.1 is already false for the
stronger reason in Section 7, so no independent counterexample to
(4.5) is needed to reject it.  Nevertheless, (4.5) cannot be treated as
a sourced proof step.

### 4.2 Series Law

KL06 say that when every \(\gamma\in S\) contains pairwise disjoint
subpaths \(\gamma^1,\ldots,\gamma^r\), one from each family
\(\Gamma^i\),

\[
 \mathcal W(S)
 \leq
 \bigoplus_{i=1}^r\mathcal W(\Gamma^i),
\qquad
 \bigoplus_i x_i
 =
 \left(\sum_i x_i^{-1}\right)^{-1}.
\tag{4.6}
\]

The response note requires precisely this leafwise disjointness for
the complete untrimmed occurrence portions.  It does not infer it from
two labels or from source-sheet distinction.  Substituting (4.4) into
(4.6) is legal because the harmonic sum is increasing in every
variable.  Therefore

\[
 \mathcal W(S)
 \leq
 \bigoplus_i\mathcal W(B^i)
\tag{4.7}
\]

is correct under the note's exact-occurrence hypotheses.

The warning about finite collar truncation is also correct.  If a full
path overflows a truncation, Series gives an upper bound for the full
family in terms of the truncation; it does not identify their widths.
A no-loss exhaustion theorem is required before replacing untrimmed
proper paths with compact truncations.

### 4.3 Parallel Law and countable decompositions

For two families, KL06 state

\[
 \mathcal W(\Gamma_1\cup\Gamma_2)
 \leq
 \mathcal W(\Gamma_1)+\mathcal W(\Gamma_2),
\tag{4.8}
\]

with equality when the families lie in disjoint open sets.

Every finite use in the four noncandidate notes has the correct
direction.  In particular, the response ledger never infers a lower
sum merely from common containment or distinct labels.

The response ledger also permits countably many packets.  Although the
quoted KL06 lines state only the binary law, countable subadditivity is
valid and can be proved directly.  For
\(\Gamma=\bigcup_{n\geq1}\Gamma_n\), choose metrics \(\rho_n\)
admissible for \(\Gamma_n\) such that

\[
 \operatorname{area}(\rho_n)
 \leq
 \mathcal W(\Gamma_n)+\varepsilon2^{-n}.
\tag{4.9}
\]

Then

\[
 \rho=\left(\sum_{n\geq1}\rho_n^2\right)^{1/2}
\tag{4.10}
\]

is admissible for \(\Gamma\), and Tonelli gives

\[
\begin{aligned}
 \operatorname{area}(\rho)
 &=
 \sum_{n\geq1}\operatorname{area}(\rho_n)\\
 &\leq
 \sum_{n\geq1}\mathcal W(\Gamma_n)+\varepsilon.
\end{aligned}
\tag{4.11}
\]

Letting \(\varepsilon\downarrow0\) proves

\[
 \mathcal W\!\left(\bigcup_n\Gamma_n\right)
 \leq
 \sum_n\mathcal W(\Gamma_n).
\tag{4.12}
\]

Thus equations (3.7) and (3.9) in the closure audit are mathematically
sound.  The later response theorem correctly restricts to finite
\(Q\), because its additive Wave loss otherwise accumulates once per
packet and requires a separate summability argument.

### 4.4 Packet algebra

Suppose

\[
 \mathcal W(S)
 \leq
 \bigoplus_{i=1}^r\mathcal W(B^i)
\tag{4.13}
\]

and a valid Wave theorem gives

\[
 \mathcal W(B^i)
 \leq
 \mathcal W(C^i)+C_b.
\tag{4.14}
\]

Writing \(M=\max_i\mathcal W(C^i)\), one obtains

\[
 \mathcal W(S)
 \leq
 \bigoplus_{i=1}^r(M+C_b)
 =
 \frac{M+C_b}{r}.
\tag{4.15}
\]

Hence

\[
 M\geq r\mathcal W(S)-C_b.
\tag{4.16}
\]

No error factor \(rC_b\) appears in (4.16): the same upper bound
\(M+C_b\) is inserted in every term before taking the harmonic sum.
The response note's algebra is correct.

For the general degree-loss estimate

\[
 \mathcal W(B^i)
 \leq d_i\bigl(\mathcal W(T)+2\bigr),
\tag{4.17}
\]

(4.13) implies

\[
 \frac1{\mathcal W(S)}
 \geq
 \sum_i\frac1{\mathcal W(B^i)}
 \geq
 \frac{\sum_i d_i^{-1}}{\mathcal W(T)+2},
\tag{4.18}
\]

and therefore

\[
 \mathcal W(T)
 \geq
 \left(\sum_i d_i^{-1}\right)\mathcal W(S)-2.
\tag{4.19}
\]

The reciprocal directions in the response note are correct.

## 5. Borel and family-validity audit

### 5.1 Closed-hit sets

For continuous
\(\Phi:\Lambda\times(0,1)\to Y\), metric \(\Lambda,Y\), and closed
\(K\subset Y\), the set of \(\lambda\) whose path hits \(K\) is

\[
 \bigcup_{m\geq3}
 \operatorname{pr}_{\Lambda}
 \{(\lambda,t)\in\Lambda\times[1/m,1-1/m]:
   \Phi(\lambda,t)\in K\}.
\tag{5.1}
\]

Each projection is closed because its second factor is compact.
The typed-realization proof is correct.

### 5.2 Unique-hit time

If every path has a unique hit time \(t_L(\lambda)\), then for rational
\(a\),

\[
 \{\lambda:t_L(\lambda)<a\}
 =
 \{\lambda:\exists t\in(0,a),\ \Phi(\lambda,t)\in L\}.
\tag{5.2}
\]

Exhausting \((0,a)\) by compact intervals makes the right side
\(F_\sigma\).  Thus \(t_L\) is Borel, and the two reparametrized fields
are jointly Borel.  The disjointness of their open images follows from
embeddedness and uniqueness.

One sentence is too broad: from “second-countable metric” alone it is
not automatic that every compact-open path space invoked is Polish or
standard Borel.  The proof needs only joint Borelness, which has already
been established.  If the path-space-valued formulation is retained,
assume that \(Y\) is Polish (or at least that the relevant continuous
path space is standard Borel and its Borel structure is generated by a
countable evaluation set).

### 5.3 What Borelness does not prove

The typed-realization note correctly does not infer any of the
following from Sections 5.1--5.2:

- existence of a continuous product presentation for the native KKL
  residual;
- a unique physical \(L_0^h\) hit;
- zero extremal width of product seams;
- proper landing of a maximal lift;
- fine/coarse marking survival;
- assembly into a valid Borel proper lamination; or
- equality of transverse measure with extremal width.

The slit-domain and two-obstacle models correctly demonstrate that
access seeds or fixed-end decompositions do not by themselves supply
whole-portion or same-occurrence identities.

### 5.4 Degree on an ideal multi-interval

KKL master 2065--2067 give an ideal-boundary covering on an open dense
domain and a pulled marking.  They do not define
\(\deg_J(P)\) for an ideal multi-interval \(J\).

The statement

\[
 \deg_J(P)\leq\deg(P)
\tag{5.3}
\]

is correct if \(\deg_J\) means any ordinary supremal sheet
multiplicity in a collar or any supremal boundary-fiber multiplicity.
It is not a theorem quoted from KKL until that definition is fixed.
Accordingly, typed-realization Lemma 6.1 is conditional on the natural
sheet-count interpretation, not source-complete.

The candidate definition

\[
 \inf_{\mathcal C'\supset J'}
 \sup_{z\in V}
 \#(f^{-1}(z)\cap\mathcal C')
\tag{5.4}
\]

is a new project definition.  In a regular cyclic collar it reproduces
the expected interval fiber count, but no checked KKL line identifies
(5.4) with the quantity used in Lemma A.13 or in the stationary
applications.  Its behavior at exceptional ideal-boundary points and
under noncyclic ideal components is also outside the printed source.
It must therefore be classified as **source mismatch**, not as a
source-locked interpretation.

## 6. Candidate local-end note: local errors

### 6.1 Proposition 5.1

The explicit curve

\[
 \widetilde\gamma(t)
 =
 a+\left(m-\frac12\right)t
 +ih_0\sin(\pi t)
\tag{6.1}
\]

is simple modulo the source period \(m\), and for
\(1\leq k\leq m-1\) it intersects its \(+k\) translate at the parameters
displayed in the candidate note.  The calculation and transversality
check are correct.

What it proves is narrower than the candidate's surrounding theorem:

1. one short endpoint interval can have boundary-fiber multiplicity
   one while one long boundary-parallel arc meets many target-deck
   translates;
2. the family consisting of one leaf has extremal width zero;
3. as written, no pulled ideal marking is specified, so KKL's
   “path” condition—non-subordination to a multi-interval of
   combinatorial length at most two—is not part of the proposition.

A sufficiently fine pulled marking can be added so that the long arc
is a KKL path, and a thin foliated neighborhood gives a genuine
positive but Shift-bounded local family.  This repairs the topological
typing, but it still does not produce an unbounded-width counterexample.
Thus Proposition 5.1 is a valid warning against *collision-count control
by one access degree*.  It is not evidence for or against the
coefficient-one Wave estimate.

### 6.2 Lemma 6.1 is false under its definitions

For a leaf hull of exact length one,

\[
 [x,x+1]\cap[x+1,x+2]=\{x+1\}.
\tag{6.2}
\]

The candidate defines

\[
 s(\widetilde\alpha)
 =
 1+\#\{k>0:
 [x,y]\cap[x+k,y+k]\neq\varnothing\}.
\tag{6.3}
\]

Hence \(s(\widetilde\alpha)=2\), while the claimed boundary degree is

\[
 \lceil y-x\rceil=1.
\tag{6.4}
\]

Therefore Lemma 6.1 is false as written.  The exact formula is

\[
 s(\widetilde\alpha)=\lfloor y-x\rfloor+1,
\tag{6.5}
\]

which differs from \(\lceil y-x\rceil\) at positive integral spans.
This endpoint defect can be repaired by counting strict interlacing
rather than closed-hull contact, or by adding one.  It is not the
principal obstruction to Lemma 6.2.

### 6.3 The dyadic parameter is not controlled as claimed

Lemma 6.2 defines \(r(\widetilde\alpha)\) as the number of chosen target
fundamental intervals met by the endpoint hull.  This is not equal to
the self-translate span \(s(\widetilde\alpha)\).  A very short interval
straddling a fundamental-domain boundary meets two fundamental
intervals while its positive translate does not overlap it, so

\[
 s(\widetilde\alpha)=1,\qquad
 r(\widetilde\alpha)=2.
\tag{6.6}
\]

Consequently (6.4) in the candidate note does not follow from its
hypothesis.  A global change of fundamental domain can fix one short
hull, but not an arbitrary family of hulls distributed around the
boundary.

### 6.4 A dyadic class need not be one Shift rectangle

The Shift Lemma applies to one rectangle \(\mathcal R\) and one
conformal image \(\mathcal R_1\) satisfying the four ordered horizontal
side conditions in DL-neutral 8850--8875.  A set of leaves selected
only by a numerical span can:

- contain several arc classes;
- have several disjoint rectangular components;
- use different endpoint intervals;
- require different deck shifts; and
- fail to be a Wave with one common crest.

Leafwise linking does not turn the union into one linked rectangle.
Even if every component has width at most \(2\), the Parallel equality
in disjoint open components permits the total class width to be
\(2N\).  No marking-independent bound for the complete \(A^t\) follows
without a uniform component count or a theorem assembling the class
into one canonical rectangle.

This invalidates the step

\[
 \mathcal W(A^t)\leq a_1
\tag{6.7}
\]

in the candidate proof.

## 7. Positive-width translated-rectangle counterexample

This section gives a finite, marked, analytic model attacking candidate
Lemma 6.2 and Theorem 7.1.  It also exposes the literal-source issue in
KKL Lemma A.13.

### 7.1 The ambiguity-free full-pullback model

Start with a target annulus

\[
 A_1=S_H/\langle T\rangle
\tag{7.A1}
\]

and a finite ideal marking \(\mathcal I\) on its lower ideal-boundary
circle.  Choose a proper boundary ideal quadrilateral \(Q\) carrying a
valid Wave \(\mathcal F\) of width

\[
 \mathcal W(\mathcal F)=w.
\tag{7.A2}
\]

Choose the marking so that the two endpoint tiles of every leaf of
\(\mathcal F\) are separated, in the selected boundary homotopy
interval, by at least one additional tile.  Equivalently, every leaf is
subordinate only to multi-intervals of combinatorial length at least
three.  It is therefore a KKL path by master 1867--1871.  By varying the
cross-ratio of the four ideal endpoints, \(w\) can be arbitrarily large.

For a fixed \(M\geq2\), take

\[
 f:A_M=S_H/\langle T^M\rangle\longrightarrow A_1
\tag{7.A3}
\]

and the pulled marking \(f^*\mathcal I\), which exists by KKL master
2065--2067.  Let

\[
 A'=f^*\mathcal F.
\tag{7.A4}
\]

This verifies the literal predicates one by one:

1. **Pulled marked paths.**  Every lifted endpoint tile is a tile of
   \(f^*\mathcal I\), and the combinatorial length of the selected
   subordinate interval is unchanged under the local lift.  Thus every
   lifted leaf remains a KKL path.
2. **Proper Borel lamination.**  The preimage is the union of the
   \(M\) disjoint lifts of a proper Borel lamination.  It is a proper
   Borel lamination.  KL06 `wad.tex` 156--158 explicitly records that
   the pullback of a proper lamination under a finite covering is a
   proper lamination and realizes the pulled WAD.
3. **Wave.**  Every lifted leaf is boundary-parallel and subordinate
   to the entire lower source ideal-boundary component.  KKL master
   1853 expressly permits an ideal-marking interval to be an entire
   ideal-boundary component, and 1874 defines a Wave by subordination
   to a multi-interval.  Thus \(A'\) is a Wave subordinate to that
   component.
4. **Ending multi-interval.**  Put \(I'\) equal to the entire lower
   source ideal-boundary component.  Master 1872 says a lamination ends
   at \(I'\) when every leaf has an endpoint in \(I'\), which holds.
   Master 1859 separately discusses the case in which a multi-interval
   is an entire ideal-boundary component.  The printed definition does
   not require the ending multi-interval in Lemma A.13 to be a proper
   interval or a minimal end.
5. **Degree.**  On the entire lower boundary component, \(f\) is the
   ordinary degree-\(M\) cyclic covering.  Component degree,
   boundary-fiber degree, and collar sheet count all give \(d=M\).
   This case is therefore independent of the ambiguity surrounding
   degree on a short local access.
6. **Source width.**  Because \(Q\) is simply connected and proper in
   one target fundamental collar, its \(M\) lifts lie in disjoint open
   quadrilaterals and each maps conformally to \(Q\).  The equality
   case of the finite Parallel Law gives
   \[
      \mathcal W(A')=M w.
   \tag{7.A5}
   \]
7. **Set-theoretic pushforward.**  Choose every lifted leaf with the
   parameterization pulled back from its target leaf.  All \(M\)
   lifted copies then push forward to the same parametrized target
   leaf.  KKL master 2070--2072 define the pushforward as a path family,
   not a multiset or a weighted current.  Hence
   \[
      f_*A'=\mathcal F
   \tag{7.A6}
   \]
   as a set of parametrized paths.  Every Wave
   \(A\subset f_*A'\) satisfies
   \[
      \mathcal W(A)\leq w.
   \tag{7.A7}
   \]

The literal KKL estimate would now say

\[
 Mw
 \leq
 w+c_{\rm W}(1+\log M).
\tag{7.A8}
\]

With \(M=2\) fixed and \(w\to\infty\), this is impossible.

There is one possible terminological objection: for a rotationally
distributed union, several proper connected boundary intervals may
also subordinate the positive-width components, so the phrase “the
smallest such multi-interval” used to name the base may not select a
unique proper interval.  This does not affect the printed Wave
predicate—subordination to the entire component is explicit—and the
lemma asks only that \(A'\) be a Wave ending at \(I'\).  If one adds an
unstated requirement that the Wave have a unique smallest base, the
zero-width outer-leaf refinement in Sections 7.2--7.7 forces such a
base without changing either side of the width contradiction.

No checked KKL line imposes a single arc class, connected support, one
canonical rectangle, or one common crest on a Wave in Lemma A.13.

### 7.2 Covering and marking for the unique-base refinement

Let

\[
 S_H=\{z:0<\operatorname{Im}z<H\},\qquad T(z)=z+1,
\tag{7.1}
\]

and fix integers

\[
 N\geq2,\qquad M=N+2.
\tag{7.2}
\]

Consider the degree-\(M\) annular covering

\[
 f:A_M=S_H/\langle T^M\rangle
 \longrightarrow
 A_1=S_H/\langle T\rangle
\tag{7.3}
\]

induced by the identity on \(S_H\).

Subdivide the lower ideal-boundary circle of \(A_1\) into at least six
marked open intervals, separated by marked endpoints.  Choose two
endpoint intervals \(E,F\) so that either boundary route supporting the
arc class used below contains at least three marked intervals.  The
pullback marking on \(A_M\) has translates

\[
 E_j=T^jE,\qquad F_j=T^jF.
\tag{7.4}
\]

Every leaf connecting \(E_j\) to \(F_j\) in the selected
boundary-parallel class is then a KKL path: its supporting
multi-interval has combinatorial length greater than two.

### 7.3 Arbitrarily wide local rectangle

Inside one target fundamental strip choose an ideal quadrilateral
\(Q\) whose two horizontal ideal sides lie in \(E\) and \(F\), and let
\(\mathcal F\) be its canonical crossing foliation.  By degenerating
the cross-ratio of the four ideal endpoints, one can prescribe

\[
 \mathcal W(\mathcal F)=w
\tag{7.5}
\]

for arbitrarily large finite \(w\), while keeping the whole
quadrilateral inside a proper interval of horizontal length less than
one.

For \(0\leq j<N\), put

\[
 Q_j=T^jQ,\qquad
 \mathcal F_j=T^j\mathcal F.
\tag{7.6}
\]

The \(Q_j\) are pairwise disjoint open quadrilaterals in one source
period, and

\[
 \mathcal W(\mathcal F_j)=w.
\tag{7.7}
\]

The finite Parallel equality therefore gives

\[
 \mathcal W\!\left(\bigcup_{j=0}^{N-1}\mathcal F_j\right)=Nw.
\tag{7.8}
\]

### 7.4 One zero-width leaf forces a connected Wave base

Choose one smooth boundary-parallel source arc \(\delta\) outside and
nested around all the \(Q_j\).  Its selected boundary homotopy interval
\(B\) begins before \(Q_0\), ends after \(Q_{N-1}\), and has length
strictly less than the source period \(M\).  It can be drawn disjoint
from every leaf in every \(\mathcal F_j\).

The singleton family \(\{\delta\}\) has width zero.  For example,
metrics of fixed line density on shrinking Euclidean tubes around
\(\delta\) are admissible for \(\delta\) and have area tending to zero.

Set

\[
 A'
 =
 \{\delta\}
 \cup
 \bigcup_{j=0}^{N-1}\mathcal F_j.
\tag{7.9}
\]

This is a Borel proper lamination of marked KKL paths.  It is subordinate
to the connected multi-interval \(B\).  The outer leaf \(\delta\)
forces every common subordinate interval for the lamination to contain
its selected minimal boundary interval \(B\); hence \(B\) is the Wave
base.  In particular, \(A'\) is one KKL Wave and it ends at the
connected multi-interval \(I'=B\).

Adding the zero-width leaf to (7.8), monotonicity and Parallel
subadditivity give the exact identity

\[
 \mathcal W(A')=Nw.
\tag{7.10}
\]

### 7.5 Degree bounds

Under the candidate's cyclic boundary-fiber definition,

\[
 \deg_\partial(f;B)
 =
 \lceil\operatorname{length}(\widetilde B)\rceil
 \leq M.
\tag{7.11}
\]

Under the global annulus-cover interpretation, the degree is exactly
\(M\).  Under a tilewise interpretation, every individual pulled
marking interval has degree one.  Thus every natural interpretation
supplies at least the safe bound

\[
 d\leq M=N+2.
\tag{7.12}
\]

The counterexample does not rely on choosing a short ending access and
then pretending that it controls the full base.

### 7.6 Collapse downstairs

Because \(f\) is induced by quotienting by \(T\),

\[
 f_*\mathcal F_0
 =
 f_*\mathcal F_1
 =
 \cdots
 =
 f_*\mathcal F_{N-1}
 =
 \overline{\mathcal F},
\tag{7.13}
\]

where

\[
 \mathcal W(\overline{\mathcal F})=w.
\tag{7.14}
\]

As a path family,

\[
 f_*A'
 =
 \overline{\mathcal F}\cup\{f\circ\delta\}.
\tag{7.15}
\]

The second family is a singleton and has width zero.  Hence every
target Wave \(A\subset f_*A'\) satisfies

\[
\begin{aligned}
 \mathcal W(A)
 &\leq
 \mathcal W\bigl(
   \overline{\mathcal F}\cup\{f\circ\delta\}\bigr)\\
 &\leq
 \mathcal W(\overline{\mathcal F})
 +\mathcal W(\{f\circ\delta\})\\
 &=w.
\end{aligned}
\tag{7.16}
\]

Multiplicity of identical parametrized paths does not change extremal
width: a path family is a set, and KKL's pushed Wave is a subfamily,
not a multiplicity-weighted current.

### 7.7 Contradiction to the candidate theorem

Candidate Theorem 7.1 would give one absolute \(c_{\rm W}\) and one
target Wave \(A\subset f_*A'\) with

\[
 Nw
 =
 \mathcal W(A')
 \leq
 \mathcal W(A)+c_{\rm W}(1+\log d)
 \leq
 w+c_{\rm W}(1+\log(N+2)).
\tag{7.17}
\]

Equivalently,

\[
 (N-1)w
 \leq
 c_{\rm W}(1+\log(N+2)).
\tag{7.18}
\]

For \(N=2\), the right side is fixed while \(w\) in (7.5) is
arbitrarily large.  This is a contradiction.

The same construction refutes candidate Lemma 6.2.  Its leafwise
self-span does not see that \(\mathcal F_j\) and
\(\mathcal F_{j+1}\) are different source components that become the
same target family.  In the candidate's decomposition the local
families can all lie in the “fundamental” class, yet that class's deck
orbit is not disjoint.  Any injective retained subfamily has width at
most one target coordinate \(w\), not \(Nw-O(\log N)\).

### 7.8 Why this does not refute the native DL lemma

DL Feigenbaum 2821--2842 assumes a Wave **above one fixed boundary
interval \(J\)**.  The translated local rectangles in (7.9) crest over
different translated boundary regions.  The outer zero-width leaf does
not make every positive-width local rectangle crest over one common
\(J\).  Thus (7.9) does not meet the native DL hypothesis.

The failed step is the attempted generalization

\[
 \text{DL Wave above one }J
 \quad\rightsquigarrow\quad
 \text{arbitrary KKL Wave ending at }I'.
\tag{7.19}
\]

That is exactly the source mismatch identified by the uniform-constant
audit.

## 8. Consequence for literal KKL Lemma A.13

KKL master 2149--2152 say only:

1. \(A'\) is a Wave in \((V',f^*\mathcal I)\);
2. \(A'\) ends at a multi-interval \(I'\);
3. \(f\) has degree at most \(d\) on \(I'\); and
4. some Wave \(A\subset f_*A'\) obeys coefficient-one logarithmic loss.

Under the printed definitions at 1844--1875, the full pullback
(7.A4) is a Wave and ends at the entire lower source boundary
component.  The endpoint marking makes every leaf a marked path, the
degree on that entire component is unambiguously \(M\), and
(7.A5)--(7.A7) contradict the printed estimate.  The unique-base
refinement (7.9) gives the same contradiction if a smallest-base
requirement is added.

This produces the following exact fork:

### Fork A — literal broad reading

With “Wave,” “ends at,” path-family pushforward, and entire ideal
boundary component interpreted exactly as printed, Lemma A.13 is false.
The counterexample uses ordinary degree \(M\) on an entire component,
so no local-degree convention removes it.

### Fork B — intended restricted reading

The source may intend an additional condition such as:

- the Wave is supported in one arc class/one canonical rectangle;
- every positive-width leaf crests over one common interval;
- the ending multi-interval is a particular minimal end with a
  no-repeat property;
- the degree quantity counts the entire occurrence multiplicity with a
  width-weighted rather than fiberwise invariant; or
- \(f_*A'\) retains source multiplicities as a weighted WAD rather than
  as an ordinary Wave subfamily.

None of these restrictions is present in the checked statement or in
the checked definition of a Wave.  The first three could exclude the
counterexample; the last two would change the stated objects.

Therefore this QA pass does not classify KKL A.13 as a verified
theorem.  Its literal printed status is:

```text
false under the printed broad definition; intended restricted theorem
requires source clarification and a new proof
```

Before any project theorem uses its coefficient-one conclusion, the
project must obtain either:

1. a source clarification and a complete proof with the exact intended
   restriction; or
2. a new theorem for the actual stationary source families proving
   that they lie in the restricted single-crest/single-rectangle class.

The safe global degree \(2^h\) does not repair the problem.  In (7.17)
the full global degree is already bounded, but parallel source width
collapses into one target conductance coordinate.

## 9. Uniform constants

### 9.1 What is verified

For the native DL annular lemma, the source proof has:

- \(O(\log m)\) dyadic classes;
- one absolute Shift loss per nonfundamental class; and
- one final absolute buffer.

The unscripted \(O\)-convention in the DL source makes the resulting
coefficient absolute.  No annulus modulus, marking cardinality, period,
or rotation number enters that native constant.

The KKL printed lemma also uses an unscripted
\(O(1+\log d)\).  As a statement-level quantifier, it purports to use
one absolute coefficient.

### 9.2 What is not verified

No complete checked proof transfers the DL constant to arbitrary KKL
Waves ending at arbitrary multi-intervals.  The candidate transfer is
false.  Therefore

```text
KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT remains open.
```

If a valid restricted Wave theorem is eventually supplied, then for a
stationary horizon \(h\leq b+2\),

\[
 d\leq2^h
 \quad\Longrightarrow\quad
 c_{\rm W}(1+\log d)
 \leq
 c_{\rm W}\bigl(1+(b+2)\log2\bigr).
\tag{9.1}
\]

This calculation is correct.  It gives a \(b\)-dependent charge, not a
universal charge when \(b\to\infty\).

The four noncandidate notes correctly keep packet count, marking
survival, output controllability, and ambient scale as separate
parameters.  None of those can be hidden in \(c_{\rm W}\).

## 10. Ambient terminality and response assembly

### 10.1 Dominant packet

If

\[
 \mathcal W(D_*)\geq2\mathcal W(S_*)-C_b,
\qquad
 \mathcal W(S_*)\geq\theta\mathcal W(A),
\quad \theta>\frac12,
\tag{10.1}
\]

then

\[
 \mathcal W(D_*)
\geq2\theta\mathcal W(A)-C_b.
\tag{10.2}
\]

For

\[
 0<\delta<2\theta-1,
\qquad
 \mathcal W(A)>
 \frac{C_b}{2\theta-1-\delta},
\tag{10.3}
\]

the right side is strictly larger than
\((1+\delta)\mathcal W(A)\).  With controllability of this
width-carrying output, KKL terminality follows.  The closure audit's
dominant-packet theorem is correct.

Its phrase “strongest ... obtainable” is a meta-maximality assertion
not proved by the displayed algebra.  It should be read only as
“the strongest theorem proved in that note from the listed scalar
inputs.”

### 10.2 Several packets

Finite pigeonholing gives only

\[
 \max_q\mathcal W(D_q)
 >
 \frac{2\epsilon}{|Q|}\mathcal W(A)-C_b.
\tag{10.4}
\]

The coefficient obstruction for \(|Q|\geq2\) is correct.  Putting all
outputs inside one Wave gives a maximum lower bound, not a sum.

### 10.3 Conditional assembly theorem

Definition 6.1 of the closure audit assumes the genuinely new analytic
inequality

\[
 \mathcal W(T)
 \geq
 \mathcal W(B_0)
 +\alpha\sum_q\mathcal W(D_q)
 -E_{\rm out}.
\tag{10.5}
\]

Given this assumption, the proof

\[
\begin{aligned}
 \mathcal W(T)
 &\geq
 \mathcal W(A)
 +(2\alpha-1)\sum_q\mathcal W(S_q)
 -E_{\rm tot}
\end{aligned}
\tag{10.6}
\]

is algebraically correct.  The need for \(\alpha>1/2\), scale control,
and controllability of the assembled \(T\) is also correct.

Equation (10.5) is not obtained from the upper Parallel Law, common
containment, deck labels, or bounded overlap alone.  It remains an open
analytic assembly certificate.

## 11. Required corrections and safe status

The following corrections are mandatory before ledger or manuscript
integration:

1. Quarantine `kkl_wave_local_end_collision_reduction.md` as false, not
   merely unreviewed.
2. Do not promote its Lemmas 6.1--6.2, Theorem 7.1, Corollary 8.1, or
   stationary formula (9.3).
3. Keep
   `KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT` open.
4. Reclassify every packet factor-two response as conditional on a
   source-correct coefficient-one Wave theorem for the actual source
   Wave class.
5. Record that KKL's phrase “degree on an ideal multi-interval” remains
   undefined in the locked source.
6. Add the translated-rectangle model to the hostile regression ledger
   as an analytic theorem test, not as a numerical proof.
7. In the typed Borel lemma, either remove the path-space “equivalently”
   sentence or assume a standard-Borel/Polish path space.
8. When countably many packet families are used, cite or include the
   countable-subadditivity proof (4.9)--(4.12).
9. Preserve all existing full-width, untrimmed, fine/coarse marking,
   no-duplication, controllability, and ambient-scale hypotheses.

### 11.1 Exact node-status recommendations

The source-record node and the usable-mathematics node must be
distinguished.

```text
KKL_WAVE_PUSHFORWARD_STATED
```

may remain `imported` **only** if its machine meaning is purely
documentary:

```text
KKL master lines 2149--2152 print the displayed assertion.
```

It must then be forbidden as a dependency that licenses the inequality
mathematically.  If `imported` in this ledger means “accepted as a valid
theorem,” the node must instead be downgraded to:

```text
status: open / source-defective
reason: counterexample (7.A1)--(7.A8) to the literal printed scope
```

The remaining frontier statuses should be:

```text
DL23_ANNULAR_WAVE_BUFFER_EXTRACTION
status: imported/verified only in its native scope
scope:
  degree-m closed annulus covering;
  one Wave above one fixed boundary interval J.

KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT
status: open
reason:
  no valid bridge from the native DL theorem to arbitrary KKL Waves;
  the proposed full-base bridge is false.

KKL_STATIONARY_EXACT_OCCURRENCE_SERIES_CONDUCTANCE
status: proved
hypotheses:
  exact full-width leafwise occurrence realization;
  pairwise disjoint untrimmed portions;
  exact holomorphic source images.

KKL_STATIONARY_CONDITIONAL_PAIRED_WAVE_RESPONSE_ALGEBRA
status: proved as an abstract conditional implication
required change:
  replace reliance on the literal KKL statement by the explicit
  hypothesis that each actual source packet has a coefficient-one
  Wave output W(B_i) <= W(C_i) + C_b.

KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION
status: open

KKL_STATIONARY_BL0_UNIFORM_SURVIVOR_RESPONSE
status: open

KKL_STATIONARY_SURVIVOR_EXCLUSION_OR_CHARGE
status: open
```

No conditional response theorem may be presented as an instantiated
stationary theorem until the new coefficient-one packet hypothesis is
proved for the actual stationary source class.

## 12. Minimal next analytic gate

The failed candidate shows that “full-base degree” is not the missing
invariant by itself.  The next gate must first determine the exact
scope of the source Wave theorem:

> **Restricted Wave pushforward/source clarification gate.**  
> Identify the precise class of Waves to which KKL Lemma A.13 is
> intended to apply.  Prove from the definitions and the actual
> stationary construction that every proof-used source Wave belongs to
> that class.  The class must exclude the translated-rectangle collapse
> in Section 7 by a stated geometric property—such as one common crest,
> one canonical rectangle/arc coordinate, or a proved nonrepetition
> condition—and must admit a complete DL-style logarithmic pruning proof
> with a documented boundary-degree definition.

Only after this gate is closed is it meaningful to resume the typed
paired-Wave response program.  If the actual stationary portions do not
belong to such a restricted class, the response invariant must retain
the number and widths of repeated source conductance coordinates; a
scalar full-base degree cannot compress them with logarithmic loss.

More explicitly, a sufficient replacement must choose one of two
forms.

1. **Coherent-packet restriction.**  Prove that all positive-width
   leaves in the proof-used source packet belong to one canonical
   rectangle or one common-crest DL Wave.  Prove that no two independent
   positive-width source coordinates have the same target coordinate.
   Only in this class is a coefficient-one logarithmic pruning estimate
   plausible.
2. **Multiplicity-aware invariant.**  Partition the source Wave into
   coherent packets \(A'_r\), record their individual widths and the
   equivalence relation
   \[
      r\sim s
      \quad\Longleftrightarrow\quad
      f_*A'_r,\ f_*A'_s
      \text{ use the same target WAD coordinate},
   \tag{12.1}
   \]
   and charge the multiplicity of every equivalence class linearly.
   The full-pullback example forces such a linear term:
   \(M\) independent width-\(w\) source coordinates can collapse to one
   width-\(w\) target coordinate.  No \(O(\log M)\) scalar error can
   replace the missing \((M-1)w\).

The general KKL pushforward estimate
\(\mathcal W(A')\leq d\mathcal W(A)+2d\) has the correct qualitative
linear dependence for unrestricted repeated sheets.  Any proposed
coefficient-one improvement must state the additional coherence or
nonrepetition hypothesis that removes this linear obstruction.

## 13. Final QA verdict

The audit preserves the following genuine progress:

- exact occurrence Series conductance;
- the conditional packet response algebra;
- the conditional dominant-packet theorem;
- the conditional ambient assembly algebra;
- the Borel closed-hit and unique-hit reductions on supplied product
  pieces; and
- the slit-domain and unequal-exit source-derivability obstructions.

It rejects the proposed full-base collision theorem and blocks any
promotion based on it.  The first priority is no longer to optimize the
packet constant.  It is to resolve whether KKL's coefficient-one Wave
pushforward lemma has a missing geometric hypothesis and whether the
actual stationary source family satisfies that hypothesis.

MLC, UPTCR, VAAPC-I, the KKL stationary repair, typed paired-Wave
realization, and uniform \(BL_0\)-survivor response remain open.
