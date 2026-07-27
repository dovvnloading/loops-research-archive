# Gate N1 — frozen backward audit of the DL relative-discard bound

## 0. Verdict

Two logically different questions must be separated.

### Question A — the new measurable-support additivity derivation

**Verdict A: exact source-semantic blocker.**

The analytic argument in

```text
kkl_stationary_n1_dl_relative_discard_bound_20260726.md
```

is correct **conditional on**

```text
DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT.
```

The frozen sources inspected in this audit do not, however, establish
that clause with the precision required for an unconditional proof.
In particular, the phrase *genuine subwave* at Feigen line 2823 does
not by itself source-lock the measurable-support convention stated in
a different paper at DL-neutral line 8538.

The first unsupported inference is the assertion at target lines
488--490 that the retained family
\(\mathscr S^{\mathrm{new}}\) has measurable geometric support.  Without
that assertion, Corollary 2.2 cannot be applied, equality (3.4) is not
established, and the displayed retained-width inequality at Feigen
2823 cannot be subtracted to obtain the relative-discard estimate
(3.5).

No circularity or independent analytic defect was found in:

1. the pre-pruning use of BOWR;
2. the finite-width argument;
3. the rectifiable-core reduction; or
4. the measurable-support additivity lemma itself.

Thus there is one exact blocker in the new additivity derivation, not
a diffuse analytic failure.

### Question B — the original DL proof-internal discard estimate

**Verdict B: PASS as a native published analytic import.**

Feigen 2827 does not merely display the retained-width conclusion.  It
announces that \(\mathscr S^{\mathrm{new}}\) is obtained “by removing
\(O(\log m)\) outermost curves.”  In the authors' buffer calculus,
“removing \(C\) curves” means deleting a curve family whose extremal
width is at most \(C\), not deleting a cardinality-\(C\) set of leaves.
This convention is source-locked by:

1. Feigen 2601, where the “width of removed curves” is explicitly
   bounded;
2. DL-neutral 2348 and 2355, where “removing \(O(1)\)-curves” is
   implemented by finitely many unit buffers and followed by the
   explicit estimate
   \(\mathcal W(\mathscr R^{\mathrm{new}})
   \geq\mathcal W(\mathscr R)-8\); and
3. the decomposition at Feigen 2830--2841 itself: there are
   \(T=O(\log m)\) nonzero packets, each has width \(O(1)\), and the
   remaining zero-span packet loses one further \(O(1)\) outer family.

Consequently the **removed family itself** has width \(O(\log m)\) by
the ordinary Parallel Law.  This proof-internal statement does not
need the retained support to be measurable and does not use
measurable-support additivity.

Therefore Gate N1 may continue to import

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND
```

directly from Feigen 2827--2841 in the authors' native buffer
terminology.  Verdict A prevents the new note from serving as a fully
independent derivation from the displayed retained-width inequality;
it does **not** reopen Gate N1's older native published analytic import.

The audited target was not edited.

## 1. Frozen objects

| object | SHA-256 |
|---|---|
| `kkl_stationary_n1_dl_relative_discard_bound_20260726.md` | `80ABC64278889469F1B95508A378D30F7DE003B5D6CECF05D64A6C84F6F419E9` |
| `kkl_stationary_n1_borel_ordered_wave_realization_20260726.md` | `6F9B4085C914BD74DD5030C67F311334A4B4882594E111FF552429E4FCC9D118` |
| `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_kl06_source/appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| `.tmp_kl06_source/wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |

All line references below are to these exact snapshots.

## 2. Dependency audit: pre-pruning BOWR

### 2.1 Required construction order

The actual dependency order is:

\[
\begin{array}{c}
\text{KL06/KKL proper stationary Wave}\\
\downarrow\\
\text{BOWR Sections 2--6: finite arc atlas and Borel path evaluation}\\
\downarrow\\
\text{BOWR Section 7.2: filtered restriction occurrences}\\
\downarrow\\
\text{N1 Lemma 4.1 and BOWR Section 7.1: the directed packet }B_I(S)\\
\downarrow\\
\text{target Lemma 2.4: Borel rectifiable core}\\
\downarrow\\
\text{Feigen 2823: annular pruning}\\
\downarrow\\
\text{relative-discard deduction, if retained support is measurable}\\
\downarrow\\
\text{Borel width-envelope regularization}\\
\downarrow\\
\text{BOWR Section 7.4 and later stationary continuation.}
\end{array}
\]

There is no back-edge from the pre-pruning construction to the
relative-discard theorem.

### 2.2 Leaf atlas

BOWR Sections 2--6 construct, before any DL pruning:

1. finitely many Borel marked-arc packets;
2. a standard-Borel code for the leaves of each packet;
3. a jointly Borel, fiberwise continuous proper-path evaluation;
4. Borel prime-end endpoint maps; and
5. continuous compactified arc or based-circle parameterizations.

These constructions depend on the KL06 proper-Borel-lamination
convention, planar nesting, the injective area coordinate, and standard
descriptive-set facts.  They do not invoke:

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND,
BOREL_WIDTH_ENVELOPE_PRUNING,
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION,
```

or any later gate.

### 2.3 Filtered restriction

BOWR Section 7.2 constructs maximal immersion-lift occurrences from a
countable inverse-branch atlas.  Properness, prime-end convergence, and
the two KKL marking filters are Borel predicates on that occurrence
space.  The construction ends at BOWR 1050--1059 with a standard-Borel
occurrence code and a proper Borel restricted lamination.

The direction predicate selecting \(B_I(S)\) is a finite
endpoint/route predicate covered by BOWR Section 7.1.  Its topological
correctness and the fact that every source leaf has at least one such
occurrence are supplied by N1 Lemma 4.1.  That lemma uses the
degree-two path-lifting and marked-circle arguments, not DL pruning.

Consequently, the Borel leaf space used at target lines 380--420 exists
before the first invocation of Feigen 2823.

### 2.4 Circularity verdict

**PASS.**  The target uses only the pre-pruning portion of BOWR.
Neither the target rectifiability split nor the construction of
\(B_I(S)\) depends on the relative-discard estimate being proved.

## 3. Finite-width audit

The subtraction in target equations (3.2)--(3.5) is valid only after
establishing

\[
\mathcal W(\mathscr S_{\mathrm{rec}})<\infty.
\]

Proposition 2.3 supplies this in three independent steps.

### 3.1 Finitely many represented arc classes

Let \(L\) be the actual stationary Wave or its filtered annular packet.
Give coefficient one to every marked arc class represented by a leaf
of \(L\).

Because all leaves of \(L\) are pairwise disjoint, the represented
classes have simultaneous disjoint representatives.  The
coefficient-one function is therefore a WAD in the literal sense of
KKL 1904.  This construction does not use the extremal width of any
class and includes represented zero-width classes.

KKL 1907--1908 bounds the support of a WAD by

\[
3|\chi(V_L)|+|\mathcal I_L|.
\]

The actual stationary surfaces and their degree-two pulled markings
are finite marked.  Thus each fixed packet has finitely many represented
arc classes.  This is a pointwise finiteness assertion; it does not
assert a bound uniform in the satellite denominator and does not need
one.

Countably many raw inverse-branch occurrence codes do not invalidate
this step.  Once the surviving occurrences form the actual lamination
on the finite-marked source surface, their represented arc classes are
still the support of the coefficient-one WAD just described.

### 3.2 Finite width of one class

For one supported class \(\alpha\), KL06 `wad.tex` 245--255 states
directly that the full family of proper paths in that class has finite
width and satisfies

\[
\mathcal W(L(\alpha))
\leq
W_{\max}(V_L,\alpha)
\leq
W_{\mathrm{can}}(V_L,\alpha)+2.
\]

KKL 1941--1943 is the marked-surface version of the same maximality
statement.

There is no hidden appeal here to the finiteness of
\(\mathcal W(L(\alpha))\).  The full class, not merely the induced
coefficient of the given lamination, is bounded by the canonical
quadrilateral.  In the minimal-marked annulus, KKL 1921--1926 gives the
finite strip model directly.  In every other allowed class, KKL
1930--1931 uses the nondegenerate ideal quadrilateral determined by the
lifted endpoint intervals.  KKL 1869 excludes paths subordinate to a
multi-interval of length at most two, which removes the boundary-
degenerate adjacent-interval classes.  A winding class is represented
by distinct lifted intervals.

### 3.3 Finite total width

The Parallel Law gives

\[
\mathcal W(L)
\leq
\sum_{\alpha\in\mathcal A(L)}
\mathcal W(L(\alpha)).
\]

The sum is finite by Sections 3.1--3.2.  No measurable-support equality
is needed for this upper bound.

### 3.4 Finite-width verdict

**PASS.**  Proposition 2.3 establishes exactly the finiteness needed
to avoid an \(\infty-\infty\) subtraction.  No uniform marking bound is
silently inferred.

## 4. Rectifiable-core audit

### 4.1 Borel length function

Uniformize the source annulus by

\[
\phi:A'\longrightarrow\{r<|z|<1\}.
\]

The prime-end extension \(\bar\phi\) is continuous.  On the
standard-Borel leaf code supplied before pruning, the total Euclidean
variation

\[
\ell_0(s)
=
\sup_{\mathcal P_{\mathbb Q}}
\sum_j
\left|
\bar\phi(e(s,t_j))-\bar\phi(e(s,t_{j-1}))
\right|
\]

is a countable supremum of Borel functions.  Rational partitions
compute total variation for each continuous compactified path.
Therefore the finite- and infinite-length leaf sets are Borel.

### 4.2 Borel geometric supports

On either leaf set, the interior evaluation

\[
(s,t)\longmapsto e(s,t),\qquad 0<t<1,
\]

is injective:

1. a single leaf is embedded in its interior; and
2. interiors of different leaves are disjoint.

Lusin--Souslin therefore makes the two geometric unions Borel.  Shared
prime-end landing points do not affect this claim because the geometric
support used by the path family is the union of the interior images.

### 4.3 The infinite-length family has zero width

The round annulus has finite Euclidean area.  For every
\(\varepsilon>0\), the constant density
\(\rho_\varepsilon=\varepsilon\) assigns infinite length to every
infinite-Euclidean-length leaf and is therefore admissible for that
family.  Its area is

\[
\varepsilon^2\pi(1-r^2).
\]

Letting \(\varepsilon\to0\) proves that the nonrectifiable family has
width zero.  Conformal invariance transfers the result back to the
physical annulus.

### 4.4 Applicability to DL

The finite-length core consists of simple rectifiable arcs in the
round-annulus model and remains leafwise above the same boundary
interval.  Uniformizing the target annulus as well conjugates the
degree-\(m\) holomorphic annular cover to another degree-\(m\)
holomorphic annular cover.  This avoids any false assertion that
rectifiability at a rough physical boundary is preserved by a boundary
Riemann map.

### 4.5 Rectifiability verdict

**PASS.**  Lemma 2.4 is Borel, conformally invariant, and independent
of the pruning estimate.

## 5. Measurable-support additivity

Let two path families have disjoint measurable geometric supports
\(Z_1,Z_2\).  Restrict any admissible density \(\rho\) for their union
to \(\rho\mathbf 1_{Z_i}\).  Each restriction is admissible for the
corresponding family, and the two areas add exactly.  Taking infima
gives the reverse of the ordinary Parallel inequality and hence

\[
\mathcal W(\Gamma_1\cup\Gamma_2)
=
\mathcal W(\Gamma_1)+\mathcal W(\Gamma_2).
\]

The same argument works in the extended half-line and for countably
many disjoint measurable supports by Tonelli.  Applied to a measurable
sublamination, the support of its leafwise complement is the
measurable set difference of supports.

**Verdict: PASS.**  This lemma is correct.  Its hypotheses, especially
measurability of the retained support, cannot be weakened.

## 6. Exact source-semantic failure

### 6.1 What Feigen actually states

The locked Feigen source says:

1. at line 2813, a Wave is “a lamination of proper paths” satisfying
   the stated above-\(J\) condition;
2. at line 2823, the input Wave contains a “genuine subwave”
   \(\mathscr S^{\mathrm{new}}\) with injective covering image and the
   retained-width lower bound;
3. at lines 2830--2838, the input is decomposed into pairwise-disjoint
   objects called laminations; and
4. at line 2841, the final family is obtained by removing an additional
   \(O(1)\) outermost portion.

The Feigen source does not define:

```text
lamination,
sublamination,
subwave,
genuine subwave,
```

in a way that states measurable support.

### 6.2 What DL2 states

DL-neutral line 8538 defines a lamination to be a family of pairwise
disjoint simple rectifiable arcs with measurable support and defines a
sublamination to be a collection of those arcs whose support is
measurable.

This is exactly the missing property, but it occurs in the separate
DL2 paper.  DL-neutral line 8547 says:

> All laminations in our paper will appear from rectangles using basic
> operations like restrictions and finite unions.

Thus the text itself scopes the convention to that paper.

### 6.3 Why the citations do not close the bridge

Feigen line 1716 gives a broad “see ... DL2 for details” citation for a
collection of width tools.  Feigen line 2839 cites specifically the
Shift Argument in DL2 Appendix A.3 to bound nonzero deck-span packets.
The cited Shift Argument at DL-neutral 8850 onward is a rectangle/shift
estimate.  It does not state that every undefined term in the Feigen
paper adopts all definitions from DL2 Appendix A.1.

Accordingly, these citations import the analytic estimate actually
invoked, but they do not constitute a source statement that the
Feigen output is a measurable sublamination in the precise DL2 sense.

The adjective *genuine* does not repair this.  Even if *subwave* is
read syntactically as “a subfamily which is itself a Wave,” Feigen
still supplies no source-locked definition of *lamination* that
includes measurable support.  An arbitrary subfamily of a
measurable-support lamination can have nonmeasurable support.

### 6.4 Fatal location in the target proof

Target lines 488--490 assert that both
\(\mathscr S_{\mathrm{rec}}\) and
\(\mathscr S^{\mathrm{new}}\) have measurable support.  The first claim
is proved by Lemma 2.4.  The second claim is precisely the unproved
cross-paper convention bridge.

Without the second claim, one cannot establish

\[
\mathcal W(\mathscr S_{\mathrm{rec}})
=
\mathcal W(\mathscr S^{\mathrm{new}})
+
\mathcal W(
\mathscr S_{\mathrm{rec}}\setminus
\mathscr S^{\mathrm{new}}
).
\]

The retained-width inequality alone does not control the complement.
The target's own Section 4 supplies an exact vertical-fiber
counterexample: a retained subfamily can have full outer-measure width
while its complement also has full width.

### 6.5 Source-semantic verdict

**BLOCKER.**  The exact missing obligation is:

```text
DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT.
```

The target correctly names this obligation at its lines 724--732, but
the locked DL-neutral definition does not by itself discharge it for
the separate Feigen source.

## 7. Independent native proof route for Gate N1

### 7.1 The removed family in the Feigen proof

Let

\[
\mathscr S
=
\mathscr S^0
\mathbin{\dot\cup}
\mathscr S^1
\mathbin{\dot\cup}\cdots\mathbin{\dot\cup}
\mathscr S^T
\]

be the decomposition at Feigen 2830, where \(T=O(\log m)\).  Let

\[
D_{>0}:=\bigcup_{t=1}^{T}\mathscr S^t.
\]

Feigen 2839 states

\[
\mathcal W(\mathscr S^t)=O(1)
\qquad(t>0).
\]

The ordinary Parallel Law, which applies to arbitrary path families,
therefore gives

\[
\mathcal W(D_{>0})
\leq
\sum_{t=1}^{T}\mathcal W(\mathscr S^t)
=
O(\log m).
\tag{7.1}
\]

After replacing \(\mathscr S\) by \(\mathscr S^0\), Feigen 2841 removes
one additional outer family \(D_0\) of \(O(1)\) curves in the authors'
width-buffer convention.  Hence

\[
\mathcal W(D_0)=O(1).
\tag{7.2}
\]

The full proof-internal discard is

\[
D_{\mathrm{DL}}
=
D_{>0}\cup D_0.
\]

A second application of the Parallel Law gives

\[
\mathcal W(D_{\mathrm{DL}})
\leq
\mathcal W(D_{>0})+\mathcal W(D_0)
=
O(\log m).
\tag{7.3}
\]

No equality, subtraction, or support measurability occurs in
(7.1)--(7.3).

### 7.2 Why “\(O(1)\) curves” is a width statement

Reading the phrase as a bound on the number of leaves would be
incompatible with the surrounding theory: Waves and rectangle
foliations normally contain uncountably many leaves, and deleting
finitely many individual leaves would not produce the displayed
positive width loss.

The source gives a direct calibration.  DL-neutral 2348 says that an
\(O(1)\)-curve deletion will be made.  At 2355 it performs that
deletion using unit buffers and concludes

\[
\mathcal W(\mathscr R^{\mathrm{new}})
\geq
\mathcal W(\mathscr R)-8.
\]

Feigen uses the same author notation and the same buffer toolkit.  At
Feigen 2601 the intended quantity is made explicit: “the width of
removed curves is bounded.”  Thus the occurrences of “remove
\(O(1)\) curves” at Feigen 2827 and 2841 are native shorthand for
bounded-width outer buffer deletion.

### 7.3 Gate-N1 verdict

For the degree-two Gate-N1 cover,

\[
m=2,
\qquad
\mathcal W(D_{\mathrm{DL}})
\leq C_{\mathrm{DL}}
\]

for an absolute constant.  This is exactly the analytic import used by
the frozen main N1 proof.  The subsequent Borel width envelope may
enlarge this arbitrary proof-internal discard to a Borel discard.  It
does so only after (7.3) has been imported, so there is no circularity.

**PASS.**  Gate N1 can use the original proof-internal DL relative
discard bound even though the separate measurable-support additivity
derivation remains conditional.

## 8. Accepted repair routes for the new additivity derivation

Exactly one of the following would close this blocker.

### Route A: explicit source confirmation

Supply a source-authoritative statement—published text, erratum,
author clarification suitable for citation, or an explicit convention
in a later frozen version—that:

1. *lamination* in Feigen 2813 uses the measurable-support definition
   of DL2 line 8538; and
2. the *genuine subwave* produced at Feigen 2823 is a sublamination in
   that same sense.

A broad toolkit citation or similarity of terminology is insufficient.

### Route B: independent measurable pruning

Construct the retained family directly on the actual BOWR packet and
prove all of the following:

1. the deck-span decomposition is a Borel leaf partition;
2. the terminal outer trimming is defined by a Borel leaf predicate,
   not by an informal order cut;
3. the retained geometric support is measurable;
4. the annular covering is injective on the retained family; and
5. the discarded family has width \(O(\log m)\), proved without first
   assuming the desired complement identity.

For Gate N1, the resulting bound must be absolute at \(m=2\).

### Route C: measurable relative discard without a measurable selector

It would also suffice to construct directly a measurable discarded
family \(D\) of width \(O(\log m)\) such that the complement is
contained in the injective DL family.  This construction must include
the final outer deletion and must not infer the bound merely from the
displayed retained-width inequality.

The Borel width envelope can regularize a discard only **after** its
relative width has been proved; it cannot establish that width and
therefore cannot be used circularly to close this source gap.

## 9. Status consequence

The frozen target establishes the conditional theorem

\[
\texttt{DL\_GENUINE\_SUBWAVE\_HAS\_MEASURABLE\_SUPPORT}
\Longrightarrow
\texttt{DL\_RELATIVE\_DISCARD\_FAMILY\_BOUND}.
\]

It does not yet establish the antecedent from the locked sources.
Separately, Feigen's proof-internal buffer deletion establishes the
consequent directly, without that antecedent.

Therefore:

| obligation | audited status |
|---|---|
| pre-pruning BOWR dependency | passed; acyclic |
| finite width of the actual packet | passed |
| Borel rectifiable-core reduction | passed |
| measurable-support width additivity | passed |
| `DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT` | **open exact blocker for the new additivity route** |
| new additivity derivation of `DL_RELATIVE_DISCARD_FAMILY_BOUND` | conditional on the preceding blocker |
| native Feigen proof-internal `DL_RELATIVE_DISCARD_FAMILY_BOUND` | **passed as published analytic import** |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | may retain its native DL analytic import; promotion still depends on its other audited clauses |
| N2, VAAPC-I, UPTCR, MLC | open |

This audit does not identify a counterexample to the DL Wave lemma or
to the desired relative bound.  It identifies a missing
source-measurability theorem only for the proposed independent
additivity rederivation.  The original published proof supplies the
relative bound through its explicit bounded-width buffer deletions.
