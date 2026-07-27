# Gate N1 actual-Wave provenance audit

## 0. Question and exact verdict

This note answers one question only:

> Does the provenance of the Wave used in KKL's stationary argument
> imply that every proof-used Wave is a finite or countable union of
> ordered rectangle foliations, thereby proving
> `STANDARD_BOREL_ORDERED_WAVE_REALIZATION`?

The answer is **no**.

There are canonical ancestors in two branches of KKL's trichotomy, but
the proof does not preserve that ancestry to the stationary
proposition.  The decisive provenance break is KKL line 1168: the proof
chooses a nearly maximal Wave among **all** \(\eta\)-controllable
Waves.  Controllability, defined at lines 1151--1153, imposes no
canonical-foliation, rectangle, or standard-Borel leaf-presentation
condition.

The direct call to the stationary proposition occurs at KKL
1628--1631.  There \(Y\), the Wave ending at \(BL_0\), is extracted
from an arbitrary \(k\)-controllable Wave \(A\) in the universally
quantified Proposition `prop:mostly short in L`.  No intervening
result replaces \(A\) or \(Y\) by a canonical rectangle foliation.

Accordingly:

1. `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` remains open;
2. the literal path-family version
   `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION_ANALYTIC` is unaffected;
3. a stronger Borel version of Gate N1 cannot be promoted from
   canonical-WAD maximality alone.

This is a source-provenance obstruction, not a proof that no new
regularization theorem can exist.  Section 8 states exactly what such
a theorem would have to prove.

Nothing in this note promotes Gate N2, VAAPC-I, UPTCR, rigidity,
parameter fibers, or MLC.

## 1. Frozen source record

The source copies used in this audit are:

| source | SHA-256 |
|---|---|
| KKL, `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| KL06, `.tmp_kl06_source/wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |
| KL06, `.tmp_kl06_source/appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |

Line numbers below refer to these immutable copies.

The relevant definitions are:

1. KL06 `wad.tex` 142--143: a proper lamination is a Borel subset of
   the surface explicitly realized as a union of disjoint proper
   paths;
2. KKL 1871--1875: a Wave is a lamination subordinate to a connected
   boundary multi-interval, with its base, ends, and crest defined from
   the leaf endpoints;
3. KKL 1904--1914: a lamination induces a valid WAD;
4. KKL 1929--1938: canonical rectangles are constructed in the
   universal cover and their descended foliations form the canonical
   lamination; and
5. KKL 1941--1943: canonical maximality is the coordinate estimate
   \[
      W(\alpha)\leq w_{\rm can}(\alpha)+2.
      \tag{1.1}
   \]

KL06 `appendix.tex` 13--36 defines extremal width for an arbitrary
path family.  Its Parallel Law at lines 59--68 likewise has no
standard-Borel leaf-space hypothesis.

## 2. Provenance map from the trichotomy to the stationary call

The entire source path is:

\[
\begin{array}{c}
\text{trichotomy Wave witness}\\
\downarrow\\
\text{near-maximal controllable Wave }A\\
\downarrow\\
\text{universal terminal/mostly-short chain}\\
\downarrow\\
A=A^{\rm sh}\cup X\cup Y\cup Z_1\cup\cdots\cup Z_k\\
\downarrow\\
\text{stationary proposition applied to }Y.
\end{array}
\tag{2.1}
\]

The provenance properties at each arrow are audited separately below.

### 2.1 The wide-Wave alternative is not defined canonically

KKL 757--761 defines

> \(\mathcal U\setminus\mathcal T\) has \(M\)-wide controllable Waves

to mean merely that **there is a Wave** \(S\) of the required width
which is over \(\partial_{\rm C}L_0\) or localized.  The definition
contains no predicate saying that \(S\):

- belongs to the canonical lamination;
- is a union of canonical rectangle foliations;
- has a standard-Borel leaf quotient; or
- is preserved by a specified rectangle atlas.

Thus the earliest formal quantifier already ranges over the full KKL
Wave class.

### 2.2 One production branch has canonical ancestry

In the proof of `prop:aligned wcan`, KKL 870--904:

1. starts with the horizontal and vertical leaves
   \(\mathcal F\) of the canonical lamination (line 872);
2. restricts them to
   \(\mathcal G\subset\mathcal U\setminus\mathcal T\)
   (line 881);
3. chooses an endpoint interval \(\mathcal B I\)
   (lines 888--900); and
4. extracts a Wave \(S\subset\mathcal G(\mathcal B I)\)
   (lines 902--904).

This gives \(S\) **canonical ancestry**.  It does not, as written, give
a theorem that the extracted subfamily is a finite/countable union of
full canonical rectangles, nor does it equip its leaves with the
standard-Borel presentation required by the project interface.

The bounded-flux branch is weaker for the present purpose.  At KKL
787--794 it starts with a lamination \(\mathcal F\) supplied by the
definition of flux and extracts a localized Wave \(S\) after
restriction.  The passage does not state the required ordered
standard-Borel leaf presentation for that restricted Wave.

We may therefore grant the strongest possible reading of both
branches--namely that the initial witnesses arise from explicitly
foliated quadrilaterals--without changing the conclusion below.

### 2.3 The decisive break: near-maximality ranges over all Waves

KKL 1151--1153 defines a \(k\)-controllable Wave by a decomposition
\[
   A=A_0\cup\cdots\cup A_k,
   \tag{2.2}
\]
where \(A_0\) crests over \(BL_0\) and the remaining \(A_j\)'s are
localized.  There is no rectangle or canonicality clause.

KKL 1168 then chooses \(A\) so that

\[
 \mathcal W(B)<(1+\delta)\mathcal W(A)
 \quad
 \text{for every \(\eta\)-controllable Wave \(B\)}.
 \tag{2.3}
\]

The quantifier in (2.3) ranges over the class defined by (2.2), not
over a canonical subclass.  The initial Wave witness proves only that
this class is nonempty and contains one wide element.  It does not
imply that a nearly maximal member of the full class can be chosen
inside any proposed rectangle-realized subclass.

Formally, if
\[
   \mathscr R_\eta\subset\mathscr C_\eta
   \tag{2.4}
\]
denote the rectangle-realized and all \(\eta\)-controllable Waves
respectively, existence of one wide member of \(\mathscr R_\eta\)
does not imply
\[
   \sup_{B\in\mathscr C_\eta}\mathcal W(B)
   =
   \sup_{B\in\mathscr R_\eta}\mathcal W(B).
   \tag{2.5}
\]
No source result proves (2.5), even up to a universal additive error.

This is the first **decisive** arbitrary-Wave quantifier: it erases
whatever canonical ancestry the original trichotomy witness may have
had.

### 2.4 The terminal chain retains the arbitrary quantifier

The loss is not repaired later:

- KKL 1158--1161 states `lem:terminal` for **any**
  \([k]\)-wide \(k\)-controllable Wave.
- Its proof starts at line 1214 with an arbitrary such
  \(A=A_0\).
- KKL 1186--1188 states `prop:mostly short` for **any** such Wave.
- Its proof again starts with arbitrary \(A\) at line 1372.
- KKL 1499--1501 states `prop:mostly short in L` for arbitrary
  \([k,\lambda]\)-wide \(k\)-controllable \(A\).

The operations used in this chain--taking short parts, breakable and
unbreakable parts, critical visits, and controllability
decompositions--are set-theoretic operations on the actual leaf
family.  KKL gives no theorem that they preserve a countable
canonical-rectangle presentation.

### 2.5 The direct stationary input is a subwave of arbitrary \(A\)

The direct use is KKL 1627--1634:

1. \(A\) is the arbitrary Wave from `prop:mostly short in L`;
2. line 1629 writes
   \[
      A=A^{\rm sh}\cup X\cup Y\cup Z_1\cup\cdots\cup Z_k;
      \tag{2.6}
   \]
3. line 1630 specifies that \(Y\) is a Wave ending at \(BL_0\); and
4. line 1631 applies `prop:into the critical limb` to this \(Y\).

The stationary proposition itself, at KKL 1535--1537, is universally
stated for every Wave ending at \(BL_0\).  Its recursion at line 1548
then takes an unspecified “maximal subwave” at each stage.  No
canonical or Borel maximal-extension theorem is cited.

Consequently, the Wave actually entering the stationary proof is not
source-restricted to a canonical rectangle class.

## 3. Formal provenance conclusion

### Proposition 3.1 (arbitrary-Wave stationary input)

In KKL's printed dependency chain, `prop:into the critical limb` must
be proved for a Wave \(Y\) which is known only to be:

1. a KKL Wave in \(\mathcal U\setminus\mathcal T\);
2. ending at \(BL_0\);
3. a subfamily of an arbitrary controllable Wave; and
4. free of short leaves in the decomposition at KKL 1629--1630.

It is not known from that dependency chain to possess a finite or
countable ordered-rectangle presentation.

#### Proof

The universal hypothesis on \(A\) is KKL 1499--1501.  The only
properties assigned to \(Y\) are those in KKL 1629--1630.  The call to
the stationary proposition is KKL 1631.  The definitions of “Wave,”
“ending,” “short,” and “controllable” at KKL 1151--1153,
1180--1183, and 1871--1875 contain no rectangle-presentation clause.
There is no intervening replacement or regularization statement
between lines 1500 and 1631.  Therefore the four listed properties are
the complete source-supported inventory. \(\square\)

### Corollary 3.2

Canonical ancestry of the initial trichotomy witness cannot, by
itself, discharge
`STANDARD_BOREL_ORDERED_WAVE_REALIZATION`.

#### Proof

Even granting canonical ancestry at KKL 787--794 and 870--904, line
1168 replaces the witness by a nearly maximal member of the entire
controllable-Wave class.  Proposition 3.1 then identifies the actual
stationary input. \(\square\)

## 4. Why canonical-WAD maximality is not a replacement theorem

Let \(W_A\) be the valid WAD induced by a proof-used Wave \(A\), and
let
\[
   S_A=\operatorname{supp}W_A.
\]
KKL 1941--1943 proves only
\[
   W_A(\alpha)\leq w_{\rm can}(\alpha)+2
   \qquad(\alpha\in S_A).
   \tag{4.1}
\]

Summing (4.1) gives at most the scalar estimate
\[
   \lVert W_A\rVert
   \leq
   \sum_{\alpha\in S_A}w_{\rm can}(\alpha)
   +2|S_A|.
   \tag{4.2}
\]

There are three independent reasons why (4.2) is insufficient.

### 4.1 The error is not source-uniform in the period

KKL 1907--1908 bounds
\[
   |S_A|\leq 3|\chi(\mathcal V)|+|\mathcal I|.
   \tag{4.3}
\]
For the dynamical marking, KKL 889 gives only
\[
   |\mathcal I|\leq 6bq,
   \tag{4.4}
\]
where \(q\) is the satellite rotation denominator.  Thus summing the
coordinate error \(2\) can produce a \(q\)-dependent charge.  No
period-independent bound needed by N1 follows from (4.2).

### 4.2 A WAD is a scalar quotient of the leaf family

KKL 1911--1914 records only one nonnegative number for each arc class.
It does not record:

- individual endpoints inside their marked intervals;
- the leafwise base and crest;
- maximal filtered immersion-lift occurrences;
- the breakable/unbreakable predicate under \(F_*\);
- the identity of leaves surviving DL pruning;
- the nested source occurrence used in stationary saturation; or
- a standard-Borel quotient of the geometric union by leaves.

Those are exactly the data needed by the stationary construction.
Equality or domination of WAD coordinates cannot be substituted for
equality or functorial transport of actual Waves.

### 4.3 The canonical inequality constructs no map

Neither KKL 1941--1943 nor KL06 245--277 constructs a map
\[
   \mathfrak R:A\longmapsto \mathfrak R(A)
   \tag{4.5}
\]
to a rectangle-realized Wave that preserves all of the data above.
In particular, (4.1) does not imply
\[
   \mathfrak R(A^{\rm nbr})
   =
   \mathfrak R(A)^{\rm nbr},
   \qquad
   F_*\mathfrak R(A)
   =
   \mathfrak R(F_*A),
   \tag{4.6}
\]
or any corresponding statement for short parts, maximal subwaves, or
full occurrence saturation.

The finite support of a WAD therefore does not mean that the original
Wave is a finite union of canonical rectangle foliations.

## 5. A local diagnostic against the “full rectangles” shortcut

This subsection is not needed for Proposition 3.1.  It isolates a
simple false shortcut.

Let
\[
   Q=(0,a)\times(0,1)
\]
be a conformal rectangle, and let \(E\subset(0,a)\) be a fat Cantor
set: \(E\) is closed, nowhere dense, and has positive Lebesgue measure.
Consider the proper path family
\[
   \mathcal F_E
   =
   \{\gamma_x(t)=(x,t):x\in E,\ 0<t<1\}.
   \tag{5.1}
\]

Its geometric union \(E\times(0,1)\) is Borel and its leaves are
pairwise disjoint proper paths.  In a boundary-parallel Wave
quadrilateral, the same construction gives a KKL/KL06 subwave.

Its extremal width is
\[
   \mathcal W(\mathcal F_E)=|E|>0.
   \tag{5.2}
\]
Indeed, if \(\rho\) is admissible, then for every \(x\in E\),
\[
   \int_0^1\rho(x,y)\,dy\geq1.
\]
Cauchy--Schwarz gives
\[
   \int_0^1\rho(x,y)^2\,dy\geq1.
\]
Integrating over \(E\) yields
\[
   \operatorname{area}_\rho(Q)\geq |E|.
\]
Conversely, the measurable metric
\(\rho=\mathbf1_{E\times(0,1)}\) is admissible for
\(\mathcal F_E\) and has area \(|E|\).  This proves (5.2).

The union \(E\times(0,1)\) has empty interior.  It therefore cannot be
a union of any nonempty collection of **full** open rectangle
foliations, since the union of the supports of such foliations is
open.

This example makes two distinctions precise:

1. the KL06 definition permits positive-width Waves which are not
   unions of full canonical rectangles; but
2. \(\mathcal F_E\) itself has the standard-Borel transverse
   parameter \(E\), so it is not a counterexample to the possibility
   of a broader ordered-*subfoliation* theorem.

Thus “replace by full rectangles” is false, while “every Wave admits
a countable ordered Borel subfoliation atlas” remains a genuine theorem
to be proved, not a consequence of the definitions.

## 6. The three exact arbitrary-Wave checkpoints

To prevent ambiguity about the phrase “first arbitrary quantifier,”
there are three relevant checkpoints:

| role | first source line | content |
|---|---:|---|
| earliest formal Wave-class quantifier | KKL 757 | “there is a wave \(S\)” in the definition of the wide-Wave alternative, with no canonical qualifier |
| decisive loss of canonical witness provenance | KKL 1168 | \(A\) is nearly maximal against **any** \(\eta\)-controllable Wave |
| direct input to stationary proposition | KKL 1629--1631 | \(Y\) is extracted from arbitrary controllable \(A\) and `prop:into the critical limb` is applied |

The universal statements at KKL 1160, 1187, 1367, and 1500 confirm
that the second and third checkpoints are not accidental choices in
one special branch.

Inside the stationary proof there is a fourth, independent
regularity gap: KKL 1548 chooses a “maximal subwave” without a
measurable or canonical maximal-extension theorem.

## 7. Failed salvage arguments

The following proposed shortcuts do not close the interface.

### 7.1 “The original witness was canonical”

This ignores the near-maximal replacement at KKL 1168 and the
universal quantifiers downstream.

### 7.2 “Every induced WAD has finite support”

Finite support gives finitely many homotopy classes for one fixed
marked surface.  It gives neither a leaf parameter in one class nor a
uniform support bound as \(q\to\infty\).

### 7.3 “Canonical maximality replaces each class”

Equation (4.1) is a coordinate inequality with an additive \(2\)
error.  It is not an actual-leaf replacement, and summing its errors
can depend on \(q\).

### 7.4 “A Borel geometric union has a Borel leaf quotient”

KL06 142--143 supplies a Borel point set and an explicit decomposition
into paths.  It does not state that the leaf equivalence relation is
Borel or smooth, nor that the decomposition has a standard-Borel
transverse parameter.  A countable inverse-branch atlas can process
already Borel path codes; it cannot create the missing path-code
space.

### 7.5 “Maximal subwaves inherit regularity”

KKL 1548 gives no uniqueness, greatestness, Borel selection, or
closure theorem for the maximal subwave.  The explicit protected-core
repair avoids this word for the analytic N1 estimate, but that does
not construct the stronger Borel presentation.

## 8. Exact replacement theorem required

There are two mathematically honest ways forward on this interface.

### 8.1 Prove the arbitrary-Wave realization theorem

Prove `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` as stated in
`kkl_stationary_n1_residual_borel_and_order_audit_20260726.md`.
In addition to the initial leaf atlas, the proof must show closure
under every operation actually used:

1. short and nonshort restriction;
2. breakable/unbreakable restriction for all required iterates;
3. critical-visit extraction;
4. controllability decomposition;
5. both KKL immersion-marking filters;
6. full retained-occurrence pullback;
7. DL deck-span classes and outer-buffer deletion;
8. central-output saturation; and
9. geometric realization of every resulting Borel leaf subset.

### 8.2 Rebuild the Wave proof inside a regular subclass

Alternatively, define a class
\(\mathscr R\) of ordered, standard-Borel rectangle subfoliations and
prove all of the following:

\[
\begin{aligned}
 &\text{the trichotomy has a witness in }\mathscr R,\\
 &\sup_{\mathscr C_\eta}\mathcal W
   \leq
   \sup_{\mathscr R\cap\mathscr C_\eta}\mathcal W+C_b,\\
 &\mathscr R\text{ is closed under every operation in Section 8.1},\\
 &C_b\text{ is independent of }q\text{ and total marking size}.
\end{aligned}
\tag{8.1}
\]

The second line is essential: without it, near-maximality inside
\(\mathscr R\) does not rule out the wider arbitrary Wave in the
terminal alternative.  A multiplicative formulation may replace the
additive one, but its loss must still be strictly smaller than the
terminal gain and uniform in \(q\).

Neither route is supplied by the locked sources.

## 9. Status after the provenance audit

| item | status | reason |
|---|---|---|
| canonical ancestry of the `prop:aligned wcan` witness | verified | KKL 872, 881, 902 |
| every Wave actually used by stationary proof is canonical/rectangle-realized | refuted as a source-provenance claim | KKL 1168 and 1629--1631 |
| full-rectangle realization of arbitrary Borel Waves | false | fat-Cantor subwave in Section 5 |
| standard-Borel ordered-*subfoliation* realization | open | no theorem in KKL/KL06 |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | open | exact missing theorem in Section 8 |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION_ANALYTIC` | unchanged/proved in the separate N1 note | literal path-family proof does not need this interface |
| stronger ledger `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | open | unconditional Borel clause remains |
| Gate N2, VAAPC-I, UPTCR, MLC | open | outside this audit |

The immediate N1 frontier is therefore not another appeal to canonical
WAD maximality.  It is either a new arbitrary-Wave measurable
realization theorem or a full regular-subclass reconstruction with the
uniform cofinality and closure properties in (8.1).
