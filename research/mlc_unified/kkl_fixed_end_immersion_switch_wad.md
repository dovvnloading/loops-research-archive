# KKL fixed-end immersion decomposition and survivor-switch WAD

## 1. Status

This note records and instantiates the strongest source theorem that
constructs a lift-until-exit family without a pointwise Borel
maximal-lift argument.

The result is positive but narrow:

1. after a valid target WAD and proper degree-one source starting ends
   are supplied, KKL construct a valid source WAD by lifting its
   realizing foliation until exit;
2. the construction gives a weight-preserving full-lift/other-end
   split; and
3. on an ambient-unbreakable survivor family, every other-end output
   has a nonempty retained successor fiber, hence a pointwise
   route-switch relation.

It does not select the proof-used stationary source end, retain the
complete occurrence marking, bound the number of replacement states,
or prove a numerical/terminal response.  The native stationary repair,
VAAPC-I, UPTCR, and MLC remain open.

## 2. Locked source

The imported KKL source is

```text
.tmp_wave_audit/not-all-good2.tex
SHA-256 B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01
```

The relevant theorem and proof are lines 514--545,
`thm:immer-decomp`.  The master source imports this file at
`.tmp_wave_audit/waves-with-Misha.tex` line 1140.

The finite-topology and valid-WAD definitions are source-locked in

```text
.tmp_kl06_source/wad.tex
SHA-256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580
```

at lines 10--20 and 142--160, respectively.  Finite topology gives
finitely many topological ends; validity requires realization by an
actual Borel proper lamination.

The dynamic restriction clauses used for the survivor corollary are
in the master source:

- lines 2083--2097: proper immersion restrictions and the two marking
  filters;
- line 2141: \(F_*=f_*\iota^*\) on paths; and
- lines 2161--2162: a path is unbreakable exactly when that filtered
  image is one path.

## 3. Source theorem in coefficient form

Let

\[
 i:V'\longrightarrow V
\tag{3.1}
\]

be a holomorphic immersion of finite-topology open Riemann surfaces.
Let \(E'\) be a set of source ends on each of which \(i\) is proper
and has degree one, and put

\[
 E=i(E').
\tag{3.2}
\]

Let \(Y\) be a valid WAD on \(V\), every arc of which has at least one
endpoint in \(E\).

KKL `thm:immer-decomp` supplies a valid WAD \(Y'\) on \(V'\), an
index set \(\mathcal A\), weights \(v_a>0\), target arcs \(\beta_a\),
and source arcs \(\beta'_a\) such that

\[
 Y=\sum_{a\in\mathcal A}v_a\beta_a,
\qquad
 Y'\ge
 \sum_{a\in\mathcal A}v_a\beta'_a,
\tag{3.3}
\]

and every index belongs to one of two classes:

\[
\begin{array}{ll}
\mathcal A_{\rm full}:&
\text{both endpoints of }\beta'_a\text{ lie in }E',
\quad i_*\beta'_a=\beta_a;\\[1mm]
\mathcal A_{\rm exit}:&
\text{one endpoint of }\beta'_a\text{ lies in }E',
\quad\text{the other does not.}
\end{array}
\tag{3.4}
\]

The proof orients a proper foliation realizing \(Y\), begins each lift
at the prescribed degree-one source end, follows it until it leaves
\(V'\), and partitions the resulting proper source foliation by
source homotopy class.

No uniqueness or canonical choice is asserted when several source
ends in \(E'\) map to the same target end.  A stationary application
must choose or measurably partition those ends before invoking the
theorem.

## 4. Exact WAD split

Define

\[
\begin{aligned}
 Y_{\rm full}
 &=\sum_{a\in\mathcal A_{\rm full}}v_a\beta_a,
&
 Z'_{\rm full}
 &=\sum_{a\in\mathcal A_{\rm full}}v_a\beta'_a,\\
 Y_{\rm exit}
 &=\sum_{a\in\mathcal A_{\rm exit}}v_a\beta_a,
&
 Z'_{\rm exit}
 &=\sum_{a\in\mathcal A_{\rm exit}}v_a\beta'_a.
\end{aligned}
\tag{4.1}
\]

### Proposition 4.1 (fixed-end full/exit decomposition)

The four WADs in (4.1) are valid, and

\[
\begin{aligned}
 Y&=Y_{\rm full}+Y_{\rm exit},\\
 Y'&\ge Z'_{\rm full}+Z'_{\rm exit},\\
 \|Y_{\rm full}\|&=\|Z'_{\rm full}\|,\\
 \|Y_{\rm exit}\|&=\|Z'_{\rm exit}\|.
\end{aligned}
\tag{4.2}
\]

Every arc in \(Z'_{\rm full}\) maps to its complete paired target arc.
Every arc in \(Z'_{\rm exit}\) is a proper source arc beginning in
\(E'\) and ending at a different source end; no complete-target-image,
ideal-access, fine-marking, or coarse-filter conclusion is added.

#### Proof

The KKL witness (3.3)--(3.4) is obtained by first subdividing one
realizing target foliation by target homotopy class and then
subdividing the corresponding lifted source foliation by source
homotopy class.  The full/exit partition is a measurable partition of
those paired foliation pieces by the endpoint alternative in (3.4).
Restricting the paired target and source foliations to either part
therefore gives partial proper foliations and hence valid sub-WADs.
This uses the foliation subdivision constructed in the source proof;
an arbitrary formal restriction of a WAD coefficient presentation
would not by itself prove validity.

The first two relations in (4.2) are (3.3) split over the disjoint
index partition (3.4).  By definition, a WAD norm is the sum of its
arc weights.  The paired source and target terms carry the identical
coefficient \(v_a\), so

\[
 \|Y_\star\|
 =
 \sum_{a\in\mathcal A_\star}v_a
 =
 \|Z'_\star\|,
 \qquad
 \star\in\{\mathrm{full},\mathrm{exit}\}.
\tag{4.3}
\]

The endpoint and full-image statements are exactly the two alternatives
in (3.4). \(\square\)

### Qualification 4.2

The equality in (4.3) is equality of the norms of the paired WAD
pieces in the KKL witness.  It is not a claim that an arbitrary
marked target-leaf selector preserves extremal width, nor that
\(\|Y'\|=\|Y\|\).  The inequality in (3.3) may contain additional
source weight.

## 5. Consequence for an ambient survivor

Fix one transition stage of an ambient \(H\)-unbreakable Wave family,
where the native stationary application has \(H=N=b+3\), although
the named route pullbacks stop at \(m=N-1=b+2\).
Let \(Y\) be a valid target sub-WAD to which Proposition 4.1 applies.
Suppose additionally that the following stage identification has been
supplied:

1. \(i:V'\to V\) is the actual stationary stage immersion on the
   source and target marked complementary surfaces;
2. \(E'\) and \(E\) are the actual proof-used ideal ends with the
   native fine and coarse markings;
3. the realizing target foliation is the stationary target
   subfoliation under study; and
4. the source foliation constructed by `thm:immer-decomp` is the named
   proof-used occurrence before the native fine/coarse filters are
   applied.

These are hypotheses, not consequences of the abstract fixed-end
theorem.

For a target path \(\delta\), let
\(\operatorname{Ret}(\delta,\delta^+)\) be the retained predecessor
fiber defined in
`kkl_stationary_route_exit_survivor_reduction.md`, equation (5.5).

### Proposition 5.1 (fixed-end survivor switch relation)

Use the realizing target foliation and lifted source foliation in
KKL's witness.  Assume almost every target leaf
\(\delta\) in the \(Y_{\rm exit}\) subfoliation belongs to the ambient
unbreakable part and has unique filtered successor \(\delta^+\).
Let \(\ell'_{\rm exit}(\delta)\) be its lifted proper source leaf.
Then almost every such target leaf has a nonempty survivor-switch
relation

\[
 \mathcal P(\delta)
 =
 \{\ell'_{\rm exit}(\delta)\}
 \times
 \operatorname{Ret}(\delta,\delta^+).
\tag{5.1}
\]

The first factor is realized collectively by a valid source WAD with
the same coefficient norm as \(Y_{\rm exit}\).  The second factor is
nonempty for almost every target leaf under the hypotheses.  It may
contain the first factor
itself if that proper other-end restriction survives the KKL filter
and has covering image \(\delta^+\); otherwise it supplies a strict
replacement restriction.

#### Proof

Proposition 4.1 gives the proper source exit foliation and the
coefficient equality

\[
 \|Z'_{\rm exit}\|=\|Y_{\rm exit}\|.
\tag{5.2}
\]

Ambient unbreakability says that \(F_*\delta\) is one nonempty proper
path \(\delta^+\).  By the source definition
\(F_*=f_*\iota^*\), after the fine/coarse filters at least one proper
source restriction must have covering image \(\delta^+\).  Thus
\(\operatorname{Ret}(\delta,\delta^+)\ne\varnothing\), which proves
that almost every fiber in (5.1) is nonempty.

If \(\ell'_{\rm exit}(\delta)\) is itself in that retained fiber, the
geometric source path survives and the defect is a complete-target or
marked-state mismatch.  If not, every member of the second factor is
a strict retained replacement. \(\square\)

### Qualification 5.2

Proposition 5.1 is deliberately relation-valued.  It does not prove:

1. a Borel selection from the second factor;
2. a uniform bound on the fiber cardinality;
3. that the replacement paths form one valid WAD;
4. a geometric separation between the exit and replacement paths;
5. that either path lands at the two line-1603 accesses; or
6. a \(V(F)\), \(R(F)\), or terminal-Wave estimate.

The relation is also relative to the realizing foliation and its
fixed-end lift chosen in the KKL witness; it is not a canonical
relation attached to an unmarked WAD.  Those are precisely the
remaining coercive interfaces.

## 6. Finite-end Borel selection and two-orientation refinement

The source theorem assumes finite-topology surfaces.  In particular,
the proof-used source end set is finite.  This makes the measurable
choice problem elementary once the actual geometric candidate
relation has been proved Borel.

### Proposition 6.1 (finite marked-end selector)

Let \(\Lambda\) be a standard Borel transversal for a realizing target
foliation, with the following saturation property: every Borel subset
of \(\Lambda\) used below has a Borel saturated union of proper leaves
and therefore realizes a proper sublamination.  For each sign
\(\varepsilon\in\{-,+\}\), let

\[
 E'_\varepsilon
 =
 \{e^\varepsilon_1,\ldots,e^\varepsilon_{q_\varepsilon}\}
\tag{6.1}
\]

be a finite set of source ends at which the actual stage immersion is
proper of degree one.  Let

\[
 \mathcal C^\varepsilon
 \subset
 \Lambda\times E'_\varepsilon
\tag{6.2}
\]

be a Borel candidate relation with every vertical fiber
\(\mathcal C^\varepsilon_\delta\) nonempty.  The relation may include
all proof-used access, sheet, occurrence, and orientation predicates;
it is not merely target-end equality.  Require, in particular, that

\[
 (\delta,e)\in\mathcal C^\varepsilon
 \quad\Longrightarrow\quad
 i(e)\text{ is the }\varepsilon\text{-oriented endpoint of }\delta
\tag{6.2a}
\]

and that \(e\) satisfies every fixed-end eligibility predicate needed
for the relevant application of `thm:immer-decomp`.

Fix an order on each finite set \(E'_\varepsilon\), and define

\[
 e^\varepsilon(\delta)
 =
 \min \mathcal C^\varepsilon_\delta.
\tag{6.3}
\]

Then:

1. both selectors \(e^-\) and \(e^+\) are Borel;
2. the pair fibers
   \[
     \Lambda_{rs}
     =
     \{\delta:
       e^-(\delta)=e^-_r,\ e^+(\delta)=e^+_s\}
   \tag{6.4}
   \]
   form a finite Borel partition of \(\Lambda\);
3. restricting the target foliation to the nonempty
   \(\Lambda_{rs}\) gives valid target sub-WADs; and
4. on each part, KKL `thm:immer-decomp` can be applied in each
   orientation from its fixed source end, producing two
   witness-relative valid source WADs with the paired coefficient
   norms of Proposition 4.1.

If a Borel occurrence code \(\xi(\delta)\) is also supplied and the
two maximal lifts are independently proved to exit at that same
actual occurrence, then the common partition (6.4) couples the two
witnesses to the same target leaf, transverse parameter, and
occurrence code.  This proves the common-leaf, transverse-parameter,
and selected-end portion of \(P_h\) as defined in
`kkl_stationary_route_exit_source_audit.md`, Section 5.3.
Access/sheet/window coupling holds only insofar as the complete
\(\xi\)-code includes and independently certifies those coordinates.
The proposition does not prove the two exit assertions \(X_h^\pm\),
filter survival \(M_h\), or concatenation into one proper two-sided
source path.

#### Proof

For a fixed end \(e^\varepsilon_r\), the set

\[
 \{\delta:e^\varepsilon(\delta)=e^\varepsilon_r\}
 =
 \{\delta:(\delta,e^\varepsilon_r)\in\mathcal C^\varepsilon\}
 \setminus
 \bigcup_{t<r}
 \{\delta:(\delta,e^\varepsilon_t)\in\mathcal C^\varepsilon\}
\tag{6.5}
\]

is Borel.  Hence each selector is Borel, and intersections of the two
selector fibers give the finite Borel partition (6.4).

A Borel restriction has a Borel saturated union by the stated
transversal hypothesis and is a proper Borel sublamination; therefore
its arc diagram is a valid target sub-WAD.  By (6.2a), on
\(\Lambda_{rs}\) every oriented leaf begins at
the image of the one fixed proper degree-one end \(e^\varepsilon_r\)
or \(e^\varepsilon_s\), respectively.  The hypotheses of
`thm:immer-decomp` consequently hold for each orientation, and
Proposition 4.1 supplies the two witness-relative source WADs and
their coefficient equalities.

The two applications use the same target-leaf partition
\(\Lambda_{rs}\).  If the independently certified exit label in each
application equals the actual code \(\xi(\delta)\), their witness
indices have the same \(\delta\), transverse parameter, and
occurrence label.  This is exactly the bookkeeping coupling asserted
above.  No statement about geometric exit, marking filters, or
two-sided properness was used or inferred. \(\square\)

### Qualification 6.2

Proposition 6.1 does not construct \(\mathcal C^\pm\).  Finite topology
does not imply that a proof-used target endpoint has a source preimage
end with the correct proper-degree-one, access, sheet, and occurrence
data.  Nor does it make those predicates Borel or supply the
Borel-saturation property.  Finiteness here concerns topological ends
only: the numbers of marked accesses, ideal intervals, sheets, and
occurrence codes may still be unbounded.  The proposition says only
that, after the geometric and measurable-lamination facts are proved,
no further measurable-selection theorem is needed for the finite
topological-end choice.  Moreover \(q_-\) and \(q_+\) are only finite
for each individual surface.  No bound uniform over stationary blocks
or primitive periods follows.  A uniform response-state or
multiplicity theorem still requires a bound
\(q_-q_+\leq q_b\), a width-compatible finite quotient, or a separate
summable charge.

## 7. What this changes in MSLS

The general marked stationary lift selector was previously phrased as
requiring a new Borel maximal-lift theorem.  Proposition 4.1 shows
that this is too broad.

For every target sub-WAD on which the following data are already
fixed:

1. one source starting-end class;
2. proper degree-one behavior of the immersion there; and
3. orientation from its target image,

KKL already supply the unmarked lift-until-exit foliation and its
full/exit WAD partition.

The first stationary construction gate is therefore the narrower
**marked fixed-end partition**:

\[
\boxed{
\begin{array}{c}
\text{partition the proof-used target Wave into uniformly controlled}\\
\text{proper degree-one starting-end/occurrence classes, and prove}\\
\text{that the KKL witness preserves their access, sheet, horizon,}\\
\text{nested-window, fine-marking, and coarse-filter records.}
\end{array}}
\tag{6.1}
\]

Raw access and component counts may grow with the period.  “Uniformly
controlled” in (6.1) requires a proved bound or a compact response
state; finite topology of each individual block is insufficient.

## 8. Why line 1600 does not yet instantiate the theorem twice

KKL master-source line 1600 asserts that each relevant leaf has an
endpoint in \(L_0^0\) and has a restriction with an endpoint in
\(L_0^n\).  This supplies one existential restriction.  It does not
by itself prove:

1. that the two proof-used line-1603 route roles correspond to two
   distinct source ends in the sense of `thm:immer-decomp`;
2. proper degree-one behavior at both such ends;
3. a measurable WAD partition between those ends;
4. complete-target images for both lifted portions; or
5. the component-to-complement incidence used at lines 1609--1617.

Reversing the target orientation and applying the fixed-end theorem
again only helps after the second source starting end and its proper
degree-one map have been identified.  The theorem cannot manufacture
that end from the phrase “passes through.”

Thus Proposition 4.1 is genuine progress on the measurable
lift-until-exit construction, but it does not prove the two line-1603
occurrences.

## 9. Adversarial audit

1. The KKL immersion-decomposition theorem is imported only in its
   finite-topology, proper-degree-one-end scope.
2. Several source ends over one target end are not silently identified.
3. A WAD witness is not called a canonical leaf selector.
4. The equality in (4.3) is coefficient-norm equality for paired WAD
   pieces, not equality of arbitrary marked curve-family moduli.
5. An other-end source arc is proper in the source but may map to only
   a strict portion of the target path.
6. Such a proper partial-image arc may itself be the retained ambient
   successor; a distinct replacement is not asserted in that case.
7. Ambient unbreakability supplies a nonempty retained fiber, not a
   unique member or a measurable selection.
8. A relation-valued switch is not a two-occurrence binder.
9. Line 1600 gives one existential restriction, not two fixed
   degree-one starting ends.
10. No source theorem is used circularly to prove line 1603.
11. No uniform bound is inferred from individual finite topology.
12. No global obligation is promoted.

## 10. Result

The exact advance is:

\[
\boxed{
\begin{array}{c}
\text{fixed proper degree-one starting-end data}\\
\Longrightarrow
\text{a source-native, weight-preserving full/exit WAD split;}\\
\text{ambient survivor on the exit part}\\
\Longrightarrow
\text{a nonempty relation-valued route-switch fiber.}
\end{array}}
\tag{9.1}
\]

The immediate missing theorem is a uniformly controlled marked
fixed-end partition plus either no-switch uniqueness or a quantitative
separation/response estimate for the switch relation.
