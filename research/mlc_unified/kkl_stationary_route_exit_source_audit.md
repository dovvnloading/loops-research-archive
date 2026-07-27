# Source audit of the KKL stationary route-exit conductance

## 1. Question, scope, and binary verdict

The proposed route-localized response is

\[
 \mathfrak E_h(F)=\mathcal W(\mathscr E_h(F)),
 \qquad
 \sum_{h=1}^{b+2}\mathfrak E_h(F)
 \le C_b\bigl(V(F)+R(F)+1\bigr),
\tag{1.1}
\]

where \(\mathscr E_h(F)\) is intended to retain the proof-used target
leaf, its selected inverse-continuation germ, the occurrence window,
the source sheet and access, and the first failure of the horizon-\(h\)
immersion branch.

The source audit has two conclusions.

\[
\boxed{
\begin{minipage}{0.88\linewidth}
KKL Wave subordination, interval itineraries, and route words do not
by themselves define \(\mathscr E_h(F)\) as a measurable marked
family.  Consequently none of KKL's Wave, domination, shift,
covering, or Wanderers estimates currently proves (1.1).
\end{minipage}}
\tag{1.2}
\]

There is, however, a narrower positive source result which must not be
overlooked.  KKL's immersion-decomposition theorem starts with:

1. an already valid weighted arc diagram;
2. an already selected set of source ends on which the immersion is
   proper of degree one; and
3. an orientation beginning at those ends.

It then lifts the realizing foliation until it leaves the source and
assembles the lifted segments into a valid source foliation.  This is
an unmarked, WAD-level lift-until-exit construction.  It does **not**
supply the missing stationary sheet selector, segmented occurrence
record, first-failure refinement, or a \(V+R\) estimate.

Thus the first gap is not the elementary existence of maximal local
lifts.  It is the absence of a canonical, transverse-measurable
choice of the proof-used initial occurrence sheet/end, together with
proof that the resulting lift-until-exit foliation represents the
actual stationary occurrence and survives every marking filter.

No ledger status is changed here.  The stationary defect estimate,
VAAPC-I, UPTCR, and MLC remain open.

## 2. Locked sources

The locked KKL master source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The master source imports

```text
.tmp_wave_audit/not-all-good2.tex
SHA-256 B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01
```

at master line 1140.  The imported file must be locked separately
because its contents are not determined by the hash of the master
file.

The exact source clauses relevant to the audit are:

- master lines 406: paths are taken up to reparameterization and
  proper paths must land in the ideal boundary;
- lines 1145--1156: the marked complementary surface and terminal
  Wave alternative;
- lines 1225--1274: the complementary-surface covering/immersion,
  induced markings, and combinatorial action;
- lines 1355--1368: breakable and unbreakable Wave parts;
- lines 1429--1492: the vertical, two-Wave, and outward breaking
  responses;
- lines 1514--1537: the three stationary Wave estimates;
- lines 1547--1622: the stationary critical-end telescope and final
  component-crossing argument;
- lines 1844--1875: ideal boundaries, marked paths, laminations,
  subordination, and Waves;
- lines 1901--1943: valid WADs and canonical laminations;
- lines 2065--2078: covering pushforward of an already constructed
  source lamination;
- lines 2081--2097: immersion restrictions and their marking filter;
- lines 2099--2108: the interval-itinerary proposition;
- lines 2141--2178: dynamic pushforward, Wave, nonbreaking, and Shift
  lemmas;
- lines 2347--2408: the Wanderers Theorem and its route partition;
- `not-all-good2.tex` lines 514--545: immersion decomposition by
  lifting a foliation from a prescribed proper degree-one end; and
- `not-all-good2.tex` lines 471--500 and 570--603: the actual
  source-scoped use of Wanderers and immersion decomposition.

## 3. The proposed symbol is not yet typed

There are two inequivalent objects which the phrase "selected
continuation family" can denote.

### 3.1 Target-leaf interpretation

Let \(Y\) be the proof-used target Wave.  Given a selector \(s_h\)
of initial horizon-\(h\) germs, one could define

\[
 E_h^{\rm tar}
 =
 \left\{
   \alpha\in Y:
   \text{the maximal lift selected by }s_h(\alpha)
   \text{ fails before the declared remote end}
 \right\}.
\tag{3.1}
\]

If \(E_h^{\rm tar}\) is measurable in the native transverse measure of
\(Y\), its width is inherited from the target Wave.  This is the
typing needed for a measurable partition of \(Y\).

The source does not provide \(s_h\).  In particular, an interval
itinerary does not choose:

- a source component of the inverse image of the leaf;
- one occurrence when the same target portion occurs more than once;
- one source access when several accesses have the same coarse target
  label; or
- one full stage path extending a strict occurrence window.

Without that choice, (3.1) is not a set.

### 3.2 Source-trace interpretation

Alternatively, one could let

\[
 E_h^{\rm src}
 =
 \left\{
   \widehat\alpha|_{J_\alpha}:
   \alpha\in Y,\ 
   J_\alpha\text{ is the maximal selected lift interval}
 \right\}.
\tag{3.2}
\]

These curves lie in \(U^h\), not in the target surface.  They may end
at a nonproper source end, may represent only strict subpaths of the
target leaves, and need not survive the fine/coarse marked-path
filters.  The source does not state that they form a lamination, nor
does it identify their source extremal width with the transverse width
of (3.1).

Consequently the expression

\[
 \mathcal W(\mathscr E_h(F))
\tag{3.3}
\]

is ambiguous until the ambient surface and the inherited measure are
declared.  The safe definition is the target-leaf definition (3.1),
with the source trace retained as a label.  It requires an explicit
measurable selector and width-preservation clause.

### 3.3 Marked multiplicity is not ordinary extremal width

Ordinary extremal width is attached to a set of curves in one
Riemann surface.  It does not count two copies of the same target
curve twice merely because they carry different sheet labels.  Hence
a "marked width" must mean one of:

1. the width of a measurable target subfamily after selecting exactly
   one mark per target leaf;
2. width on a disjoint marked cover in which the copies are genuinely
   different curves; or
3. a separately defined transverse measure with multiplicity.

KKL use the first and second types in specific constructions, but no
source clause installs one of them for \(\mathscr E_h(F)\).  This is
another reason that the labels cannot simply be appended to (3.3)
without a definition.

## 4. What KKL's restriction calculus actually supplies

### 4.1 Raw immersion restriction is set-valued

At source line 2083, for a proper target path \(\gamma\),

\[
 \iota^*\gamma
 =
 \left\{
   \text{proper source paths contained in }\iota^{-1}(\gamma)
 \right\}.
\tag{4.1}
\]

This is a set of complete proper source paths.  It is not a selected
inverse germ and it is not a maximal-continuation operator.

Lines 2096--2097 then discard every restriction which:

- is not a path in the chosen refined source marking; or
- is subordinate to one interval of the coarser pulled marking.

Therefore a path component may exist analytically and still be absent
from the proof-used \(F_*\)-image.

### 4.2 An interval itinerary is not a path selector

The itinerary proposition at lines 2099--2108 gives a finite interval
sequence.  Each adjacent pair may be related by:

1. an actual restriction path;
2. mere adjacency; or
3. membership in one coarse pulled interval.

The latter two cases contain no source curve.  Hence the itinerary
does not define a leafwise inverse branch and cannot define a first
failure time.

### 4.3 \(F_*\) retains all eligible proper restrictions

At line 2141, \(F_*=f_*\iota^*\) acts on path families using the
filtered set-valued restriction.  A path is "unbreakable" when the
result is a single retained path.  This definition does not record:

- which local source germ generated that path;
- whether another nonretained source component existed;
- a failed partial continuation; or
- a marked coupling between the input and output leaves.

A selected germ may fail even if some other retained restriction
makes \(F_*\gamma\) a singleton.  Conversely, \(F_*\gamma\) may break
because two complete restrictions survive even though a chosen germ
continues perfectly.  Thus

\[
 \text{selected route exit}
 \quad\not\Longleftrightarrow\quad
 \text{KKL breakability}.
\tag{4.2}
\]

Any proof using KKL's three breaking types must establish one
direction of (4.2) for the selected occurrence, at the correct stage.

### 4.4 Wave subordination is homotopical

Line 1868 defines subordination by requiring that, **up to homotopy
relative to endpoints**, a path lie in every neighborhood of a
boundary set.  The Wave definition at lines 1874--1875 inherits that
notion.

It follows that subordination gives no containment of the actual leaf
in:

- an embedded Kahn collar;
- the image of one immersion sheet;
- a selected localization; or
- the domain of a selected inverse branch.

The conformal example in Section 8 makes this failure exact.

## 5. The nearest positive source theorem

### 5.1 KKL immersion decomposition

`not-all-good2.tex` lines 514--545 state the following source theorem.
Let

\[
 i:V'\longrightarrow V
\]

be a holomorphic immersion of finite-topology open Riemann surfaces.
Let \(E'\) be a set of source ends on each of which \(i\) is proper
and degree one, and let \(E=i(E')\).  If \(Y\) is a valid WAD on \(V\)
whose arcs all have an endpoint in \(E\), then there is a valid WAD
\(Y'\) on \(V'\) with a weight-preserving decomposition such that each
source arc either:

1. has both endpoints in \(E'\) and maps to the full target arc; or
2. has its initial endpoint in \(E'\) and its other endpoint outside
   \(E'\).

The proof orients a realizing proper foliation from \(E\), lifts each
leaf from the prescribed end in \(E'\) until it leaves \(V'\),
assembles the lifted leaves into a partial proper foliation, and
partitions by source homotopy class.

This is a genuine source-level lift-until-exit theorem.  It prevents
the overly broad assertion that KKL never assemble pointwise exits
into a foliation.

### 5.2 Why it does not define the proposed marked family

The theorem begins after all of the following have been supplied:

1. a valid target WAD and a chosen realizing foliation;
2. an orientation of every leaf;
3. a fixed set \(E'\) of starting source ends;
4. proper degree-one extension of the immersion at every end in
   \(E'\); and
5. identification of the target starting ends as \(i(E')\).

For the stationary occurrence problem, the missing data are precisely
which proof-used source end, occurrence, access, and sheet comprise
\(E'\) for almost every leaf.  The theorem does not choose among two
degree-one source ends which have the same target access.

It also partitions only by source homotopy class.  It does not retain:

- the horizon \(h\);
- nested occurrence windows;
- the fine-marking survivor;
- the coarse-filter witness;
- the first obstacle or attachment encountered;
- the first-failure time or failure type; or
- compatibility of the choices through all prefixes.

Finally, the theorem is a domination/decomposition statement.  It
copies target weight to lifted source arcs; it gives no upper estimate
for the exit part in terms of \(V(F)\) or \(R(F)\).

### 5.3 Exact stationary instantiation test

This subsection answers two binary questions:

1. does master line 1600 supply the fixed proper-degree-one source end
   required by the immersion-decomposition theorem; and
2. can one obtain the two portions asserted at master line 1603 by
   applying that theorem in the two orientations?

The answer to both questions, from the locked clauses alone, is
**no**.

Fix a proof-used depth \(h\ge b\), and put

\[
 V=U\setminus T,\qquad
 V_h=U^h\setminus F^{-h}(T),\qquad
 i_h=\iota_h:V_h\longrightarrow V.
\tag{5.1}
\]

Here \(i_h\) is the iterated immersion, viewed with the associated
inclusion identification used in the stationary argument.  Read
literally, line 1600 supplies only

\[
 \forall\alpha\in A_h\quad
 \exists\theta_\alpha\in i_h^*\alpha
 \quad
 \left[
   \theta_\alpha\text{ has an endpoint on }L_0^h
 \right].
\tag{5.2}
\]

Even (5.2) is an existential statement about a complete restriction
path.  It does not state any of the following:

- that the other endpoint of \(\theta_\alpha\) belongs to one fixed
  source end or to a fixed finite list of source ends;
- that \(i_h\) is proper at such an end;
- that its end degree is one;
- which prime-end access or immersion sheet is used; or
- that \(\alpha\mapsto\theta_\alpha\) is a transverse-measurable
  choice.

There are two geometrically different candidate ends, and conflating
them hides the obstruction.

#### The deep \(L_0^h\)-end is not an admissible starting end

Master line 1598 proves that \(L_0^b\cap T=\varnothing\).  The same
pullback argument excludes a component of \(\mathcal K\) at every
later depth, and line 1602 explicitly separates \(T\) from
\(L_0^{n+1}\) for every \(n\ge b\).  Thus every deep end used at line
1603 lies over a continuum

\[
 L_0^h\subset U\setminus T=V.
\tag{5.3}
\]

Let \(e_h\) be a source ideal end of \(V_h\) incident to this
continuum.  Under the associated inclusion \(i_h\), a sequence in
\(V_h\) tending to \(e_h\) has image accumulating on \(L_0^h\), hence
inside \(V\).  Choose a compact neighborhood
\(K\Subset V\) of the relevant compact subcontinuum of \(L_0^h\).
A tail of that sequence maps into \(K\).  Therefore the map does not
send the end \(e_h\) out of every compact subset of \(V\):

\[
 i_h\text{ is not proper at }e_h.
\tag{5.4}
\]

In particular, \(e_h\) cannot belong to the set \(E'\) in
`thm:immer-decomp`.  Notice that the covering projection \(f^h\) may
send the selected pulled continuum toward \(L_0^0\); that fact is
irrelevant to (5.4), because the theorem is being invoked to restrict
under the immersion \(i_h\), not to lift under the covering \(f^h\).

#### The original \(BL_0\)-end is only a candidate, not a certificate

The other candidate is a source end \(e_{0,h}\) above the original
\(BL_0\)-end of \(V\).  Starting at such an end is geometrically
compatible with the incoming portion.  But line 1600 neither selects
one such access nor asserts that

\[
 i_h:e_{0,h}\longrightarrow BL_0
\quad\text{is proper of degree one}.
\tag{5.5}
\]

The one-step embedded-neighborhood observation at master line 1241
does not occur in line 1600 and is not, without an iterated collar and
access statement, the complete hypothesis (5.5).  Even if (5.5) is
proved independently, the decomposition theorem produces the
maximal lift from \(e_{0,h}\); identifying its other end with the
particular occurrence of \(L_0^h\) in (5.2) still requires an
incidence/selection theorem.

Thus the exact answer to the first question is:

\[
\boxed{\text{Line 1600 supplies no fixed proper-degree-one source end.}}
\tag{5.6}
\]

It supplies one unspecified restriction ending at the deep end.  The
deep end is not proper for \(i_h\), while the proper-degree-one status
and access of the original end are additional hypotheses.

#### The two-orientation test

Now fix \(n\ge b\), set \(h=n+1\), and suppose that a leaf
\(\alpha\in A_h\) avoids \(K_0^n\), as in the antecedent used at line
1603.  The two desired source portions are

\[
\begin{aligned}
 P^-_\alpha&:BL_0\rightsquigarrow L_0^h,\\
 P^+_\alpha&:L_0^h\rightsquigarrow
       \partial_{\rm C}T\setminus BL_0.
\end{aligned}
\tag{5.7}
\]

Applying `thm:immer-decomp` with the foliation oriented from the
\(BL_0\)-end would require (5.5).  If (5.5) were supplied, the theorem
would construct a maximal source lift from that end, but it would not
by itself prove that the first exit is the declared occurrence of
\(L_0^h\).  This is the missing incoming incidence clause.

Reversing the orientation does not start the theorem at \(L_0^h\).
That is forbidden by (5.4).  It instead requires, for the actual
remote endpoint of each leaf, a source end \(e_{+,h}(\alpha)\) such
that

\[
 i_h:e_{+,h}(\alpha)\longrightarrow
 \partial_{\rm C}T\setminus BL_0
\quad\text{is proper of degree one}.
\tag{5.8}
\]

Line 1600 says only that the remote endpoint lies somewhere in
\(\partial_{\rm C}T\setminus BL_0\).  It neither selects
\(e_{+,h}(\alpha)\) nor proves (5.8).  Moreover, a maximal lift begun
at a certified remote end may first leave \(V_h\) at an attached
component different from \(L_0^h\).  Excluding that event is exactly
the missing outgoing incidence clause; a coarse remote interval label
does not exclude it.

For reference, the complete logical reduction is

\[
\begin{split}
 &\text{two actual line-1603 portions}\\
 &\quad\Longleftarrow
 C^-_h\wedge X^-_h\wedge
 C^+_h\wedge X^+_h\wedge
 P_h\wedge M_h,
\end{split}
\tag{5.9}
\]

where:

- \(C^-_h\) is the fixed or measurably partitioned proper-degree-one
  certificate at the original \(BL_0\)-source end;
- \(X^-_h\) says its maximal lift exits at the declared
  \(L_0^h\)-occurrence;
- \(C^+_h\) is the corresponding certificate at every proof-used
  remote source end;
- \(X^+_h\) says the reverse maximal lift exits at the **same**
  \(L_0^h\)-occurrence;
- \(P_h\) couples both lifts to the same target leaf, occurrence
  window, sheet/access data, and transverse parameter; and
- \(M_h\) proves that both full source paths survive the fine/coarse
  filters and that their \(f^h\)-images are Waves with the asserted
  bases and crests.

The proof of `thm:immer-decomp` is leafwise, so it can be used after
the certificates in (5.9) have been constructed.  Its stated WAD
decomposition, however, retains only homotopy classes and weights and
does not itself output the common occurrence coupling \(P_h\).
Neither line 1600 nor the interval-itinerary proposition supplies any
of \(C_h^\pm,X_h^\pm,P_h,M_h\) in the required form.

Consequently, two formal applications with opposite orientations do
not construct (5.7) from the locked source.  One may at most obtain an
incoming lift after independently proving \(C_h^-\); the outgoing
interior-to-remote route cannot be obtained by restarting at
\(L_0^h\), and a reverse lift requires the separate
\(C_h^+,X_h^+\) theorem.

### 5.4 The actual first missing source statement

The first missing statement may be formulated as follows.

> **Marked stationary lift selector (MSLS).**  
> For every proof-used stationary Wave \(Y\) and every
> \(1\le h\le b+2\), there are:
>
> 1. a conull standard Borel transverse parameter space
>    \((\Lambda,\nu)\) for \(Y\);
> 2. a Borel map assigning to each \(\alpha_\xi\) one proof-used
>    horizon-\(h\) occurrence, source sheet, source access, and local
>    \(I_h\)-inverse germ;
> 3. a fixed source-end class on which \(I_h\) is proper of degree one,
>    or a proved finite measurable partition into such classes;
> 4. a Borel maximal-lift endpoint, remote-success/first-failure code,
>    and source homotopy class;
> 5. a proof that the selected source traces assemble into the
>    immersion-decomposition foliation and survive every proof-used
>    fine and coarse marking filter; and
> 6. equality between the restriction of \(\nu\) to every failure
>    class and the width used for that class in the later argument.

No locked KKL clause proves MSLS for the stationary critical-end
horizon.  Wave subordination addresses none of items 2--5.

Once items 2--3 are supplied, the immersion-decomposition theorem is
the correct source tool for part of items 4--6.  It should be used
rather than reproving a generic lift-until-exit foliation from
scratch.

## 6. Source-lemma audit for the proposed \(V+R\) bound

### 6.1 Vertical-width charge

At lines 1442--1444, KKL define an actual subwave \(A^{\rm ver}\)
whose source restriction contains a path joining the two boundary
components of the pulled annulus.  They prove

\[
 \mathcal W(A^{\rm ver})
 \le
 \mathcal W(U'\setminus T')
 \le 2V(F).
\tag{6.1}
\]

This controls a route-exit class only after proving that each selected
exit contains that actual vertical restriction and that the
leaf-to-restriction assignment has the required width domination.
Exiting a local sheet at a nonproper ideal end does not imply a
crossing between the two annular boundary components.

### 6.2 Domination under an immersion

The domination lemma at lines 2086--2089 starts with pre-existing
source laminations \(S'_j\) and assumes that every target leaf has a
restriction containing a leaf of each \(S'_j\).  It yields

\[
 \mathcal W(S)\le\mathcal W(S'_j),
\tag{6.2}
\]

and, under injectivity on their union, a harmonic-sum improvement.

This is not an upper bound for an unconstructed exit family.  It is
also the wrong coercive direction unless the source family on the
right is independently bounded.

### 6.3 Covering pushforward and the Wave lemma

The covering lemma at lines 2075--2078 assumes an already constructed
proper source lamination with a degree bound at a proof-used end.  The
Wave lemma at lines 2149--2152 assumes an already constructed source
Wave.  Their conclusions are respectively

\[
 \mathcal W(A')
 \le d\,\mathcal W(A)+2d
\tag{6.3}
\]

and

\[
 \mathcal W(A')
 \le\mathcal W(A)+O(1+\log d).
\tag{6.4}
\]

Neither lemma turns a coarse route label or partial inverse germ into
the source lamination \(A'\).  Neither gives a bound unless the pushed
target family \(A\) has already been placed in a controlled Wave or
renormalization class.

### 6.4 Shift

The Shift Lemma at lines 2171--2178 applies only when:

- the base shifts combinatorially;
- the input is an actual Wave subordinate to that base;
- the selected end is well inside the base; and
- one of two explicit end/crest inclusions holds.

It then controls the **unbreakable part** by \(2\).  A first inverse
failure is not shown to be unbreakable, subordinate to a shifting
base, or to satisfy either end/crest inclusion.

### 6.5 The stationary Wave estimates

The estimates at lines 1514--1537 control:

1. an unbreakable Wave over \(BL_0\);
2. an unbreakable localized Wave away from \(BL_0\); or
3. an \(N\)-unbreakable Wave ending at \(BL_0\).

They do not control an arbitrary selected-failure family.  The third
estimate is the proposition whose proof contains the disputed
pass-through step, so invoking it to charge the same unresolved route
exits would be circular.

The final \(R(F)\) charge at lines 1609--1618 starts only after an
actual lamination connecting one component of \(\mathcal K^{N-1}\) to
its complement has been constructed.  Producing that lamination is
the missing geometric incidence, not a consequence of a route word.

### 6.6 Wanderers

The Wanderers Theorem at lines 2347--2368 starts with:

- a proper holomorphic map \(g:X\to Y\) of bounded degree;
- finite compact obstacle families containing all critical values;
- an actual oriented partial foliation in \(X\);
- specified initial and terminal obstacle components;
- at least \(n-1\) actual intermediate visits; and
- a no-return condition at the initial component.

It then gives

\[
 \|\mathcal W(\mathcal F)\|
 \le
 \frac{2d}{n}
 \|\operatorname{wcan}^{h+v}(Y\setminus\mathcal B)\|
 +
 C(|\chi(Y)|,|\mathcal B|,D).
\tag{6.5}
\]

The route partition at line 2391 is formed **after** the actual
foliation and all its visits exist.  It does not construct a
foliation from a route label.

For route exits there are three independent failures of applicability:

1. the problematic map is the immersion \(I_h\), not the proper map
   required by Wanderers;
2. no source foliation with the required visits has been constructed;
3. the topology term in (6.5) is not \(O_b(1)\) without a separately
   proved bounded localization.

In KKL's actual use in `not-all-good2.tex` lines 471--500, the
foliation consists of already constructed WAD pullbacks, the backward
walks are actual, and the constants also depend on the fixed
localization parameters.  That application cannot be transplanted to
\(\mathscr E_h\) by retaining only a coarse stationary route.

### 6.7 Binary estimate verdict

The source lemmas give a \(V+R+O_b(1)\) charge only **conditionally**
after a measurable exit family has been partitioned into actual native
objects such as:

\[
 E_h^{\rm ver},\quad
 E_h^{\rm shift},\quad
 E_h^{\rm crit},\quad
 E_h^{\rm ren},
\tag{6.6}
\]

with bounded multiplicity and with every source hypothesis above
verified.  KKL do not prove that route exits admit (6.6).

Therefore (1.1) is a new analytic theorem, not a corollary of the
listed lemmas.

## 7. The exact missing topological response statement

Even MSLS only defines the family.  A numerical or terminal response
requires a second theorem.

> **Route-exit native classification (RENC).**  
> For almost every selected failure and at its first failure stage,
> construct a priority-disjoint, transverse-measurable assignment to
> one of:
>
> 1. an actual vertical annular restriction;
> 2. an actual one-Wave restriction over the pulled crest;
> 3. two actual retained Waves over the two pulled endpoints;
> 4. an actual unbreakable shifted/critical Wave in the native scope;
> 5. an actual proper component-to-complement lamination chargeable to
>    \(R(F)\); or
> 6. an explicitly retained residual response state.
>
> For cases 1--5, prove all end-properness, degree, fine-marking,
> coarse-filter, covering-image, and bounded-multiplicity hypotheses,
> and prove width domination from the target failure class to the
> constructed source object.

The "first failure stage" is essential.  The KKL three-type breaking
argument applies to a one-step breakable part in an ambient Wave.  It
does not apply merely because an iterated selected branch fails.

### 7.1 Exact survivor reduction after MSLS

The formal reduction in
`kkl_stationary_route_exit_survivor_reduction.md` is valid once MSLS
has produced a single-valued measurable target-leaf failure set
\(E_A\).  For a horizon \(H\), define

\[
\begin{aligned}
 E_A^{\rm br}
 &=
 E_A\cap A^{H\text{-br}},\\
 E_A^{\rm sh}
 &=
 E_A\cap A^{H\text{-nbr}}\cap A^{\rm sh},\\
 E_A^{\rm surv}
 &=
 E_A\cap A^{H\text{-nbr}}\setminus A^{\rm sh}.
\end{aligned}
\tag{7.1}
\]

These sets are pairwise disjoint and exhaust \(E_A\).  If

\[
 B_A=A^{H\text{-br}}\cup A^{\rm sh},
\tag{7.2}
\]

then

\[
 E_A^{\rm br}\cup E_A^{\rm sh}\subset B_A,
 \qquad
 E_A^{\rm surv}\cap B_A=\varnothing.
\tag{7.3}
\]

This is a set identity, not an analytic estimate.  It has an important
consequence for the response program: after rebuilding the
single-target-leaf partition **before** summing widths, the only
genuinely new exit term is \(E_A^{\rm surv}\).

The survivor class is exactly the mechanism isolated in (4.2): the
selected marked occurrence fails, but the complete filtered ambient
\(F_*\)-image remains a singleton, because another retained
restriction may survive.  Therefore KKL's ambient one-step breaking
proof cannot be applied to \(E_A^{\rm surv}\).

RENC should consequently be split:

1. absorb \(E_A^{\rm br}\) and \(E_A^{\rm sh}\) into the already
   present native terms on the target-leaf occurrence space; and
2. apply the new numerical/response classification only to
   \(E_A^{\rm surv}\).

A newly constructed auxiliary Wave made from survivor traces might
itself satisfy a KKL breaking hypothesis.  That possibility is not
excluded.  Constructing such a Wave, proving its width relation, and
transporting its response back to \(A\) would be a new RENC theorem;
it does not follow from ambient breakability.

### 7.2 Qualifications to the survivor schema

Four points in the current survivor note require correction.

First, a record whose first failure is a continuation exit cannot
contain a full proper stage path \(\gamma_r\) at the failure stage.
It must contain full proper stage paths only for \(j<r\), followed by:

\[
 \left(
   \widehat\gamma_r,\,
   J_r^{\max},\,
   \sup J_r^{\max},\,
   \mathsf q_r
 \right),
\tag{7.4}
\]

where \(\widehat\gamma_r\) is the maximal partial lift.  A full
\(\gamma_r\) may be retained only when the failure occurs after
analytic continuation, for example at a marking filter.

Second, the Borel structure on the proposed record space is not
defined merely by listing its fields.  This is part of MSLS, not a
proved premise.

Third, the assertion that the first-failure label set has uniformly
bounded cardinality is open.  Raw access, obstacle, component, and
marking labels can grow with the period or rotation denominator.
Classwise extraction with a factor \(1/L_b\) is uniform only after
constructing a finite failure-type quotient satisfying

\[
 |\mathcal L_b^{\rm type}|\le L(b)
\tag{7.5}
\]

and proving that this quotient preserves every response-relevant
distinction.  Finiteness separately for each block is insufficient.

Fourth, the formal identities (7.1)--(7.3) hold for every \(H\).
The later KKL fact that the unbreakable part of \(B_A\) is short and
has fixed \(12b\)-controllability uses KKL's selected horizon
\(H=N\).  The formal horizon and the source-use horizon must not be
conflated.

MSLS is the first definitional/measurable gate.  RENC is the first
coercive/topological gate.

### 7.3 Exact source semantics of an ambient-survivor switch

There is one further positive pointwise reduction.  It must be stated
without turning an untagged singleton into a unique marked
predecessor.

Let \(\alpha\in E_A^{\rm surv}\), and write the native ambient orbit
through the horizon as

\[
 \delta_0=\alpha,\qquad
 \delta_{j+1}=F_{j*}\delta_j
 \quad(0\le j<H).
\tag{7.6}
\]

Here every \(F_{j*}\) must be the actual stage presentation of the
same filtered KKL action used to define \(A^{H\text{-nbr}}\); changing
the pulled marking independently would invalidate the inference below.
Define

\[
\begin{split}
 \operatorname{Ret}_j(\delta_j,\delta_{j+1})
 =
 \{\,\gamma:\;&
   \gamma\text{ is a complete proper member of }\iota_j^*\delta_j,\\
  &\gamma\text{ survives the fine-path and coarse-interval filters},\\
  &f_{j*}\gamma=\delta_{j+1}\,\}.
\end{split}
\tag{7.7}
\]

Then

\[
 \operatorname{Ret}_j(\delta_j,\delta_{j+1})\ne\varnothing
 \qquad(0\le j<H).
\tag{7.8}
\]

Indeed, KKL define \(F_{j*}\delta_j\) by taking all complete proper
immersion restrictions, applying the line-2097 filters, and pushing
the retained restrictions by \(f_j\).  Since \(\alpha\) is
\(H\)-unbreakable, each such result is "a single path."  In the source
set-valued semantics this means a nonempty singleton
\(\{\delta_{j+1}\}\), not the empty family.  Hence at least one
retained restriction has covering image \(\delta_{j+1}\), proving
(7.8).

The conclusion does **not** say
\(|\operatorname{Ret}_j|=1\).  Several source restrictions, on
different sheets or with different occurrence/access data, can have
the same untagged \(f_j\)-image and collapse to the singleton
\(\{\delta_{j+1}\}\).  This is precisely why ambient unbreakability
does not preserve the selected route.

Finite pointwise choice from (7.8) gives paths

\[
 \widehat\gamma_j\in
 \operatorname{Ret}_j(\delta_j,\delta_{j+1}),
 \qquad 0\le j<H.
\tag{7.9}
\]

As written, (7.9) is a **stagewise retained predecessor sequence**.
To call it a segmented occurrence chain, one must additionally
construct, at every transition, an actual occurrence window

\[
 a_j:J_{\widehat\gamma_j}\hookrightarrow J_{\delta_j},
 \qquad
 \delta_j\circ a_j=\iota_j\circ\widehat\gamma_j,
\tag{7.10}
\]

with the required orientation and prefix compatibility.  The
simple-path window lemma can provide (7.10) only after the actual
containment and simple Wave representatives have been verified.  A
coarse interval itinerary cannot do so.

Let \(r\) be the first failure stage of the selected route.  Relative
to a formally exhaustive route-state predicate, (7.8) yields the
following pointwise dichotomy:

1. the selected stage-\(r\) object is not a member of
   \(\operatorname{Ret}_r\), so a full retained path is a strict
   replacement; or
2. it is a member of \(\operatorname{Ret}_r\), but one of the
   additional marked route-state predicates fails, so the first defect
   is a marked-state switch.

This dichotomy is exhaustive only if "marked route state" contains
**every** predicate which can generate the first-failure code:
access and cyclic order, exact occurrence window, sheet, obstacle and
attachment/parent data, localization, relative-cover compatibility,
remote landing, whole-target-portion coverage, both marking filters,
and future prefix compatibility.  Omitting one predicate gives an
immediate set-theoretic countermodel: take a singleton retained fiber
whose listed states agree, and let the selected route fail only by the
omitted predicate.

Accordingly, a valid marked no-switch theorem must say more than
"there is one retained state class extending the initial seed."  It
must assert that the **selected named occurrence itself** belongs to
the unique prefix-compatible retained class at every stage and that
the class satisfies every failure-code predicate.  Otherwise a strict
replacement can coexist with a unique alternative class, and the
selected route can still fail.

Thus the source-valid gain is (7.8), plus (7.9) pointwise.  Borel
selection, segmented windows, a uniform state quotient, selected-prefix
uniqueness, and a width/terminal response remain open.

## 8. Exact conformal countermodels to coarse route selection

The examples in this section are conformal dependency countermodels.
They are not asserted to be native periodically repelling stationary
KKL blocks.

### 8.1 The L-shaped two-sheet immersion

Fix \(L>4\), let

\[
 S_L=\{z=x+iy:0<x<1\},
 \qquad
 A_L=S_L/\langle z\mapsto z+iL\rangle,
\tag{8.1}
\]

and write

\[
 q_L(z)=\exp(2\pi z/L)
\tag{8.2}
\]

for the annular quotient.
Equip the inner ideal boundary with a finite marking, chosen so that
the boundary arc used below contains at least three marked intervals.
Thus the subordinate semicircles below are paths in KKL's marked
sense, rather than paths discarded for being subordinate to a
multi-interval of length at most two.

Define the connected simply connected L-shaped source

\[
\begin{split}
 X_L
 ={}&
 \{0<x<1,\ 0<y<L\}\\
 &{}\cup
 \{0<x<1/2,\ 0<y<2L\}.
\end{split}
\tag{8.3}
\]

The restriction

\[
 i_L=q_L|_{X_L}:X_L\longrightarrow A_L
\tag{8.4}
\]

is a holomorphic immersion.  On the left half of the cylinder it has
two sheets:

\[
 x+i\theta,
 \qquad
 x+i(\theta+L),
\tag{8.5}
\]

while only the lower sheet continues through \(x>1/2\).

Both source accesses at \(x=0\) map homeomorphically and with degree
one to the same target access.  Thus the target route label,
orientation, and target access do not choose between them.

### 8.2 Same subordinate path, different continuation result

Choose \(y_0=L/2\) and \(0<r<1\).  For \(a\in(0,1)\), put

\[
 \alpha_a(t)
 =
 q_L\!\left(
   a\sin(\pi t)
   +i\bigl(y_0-r\cos(\pi t)\bigr)
 \right),
 \qquad 0<t<1.
\tag{8.6}
\]

For \(r<L/4\), these are simple proper target paths with the same two
inner-boundary endpoints.  For different \(a\), they are homotopic
relative to those endpoints and subordinate to exactly the same inner
boundary interval.

Lift from the upper source access by adding \(iL\).  If \(a<1/2\), the
whole lift remains in the upper arm of \(X_L\).  If \(a>1/2\), the
maximal lift first meets the source boundary \(x=1/2\) before reaching
the remote target endpoint.

Hence

\[
 \boxed{
 \text{same endpoints + same homotopy class + same Wave subordination}
 \not\Rightarrow
 \text{same continuation outcome}.}
\tag{8.7}
\]

This is an exact conformal refutation of any attempt to infer collar
or sheet containment from Wave subordination.

### 8.3 Pointwise sheet choices need not be measurable

For \(1/2<r_0<r_1<1\), the nested semicircles

\[
 \alpha_r(t)
 =
 q_L\!\left(
   r\sin(\pi t)
   +i\bigl(y_0-r\cos(\pi t)\bigr)
 \right),
 \qquad r_0<r<r_1,
\tag{8.8}
\]

form a genuine target Wave lamination.  Every leaf has:

- a full lower-sheet lift; and
- an upper-sheet lift which fails when its real coordinate first
  reaches \(1/2\).

Both lifts have the same target route, target orientation, and target
access labels.  Let \(E\subset(r_0,r_1)\) be arbitrary.  Select the
upper germ on \(\alpha_r\) for \(r\in E\), and the lower germ otherwise.
The selected route-exit set is exactly \(E\).

The region between two of the concentric semicircles is a
quadrilateral, so the Wave has the standard atomless transverse
measure obtained by uniformizing that quadrilateral.  If \(E\) is
nonmeasurable for this measure,
the selected failure family is nonmeasurable, even though a
pointwise selected germ exists for every leaf.  If \(E\) is empty,
the exit conductance is zero; if \(E=(r_0,r_1)\), it is the positive
width of the whole Wave.

This does not say that no Borel selector exists.  The all-lower and
all-upper choices are Borel.  It proves the exact logical point:

\[
 \text{pointwise choice + coarse route labels}
 \not\Rightarrow
 \text{a canonical or measurable choice}.
\tag{8.9}
\]

The source sheet/access marking is the datum that distinguishes the
two choices.  MSLS must prove that this datum varies measurably in the
actual stationary family.

### 8.4 Why the route partition in Wanderers does not repair the model

All target leaves in (8.8) have the same coarse obstacle route.  The
Wanderers route partition therefore has one target route class.  It
cannot see the arbitrary lower/upper selection.

The upper partial lifts are not good full target-route paths ending at
the declared remote access.  Consequently no route word in the
Wanderers sense converts them into the missing full occurrence.

## 9. Audit of the broader defect-response alternative

This section audits
`kkl_stationary_defect_response_alternative.md`.

### 9.1 Conditional algebra in Theorem 4.1

The proof that QSDRA implies a short-or-terminal alternative is
algebraically correct after its hypotheses are granted:

- the vertical and responsive cases are separated first;
- the remaining three charges are absorbed at absolute scale;
- \(B_A\) retains a definite fraction \(\theta\) of \(A\);
- KKL `small breaking` is applied to \(B_A\), whose
  \(N\)-unbreakable part is short and hence \(12b\)-controllable;
- terminality transfers because
  \((1+\delta_3)\theta>1\); and
- strict shortness transfers because
  \(\lambda_3\theta>\lambda\).

The terminal constants should be displayed explicitly:

\[
 \delta
 =
 \min\{
   \delta_v,\delta_{b,\epsilon},\delta_A
 \},
 \qquad
 \eta
 =
 \max\{
   \eta_{b,\epsilon},\eta_3
 \}.
\tag{9.1}
\]

### 9.2 Universal-\(\eta\) quantifier mismatch

QSDRA allows

\[
 \eta=\eta_{b,\epsilon}.
\tag{9.2}
\]

The proof chooses \(\epsilon\) from \(\lambda\).  Therefore (9.2)
allows the output controllability to depend on \(\lambda\).

KKL Proposition `mostly short` states that the terminal
controllability is universal, while its terminal gain may depend on
\(\lambda\).  With \(b\) fixed, "universal" excludes dependence on
the input \(k\) and on \(\lambda\).

The current revision of the response note handles this correctly.  It
concludes only \(\eta_{b,\lambda}\) for a fixed-\(\lambda\) call and
states separately that source-universal controllability requires
either:

1. one \(\eta_b\) valid for all response fractions; or
2. restriction to the finite, predetermined \(\lambda\)-list in the
   final terminal proof, followed by a finite maximum.

Thus Theorem 4.1 is source-accurate on this point after revision.

### 9.3 A route exit is not automatically a KKL breaking type

The current Section 5 correctly lists the following necessary data:

1. the first failure stage \(r\);
2. the ambient stage-\(r\) Wave;
3. proof that the selected occurrence lies in its one-step breakable
   part;
4. end-properness on that Wave's crest;
5. a priority-disjoint measurable partition of the three cases; and
6. width transport from that stage back to the original Wave.

The three geometric alternatives at KKL line 1430 are not stated as
intrinsically exclusive.  A safe certificate takes vertical first,
then two-Wave, and assigns the remainder to the outward one-Wave case.

The survivor reduction sharpens the scope: this certificate can
absorb \(E_A^{\rm br}\), but it cannot be asserted for
\(E_A^{\rm surv}\) merely from the survivor's selected failure.  The
current response note has replaced the former unrestricted
route-exit-to-break target by the breakable/short/survivor trichotomy
and confines the native breaking certificate to the breakable class.
It is source-accurate on this point after revision.

### 9.4 The outward estimate is attached to the wrong family

KKL lines 1486--1488 estimate the auxiliary pulled Wave \(B\), not the
eventual pushed controllable Wave \(C\).  The current response note
now uses the correct source-facing form

\[
 \mathcal W(B)
 \ge
 \left(
   1-2\delta+
   \frac{(\epsilon-2\delta)^2}{6N_{\rm imp}}
 \right)\mathcal W(A),
\tag{9.3}
\]

where

\[
 N_{\rm imp}\le4b(2b+2)
\tag{9.4}
\]

is the number of improper intervals from source line 1464.  It is not
the stationary horizon \(N=b+3\).

The Wave lemma then gives a pushed Wave only after an additive
\(O_b(1)\) loss.  A strict gain for \(C\) follows after the absolute
scale absorbs that loss, with a smaller gain constant.  The current
revision records this loss, distinguishes \(N_{\rm imp}\) from the
horizon, and no longer uses the covering-degree symbol \(d\) for the
small terminal parameter.

### 9.5 The factor-two response needs the rest of the source argument

Lines 1454--1459 give a pulled two-Wave estimate.  To obtain
terminality one still needs:

- the Wave pushforward and its additive loss;
- the controllability transfer;
- assembly with the retained nonbreaking and outward pieces; and
- the absolute-scale absorption.

An occurrence-by-occurrence two-Wave label is not by itself the
response clause.  The current source-facing list correctly records
the pushforward, additive loss, controllability, and assembly
requirements.

Moreover, KKL's pushing-controllability lemma can depend on the input
controllability \(k\).  QSDRA requires independence from \(k\).
Therefore the response must be produced only after passing to a Wave
whose relevant unbreakable part has the fixed \(12b\)-controllability
used in the \(B_A\) construction, or a new uniform controllability
theorem must be proved.

### 9.6 Route-exit conductance alone does not exhaust all defects

A numerical route-exit estimate implies QSDRA only if:

1. route exits exhaust the uncharged residual; and
2. every non-exit defect has already been realized or charged.

The route estimate alone says nothing about marking-filter,
component-incidence, final collision, or measurable-coupling defects.
The current response note now includes this exhaustion hypothesis.

## 10. Exact next theorem

The source-accurate next pass has two ordered parts.

### Part A: construct the family

Prove MSLS by using KKL's immersion-decomposition theorem on the
actual stationary carrier.  In particular:

1. identify the proof-used proper degree-one starting ends;
2. select them measurably with full sheet/access/occurrence marks;
3. prove compatibility through the nested horizon windows;
4. refine the source WAD measurably by first failure;
5. prove all marked-path filters; and
6. identify its target transverse measure.

### Part B: obtain a response

Prove RENC and then either:

\[
 \sum_{h=1}^{b+2}
 \mathcal W(E_h^{\rm tar})
 \le C_b\bigl(V(F)+R(F)+1\bigr),
\tag{10.1}
\]

or a charged/terminal partition with source-correct universal
controllability.

If Part A fails, record the first leaf for which no measurable
proper-degree-one starting occurrence can be selected.  If Part B
fails, record the first selected exit whose source trace realizes none
of the native response classes in RENC.

## 11. Skeptic audit

1. The imported immersion-decomposition theorem is not omitted.
2. Its proper-degree-one starting-end hypothesis is not inferred from
   a target access label.
3. Its unmarked WAD decomposition is not called a marked occurrence
   selector.
4. Wave subordination is not called geometric containment.
5. An interval itinerary is not called a path.
6. A pointwise sheet choice is not called measurable.
7. Ordinary extremal width is not assigned marked multiplicity
   without a definition.
8. A partial source trace is not silently measured in the target
   surface.
9. A selected route exit is not called a KKL break.
10. The domination inequality is not used in the reverse direction.
11. The Wave and covering lemmas are not invoked before their source
    laminations exist.
12. The Shift Lemma is not applied without its shifting-base and
    end/crest hypotheses.
13. Wanderers routes are not used to construct the foliation which
    that theorem assumes.
14. The Wanderers topology constant is not called universal without a
    bounded localization.
15. The final \(R(F)\) charge is not used before actual
    component-to-complement incidence.
16. An iterated failure is not called a one-step break without a
    stage certificate.
17. KKL's auxiliary \(B\)-estimate is not relabeled as an estimate for
    the pushed Wave \(C\).
18. The two meanings of \(N\) in the source are kept distinct.
19. Universal terminal controllability is audited separately from a
    positive terminal gain.
20. No global obligation is promoted.

## 12. Conclusion

KKL contain a useful but narrower lift-until-exit foliation theorem.
It should be the starting point for a correct construction.  The
stationary route-exit conductance nevertheless remains undefined until
the proof supplies a measurable marked starting-occurrence selector
and verifies the source marking filters.

After that construction, the locked Wave, domination, shift, covering,
and Wanderers lemmas still do not provide the desired
\(V+R+O_b(1)\) charge without the new route-exit native
classification RENC.

The L-shaped annular immersion proves that coarse route words and Wave
subordination cannot replace either theorem.
