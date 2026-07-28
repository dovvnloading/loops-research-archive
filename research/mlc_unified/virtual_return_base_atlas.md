# Virtual Return-Base Atlas: Native Principal-Nest Realization and the Exact Virtual Selector Gap

## 1. Status and scope

This pass addresses the first open input of
`virtual_return_branch_language.md`:

```text
VIRTUAL_RETURN_BASE_ATLAS
```

It separates two questions which must not be conflated.

1. **Native analytic question.**  Does an actual nice puzzle base have a
   genuine first-return atlas with open branch domains, exact iterates,
   critical words, component itineraries, and prime-end markings?
2. **Virtual bridge question.**  Does the published virtual-Molecule data
   select such a base, with the required carrier and access data, at every
   intermediate virtual scale?

The first question has a complete positive answer in the principal-nest
setting.  The second remains open.  More precisely, this pass proves:

- `NATIVE_PRINCIPAL_NEST_RETURN_ATLAS`;
- `ISOTOPY_CLASS_RETURN_UNDERDETERMINATION`; and
- the necessity of the new open bridge
  `VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`.

It does **not** prove `VIRTUAL_RETURN_BASE_ATLAS`, because the checked
virtual sources do not define the map from an intermediate satellite-copy
scale to an actual principal-nest or puzzle localization.  Consequently
`VIRTUAL_RETURN_BRANCH_LANGUAGE`, `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`, VAAPC-I, UPTCR, and MLC remain open.

## 2. Source lock and allowed imports

### 2.1 Lyubich's Yoccoz-puzzle source

The source archive for M. Lyubich, *Dynamics of quadratic polynomials, I:
Combinatorics and geometry of the Yoccoz puzzle*, arXiv:math/9503215, was
locked locally as

```text
source-lock/Lyu97/source.tar
SHA256 F799BDC011BEE5F89A467F7C24AFB3C53D0AE556FE7822952A0DE8ADD141FF16
source-lock/Lyu97/src\nest.tex
SHA256 069C10711C36F5358134B418FDF6C5133A5AF16208D2B1C267EA7B4D3A5DF83A
```

The following source ranges are used.

| File and lines | Imported content |
|---|---|
| `nest.tex` 500--517 | construction of the ray/equipotential puzzle and its closed topological-disk pieces |
| `nest.tex` 520--532 | the Markov nesting/disjointness property and the degree-one/degree-two one-step alternative |
| `nest.tex` 577--586 | pullback along an orbit and first-return pullback |
| `nest.tex` 600--619 | principal-nest construction and exact critical first-return branch |
| `nest.tex` 904--919 | first-entry component maps are univalent or degree two according to criticality |
| `nest.tex` 922--949 | decomposition of a nice first-return map into disjoint puzzle domains and the exact degree dichotomy |
| `nest.tex` 975--1005 | principal return maps, boundary avoidance, pairwise disjointness, and nondegenerate annular separation |

The source is used only in this native category.  Nothing in the proof
below identifies a virtual hull with a principal-nest piece.

### 2.2 KKL source

The locked KKL v1 source is

```text
source-lock/KKL26-v1/waves-with-Misha.tex
SHA256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The relevant ranges are:

- lines 299--315: the canonical parameter-copy chain and the
  virtually-satellite classification;
- lines 381--389: virtual renormalization is deferred to a separate work;
- lines 478--490: a prime small filled Julia set is canonical, while
  quadratic-like domains are not, and the native pseudo-quadratic-like
  renormalization is built by localization;
- line 504: the native limb neighborhood \(U_I\) is chosen only up to
  isotopy relative to the small Julia cycle;
- lines 1803--1809: the canonical Yoccoz graph, critical pieces, minimal
  terminal renormalization level, and external marking.

The bibliography entry `DKL:virtual` is still `@unpublished` and marked
“In preparation.”  No theorem from that work is imported.

### 2.3 Dudko source

The locked Dudko v1 source is

```text
source-lock/Dudko25/main.tex
SHA256 FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454
```

Lines 875--892 define the parameter-copy chain and state the virtual-hull
strategy.  The connected hull is to carry the critical orbit for an
“appropriate” number of first returns.  The source does not define an open
return base, a puzzle depth, a principal-nest level, or a rule associating
one of them to a virtual scale.

## 3. Analytic definitions

Let

\[
 f:U'\longrightarrow U
\]

be a quadratic-like map with unique critical point \(0\), and let
\(\mathscr M(f)\) be a Markov Yoccoz puzzle in the sense of the locked
Lyubich source.  Every puzzle piece is understood as a closed topological
disk; its interior is the analytic domain.

### 3.1 Nice puzzle base

A puzzle piece \(V\in\mathscr M(f)\) is **nice** if

\[
 f^m(\partial V)\cap V=\varnothing
 \qquad(m\ge 1).
\tag{3.1}
\]

Set \(B=\operatorname{int}V\).  For \(q\ge1\), define the strict
first-return region

\[
 \mathcal R_q(f,B)
 =
 B\cap f^{-q}(B)\cap
 \bigcap_{k=1}^{q-1} f^{-k}(\mathbb C\setminus\overline B).
\tag{3.2}
\]

Every factor in (3.2) is open, so \(\mathcal R_q(f,B)\) is open.
Its connected components are the candidate analytic branches of return
time \(q\).

The use of \(\mathbb C\setminus\overline B\), rather than merely
\(\mathbb C\setminus B\), prevents an intermediate boundary contact from
being silently classified as an interior first return.  For puzzle
components obtained from the Markov construction, condition (3.1)
excludes the boundary ambiguity on the closed branch pieces.

### 3.2 Principal-nest bases

Write the principal nest as

\[
 Y^0\supset V^0\supset V^1\supset\cdots.
\tag{3.3}
\]

For \(n\ge2\), define

\[
 B_n:=\operatorname{int}V^{n-1}.
\tag{3.4}
\]

The source construction gives

\[
 V^{n-1}\Subset\operatorname{int}V^{n-2}
\quad\text{and}\quad
 f^m(\partial V^{n-1})
 \cap\operatorname{int}V^{n-2}=\varnothing
 \quad(m\ge1).
\tag{3.5}
\]

Since \(V^{n-1}\subset\operatorname{int}V^{n-2}\), (3.5) implies

\[
 f^m(\partial V^{n-1})\cap V^{n-1}=\varnothing.
\tag{3.6}
\]

Thus \(V^{n-1}\) is nice.  This implication is important: niceness is
derived from the stronger source boundary-avoidance statement, not assumed
after the return domains have been selected.

### 3.3 Atomic branch record

For a component \(A\) of \(\mathcal R_q(f,B_n)\) which occurs in the
principal return map, define

\[
 F_A:=f^q|_A:A\longrightarrow B_n.
\tag{3.7}
\]

The complete native branch record is

\[
 \mathfrak b(A)=
 \bigl(
 n,A,q,F_A,\mathcal P_A,\mathbf d_A,
 \operatorname{crit}_A,\operatorname{par}_A,
 \operatorname{sheet}_A,\mathcal O_A,
 \mathcal G_A,\theta_A
 \bigr).
\tag{3.8}
\]

Here:

- \(\mathcal P_A=(P_0,\ldots,P_q)\), with
  \(P_k=f^k(\overline A)\), is the actual puzzle-component itinerary;
- \(\mathbf d_A=(d_0,\ldots,d_{q-1})\), where
  \(d_k=\deg(f:P_k\to P_{k+1})\), is the chronological degree word;
- \(\operatorname{crit}_A\) records whether \(0\in A\);
- \(\operatorname{par}_A\) records the containing component at the previous
  nest level;
- \(\operatorname{sheet}_A\) is the actual inverse-component itinerary,
  with the symbol `critical` at the unique branched start when \(0\in A\);
- \(\mathcal O_A\) records every avoided copy of \(B_n\), the puzzle graph,
  and the terminal return;
- \(\mathcal G_A\) is the finite prime-end marking induced by all
  ray/equipotential boundary vertices and their pullbacks; and
- \(\theta_A\) is the phase fixed by the external-angle coordinate, with
  the least marked angle in \([0,1)\) used as the base access.

The obstacle record in (3.8) is complete for the native first-return
proof.  It is not asserted to contain every obstacle later needed by a
virtual Wave argument.

## 4. Native principal-nest return-atlas theorem

### Theorem 4.1 (`NATIVE_PRINCIPAL_NEST_RETURN_ATLAS`)

Let \(f\) and the principal nest (3.3) satisfy the locked Lyubich
hypotheses, and let \(n\ge2\) be a level at which the critical point
returns to \(B_n\).  Then the first return to \(B_n\) has a countable
family of pairwise disjoint open puzzle domains

\[
 \{A_{n,i}\}_{i\in I_n}
\tag{4.1}
\]

with integer return times \(q_{n,i}\ge1\) such that:

1. \(\overline{A_{n,i}}\Subset B_n\);
2. \(f^{q_{n,i}}:A_{n,i}\to B_n\) is proper and onto;
3. exactly one domain \(A_{n,0}\) contains \(0\);
4. the central branch has degree two and every other branch is univalent;
5. the exact chronological degree word is

   \[
   \mathbf d_{n,0}=(2,1,\ldots,1),
   \qquad
   \mathbf d_{n,i}=(1,\ldots,1)\quad(i\ne0);
   \tag{4.2}
   \]

6. the domain, return time, component itinerary, parent, and sheet are
   actual dynamical objects, not combinatorial labels;
7. the branch maps extend to the prime-end compactifications, preserving
   cyclic order, and the external marking fixes \(\mathcal G_A\) and
   \(\theta_A\) without assuming local connectivity of \(J(f)\).

Consequently the records (3.8) form an actual analytic return atlas for
the native principal-nest level.

### Proof

We verify each assertion independently.

#### Step 1: the base is nice

Equation (3.5) is the source boundary-avoidance statement for the
principal nest.  Because

\[
 V^{n-1}\subset\operatorname{int}V^{n-2},
\]

an intersection

\[
 f^m(\partial V^{n-1})\cap V^{n-1}\ne\varnothing
\]

would also be an intersection with
\(\operatorname{int}V^{n-2}\), contradicting (3.5).  Hence (3.6) holds.

#### Step 2: actual return domains

Let \(z\in B_n\) have first return time \(q\).  Pull \(V^{n-1}\) back
along

\[
 z,f(z),\ldots,f^q(z)
\tag{4.3}
\]

and take the component containing \(z\).  The Markov property says that
this component is a puzzle piece.  Its interior \(A(z)\) is connected and
open.  For \(1\le k<q\),

\[
 f^k(A(z))\cap B_n=\varnothing.
\tag{4.4}
\]

Indeed, if the two puzzle-piece interiors met, the Markov nesting rule
would force the image component to lie in \(V^{n-1}\), contradicting the
minimality of \(q\).  Thus

\[
 A(z)\subset\mathcal R_q(f,B_n).
\]

Conversely, every component of (3.2) consists of points with the same
first-return time \(q\) and belongs to the corresponding pullback puzzle
piece.  The return domain is therefore an actual connected component, not
merely a word in a transition graph.

Two such open puzzle components are either identical or disjoint by the
Markov property.  This gives (4.1).

#### Step 3: compact containment

Suppose \(\overline{A_{n,i}}\) met \(\partial V^{n-1}\).  Since its
terminal image is \(V^{n-1}\), following the boundary point through the
closed pullback chain would produce some \(m\ge1\) for which

\[
 f^m(\partial V^{n-1})\cap V^{n-1}\ne\varnothing.
\]

This contradicts niceness (3.6).  Therefore

\[
 \overline{A_{n,i}}\Subset B_n.
\tag{4.5}
\]

This is the same boundary argument used in the locked source to obtain
pairwise disjoint closed return pieces and nondegenerate separating
annuli.

#### Step 4: properness and surjectivity

The closed pullback component \(\overline{A_{n,i}}\) maps onto
\(V^{n-1}\) by construction.  Restriction to interiors gives

\[
 f^{q_{n,i}}:A_{n,i}\to B_n.
\]

Because the map extends continuously to the compact closures and maps
boundary to boundary, the interior restriction is proper.  The image is
both open and closed in the connected domain \(B_n\), so it is all of
\(B_n\).

#### Step 5: critical chronology

The unique critical point \(0\) lies in \(B_n\).  If an intermediate
component \(f^k(A_{n,i})\), \(0<k<q_{n,i}\), contained \(0\), it would meet
\(B_n\).  This contradicts (4.4).  Hence the orbit of a return domain can
meet the critical point only at time zero.

If \(0\notin A_{n,i}\), none of the one-step restrictions in the branch
chain is critical.  Every step has degree one, and the branch is
univalent.

If \(0\in A_{n,i}\), the first one-step restriction has degree two and
all later restrictions have degree one.  Since two distinct puzzle-piece
interiors cannot both contain \(0\), there is exactly one such central
domain.  This proves (4.2) and the degree assertions.

#### Step 6: exact metadata

Each \(P_k=f^k(\overline A)\) is the component appearing in the actual
pullback chain, so \(\mathcal P_A\), the parent route, and the selected
sheet are fixed by the dynamics.  The first-return condition (4.4)
supplies the full native obstacle record: every intermediate component
avoids \(B_n\), and the terminal component is \(V^{n-1}\).

No terminal label is used to reconstruct an itinerary.  The full ordered
component list is stored.

#### Step 7: prime ends and phase

The puzzle pieces are topological disks bounded by finitely many
ray/equipotential arcs.  Therefore \(A_{n,i}\) and \(B_n\) are Jordan
domains.  A Riemann map from the disk to either domain extends
homeomorphically to its prime-end compactification.  Conjugating
\(F_A\) by these Riemann maps gives:

- a disk automorphism in the univalent case; or
- a finite Blaschke product of degree two in the central case.

Both extend continuously to the prime-end circle.  Holomorphic orientation
preserves cyclic order; in the degree-two case the boundary action is an
orientation-preserving two-fold covering.

The marked puzzle vertices are specified by external ray angles and the
chosen equipotential.  Their complete inverse images give
\(\mathcal G_A\).  External angle provides a global circular coordinate;
choosing the least marked representative in \([0,1)\) fixes
\(\theta_A\).  This construction concerns the Jordan puzzle boundary, not
all points of \(J(f)\), so it does not assume local connectivity of the
Julia set.

All seven clauses follow. \(\square\)

## 5. What the theorem does and does not import

Theorem 4.1 is an actual analytic result.  In particular, it repairs four
common type errors:

1. the return base is open;
2. every edge is a restriction on an actual connected component;
3. the iterate is an integer first-return time attached to that component;
4. the degree word is derived from the chronological critical encounters.

However, its quantifier is:

> for a specified native principal-nest level.

It is not:

> for every intermediate virtual-Molecule scale.

The latter requires a theorem selecting the level and proving that its
base carries the virtual hull, orbit package, Wave accesses, and
enlargement data.

## 6. Isotopy does not select a return atlas

KKL's native limb localization \(U_I\) is chosen only up to isotopy
relative to the small Julia cycle.  That is adequate for topological
localization statements, but it does not by itself determine a
first-return branch.

### Proposition 6.1 (`ISOTOPY_CLASS_RETURN_UNDERDETERMINATION`)

An isotopy class of Jordan neighborhoods relative to a compact seed does
not determine the first-return time, even for a quadratic polynomial.

### Proof

Take

\[
 f(z)=z^2-1,\qquad K=\{-1\}.
\]

The orbit is

\[
 -1\longmapsto0\longmapsto-1.
\tag{6.1}
\]

Consider the concentric Jordan disks

\[
 Y_s=D(-1,1/4),
 \qquad
 Y_\ell=D(-1,5/4).
\tag{6.2}
\]

Both contain \(K\).  They lie in the same ambient isotopy class relative
to \(K\): the affine isotopy

\[
 h_t(z)
 =
 -1+\bigl(1+4t\bigr)(z+1),
 \qquad 0\le t\le1,
\tag{6.3}
\]

fixes \(-1\), is orientation preserving for every \(t\), starts at the
identity, and maps \(Y_s\) to
\(D(-1,(1+4t)/4)\); at \(t=1\) this is \(Y_\ell\).

For \(Y_s\), the point \(0\) is outside \(\overline{Y_s}\) and the next
iterate is \(-1\), so the first return time of \(-1\) is two.  For
\(Y_\ell\), \(0\in Y_\ell\), so the first return time is one.

Thus even an explicit isotopy relative to the seed preserves neither the
first-return time nor the branch atlas. \(\square\)

### Consequence 6.2

Neither of the following data is sufficient to instantiate
`VIRTUAL_RETURN_BASE_ATLAS`:

- a compact virtual carrier by itself; or
- an isotopy class of Jordan neighborhoods relative to that carrier.

An actual embedded base, or a canonical construction determining one
together with exact transport maps, is required.

## 7. Attempted virtual instantiation

Fix a primitive quadratic-like renormalization encoded by a maximal
primitive copy \(M_1\), with the canonical satellite-copy chain

\[
 M^{(0)}\supset M^{(1)}\supset\cdots\supset M^{(N+1)}
 \supset M_1
\tag{7.1}
\]

from the checked Dudko/KKL discussion.

To apply Theorem 4.1 at a virtual scale \(s\), one must construct a row

\[
 \mathfrak S_s=
 \bigl(
 s,\nu(s),V^{\nu(s)},H_s,\mathscr K_s,\mathscr O_s,
 \mathscr G_s,\mathscr W_s,\mathscr D_s
 \bigr),
\tag{7.2}
\]

where:

- \(\nu(s)\) is the selected puzzle/principal-nest level;
- \(V^{\nu(s)}\) is the actual embedded nice base;
- \(H_s\) is the completed virtual carrier inside it;
- \(\mathscr K_s\) is the complete small-Julia component inventory;
- \(\mathscr O_s\) is the critical-orbit package through the selected
  returns;
- \(\mathscr G_s\) is the complete protected access marking and phase;
- \(\mathscr W_s\) is the obstacle/localization/sheet ledger; and
- \(\mathscr D_s\) is the frozen Wave demand schema.

The source-to-field audit is:

| Field | Published source status |
|---|---|
| chain index \(s\) and copies \(M^{(s)}\) | supplied in parameter/combinatorial form |
| terminal primitive renormalization level | supplied for KKL's terminal Yoccoz puzzle |
| intermediate selector \(\nu(s)\) | absent |
| actual intermediate base \(V^{\nu(s)}\) | absent |
| equality/containment relating the virtual hull to that base | absent |
| exact number of retained critical first returns | absent |
| complete branch-component list | absent |
| access phase and obstacle ledger | absent |
| Wave demand schema | absent |
| enlargement morphisms between rows | absent |

The attempted instantiation therefore stops before Theorem 4.1 can be
applied at an intermediate virtual scale.  The first missing map is

\[
 s\longmapsto \nu(s).
\tag{7.3}
\]

This is sharper than saying merely that “some neighborhood is missing.”
Native nice neighborhoods are available; what is missing is a
source-faithful rule selecting the correct one and proving its
compatibility with the virtual carrier and all later proof uses.

## 8. Exact replacement theorem

### Open problem 8.1 (`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`)

For every actual virtual-Molecule block, construct the rows (7.2) and
prove:

1. **Selection.**  The index \(\nu(s)\) is defined from the block's
   regulated puzzle/renormalization data before any a priori bound,
   stopping outcome, or completed Wave horizon is known.
2. **Niceness.**  The selected embedded base satisfies (3.1), with the
   proof valid uniformly in satellite period and chain length.
3. **Carrier placement.**  The completed virtual carrier and every
   proof-used orbit segment lie in the authorized base/localization.
4. **Return completeness.**  Every first-return component requested by
   the frozen Wave demand schema appears in the atlas of Theorem 4.1, or
   in a proved multi-base extension with an exact analytic transition.
5. **Marking completeness.**  Every proof-used access is present, its
   prime-end phase is fixed, and cyclic order agrees with the virtual
   carrier marking.
6. **Obstacle and sheet compatibility.**  Every filled or ambient
   component is absorbed or separated explicitly, and no two selected
   sheets merge.
7. **Presentation invariance.**  Equivalent descriptions of the same
   satellite-copy chain induce exactly isomorphic selected atlases.
8. **Enlargement naturality.**  Provisional-to-final root enlargement
   supplies the edgewise analytic squares and component bijections
   required by `RETURN_ATLAS_ENLARGEMENT_NATURALITY`.
9. **Uniformity.**  No constant, marking bound, or defect window depends
   on the satellite period, rotation denominator, or virtual-chain length.

If no single base can satisfy Items 3--5, the replacement object must be an
explicit finite or future-faithfully compactified **multi-base return
groupoid**.  Its transition maps must be actual restrictions of iterates;
coarse relabeling of terminal components is not an acceptable substitute.

### Conditional corollary 8.2

The conjunction

\[
 \texttt{NATIVE\_PRINCIPAL\_NEST\_RETURN\_ATLAS}
 \land
 \texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}
\tag{8.1}
\]

supplies the analytic-base portion of
`VIRTUAL_RETURN_BASE_ATLAS`.  The latter still requires the selector's
uniform quantifier over every admissible virtual block and its exact
enlargement maps.  The conditional implication (8.1) does not prove the
open selector.

## 9. Enlargement cross-examination

Suppose a provisional root package \(R\) is enlarged to \(R^+\).
Even if the underlying polynomial \(f\) is unchanged, one must separately
check:

1. whether \(\nu_R(s)=\nu_{R^+}(s)\);
2. whether the selected embedded bases are literally equal or related by
   a declared analytic embedding;
3. whether every old return component maps to one exact new component;
4. whether two old components merge after carrier filling;
5. whether a new component is demanded by a newly exposed access;
6. whether the base access used for \(\theta_A\) survives;
7. whether all old and new obstacle records agree on the common domain.

An injection of old branch words proves persistence only.  No-birth and
no-loss require a bijection on demanded branch-component pairs at every
reached prefix, exactly as in
`RETURN_ATLAS_ENLARGEMENT_NATURALITY`.

The native principal-nest theorem does not settle this audit because its
base is fixed before a virtual carrier enlargement is considered.

## 10. Adversarial audit

1. **Closed puzzle piece used as a holomorphic domain.**  Rejected:
   \(B_n=\operatorname{int}V^{n-1}\) and every branch domain is open.
2. **Return component inferred from an itinerary word.**  Rejected: each
   \(A_{n,i}\) is an actual connected pullback component.
3. **Critical degree placed at an unspecified time.**  Rejected: an
   intermediate critical hit would be an early return because
   \(0\in B_n\); therefore the only possible degree-two step is the
   central branch's first step.
4. **Boundary return ignored.**  Rejected: niceness is derived from the
   stronger principal-nest boundary-avoidance statement.
5. **Local connectivity assumed.**  Rejected: prime ends are attached to
   Jordan puzzle boundaries; no global identification of all Julia
   boundary points with external angles is used.
6. **Isotopy treated as analytic equality.**  Refuted by Proposition 6.1.
7. **Terminal Yoccoz level called a virtual scale.**  Rejected: the missing
   selector (7.3) is recorded explicitly.
8. **Parameter-copy inclusion treated as dynamical-domain inclusion.**
   Rejected: (7.2) requires actual embedded carriers and bases.
9. **The phrase “appropriate number” treated as an integer.**  Rejected:
   the exact retained-return count remains a field of the selector.
10. **One successful block promoted to a uniform theorem.**  Rejected:
    Open Problem 8.1 quantifies over every virtual block and requires
    period-independent bounds.
11. **Old branches persist, hence no new branch exists.**  Rejected:
    persistence is injective; no-birth requires demand-bijectivity.
12. **A native obstacle ledger declared Wave-complete.**  Rejected:
    Theorem 4.1 records only the native first-return obstacles.
13. **Unpublished virtual theorem imported.**  Rejected: the source is
    used only to identify a missing bridge.
14. **Circular selector.**  Forbidden: \(\nu(s)\) may not be chosen using
    the desired width bound, compactness, rigidity, or MLC conclusion.

## 11. Promotion decision

The following statuses are justified:

```text
LYUBICH_PRINCIPAL_RETURN_MAP           imported
NATIVE_PRINCIPAL_NEST_RETURN_ATLAS     proved
ISOTOPY_CLASS_RETURN_UNDERDETERMINATION proved
VIRTUAL_SCALE_TO_PUZZLE_SELECTOR       open
VIRTUAL_RETURN_BASE_ATLAS              open
VIRTUAL_WAVE_DEMAND_SCHEMA             open
VIRTUAL_RETURN_BRANCH_LANGUAGE         open
```

The immediate next proof target is no longer an arbitrary search for a
Jordan disk.  It is:

> construct the selector row (7.2) for the first intermediate member of a
> specified satellite-copy chain, prove carrier placement and niceness,
> and compare its actual branch-component inventory with the first
> syntactic Wave demands.

Failure must identify the first chain index \(s\), the candidate
\(\nu(s)\), the first carrier component or access outside the selected
base, its complete itinerary and sheet, and whether the required repair is
a deeper puzzle level, a multi-base groupoid, a defect-window enlargement,
or a revised localization.

## 12. First direct-decoration selector: proved partial instantiation

The follow-up pass
`virtual_scale_to_puzzle_selector.md` source-locks the Kahn--Lyubich
decoration puzzle and modified principal nest.  At the first satellite
scale visible in the original connected dynamical plane, let \(q\) be the
satellite denominator and let

\[
n=\min\{m\ge1:f^{mq}(0)\in\operatorname{int}Z_j^1
\text{ for some }j\}.
\]

Then the actual selected escape piece is

\[
V_{\rm esc}=f^{-nq}(Z_\kappa^1)|_0=Y^{nq+1},
\qquad
\nu_{\rm dec}(1)=nq+1.
\]

Its first-return map has actual compactly contained puzzle domains, exact
integer iterates, central word \((2,1,\ldots,1)\), univalent lateral
words, component/parent/sheet itineraries, and native branch prime-end
markings.  This proves `FIRST_DECORATION_SCALE_ESCAPE_ATLAS`.

It does not fill the selector row (7.2).  If

\[
f^P:A_0\to B
\]

is the terminal primitive first-return branch and
\(K_i=f^i(K_0)\), then first return gives

\[
K_i\cap B=\varnothing,\qquad 1\le i<P.
\]

Thus the first component excluded from the single critical base is
\(K_1\), with complete component itinerary

\[
K_1\to K_2\to\cdots\to K_{P-1}\to K_0
\]

and full degree word \((2,1,\ldots,1)\).  The actual replacement skeleton
is the multi-base chain

\[
A_0\to A_1\to\cdots\to A_{P-1}\to B,
\qquad A_i=f^i(A_0),
\]

together with \(A_0\hookrightarrow B\).

The direct-decoration source does not construct a continuum in \(J(f)\)
connecting the pairwise-disjoint primitive little Julia sets.  The
follow-up KKL native-tree audit below supplies a terminal native connector
and ideal side, but not a protected analytic access for the partial virtual
carrier.  Moreover the raw separator puzzle
has exactly \(2^n\) vertices and pairwise-disjoint pullbacks \(Q^v\);
there is no uniform bound for the complete raw fan.  A protected analytic
connector and either a bounded proof-complete access selection or a
future-faithful compression of the demanded subset are therefore the
immediate missing fields.  The universal
`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR` remains open.

## 13. Terminal Hubbard-tree anchor refinement

The follow-up pass `terminal_hubbard_anchor.md` supplies the connected
terminal-cycle anchor in KKL's native prime primitive category. The
complete terminal cycle has the native Hubbard tree as a compact connected
forward-invariant carrier, and the unique path from \(K_1\) to \(K_0\)
selects a native ideal attachment side. Finite selected vertex packages
have unique convex subtrees, exact hull transport on an injective branch,
and one-gate enlargement forests.

This does not construct an intermediate virtual return base. The follow-up
type audit `virtual_cantor_package_interface.md` shows that the full Cantor
component family must be realized before a finite terminal-tree trace is
selected. A native ideal side is not yet a protected crosscut chain for the
partial carrier. The source-facing order is therefore

\[
\texttt{VIRTUAL\_CANTOR\_PACKAGE\_REALIZATION}
\longrightarrow
\texttt{VIRTUAL\_PROOF\_USE\_TRACE\_SELECTOR}
\longrightarrow
\texttt{VIRTUAL\_VERTEX\_PACKAGE\_SELECTOR}
\longrightarrow
\texttt{VIRTUAL\_SCALE\_TO\_PUZZLE\_SELECTOR}
\longrightarrow
\texttt{VIRTUAL\_RETURN\_BASE\_ATLAS}.
\]

All five obligations remain open.
