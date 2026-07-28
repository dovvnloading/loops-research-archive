# First Virtual Scale: Decoration-Escape Selector and the Multi-Base Obstruction

## 1. Result of this pass

This pass attacks the open obligation

```text
VIRTUAL_SCALE_TO_PUZZLE_SELECTOR
```

at the first satellite copy visible in the original dynamical plane.  It
does not solve that obligation uniformly.  It proves three narrower,
source-checkable statements.

1. `FIRST_DECORATION_SCALE_ESCAPE_ATLAS`: a non-principal decoration of a
   directly attached satellite copy canonically selects an actual escape
   puzzle and an actual first-return atlas.  In the notation below,

   \[
   \nu_{\rm dec}(1)=nq+1.
   \]

2. `CRITICAL_BASE_CYCLE_EXCLUSION`: the single critical return base at the
   terminal primitive level cannot contain the complete cycle of terminal
   little Julia sets.  The first excluded component is \(K_1=f(K_0)\), and
   its complete component and degree itinerary are explicit.

3. `DECORATION_FAN_GROWTH`: the raw separating fan in the decoration
   puzzle has exactly \(2^n\) marked vertices in degree two.  Consequently
   the uncompressed access inventory is not uniformly bounded as the
   decoration depth \(n\) varies.

The pass therefore replaces the unsupported idea that one critical puzzle
piece is the whole virtual carrier by an actual finite analytic return
chain

\[
A_0\overset f\longrightarrow A_1\overset f\longrightarrow\cdots
\overset f\longrightarrow A_{P-1}\overset f\longrightarrow B,
\qquad A_0\Subset B,
\]

with one degree-two arrow and all remaining arrows univalent.  This chain
is an analytic skeleton for a future multi-base carrier.  It does not
construct the source-faithful connected subset of \(J(f)\) joining the
little Julia sets, the protected attachment accesses, the complete Wave
demand relation, or their enlargement naturality.  Hence
`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`, VAAPC-I, UPTCR, and MLC remain open.

## 2. Source lock

### 2.1 Kahn--Lyubich decoration puzzle

The source archive for J. Kahn and M. Lyubich, *A priori bounds for some
infinitely renormalizable quadratics. II. Decorations*,
arXiv:math/0609046, is locked as

```text
source-lock/KL08/source.tar
SHA256 DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234

source-lock/KL08/kingdom.tex
SHA256 5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
```

The following exact source ranges are used.

| `kingdom.tex` lines | Imported content |
|---|---|
| 21--54 | the ray/equipotential Yoccoz puzzle associated to a satellite rotation \(p/q\) |
| 68--86 | the candidate immediate satellite return and the satellite copy \(M_{p/q}\) |
| 90--107 | the least escape number \(n\), the escape piece, and the complete escape route \(\bar\kappa\) |
| 109--118 | decoration labels and the puzzle piece \(P=Y^{(n-1)q+1}\), which has \(2^n\) vertices |
| 133--155 | the two univalent \(f^q\)-pullbacks and the pairwise-disjoint family \(Q^v\), one for every vertex \(v\) of \(P\) |
| 181--225 | first/fine children, the modified principal nest, the terminal primitive renormalization, and its little Julia cycle |
| 230--233 | analytic extensions of the modified principal return maps |

This source constructs a decoration-scale puzzle and a terminal primitive
nest.  It does not construct Dudko's connected virtual Julia carrier.

### 2.2 Kahn--Lyubich modified principal nest

The source archive for J. Kahn and M. Lyubich, *Local connectivity of
Julia sets for unicritical polynomials*, arXiv:math/0505194, is locked as

```text
source-lock/KL09/source.tar
SHA256 03221A00D020656BA3470E7F4C985CF613C4F26B1C766BFA87BA7A6D1A7B0C7F

source-lock/KL09/kingdom.tex
SHA256 2DF0B51CB7DC8BB421AD72684F187D3502A7CA8599F10CDF9DAC9A7E844253BA
```

The imported ranges are:

| `kingdom.tex` lines | Imported content |
|---|---|
| 7--54 | generalized polynomial-like maps and actual first-return generalized renormalization |
| 102--175 | central cascades, kingdom renormalization, and first-return restriction to the king |
| 183--223 | the dynasty and modified principal nest; every consecutive map is an actual iterate |
| 227--280 | the first satellite escape piece \(V^0\), its first-return map, compact containment of all return domains, and terminal primitive renormalization |
| 411--427 | analytic enlargements and extended iterate maps |

The published version is J. Kahn and M. Lyubich, *Annals of Mathematics*
170 (2009), 413--426, DOI `10.4007/annals.2009.170.413`.

### 2.3 Virtual source boundary

Dudko `main.tex` lines 875--892 and KKL `waves-with-Misha.tex` lines
299--303 provide the satellite-copy chain and the virtual-Molecule
strategy.  They do not define the connected carrier, the retained-return
number, or the protected access set.  The unpublished
Dudko--Kahn--Lyubich virtual-renormalization paper is not imported.

## 3. First-scale analytic datum

Fix a quadratic polynomial

\[
f=f_c:z\longmapsto z^2+c
\]

with connected filled Julia set and with the ray portrait required by the
Kahn--Lyubich decoration construction.  Fix a directly attached satellite
copy \(M^{(1)}=M_{p/q}\), \(q>1\), and suppose that the primitive copy
\(M_1\) encoding the first primitive renormalization lies in one fixed
non-principal decoration of \(M^{(1)}\).  We work at parameters of \(M_1\)
for which the marked puzzle is defined.  The periodically repelling case
is the source category needed later by KKL.

Let \(\alpha\) be the dividing fixed point and let

\[
\mathcal R_\alpha=\{R_0,\ldots,R_{q-1}\}
\]

be the cyclically ordered external rays landing at \(\alpha\).  They define
the depth-zero pieces \(Y_i^0\), the critical depth-one piece \(Y^1\), and
the off-critical pieces \(Z_j^1\).

Because \(c\notin M^{(1)}\), the candidate immediate satellite
renormalization is disconnected.  The decoration source defines

\[
n
=
\min\{m\ge1:f^{qm}(0)\in\operatorname{int}Z_j^1
\text{ for some }j\}.
\tag{3.1}
\]

The interiors of the \(Z_j^1\) are disjoint.  Thus the terminal index
\(\kappa_n\) in (3.1) is unique.  Pulling the visited components back
along the critical orbit gives the complete escape route

\[
\bar\kappa=(\kappa_1,\ldots,\kappa_n).
\tag{3.2}
\]

Define

\[
V_{\rm esc}
=
f^{-nq}(Z_{\kappa_n}^1)\big|_0
=
Y^{nq+1},
\qquad
B_{\rm esc}=\operatorname{int}V_{\rm esc}.
\tag{3.3}
\]

The selected relative puzzle depth is therefore

\[
\boxed{\nu_{\rm dec}(1)=nq+1.}
\tag{3.4}
\]

This selection uses only the marked ray portrait and the first escape of
the critical orbit.  It does not use an a priori bound, a Wave stopping
outcome, compactness, rigidity, or MLC.

## 4. First decoration-scale escape atlas

### Theorem 4.1 (`FIRST_DECORATION_SCALE_ESCAPE_ATLAS`)

For the datum of Section 3:

1. \(V_{\rm esc}\) is an actual marked Yoccoz puzzle piece selected by
   (3.1)--(3.4).
2. The first-return map to \(B_{\rm esc}\) is defined on actual open
   puzzle domains \(W_i\Subset B_{\rm esc}\), each with an exact integer
   return time \(r_i\):

   \[
   F_i=f^{r_i}|_{W_i}:W_i\longrightarrow B_{\rm esc}.
   \tag{4.1}
   \]

3. Exactly one return domain contains \(0\).  Its chronological degree
   word is

   \[
   (2,1,\ldots,1),
   \tag{4.2}
   \]

   while every noncentral word is

   \[
   (1,\ldots,1).
   \tag{4.3}
   \]

4. Every branch has an exact ordered component itinerary, parent
   pullback, and inverse-sheet record.
5. The ray angles and equipotential corners give a finite prime-end
   marking on each individual branch, and every univalent branch
   preserves its cyclic order.
6. At a fixed marked polynomial, the data are unchanged by a different
   verbal presentation of the same marked decoration: they are recovered
   from the least escape (3.1) and actual pullback components.

This theorem constructs the analytic escape-atlas part of the first
selector row.  It does not assert that its branch marking is the complete
Wave marking.

### Proof

#### Step 1: existence and uniqueness of the selected depth

The satellite copy \(M_{p/q}\) consists of parameters for which the
critical point never escapes the candidate satellite domain.  Our
primitive copy \(M_1\) lies in a decoration outside \(M_{p/q}\).
Consequently an escape in (3.1) occurs.

The positive integers are well ordered, so the least escape number \(n\)
exists.  At time \(nq\), the orbit belongs to exactly one of the disjoint
open pieces \(\operatorname{int}Z_j^1\); hence \(\kappa_n\) is unique.
At every earlier \(q\)-return the Markov partition determines a unique
inverse component containing the critical orbit.  Induction from time
\(nq\) to time zero therefore gives the unique route (3.2) and the actual
pullback (3.3).  This proves Item 1.

#### Step 2: actual return domains

Kahn--Lyubich define \(V_{\rm esc}\) as the first kingdom and define the
full first-return map to it.  Their construction states that every return
domain \(W_i\) is a topological disk compactly contained in
\(V_{\rm esc}\).  Each branch is an actual restriction of one iterate
\(f^{r_i}\), where \(r_i\) is the least positive return time on that
component.  Passing to interiors yields (4.1).

No symbolic word is used to create a domain.  The domain is first selected
as the connected pullback component; its word is then read from the
actual orbit of that component.  This proves Item 2 and the existence
part of Item 4.

#### Step 3: chronological critical degree

The polynomial \(f\) has the unique critical point \(0\), and
\(0\in B_{\rm esc}\).  Let

\[
W_i,\ f(W_i),\ldots,f^{r_i}(W_i)=B_{\rm esc}
\tag{4.4}
\]

be a first-return component chain.  If an intermediate image
\(f^k(W_i)\), \(0<k<r_i\), contained \(0\), then it would meet
\(B_{\rm esc}\), contradicting the definition of \(r_i\).  Thus a
component chain can encounter the critical point only at time zero.

There is exactly one component \(W_0\) containing \(0\), because distinct
first-return domains have disjoint interiors.  On \(W_0\) the first
one-step restriction has degree two and all later steps have degree one.
On every other \(W_i\), every step has degree one.  This proves
(4.2)--(4.3).

#### Step 4: components, parents, and sheets

For each \(0\le k\le r_i\), let \(P_{i,k}\) be the connected puzzle
component containing \(f^k(W_i)\).  The ordered list

\[
(P_{i,0},P_{i,1},\ldots,P_{i,r_i})
\tag{4.5}
\]

is the component itinerary.  The inclusion of each component in the
previous puzzle depth records its parent.  For a noncritical one-step map,
the actual inverse component in (4.5) records the chosen sheet.  For the
central first step, the sheet record is the declared critical double
cover.  These records are determined by (4.4), so Item 4 follows.

#### Step 5: prime ends

Every puzzle component used here is a Jordan disk bounded by finitely
many external-ray and equipotential arcs.  Hence its prime-end
compactification is a closed disk.  A univalent branch between two such
domains extends homeomorphically to their prime-end circles and preserves
cyclic order because it is holomorphic.  The central branch extends as an
orientation-preserving degree-two boundary covering.

The external angles of the landing rays, together with their cyclic
order, provide a finite branch marking.  This proves Item 5.  It does not
prove that later Wave, Wanderers, covering, or quasi-additivity calls need
no additional accesses.

#### Step 6: fixed-map presentation invariance

The tuple

\[
(q,n,\bar\kappa,V_{\rm esc},\{W_i,r_i,P_{i,\bullet}\})
\tag{4.6}
\]

is recovered from the marked ray portrait, the least-event definition
(3.1), and connected pullback components.  Rewriting the same marked
decoration without changing those geometric data leaves (4.6) literally
unchanged.  This is the fixed-map invariance asserted in Item 6.

The theorem deliberately does not claim analytic equality of atlases for
two different polynomials in the same parameter decoration.  Such maps
have a canonical combinatorial correspondence of ray markings, not
literal equality of embedded domains.  \(\square\)

## 5. The terminal primitive return chain

The modified principal nest starting at \(V_{\rm esc}\) terminates at a
primitive quadratic-like map.  Write it as

\[
f^P:A_0\longrightarrow B,
\qquad
A_0\Subset B,
\tag{5.1}
\]

where \(A_0\) is the central first-return domain, \(B\) is its return
base, and \(P>1\) is the primitive renormalization period.  Let

\[
K_0=K(f^P|_{A_0}),
\qquad
K_i=f^i(K_0),\quad 0\le i<P.
\tag{5.2}
\]

Primitivity means that the \(K_i\) are pairwise disjoint.  Set

\[
A_i=f^i(A_0),\qquad 0\le i<P.
\tag{5.3}
\]

Because (5.1) is a first-return branch, the chain

\[
A_0\xrightarrow{f}A_1\xrightarrow{f}\cdots
\xrightarrow{f}A_{P-1}\xrightarrow{f}B
\tag{5.4}
\]

is an actual analytic multi-base return chain.  The inclusion

\[
\eta:A_0\hookrightarrow B
\tag{5.5}
\]

closes it as a covering/inclusion pair.  This is the native precursor of
the carrier pairs sought in VAAPC-I.

## 6. A single critical base cannot carry the cycle

### Proposition 6.1 (`CRITICAL_BASE_CYCLE_EXCLUSION`)

In the setting of Section 5:

\[
K_i\cap B=\varnothing
\qquad(1\le i<P),
\tag{6.1}
\]

where \(B\) denotes the open return base.  Thus no carrier contained in
the one critical base \(B\) can contain the complete terminal little-Julia
cycle.  The first excluded component is

\[
X_1=K_1=f(K_0).
\tag{6.2}
\]

Its complete return itinerary and chronological degree word are

\[
\tau(X_1)
=
(K_1,K_2,\ldots,K_{P-1},K_0),
\tag{6.3}
\]

\[
\mathbf d(K_0\to K_0)
=(2,1,\ldots,1).
\tag{6.4}
\]

### Proof

The integer \(P\) is the first positive return time of the central domain
\(A_0\) to \(B\).  Therefore

\[
f^i(A_0)\cap B=\varnothing
\qquad(1\le i<P).
\tag{6.5}
\]

Since \(K_0\subset A_0\), applying \(f^i\) gives

\[
K_i=f^i(K_0)\subset f^i(A_0)=A_i.
\]

Equation (6.1) follows from (6.5), and \(i=1\) gives the first excluded
component (6.2).

The ordered images in (5.2) give (6.3).  The only critical point of \(f\)
is \(0\), and \(0\in K_0\).  Primitivity and pairwise disjointness imply
\(0\notin K_i\) for \(i>0\).  Equivalently, the first step in the
factorization of the degree-two return (5.1) is the unique quadratic
step, while every later step is univalent.  This proves (6.4).
\(\square\)

### Exact obstruction record

The first-scale single-base attempt therefore has the record

\[
\mathfrak X_1
=
\bigl(
X_1=K_1,\ 
\operatorname{parent}(X_1)=A_1,\ 
\operatorname{sheet}(X_1)=f(A_0),\
\tau(X_1),\
\mathbf d
\bigr).
\tag{6.6}
\]

What (6.6) does **not** contain is an attachment access joining \(K_1\)
to \(K_0\) inside \(J(f)\).  This is not a forgotten label: the
direct-decoration return chain does not construct a connected virtual
carrier, and the finite
pairwise-disjoint union

\[
\bigcup_{i=0}^{P-1}K_i
\tag{6.7}
\]

is disconnected.  A connected carrier must add a continuum in \(J(f)\).
Neither the return chain nor the external marking chooses that continuum
or its first prime-end attachment. At this point in the source order, the
collision coordinate is therefore

\[
\chi_{\rm access}=\bot_{\rm missing\ analytic\ connector},
\tag{6.8}
\]

not \(0\).  It would be circular to replace \(\bot\) by a guessed access
and then declare naturality.

The later pass `terminal_hubbard_anchor.md` legitimately refines this
record in KKL's native terminal category. Its Hubbard tree supplies the
connector and the unique tree path from \(K_1\) to \(K_0\) supplies a
native ideal side. Thus the updated record is

\[
\chi_{\rm ideal}=0,
\qquad
\chi_{\rm protected\ analytic}=\bot.
\tag{6.9}
\]

The remaining bottom symbol records the absence of a protected crosscut
chain for the partial virtual carrier, not the absence of every native
terminal connector.

The required replacement invariant is consequently:

1. retain the actual multi-base chain (5.4)--(5.5);
2. construct a protected regulated connector in \(J(f)\) joining the
   required \(K_i\);
3. record every first attachment access by a prime-end chain;
4. prove that the resulting connector survives all proof-used returns and
   final-root enlargement.

The existing protected-connector theorems in this project explain what a
finite routing certificate would imply. The KKL native tree supplies the
terminal anchor, but neither result selects the source-faithful partial
Dudko virtual package.

## 7. Raw access growth

Let

\[
P_{\rm sep}=Y^{(n-1)q+1}.
\tag{7.1}
\]

The decoration source proves that \(P_{\rm sep}\) has exactly \(2^n\)
vertices in the quadratic case and, for every vertex \(v\), constructs a
pairwise-disjoint univalent pullback

\[
Q^v\subset P_{\rm sep}.
\tag{7.2}
\]

### Proposition 7.1 (`DECORATION_FAN_GROWTH`)

Any raw marking which retains every separator vertex and its pullback
(7.2) has cardinality at least

\[
|\mathscr G_{\rm raw}|\ge 2^n.
\tag{7.3}
\]

In particular, no constant independent of \(n\) bounds this raw marking
over all decoration depths.

### Proof

There are exactly \(2^n\) distinct vertices \(v\) of \(P_{\rm sep}\).
The source constructs one \(Q^v\) for each vertex and proves that the
\(Q^v\) are pairwise disjoint.  Therefore different vertices give
different marked pullback components.  A marking retaining every such
pair contains at least one distinct record per vertex, proving (7.3).
Since \(2^n\to\infty\), no universal raw-cardinality bound exists.
\(\square\)

This is not a refutation of UPTCR.  It proves that UPTCR cannot use the
uncompressed decoration fan as its uniformly bounded response state.
A valid compression must satisfy the already-proved
`WAD_TRANSPORT_QUOTIENT_CRITERION` and `WAD_FUTURE_OBSERVABILITY`; merely
replacing a dyadic address by a coarse label is insufficient.

## 8. The partially filled first selector row

The proved data fill the following fields:

\[
\mathfrak S^{\rm raw}_1
=
\left(
\begin{array}{c}
s=1,\quad \nu_{\rm dec}(1)=nq+1,\quad V_{\rm esc},\\
\bar\kappa,\quad \{W_i,r_i,P_{i,\bullet}\},\\
(A_0,\ldots,A_{P-1},B,\eta),\quad
\{K_0,\ldots,K_{P-1}\},\\
\text{branch prime-end markings},\quad
\{Q^v\}_{v\in\operatorname{Vert}(P_{\rm sep})}
\end{array}
\right).
\tag{8.1}
\]

The full requested row

\[
\mathfrak S_1=
\bigl(
1,\nu(1),V^{\nu(1)},H_1,\mathscr K_1,\mathscr O_1,
\mathscr G_1,\mathscr W_1,\mathscr D_1
\bigr)
\tag{8.2}
\]

still has the following unresolved fields.

| Field | Status after this pass |
|---|---|
| first-scale puzzle depth | **proved:** \(nq+1\) in the direct-decoration source category |
| actual return domains and iterates | **proved** |
| critical and sheet chronology | **proved** |
| terminal little-Julia cycle | **imported and placed in the multi-base chain** |
| one connected \(H_1\subset J(f)\) | **terminal native anchor now exists; the partial Dudko carrier is still open** |
| first attachment access of \(K_1\) | **native ideal side proved; protected analytic access remains undefined** |
| retained critical-orbit stopping number for Dudko's hull | **open** |
| proof-complete Wave marking | **open** |
| obstacle and localization ledger | **open** |
| frozen Wave demand schema | **open** |
| final-root enlargement squares | **open** |
| uniform access compression | **open; raw growth is \(2^n\)** |
| selector at deeper virtual copies \(s\ge2\) | **open** |

## 9. Why the construction does not automatically iterate

The construction above applies at a satellite copy whose decoration is
visible in the original connected dynamical plane.  At a deeper virtual
copy \(M^{(s)}\), \(s\ge2\), the naive instruction “straighten the
previous scale and repeat” is invalid: the parameter lies outside the
previous satellite copy, so the candidate intermediate small Julia set is
disconnected, and the desired virtual renormalization is exactly the
missing bridge.

Thus (3.4) proves the first direct-decoration selector, but it does not
define a recursive scalar

\[
s\longmapsto \nu(s)
\]

for the entire virtual chain.  A legitimate iteration must use the
multi-base analytic chain, protected connectors, and compatible
localizations; it may not assume the virtual renormalization that it is
trying to construct.

The follow-up pass
[`terminal_hubbard_anchor.md`](terminal_hubbard_anchor.md) removes one
ambiguity without weakening this warning. KKL's native terminal Hubbard
tree is an actual connected forward-invariant carrier for the complete
terminal primitive cycle. Its unique path from \(K_1\) to \(K_0\) selects
a native ideal attachment side. Finite selected vertex packages have
unique convex subtrees, exact transport under an injective tree branch, and
one-gate enlargement forests.

This does not define the \(s\ge2\) virtual package. The first missing
recursive map is now the typed vertex-package selector

\[
 (B,s,\text{copy-chain data})\longmapsto\mathscr S_s.
\]

Dudko's public copy chain does not specify which terminal-tree vertices
represent the Cantor components at scale \(s\), the retained return number,
protected sides, obstacles, or proof-use demands. Thus the native terminal
tree supplies the ambient connector, while
`VIRTUAL_VERTEX_PACKAGE_SELECTOR` remains open.

## 10. Adversarial audit

1. **Decoration label treated as an embedded base.** Rejected.  The base
   is the actual pullback component (3.3).
2. **Escape number chosen after seeing a width estimate.** Rejected.
   Equation (3.1) is a least critical-orbit event.
3. **Return word used to invent a domain.** Rejected.  Connected pullback
   components precede their words.
4. **A critical encounter hidden in the middle of a branch.** Rejected.
   It would be an early return because \(0\in B_{\rm esc}\).
5. **Branch prime ends called Wave-complete.** Rejected.  The theorem
   proves only the native puzzle-boundary marking.
6. **A single critical base said to contain the terminal cycle.**
   Refuted by Proposition 6.1.
7. **The union of little Julia sets called connected.** Rejected.
   Primitivity gives a finite pairwise-disjoint family.
8. **An attachment access inferred from an external-angle label.**
   Rejected.  Equation (6.8) records the missing analytic connector.
9. **The \(2^n\)-fan called uniformly finite.** Refuted by Proposition
   7.1.
10. **Every raw fan vertex declared Wave-essential.** Rejected.  The
    source constructs the full separator family, but the open demand
    schema may select a proper subset.  One must prove either a bounded
    proof-complete subset or a faithful compression of the demanded
    subset.
11. **A dyadic-address quotient assumed future-faithful.** Rejected.
    It must pass the WAD transport and future-observability kernel tests.
12. **The direct-decoration construction recursively reused at deeper
    virtual scales.** Rejected by the disconnected-intermediate-scale
    type mismatch.
13. **Local connectivity used to draw regulated arcs.** Rejected.  No
    such arcs are asserted.
14. **The modified nest terminology used as proof of exact return.**
    Rejected.  The exact GPL first-return construction is source-locked
    separately.
15. **One first-scale row promoted to the universal selector.** Rejected.
    The universal quantifier and all fields in (8.2) remain live.

## 11. Promotion decision and next gate

The justified statuses are

```text
KL_DECORATION_ESCAPE_PUZZLE              imported
FIRST_DECORATION_SCALE_ESCAPE_ATLAS      proved
CRITICAL_BASE_CYCLE_EXCLUSION            proved
DECORATION_FAN_GROWTH                    proved
KKL_NATIVE_TERMINAL_HUBBARD_TREE         imported
NATIVE_HUBBARD_SUBTREE_FUNCTORIALITY     proved
TERMINAL_CYCLE_HUBBARD_ANCHOR            proved
VIRTUAL_VERTEX_PACKAGE_SELECTOR          open
VIRTUAL_SCALE_TO_PUZZLE_SELECTOR         open
VIRTUAL_RETURN_BASE_ATLAS                open
VIRTUAL_WAVE_DEMAND_SCHEMA               open
VIRTUAL_RETURN_BRANCH_LANGUAGE           open
VIRTUAL_WAVE_MARKED_CORRESPONDENCE       open
VIRTUAL_WAVE_HORIZON_CERTIFICATE         open
VAAPC-I                                  open
UPTCR                                    open
MLC                                      open
```

The immediate next proof gate is now sharper:

> construct the typed virtual vertex package \(\mathscr S_2\) from the
> first two satellite-copy escape routes, including the least-event return
> cutoff, protected sides, obstacles, and frozen proof-use demands. Then
> take its forced native convex subtree and verify analytic corridor
> transport and protected-access survival—or emit the first component,
> gate, side, itinerary, and collision tuple that prevents it.

The native terminal anchor is not a promotion of the recursive selector.

## 12. Pullback-compactification refinement

The subsequent pass
`virtual_cantor_pullback_compactification.md` constructs the outer rooted
component substrate from the actual univalent \(f^q\)-pullbacks
\(Q_0,Q_1\subset P\).  Finite addresses give actual preterminal Julia
pullbacks, infinite addresses give connected nested puzzle fibers, and
\(f^q\) deletes the first address symbol.  Geometric nesting separately
deletes the last symbol.

This removes the claim in Section 9 that no deeper address-to-component map
has been constructed at all.  What remains undefined is the transfer of the
second satellite portrait to actual bases and iterates on those components
and ends:

```text
VIRTUAL_DISCONNECTED_MARKING_TRANSFER  open
```

The refined failure occurs before a second-scale return base is defined.
It therefore does not promote `VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`.

## 13. Prefix-local selector and downstream trace split

The dependency order must distinguish two different selectors.

`VIRTUAL_PREFIX_LOCAL_SCALE_SELECTOR` is upstream.  For each finite
satellite-copy prefix, it must choose the embedded return base, actual
component branch, sheet, critical chronology, and presentation/enlargement
map using only the realized package and prefix-local dynamics.  It may not
read a completed Wave horizon or a proof-use trace.  This selector is the
input to `VIRTUAL_RETURN_BASE_ATLAS`.

After that atlas supplies the branch language and marked correspondence,
`VIRTUAL_WAVE_HORIZON_CERTIFICATE` freezes the complete finite stopping
horizon.  Only then may `VIRTUAL_PROOF_USE_TRACE_SELECTOR` compress the
actual component universe, and only after that may
`VIRTUAL_VERTEX_PACKAGE_SELECTOR` and the final
`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR` assert proof-use-complete placement.

Thus the corrected order is

\[
\begin{split}
&\text{realized virtual package}
\longrightarrow
\text{prefix-local scale selector}
\longrightarrow
\text{return atlas and branch language}\\
&\longrightarrow
\text{marked correspondence}
\longrightarrow
\text{frozen Wave horizon}
\longrightarrow
\text{proof-use trace}
\longrightarrow
\text{final proof-complete selector}.
\end{split}
\]

No arrow in this chain points from the final trace back into the return
atlas.  Both selector obligations remain open.
