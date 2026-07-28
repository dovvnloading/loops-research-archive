# VAAPC-I Horizon-First Inventory and Source-Adequacy Audit

## 1. Status and purpose

This note addresses only the first clause of the open
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`:

> `VAAPC-I`: after the last future root enlargement, freeze the actual
> virtual-Molecule component inventory and its typed packet assignment
> through the complete Wave horizon.

The conclusions of this pass are deliberately narrower.

- `HORIZON_FIRST_INVENTORY_AUDIT` is proved below.
- `VIRTUAL_WAVE_HORIZON_CERTIFICATE` is isolated as an open analytic input.
- `VAAPC-I` remains open.
- No actual virtual-Molecule collision or counterexample is asserted.
- `VAAPC-C`, `VAAPC-P`, `VAAPC-H`, `VAAPC-U`, UPTCR, and MLC remain open.

The proved result explains exactly why the complete horizon must be defined
before an inventory can be frozen, gives the unique dependency closure once
the horizon data exist, and supplies a necessary-and-sufficient audit for
stability under horizon extension.  It does not manufacture the missing
virtual dynamics.

## 2. Source lock

The source audit uses the following exact files.

1. Dzmitry Dudko, *On the MLC Conjecture and the Renormalization Theory in
   Complex Dynamics*, arXiv:2512.24171v1:

   - locked source:
     `source-lock/Dudko25/main.tex`;
   - SHA-256:
     `FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454`;
   - relevant TeX lines: 875--892;
   - public record:
     <https://arxiv.org/abs/2512.24171>.

2. Jeremy Kahn, Alex Kapiamba, and Mikhail Lyubich, *MLC for
   parabolically bounded primitive renormalization*, arXiv:2606.27272v1:

   - locked source:
     `source-lock/KKL26-v1/waves-with-Misha.tex`;
   - SHA-256:
     `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`;
   - relevant TeX lines: 374--385, 512--557, and 750--765;
   - public record:
     <https://arxiv.org/abs/2606.27272>.

The arXiv submission histories were rechecked on 2026-07-24.  Both records
still have only version 1.  Fresh exact-title, author, and phrase searches
found no public Dudko--Kahn--Lyubich virtual-renormalization manuscript.
KKL line 381 continues to describe that work as forthcoming.

This availability statement is only a source audit.  It is not evidence
that the required theorem is false.

## 3. The typed horizon problem

### 3.1 Horizon skeleton

A **declared virtual Wave horizon skeleton** is a tuple

\[
  \mathcal H
  =
  \left(
    B,N,\sigma,
    \{U_j^-,U_j^+,F_j,d_j\}_{0\leq j<N}
  \right),
\tag{3.1}
\]

where:

1. \(B\) is one actual virtual-Molecule block;
2. \(N<\infty\) is the final proof-use stage;
3. \(\sigma\) is the stopping interface, including the rule that selects it;
4. \(U_j^\pm\) are the authorized source and target localizations;
5. \(F_j:U_j^-\to U_j^+\) is the selected return or
   antirenormalization branch; and
6. \(d_j\) is its declared degree and complete critical word.

The word *declared* is important.  At the inventory stage, (3.1) records
which branches will be audited.  The later clause `VAAPC-H` must still prove
that these maps are defined and univalent on neighborhoods of the completed
packets and transport all markings correctly.

The stopping rule is not interchangeable with a large unspecified integer.
It must identify the last use of every Wave, Wanderers, covering,
quasi-additivity, and width object in the block.

### 3.2 Typed records

For a fixed skeleton \(\mathcal H\), let

\[
  X_{\mathcal H}
  =
  \bigsqcup_{j=0}^{N}X_j
\tag{3.2}
\]

be a disjoint typed universe.  Its allowed record types are:

\[
\begin{split}
 \mathsf{Atom},\quad
 \mathsf{Collar},\quad
 \mathsf{CriticalExclusion},\quad
 \mathsf{AmbientComponent},\\
 \mathsf{LocalizationExclusion},\quad
 \mathsf{ProtectedImpression},\quad
 \mathsf{Transport},\quad
 \mathsf{CurveFamily}.
\end{split}
\tag{3.3}
\]

Every record \(x\in X_{\mathcal H}\) must carry:

\[
  m(x)
  =
  \bigl(
    j(x),C(x),\tau(x),w(x),p(x),s(x),J_{\rm use}(x)
  \bigr),
\tag{3.4}
\]

where \(j(x)\) is the stage, \(C(x)\) is the actual component or geometric
object, \(\tau(x)\) its attachment trace, \(w(x)\) its full return or critical
word, \(p(x)\) its parent route, \(s(x)\) its selected sheet, and
\(J_{\rm use}(x)\subset\{0,\ldots,N\}\) its proof-use interval.

An infinite ambient family is not silently called finite.  Either
\(X_{\mathcal H}\) is proved finite, or the construction must provide a
finite summary together with a theorem that every later proof-use query
factors through that summary.  The latter is a mathematical assertion, not
an implementation convention.

### 3.3 Proof seeds and dependency edges

Let \(\mathscr Q_{\mathcal H}\) be the complete finite proof-use ledger.
For every invocation \(q\in\mathscr Q_{\mathcal H}\), let

\[
  S(q)\subset X_{\mathcal H}
\tag{3.5}
\]

be the typed set of records read directly by that invocation.  Put

\[
  S_{\mathcal H}
  =
  \bigcup_{q\in\mathscr Q_{\mathcal H}}S(q).
\tag{3.6}
\]

The **dependency relation**

\[
  E_{\mathcal H}\subset
  X_{\mathcal H}\times X_{\mathcal H}
\tag{3.7}
\]

is oriented so that \(xE_{\mathcal H}y\) means:

> retaining \(x\) forces retention of \(y\).

Examples include:

- a component forces its attachment trace and parent;
- a transported record forces every intervening source and target record;
- a return word forces every declared critical encounter;
- a proof-used access forces its protected impression and collar;
- a late root shadow forces the earlier component in which that shadow is
  routed; and
- a curve family forces every obstacle and marked end used to define its
  homotopy class.

The edge is entered only with a proof of the asserted forcing relation.
Merely drawing two records adjacent in a ribbon graph does not establish
one.

### 3.4 Dependency closure

For \(A\subset X_{\mathcal H}\), define

\[
\begin{aligned}
  R_{\mathcal H}^0(A)&=A,\\
  R_{\mathcal H}^{r+1}(A)
    &=
    R_{\mathcal H}^{r}(A)
    \cup
    \{y:\exists x\in R_{\mathcal H}^{r}(A),
                  \ xE_{\mathcal H}y\}.
\end{aligned}
\tag{3.8}
\]

The horizon inventory is

\[
  I(\mathcal H)
  =
  \bigcup_{r\geq0}R_{\mathcal H}^{r}(S_{\mathcal H}).
\tag{3.9}
\]

Equation (3.9) is the predecessor/last-use refinement of the minimal
proof-use union in Proposition 3.1 of
`canonical_virtual_interface_carrier.md`.

## 4. Horizon-first inventory theorem

### Theorem 4.1 (horizon-first inventory and extension law)

Assume that \(\mathcal H\), \(X_{\mathcal H}\),
\(\mathscr Q_{\mathcal H}\), \(S(q)\), and \(E_{\mathcal H}\) are all
specified and finite.

1. The iteration (3.8) stabilizes after at most
   \(|X_{\mathcal H}|-|S_{\mathcal H}|\) strict enlargements.
2. \(I(\mathcal H)\) is the unique least subset of
   \(X_{\mathcal H}\) which contains all proof seeds and is closed under
   every declared dependency.
3. Let \(\mathcal H\preceq\mathcal H'\) be a horizon extension for which
   \(X_{\mathcal H}\subset X_{\mathcal H'}\), old proof seeds remain
   seeds, and old dependency edges remain edges.  Then
   \[
      I(\mathcal H)\subset I(\mathcal H').
   \tag{4.1}
   \]
4. The old inventory is stable under this extension,
   \[
      I(\mathcal H')\cap X_{\mathcal H}=I(\mathcal H),
   \tag{4.2}
   \]
   if and only if there is no directed dependency path in
   \(E_{\mathcal H'}\) from a seed in \(S_{\mathcal H'}\) to a record in
   \(X_{\mathcal H}\setminus I(\mathcal H)\).
5. Consequently, an inventory frozen before the stopping interface is
   complete exactly when every admissible later extension satisfies (4.2).

#### Proof

Set \(I_r=R_{\mathcal H}^r(S_{\mathcal H})\).  By construction,

\[
  I_0\subset I_1\subset I_2\subset\cdots\subset X_{\mathcal H}.
\tag{4.3}
\]

If \(I_{r+1}\neq I_r\), at least one new element of the finite set
\(X_{\mathcal H}\setminus I_r\) is added.  There are initially at most
\(|X_{\mathcal H}|-|S_{\mathcal H}|\) such elements.  Hence after at most
that many strict inclusions the sequence is constant.  This proves item 1
and shows that (3.9) is finite.

The set \(I(\mathcal H)\) contains \(S_{\mathcal H}\) because
\(I_0=S_{\mathcal H}\).  If \(x\in I(\mathcal H)\) and
\(xE_{\mathcal H}y\), then \(x\in I_r\) for some \(r\), so
\(y\in I_{r+1}\subset I(\mathcal H)\).  Thus it is dependency-closed.

Now let \(J\subset X_{\mathcal H}\) contain \(S_{\mathcal H}\) and be
dependency-closed.  Inductively, \(I_0\subset J\).  If \(I_r\subset J\),
then every new \(y\in I_{r+1}\setminus I_r\) has
\(xE_{\mathcal H}y\) for some \(x\in I_r\subset J\).  Closure of \(J\)
gives \(y\in J\), hence \(I_{r+1}\subset J\).  Therefore
\(I(\mathcal H)\subset J\).  This proves leastness.  Two least sets contain
one another, so they are equal.  Item 2 follows.

For item 3, every directed path in \(E_{\mathcal H}\) is also a directed
path in \(E_{\mathcal H'}\), and every old seed remains a seed.  Therefore
every record reachable from \(S_{\mathcal H}\) in the old graph is reachable
from \(S_{\mathcal H'}\) in the extended graph.  This is exactly (4.1).

For item 4, suppose first that (4.2) holds.  A directed path from an extended
seed to some \(x\in X_{\mathcal H}\setminus I(\mathcal H)\) would put
\(x\) in \(I(\mathcal H')\cap X_{\mathcal H}\), contradicting (4.2).
Thus no such path exists.

Conversely, assume no such path exists.  Inclusion (4.1) gives
\[
  I(\mathcal H)
  \subset
  I(\mathcal H')\cap X_{\mathcal H}.
\tag{4.4}
\]
If the inclusion were strict, choose
\(x\in(I(\mathcal H')\cap X_{\mathcal H})\setminus I(\mathcal H)\).
By definition of \(I(\mathcal H')\), a directed dependency path joins an
extended seed to \(x\), contrary to the assumption.  Equality (4.2)
follows.

Finally, “freezing before the stopping interface is complete” means precisely
that no permitted continuation can force an omitted old record.  By item 4,
this is equivalent to (4.2) for every admissible continuation.  This proves
item 5. \(\square\)

### Corollary 4.2 (late-use obstruction)

A finite inventory at stage \(N\) cannot be certified as final merely
because it is dependency-closed for the records then known.  One must also
prove that no later proof seed or newly discovered dependency path reaches
an omitted record at a stage at most \(N\).

#### Proof

The asserted later path is exactly the negation of Theorem 4.1(4).
\(\square\)

### Example 4.3 (smallest horizon-instability model)

Let the initial resolved universe be

\[
  X_{\mathcal H}=\{a,b\},\qquad
  S_{\mathcal H}=\{a\},\qquad
  E_{\mathcal H}=\varnothing.
\tag{4.5}
\]

Then \(I(\mathcal H)=\{a\}\).  Extend the horizon by one record \(c\):

\[
  X_{\mathcal H'}=\{a,b,c\},\qquad
  S_{\mathcal H'}=\{a,c\},\qquad
  E_{\mathcal H'}=\{(c,b)\}.
\tag{4.6}
\]

Now

\[
  I(\mathcal H')=\{a,b,c\},
  \qquad
  I(\mathcal H')\cap X_{\mathcal H}=\{a,b\}
  \neq I(\mathcal H).
\tag{4.7}
\]

The record \(b\) can model a stage-zero ambient component whose relevance is
first exposed by a later root shadow \(c\).  The example proves only the
logical need for a final-horizon certificate.  It is not a virtual-Molecule
counterexample.

## 5. Inventory does not determine packet assignment

Let \(\Lambda\) be the set of atom and obstacle labels.  A typed packet
assignment is a function

\[
  \ell:I(\mathcal H)\longrightarrow\Lambda.
\tag{5.1}
\]

It must respect actual attachment, sheet, localization, and source-routing
constraints.  The dependency closure (3.9) does not select \(\ell\).

### Proposition 5.1 (assignment independence)

The unlabelled dependency graph
\((I(\mathcal H),E_{\mathcal H})\) does not logically determine the
source-faithful packet assignment in general.

#### Proof

Take two inventory records \(x,y\) with no dependency edge between them and
two labels \(\lambda_1,\lambda_2\).  Consider two geometric realizations of
this same unlabelled graph.  In the first, the source attachment data declare
\(y\) to be a separated obstacle; in the second, they declare \(y\) to be a
piece attached to the atom represented by \(x\).  These declarations do not
change the unlabelled two-vertex dependency graph, but source faithfulness
requires, respectively, the assignments

\[
\begin{array}{c|cc}
 &x&y\\ \hline
\ell&\lambda_1&\lambda_2\\
\ell'&\lambda_1&\lambda_1
\end{array}
\tag{5.2}
\]

They can lead to different raw packet seeds and hence different filled
packets.  Since the same unlabelled graph occurs in both realizations but
the source-faithful labels differ, the graph alone does not determine the
assignment.  A geometric attachment or routing theorem is required.
\(\square\)

This proposition prevents a second shortcut.  Even after a complete horizon
and inventory are supplied, `VAAPC-I` still needs an actual typed assignment.
The fixed-packet theorem proves what happens *after* that assignment is
fixed; it does not choose the labels.

## 6. Source-adequacy criterion

### Definition 6.1 (source witness)

A record or relation has a **source witness** if it is:

1. explicitly defined in the locked source; or
2. derived from a stated source theorem after every hypothesis of that
   theorem has been verified for the current block.

A phrase of intent, an unproved strategy, or an in-preparation citation is
not a source witness.

### Definition 6.2 (VAAPC-I data adequacy)

A source package is **VAAPC-I data-adequate** for a block \(B\) if it
supplies source witnesses for:

`I0.` the actual block and all renormalization-copy indices;

`I1.` the finite stopping integer \(N\) and stopping interface \(\sigma\);

`I2.` every authorized localization and selected stage branch in (3.1);

`I3.` a finite resolved universe (3.2)--(3.4), or a proved finite faithful
summary of an infinite family;

`I4.` the complete proof-use ledger and direct seed supports (3.5)--(3.6);

`I5.` every dependency edge (3.7), including future root-shadow and
last-use dependencies;

`I6.` the typed packet assignment (5.1); and

`I7.` the finality assertion that every later admissible extension satisfies
(4.2).

### Theorem 6.3 (data-adequacy equivalence)

For a fixed block \(B\), a source-faithful formal `VAAPC-I` record can be
constructed from the audited source package if and only if `I0`--`I7` are
discharged.

This equivalence concerns construction of the frozen input only.  It does
not imply packet disjointness, port exposure, full-packet transport, or
uniform incidence.

#### Proof

Assume `I0`--`I7`.  Items `I0`--`I2` define the skeleton (3.1).
Items `I3`--`I5` define the finite graph, proof seeds, and metadata in
(3.2)--(3.7).  Theorem 4.1 constructs its unique least source-complete
inventory.  Item `I6` labels every inventory record.  Item `I7` proves that
the result is not invalidated by a later root enlargement or proof use.
Thus the resulting record is frozen, actual, typed, source-complete, and
source-witnessed: it is precisely the formal content of `VAAPC-I`.

Conversely, suppose a source-faithful formal `VAAPC-I` record has been
constructed.  Its block identity gives `I0`; its complete finite horizon
gives `I1`; its stage records give `I2`; its actual finite inventory and
metadata give `I3`; completeness through last use gives `I4` and `I5`; its
packet labels give `I6`; and the assertion that it is frozen after the last
future root enlargement gives `I7`.  Hence every listed item is necessary.
\(\square\)

The theorem is an audit equivalence, not an analytic existence theorem.
Its use is to prevent a missing datum from being hidden inside the word
“canonical.”

## 7. Audit of the two public sources

### 7.1 Dudko's virtual-Molecule paragraph

Dudko TeX lines 875--881 define:

- the first primitive quadratic-like renormalization \(f\mapsto f_1\);
- the maximal primitive copy \(\mathcal M_1\);
- the canonical nested satellite copies
  \(\mathcal M^{(0)}\supsetneq\cdots\supsetneq
    \mathcal M^{(\mathbf n+1)}\); and
- the two virtual-Molecule subcases.

This supplies combinatorial information toward `I0`.

Lines 885--888 explicitly state the development of a Virtual Molecule
Near-Degenerate Regime as an interpolation problem.  Line 892 proposes
partially invariant connected hulls of Cantor small Julia sets carrying the
critical orbit for an “appropriate number” of first returns.

No integer, stopping rule, or stopping interface is defined for that number.
Therefore `I1` is the first failed audit item.  Since \(N\) is undefined:

- the stage index set in (3.1) is undefined;
- “through last use” in (3.4) has no endpoint;
- the proof-use ledger in (3.5) cannot be enumerated;
- future root enlargement cannot be certified final; and
- Theorem 4.1 cannot be instantiated.

The same paragraph also does not supply `I2`--`I7`: it gives no stagewise
Jordan localizations, selected branch list, collar/obstacle universe,
virtual Wave proof ledger, dependency graph, packet labels, or
horizon-stability theorem.

The conclusion is exact:

\[
  \text{Dudko's public paragraph}
  \not\Rightarrow
  \text{a source-faithful `VAAPC-I` record}.
\tag{7.1}
\]

Equation (7.1) is a statement about the content of the locked source, not
about what may be provable by new work.

### 7.2 KKL's native carrier

KKL TeX lines 514--543 define, for a primitively renormalizable periodically
repelling pseudo-quadratic-like map:

- the complete cycle of small filled Julia sets \(\mathcal K\);
- the Hubbard tree \(\mathcal T\);
- its vertices, edges, limbs, and pullback tree;
- the induced edge transformation; and
- the rational-lamination model and lift when the full filled Julia set is
  not locally connected.

Lines 550--557 define the native Hubbard arc diagrams.  Lines 750--765 equip
the complement of \(\mathcal T\) with the ideal marking induced by its actual
sides and state the Wave/tame dichotomy in that native setting.

These definitions provide a positive control for the KKL category.  They do
not define the partial virtual-Molecule carrier of Dudko line 892.

### Proposition 7.1 (inventory transport requires a typed bridge)

Let \(I_{\rm KKL}\) be a source-complete inventory in the native KKL
category and \(X_{\rm vir}\) a proposed virtual typed universe.  Transporting
\(I_{\rm KKL}\) to a source-complete virtual inventory requires a map

\[
  \Phi:I_{\rm KKL}\longrightarrow X_{\rm vir}
\tag{7.2}
\]

which:

1. is defined on every proof seed;
2. preserves record types and actual component incidence;
3. carries dependency edges to proved virtual dependency paths;
4. commutes with every selected stage branch;
5. preserves critical words, sheet labels, and parent routes; and
6. preserves the complete ideal/prime-end marking used by the proof.

Without these properties, source completeness of \(I_{\rm KKL}\) does not
imply source completeness of its proposed virtual image.

#### Proof

If item 1 fails, a KKL proof-used record has no virtual representative.
If item 2 fails, the image does not represent the same geometric object or
incidence relation.  If item 3 fails, a forced KKL dependency may be omitted
from the virtual closure.  If item 4 fails, the stage itinerary and last-use
history are not transported.  If item 5 fails, the selected inverse
component or critical encounter can change.  If item 6 fails, a curve family
or Wave interval used in KKL can lose or identify an endpoint.  Each failure
invalidates the assertion that every source proof query has a faithful
virtual answer.  All six conditions are therefore necessary.

If all six hold, the image of every KKL proof seed and every dependency path
is represented faithfully.  This proves only transport of that inventory;
it does not prove that the image exhausts additional virtual proof uses.
\(\square\)

No map satisfying (7.2) is constructed in the checked sources.  KKL TeX
line 381 instead points to the separate virtual-renormalization work as
forthcoming.  Copying KKL's native horizon or ideal marking into the virtual
setting without (7.2) would therefore assume an unproved bridge.

## 8. Exact replacement input

The first open analytic input is recorded as follows.

### `VIRTUAL_WAVE_HORIZON_CERTIFICATE` (open)

For every actual virtual-Molecule block \(B\), construct a finite horizon
skeleton (3.1) such that:

`WH1.` \(N\) and \(\sigma\) are selected by an explicit stopping rule stated
before any desired width or compactness conclusion is used;

`WH2.` every selected stage localization, return branch, degree, and critical
word is defined;

`WH3.` the complete Wave, Wanderers, covering, quasi-additivity, and width
proof ledger through \(\sigma\) is finite and has explicit seed supports;

`WH4.` every future root-shadow or last-use forcing relation is recorded as
a dependency edge;

`WH5.` the resolved record universe is finite, or an explicit finite
future-faithful summary is proved;

`WH6.` extension stability (4.2) holds after the declared final root
enlargement; and

`WH7.` every entry has an actual component and the metadata (3.4).

This certificate does not yet select the packet labels (5.1).  Once it is
proved, the remaining part of `VAAPC-I` is the source-faithful typed
assignment.  Then and only then may the fixed-packet closure audit be used
to test `VAAPC-C` and `VAAPC-P`.

The non-instantiation certificate for the current public source is

\[
\begin{split}
  \mathfrak F_{\rm inv}
  =(&B,\text{Dudko v1 lines }875\text{--}892,\\
    &N_{\rm stop}=\bot,\ \sigma=\bot,\
      \{U_j^\pm,F_j\}=\bot,\
      \mathscr Q=\bot,\
      X_{\mathcal H}=\bot,\
      E_{\mathcal H}=\bot,\
      \ell=\bot).
\end{split}
\tag{8.1}
\]

The ordering in (8.1) matters.  The first undefined datum is the stopping
horizon.  The later symbols are not claimed impossible; they are not
enumerable from the checked paragraph once the stage set itself is
undefined.

## 9. Adversarial cross-examination

| Attack | Verdict | Reason |
|---|---|---|
| Choose a very large \(N\) and call it complete | Rejected | Completeness is the path-exclusion criterion (4.2), not numerical largeness. |
| Freeze the inventory now and add late root shadows later | Rejected | Example 4.3 and Theorem 4.1(4) show that later seeds can force omitted old records. |
| Use the union of everything mentioned in Dudko line 892 | Rejected | The line gives no stopping number, stage maps, collars, obstacles, proof ledger, or labels. |
| Copy the KKL Hubbard-tree inventory | Rejected without (7.2) | KKL's proof uses its native complete primitive carrier and its induced ideal marking. |
| Treat the KKL rational-lamination quotient as the virtual bridge | Rejected | A quotient can identify a proof-used virtual access unless component and prime-end faithfulness are proved. |
| Infer packet labels from the minimal inventory | Rejected | Proposition 5.1 gives two distinct assignments on the same dependency graph. |
| A finite stage count implies a finite component inventory | Rejected | One stage may encounter infinitely many accumulating ambient components; finite resolution or faithful compression is separate. |
| The graph regression passes | Diagnostic only | It checks the finite closure algebra, not existence of actual virtual components or branches. |
| Declare no later proof uses by definition | Rejected | The definition must cover every proof invocation actually used downstream; otherwise it changes the theorem. |
| Let the stopping rule depend on the desired a priori bound | Circular | `WH1` requires the rule before the width/compactness conclusion. |
| Promote `VAAPC-I` after proving Theorem 4.1 | Rejected | The theorem constructs the closure only after the actual horizon graph and labels exist. |

## 10. Promotion decision

Promote:

- `HORIZON_FIRST_INVENTORY_AUDIT`.

Add and keep open:

- `VIRTUAL_WAVE_HORIZON_CERTIFICATE`.

Keep open:

- `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`, including `VAAPC-I`;
- `VIRTUAL_COMMON_FREE_COMPONENT`;
- `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`;
- `VIRTUAL_CANONICAL_INTERFACE_CARRIER`;
- UPTCR-1, UPTCR, and MLC.

The next proof move is now ordered and falsifiable:

1. define the actual virtual stopping rule \(N,\sigma\);
2. list the stage branches and proof calls through that horizon;
3. resolve their component/dependency universe and prove finality (4.2);
4. construct the typed packet assignment;
5. compute the unique completed packets; and
6. prove `VAAPC-C` and `VAAPC-P`, or emit the first actual closure or exposure
   failure certificate.

No later step is allowed to backfill an omitted earlier record without
reopening the horizon audit.
