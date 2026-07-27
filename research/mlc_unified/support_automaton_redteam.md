# Red-team audit: support automata, entropy/shear, and corridor certificates

## 1. Scope and verdict

This audit independently checked:

- `corridor_support_automaton.md`;
- `corridor_entropy_shear_dichotomy.md`;
- `dynamical_corridor_certificate.md`;
- the corresponding entries in `proof_obligations.json`;
- the counter-aware ledger correction in `virtual_language_memory.md` where it
  changes the scope of support pumping.

No MLC conclusion is asserted here.

The finite Boolean-support pumping argument is sound **for a genuinely exact finite
automaton with no omitted endpoint state**.  The delay-robust primitivity witness is
also sound in the nondegenerate setting in which it is used.  Several surrounding
claims are nevertheless false as presently quantified, and the transfer convention
is not coherent across the files.  In particular:

1. transient zero strongly connected components are currently misclassified as
   branch-recurrent entropy;
2. the row-outgoing convention conflicts with the reverse chronological product and
   permutation-gauge formula;
3. spectral radius and branch recurrence of an open layer-to-layer transfer are not
   invariant under independent endpoint relabeling;
4. the proposed trichotomy omits nilpotent/extinction transfers unless its shear
   branch is explicitly enlarged;
5. cloning does not preserve strong connectivity for the degenerate one-vertex
   edgeless base covered by the present quantifiers;
6. the new counter-safe “only if” ledger claim is itself too strong.

These are not numerical objections.  Explicit matrices and graphs below falsify the
literal statements.

Severity in this report means:

- **fatal**: an explicit counterexample falsifies a proved statement, or destroys the
  stated dynamical interpretation of a proved algebraic statement;
- **material**: the conclusion may be repairable, but an essential hypothesis or
  proof is missing;
- **minor**: terminology or presentation can cause an incorrect downstream use.

## 2. Fatal findings

### F1. Zero singleton components invalidate the branch-entropy corollary

`corridor_support_automaton.md` calls a support matrix branch-recurrent when one of
its strongly connected diagonal components “is not a single directed cycle.”
Under the standard SCC convention, a singleton vertex with no self-loop is an SCC.
It is not a directed cycle.

Take
\[
 P=
 \begin{pmatrix}
 1&0\\
 0&0
 \end{pmatrix}.
\tag{2.1}
\]
The support has two singleton SCCs.  The second has no loop and hence is not a
directed cycle.  Thus \(P\) is branch-recurrent by the literal definition, whereas
\[
 \rho(P)=1
 <
 2^{1/4}.
\tag{2.2}
\]
This directly contradicts Corollary 4.2 and the second assertion of the proved ledger
node `BOUNDED_BRANCH_SUPPORT_WITNESS`.

The scalar matrix
\[
 B=[0]
\tag{2.3}
\]
also exposes the boundary error in
`IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY`.  In the standard matrix-theoretic convention
\([0]\) is irreducible as a \(1\times1\) matrix, but it is neither a cycle
permutation nor does it have spectral radius at least \(2\).  If the manuscript
intends “irreducible” to require a positive-length return, that nonstandard
qualification must be stated.

**Required repair.** Define an entropy-producing component to be a **cyclic SCC**
which is not a simple directed cycle: it must contain at least one positive-length
closed walk.  State the irreducible entropy theorem for a nonzero irreducible matrix,
or for an irreducible component containing a directed cycle.  Zero singleton blocks
must be classified as transient, not branching.  Until both changes are made,
`IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY` and
`BOUNDED_BRANCH_SUPPORT_WITNESS` are not proved as written.

### F2. Product order is inconsistent with the declared edge orientation

`corridor_entropy_shear_dichotomy.md` declares that row \(i\) lists edges outgoing
from \(i\).  Under this convention, a chronological row-vector transfer along
\(A,B,C\) is \(ABC\).  `corridor_support_automaton.md`, however, defines the same
chronological word to have product \(CBA\).

This is not harmless for a nonstationary word.  Let
\[
 A=
 \begin{pmatrix}0&0\\1&1\end{pmatrix},\qquad
 B=
 \begin{pmatrix}0&0\\0&1\end{pmatrix},\qquad
 C=
 \begin{pmatrix}0&1\\0&1\end{pmatrix}.
\tag{2.4}
\]
Then
\[
 ABC=
 \begin{pmatrix}0&0\\0&1\end{pmatrix},
 \qquad
 \rho(ABC)=1,
\tag{2.5}
\]
while
\[
 CBA=
 \begin{pmatrix}1&1\\1&1\end{pmatrix},
 \qquad
 \rho(CBA)=2.
\tag{2.6}
\]
The reverse product therefore manufactures a branch-recurrent positive-entropy
matrix from a chronological row-outgoing transfer having only one recurrent loop.

The same mismatch appears in Lemma 2.1 of
`corridor_entropy_shear_dichotomy.md`.  Its formula
\[
 Q_{k+1}^{-1}B_kQ_k
\tag{2.7}
\]
is a column-vector/source-column formula, not the natural row-outgoing adjacency
relabeling formula.  The conclusion that a permutation cocycle can be gauged to the
identity is true, but the proof and the declared convention do not describe the same
object.

**Required repair.** Lock one convention globally before any WAD or Value comparison:

- with the project's source-column count convention, use
  \(T_{\mathrm{target},\mathrm{source}}\), chronological products
  \(B_m\cdots B_1\), and (2.7), while changing every “row outgoing” walk proof to
  “column outgoing” or transposing it;
- with row-outgoing adjacency, use chronological products
  \(B_1\cdots B_m\) and the corresponding domain/codomain relabeling formula.

Left/right Perron weights and WAD incidence make this more than a typographical
choice.  No source-identity claim is checkable while both conventions coexist.

### F3. Entropy of an open layered transfer is not endpoint-gauge invariant

A matrix from \(E_0\) to a distinct set \(E_1\) is a bipartite transfer, not an
endomorphism until an identification \(E_1\simeq E_0\) is fixed.  Independent
relabeling of the target multiplies the matrix on only one side, not by similarity,
and can change its spectral radius and Frobenius type.

For example, let
\[
 S=
 \begin{pmatrix}1&1\\0&1\end{pmatrix},
 \qquad
 J=
 \begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{2.8}
\]
In a row-outgoing convention, merely swapping the target labels replaces \(S\) by
\[
 SJ=
 \begin{pmatrix}1&1\\1&0\end{pmatrix}.
\tag{2.9}
\]
Yet
\[
 \rho(S)=1,
 \qquad
 \rho(SJ)=\frac{1+\sqrt5}{2}.
\tag{2.10}
\]
The first support is reducible unipotent shear; the second is irreducible and
branching.  In the column convention, the analogous example is \(JS\), with the same
Perron root.  Both matrices represent the same unlabeled one-step bipartite
transition with a different output frame.

Consequently, a branch-recurrent accepted **open word** is not intrinsically a
positive-entropy dynamical block.  It becomes meaningful only if:

1. the word is a closed return to the same source state and the state carries the
   same endpoint frame; or
2. a canonical source-licensed endpoint identification is part of the data.

The pumping theorem itself is algebraically valid for its declared matrices.
However, Theorem 4.1 cannot be used as an automaton-language entropy witness merely
because a bounded accepted word has branch-recurrent support.  A one-way accepted
word need not be repeatable, and its square matrix may be an artifact of endpoint
labeling.

**Required repair.** Add a frame/holonomy component to the automaton state, and
restrict entropy certification to closed, repeatable, source-licensed return words.
Alternatively, formulate nonstationary growth using a gauge-invariant singular/cone
quantity and separately prove its connection to KKL Value.  The ledger node
`BOUNDED_BRANCH_SUPPORT_WITNESS` may remain as a bare matrix lemma after F1 is fixed,
but it must not be described as dynamical entropy without this closure hypothesis.

### F4. The counter-safe “only if” ledger claim is false

The counter correction is necessary, but Lemma 5.1 of
`virtual_language_memory.md` and ledger node `COUNTER_SAFE_PUMPING` say that deleting
a nonzero-increment loop preserves an endpoint condition **only if** the endpoint
predicate is invariant under that increment.

For one counter, take loop increment \(\Delta=1\) and endpoint predicate
\[
 \Phi(\nu)\iff \nu\in\{0,1\}.
\tag{2.11}
\]
Starting at \(\nu=0\), the word with the loop ends at \(1\) and the deleted word ends
at \(0\).  Both satisfy \(\Phi\), so deletion preserves the endpoint condition for
this path, although \(\Phi\) is not invariant under \(+1\) globally.

The exact pathwise criterion is
\[
 \Phi(\nu+\eta)=\Phi(\nu+\Delta+\eta)
\tag{2.12}
\]
for the relevant reachable continuation \(\eta\).  Invariance under \(\Delta\) on
the entire relevant reachable set is a clean **uniform sufficient** condition, not a
necessary condition without further quantifiers.

**Required repair.** Replace “only if” by the exact fiber condition (2.12), followed
by zero increment or reachable-set invariance as convenient sufficient hypotheses.
The proved ledger statement must be changed accordingly.

## 3. Material findings

### M1. The trichotomy omits nilpotent/extinction transfers

The announced alternatives are translation, positive entropy, and spectral-radius-one
shear.  But
\[
 N=
 \begin{pmatrix}0&1\\0&0\end{pmatrix}
\tag{3.1}
\]
has \(\rho(N)=0\), is not a permutation, and is not covered by Theorem 4.1, whose
hypothesis is \(\rho(B)=1\).  It is a purely transient/extinction transfer.

This may be harmless in a recurrent dynamical core, but recurrence has not been
stated or proved for every grouped virtual transfer.  As written, the “refined
trichotomy” is not exhaustive.

**Repair.** Either prove that every complete source core has a recurrent component
with spectral radius at least one, or enlarge the zero-entropy branch to all
\(\rho(B)\le1\), separating nilpotent transient blocks from unipotent shear.  The
Frobenius conclusion extends naturally: diagonal blocks are cycle blocks or zero,
with the all-zero case eventually nilpotent.

### M2. Permutation layers prove only an identity interior cocycle

Even after correcting the matrix convention, permutation matrices establish only
that the layer-to-layer interior edges can be relabeled as identities.  They do not
prove the full exact-corridor conditions in `corridor_clone_criterion.md`:

- no side edge may enter or leave an interior cell;
- entry and exit multiplicities must be the declared ones;
- the quotient gate must be a cross section;
- critical/access/WAD incidences must be complete.

For an explicit graph, take singleton cells \(E_0,E_1,E_2\) with the identity chain
\[
 E_0\longrightarrow E_1\longrightarrow E_2
\]
and add an edge from \(E_1\) to an active vertex \(x\).  Both layer matrices are
\([1]\), but this is not an exact translation corridor because a non-chain edge is
incident to the interior cell.  Alternatively, add a disjoint active directed cycle;
the quotient gate is then not a cross section despite all corridor layer matrices
being permutations.

Thus the proved nodes `PERMUTATION_COCYCLE_GAUGE` and
`DEFECT_RUN_DECOMPOSITION` should say **identity interior runs**, not exact clone
corridors, unless all `FC2`--`FC4` hypotheses are added.

### M3. Clone strong connectivity has a degenerate counterexample

Let \(G_0\) consist of one vertex \(e\), no edges, and \(E=\{e\}\).  Under the
standard convention allowing a length-zero path, \(G_0\) is strongly connected.
It also satisfies the cross-section condition and has no \(E\)-to-\(E\) edge.

For \(n\ge1\), its clone is the directed chain
\[
 e_0\longrightarrow e_1\longrightarrow\cdots\longrightarrow e_n,
\tag{3.2}
\]
which is not strongly connected.  Hence `CLONE_STRONG_CONNECTIVITY` is false under
its current quantifiers.

The robust-primitivity theorem is not damaged: its two positive closed-walk witnesses
exclude this example.  The certificate also includes those witnesses.  The lemma and
ledger node should nevertheless require a nontrivial strongly connected base, or
explicitly require every \(e\in E\) to lie on a positive-length closed walk.

### M4. The Frobenius polynomial-growth proof skips the transient-block argument

The conclusion of Theorem 4.1 is standard and appears correct after the zero case is
included, but the displayed binomial proof handles only the principal recurrent
part.  On the full Frobenius matrix, after the common cycle power the diagonal is a
mixture of identity blocks and zero blocks.  It is not globally \(I+N\), and the
diagonal part does not generally commute with the strict block-upper part.

For instance,
\[
 \begin{pmatrix}1&1\\0&0\end{pmatrix}
\tag{3.3}
\]
already has one identity and one zero diagonal block.  The sentence that transient
blocks “only add finitely many feed-forward stages” is plausible, but is not a proof
of the claimed degree bound.

**Repair.** Give a path-counting proof on the condensation DAG: a walk chooses at
most \(s-1\) strict component transitions, while residence in each cycle block is
periodic; summing the possible residence times gives a polynomial of degree at most
\(s-1\).  A Jordan-form proof is also possible, but the integral graph proof better
preserves the intended source interpretation.

### M5. Support-neutral loops are contextual and need not form a finite list

Theorem 3.1 correctly records a deleted word \(\beta\) satisfying
\[
 \operatorname{supp}P(\alpha\beta)
 =
 \operatorname{supp}P(\alpha).
\tag{3.4}
\]
This is neutrality **on the particular prefix support**.  It does not assert
\(\operatorname{supp}P(\beta)=I\), nor does it permit two recorded loops to be
reordered or applied on another support face.

Moreover, the theorem bounds only the Boolean skeleton.  It does not bound:

- the number of inserted loops;
- the length of an inserted loop;
- the numerical entries of its product;
- the number of changing Frobenius frames across nested loops.

For a full prefix support, almost any matrix with no zero row is support-neutral, so
the reduction may retain essentially the entire numerical problem.  This is not a
counterexample to pumping, but it prevents the statement “finite pumping reduces the
nonstationary problem” from being read as a finite classification theorem.

**Repair.** Say “prefix-face-neutral loop occurrence,” preserve the nesting order,
and make the open realization theorem prove a uniform classification of the
resulting loop semigroup rather than of individual letters.

### M6. Exact pumping does not survive omitted time/future state

Within a true automaton, equality of the automaton state makes the splice accepted.
For a dynamical language with an external exact return time, critical itinerary, or
WAD future, equality of finite control and Boolean support is insufficient.
`virtual_language_memory.md` correctly identifies this general issue.

The current evidence link for `H2_VIRTUAL_SUPPORT_AUTOMATON` points to Section 6 of
`corridor_support_automaton.md`, whose statement is still an unqualified finite
automaton theorem.  The ledger statement has meanwhile been changed to say “after
all declared unbounded counters are factored out” and “counter-safe.”  The anchor
exists, so `audit_proof.py` cannot detect that the evidence text and ledger statement
are semantically different.

**Repair.** Update the support-automaton manuscript itself to:

1. take the counter-follower theorem as an explicit hypothesis;
2. pump only zero-counter or fiber-safe loop occurrences;
3. retain nonzero increments in the exact weighted clone/sectorial equation.

### M7. The finite-state corridor certificate compresses source hypotheses

The graph portion of Theorem 4.1 in `dynamical_corridor_certificate.md` is a valid
conditional implication after M3 is patched.  Its Value conclusion is stronger than
the graph certificate alone: it also needs the full KKL periodically repelling
\(\psi\)-ql hypotheses, the typed raw incidence \(B=N^{\mathsf T}\) with the KKL
left/right Value roles, the associated WAD pullback valuation, an independently
verified clone recurrence, and the complete-block exponent.

The theorem text adds an “if the source-licensed Value hypotheses hold” clause.  The
proved ledger node `FINITE_STATE_CORRIDOR_CERTIFICATE` compresses this to
“source-faithful finite-horizon WAD incidence,” which is not by itself the full KKL
hypothesis set.

**Repair.** Keep the graph implication proved, but state the Value conclusion as a
separate conditional corollary depending explicitly on `KKL_VALUE_CONTRACTION` and
the source \(\psi\)-ql hypotheses.  No response or additive error has been controlled
by the certificate.

## 4. Minor findings

### m1. “Directed path” must mean walk

The cross-section/DAG equivalence is correct when directed paths may repeat vertices,
that is, when “path” means a directed walk in the usual matrix-power sense.  If
“path” means a simple path, every finite graph has a uniform path-length bound and
the equivalence is false.  KKL's use must be copied with an explicit convention.

### m2. The restored loop representation is nested, not commutative

Restoring deleted factors in reverse deletion order reconstructs the word.  The
manuscript should explicitly call this a nested insertion history.  A flat multiset
of loops would lose the prefix supports on which (3.4) was proved.

### m3. Encoding corruption appears in source-critical prose

`dynamical_corridor_certificate.md` contains
“eigenweights—not,” and several files contain similarly corrupted quotation marks.
This is not mathematical, but it makes exact source-lock language harder to audit.

## 5. Claims that survived this audit

Subject to the scopes above, the following arguments survived direct reconstruction:

1. `BOOLEAN_SUPPORT_FUNCTOR`;
2. `SUPPORT_AUTOMATON_PUMPING` for an exact finite automaton, with contextual loop
   restoration;
3. the bounded shortest-witness part of `BOUNDED_BRANCH_SUPPORT_WITNESS` after the
   definition of branch recurrence is corrected;
4. the positive recurrent part of the irreducible integer entropy gap;
5. `ZERO_ENTROPY_SHEAR_NO_GO`;
6. `CROSS_SECTION_DAG_EQUIVALENCE` with “path” defined as walk;
7. `ROBUST_CLONE_PRIMITIVITY`;
8. `PRIMITIVE_BASE_CLONE_NO_GO`;
9. the graph-theoretic part of `FINITE_STATE_CORRIDOR_CERTIFICATE`, conditional on
   all `FC` hypotheses and with the degenerate base excluded.

The finite-support skeleton theorem therefore remains useful.  What it does **not**
yet provide is a gauge-invariant, counter-safe, source-licensed entropy window.

## 6. Required ledger actions

Before these nodes are used as proved dependencies:

1. patch or demote `IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY`;
2. patch or demote `BOUNDED_BRANCH_SUPPORT_WITNESS`;
3. qualify `CLONE_STRONG_CONNECTIVITY`;
4. narrow `PERMUTATION_COCYCLE_GAUGE` and `DEFECT_RUN_DECOMPOSITION` to interior
   cocycles;
5. correct `COUNTER_SAFE_PUMPING` from a false necessary condition to the exact fiber
   condition;
6. make the product/orientation convention a source-locked definition used by every
   transfer, eigenvector, and WAD incidence;
7. add the endpoint-frame/closed-return hypothesis before treating support spectral
   radius as entropy;
8. update the evidence text for `H2_VIRTUAL_SUPPORT_AUTOMATON` to match its
   counter-factored ledger statement;
9. separate the graph certificate from the conditional KKL Value corollary.

## 7. Concise remediation map

The status labels below have the following exact meaning:

- **repair as proved**: the counterexample is defeated by weakening or qualifying the
  statement, and the proof already present (possibly with the indicated elementary
  completion) proves that weakest version; this is not a new MLC obligation;
- **demote until repaired**: the current literal ledger statement is false or its
  proof is incomplete and therefore cannot remain `proved` in an unedited snapshot;
- **remain open**: the correction belongs to an already open dynamical realization
  theorem and cannot be promoted by the finite matrix argument.

### F1 — zero SCCs

- **Affected text:** `corridor_entropy_shear_dichotomy.md`, Section 3, Theorem 3.1;
  `corridor_support_automaton.md`, Section 4, the definition preceding Theorem 4.1
  and Corollary 4.2.
- **Direct ledger IDs:** `IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY`,
  `BOUNDED_BRANCH_SUPPORT_WITNESS`.
- **Downstream open IDs:** `H2_VIRTUAL_SUPPORT_AUTOMATON`,
  `H2_VIRTUAL_TRANSFER_TRICHOTOMY`, `H2_ENTROPY_DICHOTOMY`.
- **Weakest surviving statement:** a **nonzero** irreducible nonnegative integer
  matrix is a simple cycle permutation or has
  \(\rho\ge2^{1/d}\). A support component is entropy-branching only when it is a
  cyclic SCC, containing a positive-length closed walk, and is not a simple directed
  cycle.  With that definition, the shortest-witness bound and Perron gap survive.
- **Ledger action:** both direct IDs must be **demoted until repaired**, then may be
  restored as `proved` with the qualified statements.  The three `H2` nodes remain
  open.

### F2 — orientation and product order

- **Affected text:** `corridor_support_automaton.md`, Section 2, equation (2.1);
  `corridor_entropy_shear_dichotomy.md`, Section 2, Lemma 2.1, and Section 3's
  row-outgoing convention; `dynamical_corridor_certificate.md`, `FC6`.
- **Direct ledger IDs:** `PERMUTATION_COCYCLE_GAUGE`,
  `BOOLEAN_SUPPORT_FUNCTOR`, `SUPPORT_AUTOMATON_PUMPING`,
  `FINITE_STATE_CORRIDOR_CERTIFICATE`.
- **Downstream open IDs:** `H2_VIRTUAL_SUPPORT_AUTOMATON`,
  `H2_VIRTUAL_TRANSFER_TRICHOTOMY`, `H2_VIRTUAL_CLONE_REALIZATION`.
- **Weakest surviving statement:** after one global convention is fixed, support is
  functorial and the pumping proof holds for products in that convention.
  Permutation cocycles can be gauged to identity using the relabeling formula
  compatible with that convention.  No WAD/core source identity follows until the
  same convention is used in `FC6`.
- **Ledger action:** `BOOLEAN_SUPPORT_FUNCTOR` and
  `SUPPORT_AUTOMATON_PUMPING` may **remain proved** as abstract algebra once their
  convention is stated.  `PERMUTATION_COCYCLE_GAUGE` must be **demoted until its
  formula is repaired**, then can be restored as `proved`.
  `FINITE_STATE_CORRIDOR_CERTIFICATE` can be repaired as a conditional proved theorem
  by adding the convention to its antecedent.  All three `H2` nodes remain open.

### F3 — endpoint gauge and open words

- **Affected text:** `corridor_support_automaton.md`, Section 4, Corollary 4.2 and
  Section 6; `corridor_entropy_shear_dichotomy.md`, Section 3, Corollary 3.2 and
  Section 6; `dynamical_corridor_certificate.md`, `FC6` and Theorem 4.1.
- **Direct ledger IDs:** `BOUNDED_BRANCH_SUPPORT_WITNESS`,
  `FINITE_STATE_CORRIDOR_CERTIFICATE`.
- **Downstream open IDs:** `H2_VIRTUAL_SUPPORT_AUTOMATON`,
  `H2_VIRTUAL_TRANSFER_TRICHOTOMY`, `H2_VIRTUAL_CLONE_REALIZATION`,
  `H2_VIRTUAL_CORRIDOR_GRAPH_REALIZATION`.
- **Weakest surviving statement:** after F1, a branch-recurrent square matrix has the
  stated Perron gap.  That gap is dynamical entropy only for a repeatable closed word
  returning to the same framed automaton state, or for a separately proved canonical
  source endomorphism.  An open word gives no gauge-invariant entropy conclusion.
- **Ledger action:** repair `BOUNDED_BRANCH_SUPPORT_WITNESS` as a **bare matrix
  lemma** and retain it as `proved`; do not let that node discharge framed source
  realization.  Add frame/holonomy and closed-return identity to the four open
  `H2` nodes, which remain open.  `FINITE_STATE_CORRIDOR_CERTIFICATE` can remain
  conditionally proved only after its source-identity antecedent explicitly includes
  the endpoint frame.

### F4 — counter-safe necessity

- **Affected text:** `virtual_language_memory.md`, Section 5, Lemma 5.1 and
  Corollary 5.2; the counter qualification imported into
  `corridor_support_automaton.md`, Section 6.
- **Direct ledger ID:** `COUNTER_SAFE_PUMPING`.
- **Downstream open IDs:** `H2_UNIFORM_COUNTER_FOLLOWER`,
  `H2_VIRTUAL_SUPPORT_AUTOMATON`.
- **Weakest surviving statement:** deletion of a loop of increment \(\Delta\) for a
  fixed prefix and continuation is endpoint-safe exactly when
  \[
    \Phi(\nu+\eta)=\Phi(\nu+\Delta+\eta).
  \]
  Zero increment and invariance on the relevant reachable fiber are uniform
  sufficient conditions.
- **Ledger action:** `COUNTER_SAFE_PUMPING` must be **demoted until repaired**, then
  may be restored as `proved` with the fiber criterion.  Both `H2` nodes remain open.

### M1 — missing nilpotent/extinction branch

- **Affected text:** `corridor_entropy_shear_dichotomy.md`, Sections 1, 4, and 6.
- **Direct ledger ID:** `ZERO_ENTROPY_SHEAR_NORMAL_FORM`.
- **Downstream open IDs:** `H2_VIRTUAL_TRANSFER_TRICHOTOMY`,
  `H2_ENTROPY_DICHOTOMY`.
- **Weakest surviving statement:** for a nonnegative integer matrix with
  \(\rho\le1\), every cyclic diagonal SCC is a simple cycle and every other diagonal
  block is zero; the \(\rho=0\) case is nilpotent extinction, while the
  \(\rho=1\) case may have polynomial feed-forward shear.
- **Ledger action:** extend `ZERO_ENTROPY_SHEAR_NORMAL_FORM` and complete its proof as
  in M4; it can then be **repaired as proved**.  The two `H2` nodes must remain open
  and must either include extinction or prove recurrent nonextinction.

### M2 — permutation interiors are not full corridors

- **Affected text:** `corridor_entropy_shear_dichotomy.md`, Section 2, Lemma 2.1 and
  Section 5, Lemma 5.1; compare `corridor_clone_criterion.md`, Definition 3.1 and
  `dynamical_corridor_certificate.md`, `FC2`--`FC4`.
- **Direct ledger IDs:** `PERMUTATION_COCYCLE_GAUGE`,
  `DEFECT_RUN_DECOMPOSITION`.
- **Unaffected comparison IDs:** `EXACT_CORRIDOR_CLONE_CRITERION`,
  `FINITE_STATE_CORRIDOR_CERTIFICATE`.
- **Weakest surviving statement:** permutation layer transfers gauge to an identity
  **interior cocycle**.  Removing \(q\) non-permutation layers leaves at most
  \(q+1\) identity interior runs.  Neither statement supplies side-edge exclusion,
  endpoint control, or the quotient cross-section property.
- **Ledger action:** both direct IDs must be **demoted until narrowed**, then can be
  restored as `proved`.  The two comparison IDs need no demotion because their
  hypotheses already require the missing full-graph data.

### M3 — degenerate clone connectivity

- **Affected text:** `dynamical_corridor_certificate.md`, Section 3, Lemma 3.1.
- **Direct ledger ID:** `CLONE_STRONG_CONNECTIVITY`.
- **Dependent proved ID:** `ROBUST_CLONE_PRIMITIVITY`.
- **Weakest surviving statement:** cloning preserves strong connectivity when the
  base is strongly connected and nontrivial; equivalently for this purpose, every
  \(e\in E\) must lie on a positive-length closed walk.  The latter condition is
  automatic for a strongly connected graph with more than one vertex.
- **Ledger action:** `CLONE_STRONG_CONNECTIVITY` must be **demoted until qualified**,
  then can be restored as `proved`.  `ROBUST_CLONE_PRIMITIVITY` may remain `proved`
  because its two closed-walk witnesses exclude the edgeless singleton; its
  dependency should point to the qualified lemma.

### M4 — transient Frobenius proof gap

- **Affected text:** `corridor_entropy_shear_dichotomy.md`, Section 4, Theorem 4.1.
- **Direct ledger ID:** `ZERO_ENTROPY_SHEAR_NORMAL_FORM`.
- **Downstream open IDs:** `H2_VIRTUAL_SUPPORT_AUTOMATON`,
  `H2_VIRTUAL_TRANSFER_TRICHOTOMY`.
- **Weakest surviving statement:** after the common cycle power, walk counts across
  the condensation DAG grow polynomially of degree at most the number of diagonal
  components minus one; transient zero blocks are handled by strict component
  transitions, not by applying \((I+N)^m\) to the full matrix.
- **Ledger action:** the direct ID must be **demoted until the path-counting or
  Jordan proof is inserted**.  After that elementary completion, it may be restored
  as `proved` (preferably with M1's \(\rho\le1\) extension).  The `H2` nodes remain
  open.

### M5 — contextual, nested support loops

- **Affected text:** `corridor_support_automaton.md`, the final paragraph of
  Theorem 3.1 and Sections 5--6.
- **Direct ledger ID:** `SUPPORT_AUTOMATON_PUMPING`.
- **Downstream open ID:** `H2_VIRTUAL_SUPPORT_AUTOMATON`.
- **Weakest surviving statement:** every accepted word has a skeleton of length at
  most \(s2^{d^2}-1\) together with an **ordered nested insertion history** of loop
  occurrences, each preserving the support of its recorded prefix face.  There is no
  bound on loop number, loop length, numerical product, or free reordering.
- **Ledger action:** `SUPPORT_AUTOMATON_PUMPING` may **remain proved** after this
  wording clarification; its present formula already proves the weak statement.
  The semigroup classification stays in the open `H2_VIRTUAL_SUPPORT_AUTOMATON`.

### M6 — omitted counters and future state

- **Affected text:** `corridor_support_automaton.md`, Sections 3 and 6;
  `virtual_language_memory.md`, Sections 5--6; the evidence link for
  `H2_VIRTUAL_SUPPORT_AUTOMATON`.
- **Direct proved IDs:** `SUPPORT_AUTOMATON_PUMPING`, `COUNTER_SAFE_PUMPING`.
- **Open IDs:** `H2_UNIFORM_COUNTER_FOLLOWER`,
  `H2_VIRTUAL_SUPPORT_AUTOMATON`.
- **Weakest surviving statement:** finite support pumping is exact only after every
  acceptance-relevant future datum is in the automaton state; in a counter model it
  applies only to loop occurrences satisfying F4's endpoint fiber equality.
- **Ledger action:** keep `SUPPORT_AUTOMATON_PUMPING` `proved` in its finite-automaton
  scope; repair `COUNTER_SAFE_PUMPING` as in F4.  Both `H2` nodes remain open, and the
  support-automaton evidence section must be edited to state their counter-follower
  hypothesis.

### M7 — graph certificate versus KKL Value

- **Affected text:** `dynamical_corridor_certificate.md`, Section 4, Theorem 4.1.
- **Direct ledger ID:** `FINITE_STATE_CORRIDOR_CERTIFICATE`.
- **Supporting IDs:** `VARIABLE_CLONE_BLOCK_CONTRACTION`,
  `KKL_VALUE_CONTRACTION`.
- **Downstream open ID:** `H2_VIRTUAL_CORRIDOR_GRAPH_REALIZATION`.
- **Weakest surviving statement:** `FC1`--`FC6` produce an exact primitive clone
  graph with bounded gate and label depth.  The Value estimate follows only under
  the additional full KKL periodically repelling \(\psi\)-ql hypotheses, exact
  source-oriented core/WAD identity, and the complete-block exponent.  The graph
  certificate alone says nothing about the additive outgoing Value error.
- **Ledger action:** rewrite `FINITE_STATE_CORRIDOR_CERTIFICATE` as the graph theorem
  plus an explicitly conditional Value clause.  Because
  `VARIABLE_CLONE_BLOCK_CONTRACTION` already depends on imported
  `KKL_VALUE_CONTRACTION`, the narrowed implication can be **repaired as proved**.
  If that antecedent is not made explicit, demote the current compressed statement.
  The realization node remains open.

### Status summary

The following current literal nodes must not remain `proved` without a source/ledger
edit:

\[
\begin{gathered}
\texttt{IRREDUCIBLE\_TRANSFER\_ENTROPY\_DICHOTOMY},\\
\texttt{BOUNDED\_BRANCH\_SUPPORT\_WITNESS},\\
\texttt{PERMUTATION\_COCYCLE\_GAUGE},\quad
\texttt{DEFECT\_RUN\_DECOMPOSITION},\\
\texttt{CLONE\_STRONG\_CONNECTIVITY},\quad
\texttt{COUNTER\_SAFE\_PUMPING},\\
\texttt{ZERO\_ENTROPY\_SHEAR\_NORMAL\_FORM}.
\end{gathered}
\]

All seven can be restored as `proved` after the weakest corrections above; none
requires solving a new virtual-dynamics theorem.  The current
`FINITE_STATE_CORRIDOR_CERTIFICATE` should also be demoted unless its Value antecedent
is expanded, but its corrected graph-plus-conditional-Value form is already
supportable as `proved`.

The following may remain proved in their stated algebraic scope:

\[
 \texttt{BOOLEAN\_SUPPORT\_FUNCTOR},\qquad
 \texttt{SUPPORT\_AUTOMATON\_PUMPING},\qquad
 \texttt{ROBUST\_CLONE\_PRIMITIVITY},\qquad
 \texttt{VARIABLE\_CLONE\_BLOCK\_CONTRACTION}.
\]

Every `H2_*` node named above remains open.  In particular, no finite-matrix repair
closes framed source realization, counter-follower realization, or WAD/Value error
control.

`audit_proof.py` checks graph syntax, anchors, dependency cycles, and open dependency
status.  It cannot detect any of F1--F4 or the semantic evidence drift in M6.

## 8. Machine consistency check

Running
```text
python research/mlc_unified/audit_proof.py
```
on the ledger snapshot reviewed here returned exit status \(0\):

```text
ledger: valid (115 obligations)
statuses: imported=9, proved=82, open=24
target: MLC [open]
```

This means only that the JSON dependency graph and Markdown evidence anchors are
internally well formed.  It does not override the mathematical counterexamples in
Sections 2--3.  In particular, a ledger can be syntactically valid while a node
marked `proved` has a false statement.

A later rerun, after concurrent edits to
`corridor_entropy_shear_dichotomy.md`, returned nonzero because the Section 4 heading
was renamed while two ledger evidence links retained the old anchor:

```text
ZERO_ENTROPY_SHEAR_NORMAL_FORM:
  missing #4-reducible-zero-entropy-is-polynomial-shear
ZERO_ENTROPY_SHEAR_NO_GO:
  missing #4-reducible-zero-entropy-is-polynomial-shear
```

The new heading is `#4-reducible-nonexpansion-is-extinction-or-polynomial-shear`.
This report does not edit the concurrently owned manuscript or ledger; their owner
must update those two evidence strings.

## 9. Bottom line

The exact next invariant is not merely Boolean support.  A valid virtual transfer
state must carry, at minimum:

\[
 \text{finite control}
 \;+\;
 \text{endpoint frame/holonomy}
 \;+\;
 \text{prefix support face}
 \;+\;
 \text{declared counters}
 \;+\;
 \text{optional source-faithful stack word}
 \;+\;
 \text{source WAD/core incidence}.
\]

Only a closed, repeatable, counter-fiber-safe, stack-neutral return in this decorated
state has a
gauge-invariant Perron interpretation eligible for the KKL Value theorem.  That is
the adversarially stable doorway; the current unframed support-word criterion is not.

## 10. Remediation status after the audit

The owner subsequently applied the weakest repairs listed in Section 7:

- cyclic non-simple SCCs now exclude transient zero singletons;
- all transfer files use one source-column chronological convention;
- spectral certification is restricted to framed returns;
- the nonexpanding branch includes nilpotent extinction;
- permutation cocycles claim only an identity interior gauge;
- clone connectivity requires positive recurrence at the gate;
- endpoint pumping uses the exact reachable counter-fiber equality;
- contextual loop occurrences retain their nested order;
- the graph clone certificate and conditional KKL Value corollary are separate.

The two stale Section 4 anchors were also updated. The latest machine audit at that
repair point reports 124 obligations: 9 imported, 90 proved internally, and 25 open.
MLC remains open. This status paragraph records remediation of the finite
counterexamples; it is not an independent re-proof of the analytic open nodes.

A later source audit found that KKL's symbol \(T_F\) itself has incompatible
orientation cues. The safe live convention is now stated without that symbol: for
raw source-to-target incidence \(N\), the project count transport is
\(B=N^{\mathsf T}\), KKL \(v,w\) become project-left/project-right, and Value uses
\(v^2w\). A second automaton audit also separated universal transfer dimensions,
memory-safe compilation, and compositional WAD transport from the finite signature
criterion. At that later audit point the ledger contained 132 obligations:
8 imported, 96 proved, and 28 open. The live post-occupancy-scope ledger contains
138 obligations: 9 imported, 98 proved, and 31 open. The 124-count paragraph above
remains the historical first-repair point.
