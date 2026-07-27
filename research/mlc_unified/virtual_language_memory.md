# Future equivalence, bounded memory, and virtual counters

## 1. Status

`corridor_support_automaton.md` proves an exact pumping theorem **once** a uniformly
finite, source-faithful automaton has been constructed. This note proves that finite
horizon and a finite local alphabet do not imply such an automaton.

The exact missing invariant is future-equivalence index. Exact corridor lengths and
first-return times may instead require unbounded additive counters, while an ordered
nested molecule word may require a finite-alphabet stack if it must be unwound in
reverse order. The corrected target is therefore finite control with universally
many declared counters and, if dynamically necessary, one explicitly retained
source-faithful stack—not an unqualified finite-state language.

All language and counter results here are internal. Their realization by quadratic
dynamics is open.  The future-observable theorem in Section 6 now supplies a
canonical compact end topology for every already realized countably presented
system and compact proof-use catalog.  It does not supply that realization,
finite-dimensional compression, or analytic nondegeneration.

## 2. Source-faithful future equivalence

Let \(\mathcal A\) be a finite alphabet of fully decorated transition atoms. An atom
records not only core support, but every critical/access and WAD-to-core incidence
needed later. Let
\[
  \mathcal L\subseteq\mathcal A^*
\]
be the language of dynamically admissible finite block words.

For any word \(u\in\mathcal A^*\), define its future language
\[
  \operatorname{Fut}_{\mathcal L}(u)
  =
  \{z\in\mathcal A^*:uz\in\mathcal L\}.
\tag{2.1}
\]
Define the right equivalence
\[
  u\equiv_{\mathcal L}v
  \quad\Longleftrightarrow\quad
  \operatorname{Fut}_{\mathcal L}(u)
  =
  \operatorname{Fut}_{\mathcal L}(v).
\tag{2.2}
\]
Because the atoms are fully decorated, equality in (2.2) includes future WAD and
critical/access outputs. If outputs are stored separately, (2.2) must be refined to
equality of both admissibility and every future output.

### Theorem 2.1 (minimal complete exact automaton)

The language \(\mathcal L\) is recognized by a **complete** deterministic exact
automaton with at most \(s\) reachable states, including the dead state when it is
reachable, if and only if \(\equiv_{\mathcal L}\) has at most \(s\) classes.

**Proof.** Suppose an exact deterministic automaton recognizes \(\mathcal L\).
Words reaching the same state admit exactly the same continuations, so each
reachable state contains at most one future-equivalence class. Hence the number of
classes is at most the number of states.

Conversely, use the future-equivalence classes as states. Define
\[
  [u]\xrightarrow{a}[ua]
\]
for every \(u\in\mathcal A^*\) and \(a\in\mathcal A\). This is well-defined: if
\(u\equiv_{\mathcal L}v\), then for every \(z\),
\[
  uaz\in\mathcal L
  \quad\Longleftrightarrow\quad
  vaz\in\mathcal L,
\]
so \(ua\equiv_{\mathcal L}va\). The class with empty future is the dead state when it
exists. Mark a class accepting exactly when its members lie in \(\mathcal L\). The
resulting complete automaton recognizes precisely \(\mathcal L\).
\(\square\)

For a partial deterministic automaton one may omit the empty-future class. Its
minimal live-state count is the number of nonempty residuals, with at most one
additional state needed for completion.

Thus a universal automaton bound is exactly a universal bound on the number of
distinct dynamical futures. It does not follow from the number of present local
types.

## 3. Finite horizon and alphabet do not bound the index

### Proposition 3.1 (exponential copy-language obstruction)

For every \(m\), there is a finite prefix-closed language over the fixed alphabet
\[
  \{0,1,\#\}
\]
whose words have length at most \(2m+1\), but whose exact deterministic automaton
needs at least \(2^m\) states.

**Proof.** Let \(\mathcal L_m\) be the prefix closure of
\[
  \{x\#x:x\in\{0,1\}^m\}.
\]
For distinct \(x,y\in\{0,1\}^m\), the continuation \(\#x\) belongs to
\(\operatorname{Fut}_{\mathcal L_m}(x)\), because \(x\#x\in\mathcal L_m\), but it
does not belong to \(\operatorname{Fut}_{\mathcal L_m}(y)\). Therefore the \(2^m\)
length-\(m\) prefixes lie in distinct future-equivalence classes. Apply
Theorem 2.1. \(\square\)

Every atom in this example may be assigned the same identity core-support matrix.
Thus Boolean support can remain constant while future WAD/access admissibility has
exponentially many states.

### Proposition 3.2 (exact-exit counter obstruction)

For every \(m\), the prefix-closed language
\[
  \mathcal K_m
  =
  \operatorname{Pref}\{a^m b\}
\tag{3.1}
\]
requires at least \(m+1\) exact deterministic states before the terminal transition.

**Proof.** The prefixes
\[
  1,a,\ldots,a^m
\]
have distinct futures. If \(0\le i<j\le m\), then
\[
  a^{m-i}b
\]
continues \(a^i\) to \(a^m b\), while appending it to \(a^j\) exceeds the unique
permitted exit time and is not in \(\mathcal K_m\). Theorem 2.1 gives the lower
bound. \(\square\)

This is the language-theoretic form of a prescribed first return or corridor exit.
A one-state loop labeled \(a\) followed by \(b\) accepts all exit times and therefore
enlarges the language.

### Proposition 3.3 (reverse words require stack memory)

Let \(\mathcal R_m\) be the prefix closure of
\[
  \{x\#x^{\rm rev}:x\in\{0,1\}^m\}.
\tag{3.2}
\]
Its future-equivalence index is at least \(2^m\), but the union over all \(m\) is
recognized by finite control with one stack over the alphabet \(\{0,1\}\).

**Proof.** Distinct length-\(m\) prefixes \(x,y\) are separated by the continuation
\(\#x^{\rm rev}\), exactly as in Proposition 3.1. Hence the finite automaton lower
bound is \(2^m\).

A pushdown machine pushes each bit before \(\#\). After \(\#\), it pops one symbol for
each input bit and requires equality. It accepts every input whose run has not
encountered a mismatch, over-pop, or second separator; in particular, a matching
post-separator prefix may stop with symbols still on the stack. This recognizes
precisely the union of the prefix closures of all reverse copies.
\(\square\)

This is the natural abstract model when a nested molecule word must be unwound in
last-in, first-out order. It is only an analogy until the actual antirenormalization
itinerary is proved to have this stack discipline.

## 4. A sufficient bounded-memory theorem

Let \(M\) be a finite set of dynamical modes. Suppose there is a universal
\(R<\infty\) such that:

1. the legality and decorated output of the next atom depend only on the current mode
   and the last at most \(R\) atoms;
2. the next mode is a deterministic function of those same data;
3. endpoint acceptance is a function of those same data.

### Theorem 4.1 (bounded memory gives bounded automata)

Under these hypotheses the exact decorated language has a deterministic automaton
with at most
\[
  |M|\sum_{j=0}^{R}|\mathcal A|^j
\tag{4.1}
\]
states.

**Proof.** A state consists of the current mode and the suffix of length at most
\(R\). The hypotheses make both the permitted next atoms and the state update
functions of this state. Induction on continuation length shows that equal states have
equal decorated future languages. The number of possible states is bounded by
(4.1). \(\square\)

For virtual dynamics, the content is proving a universal memory \(R\) after
translation, neutral, critical, and access data have all been included. Merely
declaring a localization radius does not prove the future-equivalence hypothesis.

## 5. Counter-aware finite control

Exact return times suggest a hybrid state
\[
  (q,\boldsymbol\nu),
\qquad
  q\in Q,
  \quad
  \boldsymbol\nu\in\mathbb Z_{\ge0}^{k},
\tag{5.1}
\]
where \(Q\) is finite control and \(\boldsymbol\nu\) records corridor lengths,
satellite depths, or return clocks. A transition changes the counter by a declared
increment.

### Lemma 5.1 (exact counter-fiber criterion)

Let two prefixes reach the same finite-control state and the same Boolean support.
Suppose the intervening loop has counter increment \(\Delta\), a fixed continuation
has increment \(\eta\), and its endpoint predicate is \(\Phi\). If the counter before
the loop is \(\boldsymbol\nu\), deleting the loop preserves endpoint acceptance
exactly when
\[
  \Phi(\boldsymbol\nu+\eta)
  =
  \Phi(\boldsymbol\nu+\Delta+\eta).
\tag{5.2}
\]
Consequently, deletion is uniformly endpoint-safe on a declared reachable fiber
precisely when (5.2) holds for every reachable
\((\boldsymbol\nu,\eta)\) in that fiber. Zero increment and invariance of \(\Phi\)
under \(\Delta\) on the reachable fiber are convenient sufficient conditions, not
necessary conditions for one particular path.

**Proof.** The deleted word ends with counter
\(\boldsymbol\nu+\eta\); the original word ends with
\(\boldsymbol\nu+\Delta+\eta\). Equality of their two predicate values is therefore
necessary and sufficient for that continuation. Quantifying this equality over the
declared reachable fiber gives the uniform statement. \(\square\)

This lemma concerns the endpoint predicate. A full dynamical splice must also
preserve every intermediate counter guard and decorated output used by the
continuation; those data belong in the source-faithful follower state.

The KKL clone syntax retains its length \(n\) as an explicit nonzero parameter
rather than compressing it away. The printed \(+\lambda^k\) weighted equation in the
checked snapshot is quarantined by `kkl_transfer_orientation_audit.md`, Section 6;
it is not imported here. For a realized literal clone, the independent corrected
equation is \(\rho(\sum_k\lambda^{-k}R_k)=\lambda^n\). The memory lesson is that a
counter-aware reduction must retain \(n\), the actual return-length labels, and every
branch needed by that typed equation.

### Corollary 5.2 (memory projection does not license pumping)

Factoring clocks into counters and nesting into a stack does **not** by itself permit
the finite-control pumping theorem. The repeated finite-control/support pair supplied
by pigeonhole may enclose a nonzero counter increment or a nonidentity stack action.
The exact-exit language \(\operatorname{Pref}\{a^m b\}\), projected to one control
state with identity support, is an explicit example: every repeated pair encloses a
positive clock increment.

The pumping theorem applies to the augmented dynamics only after one of the following
is proved:

1. the chosen finite pumping summary is a memory congruence, so every repeated
   summary induces the identity on every relevant reachable counter/stack fiber;
2. every memory-changing run is first compiled into an exact checkpoint macro and
   the resulting checkpoint language is an exact finite-state language; or
3. counter/stack state itself has a finite exact quotient and is included in the
   automaton state.

Checking that a loop is counter-fiber-safe and stack-neutral is necessary for
deleting that specified occurrence, but it does not prove that the pigeonhole
argument will find such a loop. Without Items 1--3 there is no bounded accepted
support skeleton for the augmented language.

### Proposition 5.3 (bounded additive counters do not hide arbitrary memory)

Fix \(s,k,C<\infty\). Consider deterministic finite control with \(s\) states and
\(k\) integer counters, started from one fixed configuration, where every transition
adds a vector in
\[
  [-C,C]^k.
\]
After reading \(m\) symbols, the number of possible control/counter configurations is
at most
\[
  s(2Cm+1)^k.
\tag{5.3}
\]
Consequently such a system cannot distinguish all \(2^m\) binary prefixes for every
large \(m\), and cannot recognize the copy languages in Proposition 3.1 from a common
initial configuration.

**Proof.** Each counter lies in an interval of at most \(2Cm+1\) integers around its
initial value. Multiply the \(k\) counter possibilities by the \(s\) control states.
For fixed \(s,k,C\), this is polynomial in \(m\), while \(2^m\) is exponential.
Two binary prefixes eventually reach the same configuration and therefore have the
same future, contradicting Proposition 3.1. \(\square\)

Allowing one counter to encode the entire word as a base-\(|\mathcal A|\) integer and
then permitting arbitrary digit decoding would evade Proposition 5.3, but would make
"bounded counter dimension" vacuous. Every counter in the proof program must have a
declared geometric meaning, a universal update rule, and a restricted endpoint
predicate; it cannot be an opaque code for the omitted itinerary.

## 6. Corrected virtual language theorem

### Uniform Counter/Stack-Follower Theorem (`OPEN`)

Every virtual-Molecule block admits a source-faithful decorated transition model with
universal constants
\[
  |\mathcal A|\le a_0,
  \qquad
  |M|\le m_0,
  \qquad
  R\le R_0,
  \qquad
  k\le k_0,
  \qquad
  |\mathcal T|\le t_0,
  \qquad
  C\le C_0,
  \qquad
  |\mathcal G|\le g_0,
\tag{6.1}
\]
such that:

1. every ordinary transition consumes one structural token—there are no hidden
   epsilon computations—and future admissibility and every WAD-to-core output are
   determined by a mode, an
   \(R_0\)-suffix, \(k_0\) explicit additive counters, and, when necessary, a
   LIFO stack over the finite alphabet \(\mathcal T\);
2. counter updates agree with the actual selected return correspondence, belong to a
   universal finite set in \([-C_0,C_0]^{k_0}\), and do not decode an opaque
   itinerary;
3. stack push/pop operations agree with the actual nesting and antirenormalization
   order of satellite copies and inspect only the top symbol or empty-stack status;
4. transition and endpoint guards come from a listed universal finite catalog
   \(\mathcal G\) of bounded-coefficient affine counter tests, fixed bounded residues,
   and top/empty-stack tests; arbitrary predicates of a whole integer encoding or
   stack word are forbidden;
5. the memory-changing part is compiled into exact checkpoint macro-edges, or a
   finite pumping congruence is proved for which every repeated summary is
   configuration-neutral on its reachable fiber;
6. every macro parameter is a read-only edge field, the layerwise or checkpoint trace
   resolution is fixed once, and every downstream lemma uses that same resolution;
7. nonzero-counter or stack-changing runs are grouped into exact clone equations,
   sectorial antirenormalization blocks, or an explicitly weighted transfer equation;
8. critical visits, changes of access marking, and changes of Frobenius flag either
   reset counters by a declared rule or terminate the current block;
9. the number of counters, guard types, and stack alphabet are independent of molecule depth,
   satellite periods, and the finite postcritical horizon;
10. every numerical transfer, critical/WAD emission, Value contribution, error, and
    shear moment inside a configuration-neutral loop or macro remains in the retained
    block record.

This theorem is stronger and more precise than simply requesting a finite automaton.
It allows the unbounded lengths which the clone and neutral theories are designed to
measure and the ordered nesting which a stack can retain, while requiring uniformly
finite control over their interactions. If the dynamics admits a bounded-counter
normal form, the stack is empty. Otherwise the entire stack word
\(\omega_B\in\mathcal T^*\) remains explicit side data and is never compressed into a
homogeneous coordinate.

### Proposition 6.1 (discrete side-data compactness obstruction)

Let \(K\) be any nonempty compact geometric state space. If either:

1. an integer counter ranges over an unbounded subset of \(\mathbb Z^k\) with the
   discrete topology; or
2. stack words have unbounded length in \(\mathcal T^*\) with the discrete topology
   for a nonempty finite alphabet \(\mathcal T\),

then the corresponding product with \(K\) is not precompact.

**Proof.** An unbounded subset of the discrete lattice and an infinite set of
distinct finite words in the discrete word topology each contain an infinite
\(1\)-separated sequence. Hence neither is precompact. The coordinate projection of
a precompact product is precompact, so multiplying by \(K\) cannot repair the
failure. \(\square\)

Consequently, calling counters and stacks “side data” does not by itself close the
global compactness argument. The coercivity theorem must prove at least one of:

1. the side data are forgotten by the compactness topology after their complete
   block has closed;
2. their relevant values are uniformly bounded;
3. they admit a declared compact end/cylinder topology in which the virtual hull,
   endpoint guards, and transition maps extend continuously.

Alternative 3 has the formal implementation in Theorem 6.4 once the exact
transition system and compact target encodings have been supplied.  Constructing
the source-faithful virtual system remains part of the open H1/H2 program.

### Theorem 6.2 (countable-follower Stone compactification)

Let \(X\) be a countable set of exact symbolic configurations, let
\[
  T_e:D_e\longrightarrow X,\qquad e\in E,
\tag{6.2}
\]
be a countable family of partial deterministic transitions, and let
\(\mathcal O\) be a countable family of proof-used observable subsets of
\(X\).  There are a compact metrizable zero-dimensional space \(K\), an
injective dense map \(\iota:X\to K\), a clopen set
\(\widehat D_e\subset K\) and a continuous extension
\[
  \widehat T_e:\widehat D_e\longrightarrow K
\tag{6.3}
\]
for every \(e\), and a clopen extension of every member of
\(\mathcal O\).

#### Proof

Let \(\mathfrak B\) be the smallest Boolean algebra of subsets of \(X\)
which contains every singleton, every \(O\in\mathcal O\), every \(D_e\),
and \(T_e^{-1}(A)\) whenever \(A\in\mathfrak B\).  The generating data are
countable.  Closing them successively under countably many inverse-image
operations and finite Boolean operations gives a countable union of
countable families, so \(\mathfrak B\) is countable.

Let \(K=\operatorname{Ult}(\mathfrak B)\).  For \(A\in\mathfrak B\), put
\[
  \widehat A=\{u\in K:A\in u\}.
\tag{6.4}
\]
Stone duality makes \(K\) compact, Hausdorff, and zero-dimensional, with
the sets (6.4) as a clopen base.  Countability of \(\mathfrak B\) makes
this base countable, hence \(K\) is metrizable.

The principal-ultrafilter map
\[
  \iota(x)=\{A\in\mathfrak B:x\in A\}
\tag{6.5}
\]
is injective because \(\{x\}\in\mathfrak B\).  Every nonempty basic
clopen \(\widehat A\) contains \(\iota(x)\) for some \(x\in A\), so its
image is dense.

For \(u\in\widehat D_e\), define
\[
  \widehat T_e(u)
  =
  \{A\in\mathfrak B:T_e^{-1}(A)\in u\}.
\tag{6.6}
\]
The inverse-image operation preserves intersections and sends \(X\) to
\(D_e\).  It preserves complements relative to \(D_e\):
\[
  T_e^{-1}(X\setminus A)
  =
  D_e\setminus T_e^{-1}(A).
\tag{6.7}
\]
Since \(D_e\in u\), equations (6.6)--(6.7) show that (6.6) is an
ultrafilter on \(\mathfrak B\).  Moreover,
\[
  \widehat T_e^{-1}(\widehat A)
  =
  \widehat{T_e^{-1}(A)}\cap\widehat D_e,
\tag{6.8}
\]
so \(\widehat T_e\) is continuous, and direct substitution gives
\(\widehat T_e(\iota(x))=\iota(T_e(x))\) for \(x\in D_e\).
Finally, each \(O\in\mathcal O\) extends to the clopen
\(\widehat O\). \(\square\)

### Corollary 6.3 (conditional geometric coupling)

Suppose additionally that \(G\) is a compact metric space,
\(g:X\to G\), and every \(e\) has a continuous map \(S_e:G\to G\)
satisfying
\[
  g(T_e x)=S_e(g(x)),\qquad x\in D_e.
\tag{6.9}
\]
Then
\[
  Z=\overline{\{(g(x),\iota(x)):x\in X\}}\subset G\times K
\tag{6.10}
\]
is compact metrizable, and
\[
  (y,u)\longmapsto (S_e(y),\widehat T_e(u))
\tag{6.11}
\]
restricts to a continuous self-map of
\(Z\cap(G\times\widehat D_e)\).

#### Proof

Only invariance of \(Z\) needs proof.  If
\((g(x_n),\iota(x_n))\to(y,u)\) and \(u\in\widehat D_e\), clopenness of
\(\widehat D_e\) implies \(x_n\in D_e\) eventually.  Equation (6.9)
then places every image under (6.11) in the defining diagonal set of
(6.10), and continuity places the limit in \(Z\). \(\square\)

Theorem 6.2 proves that unbounded exact counters and finite stack words do
not, by themselves, obstruct a compact **Boolean symbolic** topology once
the actual countable deterministic follower and catalog have been fixed.
It does not by itself treat arbitrary compact-valued observables.  The
following future-observable construction supplies exactly that stronger
interface.

### Theorem 6.4 (future-observable compactification)

Let \(X\) be an arbitrary exact state set, let
\[
  T_e:D_e\longrightarrow X,\qquad e\in E,
\tag{6.12}
\]
be countably many partial deterministic transitions, and let
\[
  O_j:X\longrightarrow Y_j,\qquad j\in J,
\tag{6.13}
\]
be a countable catalog with compact metrizable targets.  Add the constant
observable \(O_*:X\to\{0\}\).  For every finite transition word \(w\), let
\(T_w\) have domain \(D_w\), put \(Y_j^\bot=Y_j\sqcup\{\bot\}\), and define
\[
  \Phi(x)_{w,j}
  =
  \begin{cases}
    O_j(T_wx),&x\in D_w,\\
    \bot,&x\notin D_w.
  \end{cases}
\tag{6.14}
\]
Then
\[
  K_{\rm fut}
  =
  \overline{\Phi(X)}
  \subset
  \prod_{(w,j)\in E^{<\mathbb N}\times(J\cup\{*\})}Y_j^\bot
\tag{6.15}
\]
is compact metrizable.  Every exact transition domain extends to the
clopen set
\[
  \widehat D_e=\{z:z_{e,*}=0\},
\tag{6.16}
\]
and
\[
  (\widehat T_ez)_{w,j}=z_{ew,j}
\tag{6.17}
\]
defines a continuous extension.  Every declared observable extends by its
empty-word coordinate, and every finite transition identity valid on its
exact domain remains valid on the corresponding compactified domain.

The quotient \(\Phi(X)\) identifies exactly the states having identical
declared observations after all finite continuations.  It is minimal:
every compact Hausdorff realization extending the same data on clopen
domains maps continuously onto \(K_{\rm fut}\).  If \(X\) is countable and
all point predicates are included, \(\Phi\) is injective.

#### Proof

The coordinate set in (6.15) is countable, so the ambient product and its
closed subset \(K_{\rm fut}\) are compact metrizable.  Define the
coordinate shift \(S_e\) by
\[
  (S_ez)_{w,j}=z_{ew,j}.
\]
If \(z\in\widehat D_e\) and \(\Phi(x_n)\to z\), convergence in the
discrete \((e,*)\)-coordinate gives \(x_n\in D_e\) eventually.  Hence
\[
  S_e\Phi(x_n)=\Phi(T_ex_n),
\]
so \(S_ez\in K_{\rm fut}\).  This proves (6.16)--(6.17).

For every finite word \(w\), its compactified domain
\(\widehat D_w=\{z:z_{w,*}=0\}\) is clopen and
\(\Phi(D_w)\) is dense in it: every nonempty relatively open subset of
\(\widehat D_w\) meets the dense exact image, and its exact points have
the word \(w\) defined.  Continuous finite compositions agreeing on
\(D_w\) therefore agree on \(\widehat D_w\).

For minimality, form the future-observation map from any competing compact
realization into the product (6.15), using \(\bot\) off each clopen word
domain.  It is continuous and agrees with \(\Phi\) on the dense exact
subset.  Its image is compact and equals \(\overline{\Phi(X)}\).  Point
predicates give injectivity in the countable case. \(\square\)

### Corollary 6.5 (symbolic side compactness)

For every realized exact counter/stack transition system with countable
transition and proof-use catalogs, after every non-discrete output is put
in a specified compact metrizable encoding, Theorem 6.4 gives a compact
metrizable end topology on which all declared guards, hull encodings, and
transitions extend continuously.  Distinct values in a countable side
projection remain distinct by declaring its countably many point
predicates.

This proves the compact-topology alternative in
`H3_SYMBOLIC_SIDE_COMPACTNESS`.  It does not prove that a limiting encoded
hull is a nondegenerate admissible renormalization; that remains in
`H3_COERCIVITY`.  It also does not prove
`H2_UNIFORM_COUNTER_FOLLOWER` or
`H2_MEMORY_SAFE_PUMPING_COMPILATION`.

### Corollary 6.6 (future-faithful trace topology)

After an actual virtual component transition system and its complete
countable proof-use catalog are frozen, equality of all coordinates in
(6.14) is the canonical future-faithful quotient.  Its closure (6.15) is
a compact metrizable end topology through which every declared Wave,
Wanderers, covering, quasi-additivity, width, transport, access, obstacle,
and authorized enlargement observable factors.

Thus the compact-end-topology branch of
`VIRTUAL_PROOF_USE_TRACE_SELECTOR` is formal after its actual component
system and complete Wave horizon are supplied.  No universal finite
cardinality or response-dimension bound follows.

## 7. Adversarial audit

Any proposed realization must defeat:

1. the exponential copy language of Proposition 3.1;
2. the exact-exit language of Proposition 3.2;
3. two prefixes with equal core support but distinct future WAD/access outputs;
4. an automaton loop whose deletion changes the prescribed first-return time;
5. a counter whose reset depends on an omitted critical branch;
6. a number of independent satellite clocks growing with virtual-molecule depth;
7. a claimed memory radius that grows with the postcritical horizon;
8. replacement of an exact endpoint counter by a residue without proving residue
   invariance;
9. pumping a nonzero-counter loop without retaining its weighted spectral effect;
10. encoding the entire satellite word in one integer and calling it one geometric
    counter;
11. assuming LIFO stack order without proving that antirenormalization unwinds the
    virtual satellite chain in reverse;
12. claiming compactness of the full marked state while unbounded counters or finite
    stack words retain the discrete topology.

Finite present complexity is not the required invariant. Uniformly bounded decorated
future complexity, modulo explicitly retained counters and a proved source-faithful
stack discipline when necessary, is.
