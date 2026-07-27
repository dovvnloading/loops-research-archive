# From a marked cell tree to a source-faithful support automaton

## 1. Status and purpose

`corridor_support_automaton.md` proves a finite pumping theorem once a
source-faithful transfer automaton has been supplied. This note isolates the exact
combinatorial construction required to supply one.

The main conclusions are:

1. a finite marked return presentation has a canonical minimal automaton obtained by
   future equivalence;
2. a uniformly bounded automaton follows from a uniformly bounded
   **Markov-complete signature**, not from finiteness or bounded local valence alone;
3. WAD coordinates may be merged exactly only when every future core-incidence and
   Value observable is constant on the merged class;
4. a pure corridor of prescribed length \(n\) cannot be represented exactly by a
   uniformly bounded ordinary automaton over a fixed layer alphabet;
5. the exact length must therefore remain in a declared counter/clone equation, or
   be compressed to a length-parameterized macro-edge when its interior has no
   proof-used branch, marking, WAD event, or checkpoint.

All finite-state and linear-algebra assertions in this note are proved. The analytic
realization of the hypotheses for a virtual Julia-set hull remains open.

## 2. Exact source data

### 2.1 The transfer-incidence monoid

Fix nonnegative integers \(d,w\). Let \(\mathfrak S_{d,w}\) be the set of block
matrices
\[
  \widehat M
  =
  \begin{pmatrix}
    B&C\\
    0&R
  \end{pmatrix},
  \qquad
  B\in M_d(\mathbb Z_{\ge0}),\quad
  C\in M_{d\times w}(\mathbb Z_{\ge0}),\quad
  R\in M_w(\mathbb Z_{\ge0}).
\tag{2.1}
\]
All blocks use the source-column convention locked in
`transfer_convention_and_frame.md`: columns are source coordinates, rows are target
coordinates, and chronological maps compose by left multiplication. Core frames at
the endpoints are part of the resolved decoration; spectral data are used only for a
framed return.
The intended meanings are:

- \(B\): the exact finite core/Hubbard pushforward, including multiplicity;
- \(R\): transport of the retained WAD coordinates;
- \(C\): incidence of those WAD coordinates with the core occurrences produced at
  this step.

Ordinary matrix multiplication makes \(\mathfrak S_{d,w}\) a monoid. In particular,
\[
  \begin{pmatrix}B_2&C_2\\0&R_2\end{pmatrix}
  \begin{pmatrix}B_1&C_1\\0&R_1\end{pmatrix}
  =
  \begin{pmatrix}
    B_2B_1&B_2C_1+C_2R_1\\
    0&R_2R_1
  \end{pmatrix}.
\tag{2.2}
\]
Thus the upper-right block retains both earlier incidence pushed through the later
core map and new incidence applied to the transported WAD data.

The matrix model is not asserted to encode cyclic order, oriented prime-end sides, or
critical labels. Those are retained as finite discrete decorations below.

For a path \(e_1\cdots e_m\), in chronological order, set
\[
  \widehat M(e_1\cdots e_m)
  =
  \widehat M(e_m)\cdots\widehat M(e_1).
\tag{2.3}
\]

### Lemma 2.1 (incidence composition)

If the one-step source data satisfy (2.1), then (2.3) gives the exact iterated core
transfer, WAD transport, and accumulated WAD-to-core incidence.

**Proof.** The assertion for two steps is (2.2). Induction on the path length proves
the general statement. \(\square\)

This is only a formal composition theorem. Showing that the actual KKL core
pushforward and WAD pullback incidence admit such a finite coordinate system is part
of the open realization problem.

### 2.2 Resolved marked return presentations

A **resolved marked return presentation** is a tuple
\[
  \mathfrak P=(X,x_\ast,\Gamma,\delta,o,\widehat M,\rho)
\tag{2.4}
\]
with the following data.

1. \(X\) is a finite set of reachable configurations and \(x_\ast\in X\) is the
   selected initial configuration.
2. \(\Gamma\) is a finite set of **decorated branch tokens** for this presentation.
3. \(\delta:X\times\Gamma\rightharpoonup X\) is a partial deterministic transition.
4. \(o:X\to Z\) is a terminal color. It records every distinction later used at a
   checkpoint: ordinary, block exit, critical exit, horizon stop, corridor side, and
   any other proof-used terminal class.
5. Each token \(\gamma\) has an exact source label
   \[
     \widehat M(\gamma)\in\mathfrak S_{d,w}
   \]
   and a finite ribbon/access decoration \(\rho(\gamma)\).
6. Every selected source branch has exactly one token, and two branches with the same
   matrix label but different future domain, ribbon order, critical status, or access
   behavior have different tokens.
7. Parallel branches represented by one token and one successor are aggregated with
   their exact occurrence multiplicity in \(\widehat M(\gamma)\); otherwise they
   receive distinct occurrence tokens.

The word *resolved* means that after the token has been specified there is at most
one successor. A multivalued pullback correspondence must first be split into branch
tokens. Merely giving two different successors the same token is not a resolved
presentation. Identical parallel occurrences may be aggregated only as allowed by
Item 7; the accepted language then records occurrence types while the matrix records
their exact multiplicity.

A word \(u=\gamma_1\cdots\gamma_m\) is a path from \(x\) if the successive partial
transitions are defined. Let \(\delta(x,u)\) denote its endpoint. The
terminal-colored future of \(x\) is
\[
  \mathcal F(x)
  =
  \left\{
    (u,o(\delta(x,u))):
    u\text{ is a finite path from }x
  \right\}.
\tag{2.5}
\]
The empty word is included. Hence \(\mathcal F(x)\) records \(o(x)\).

The presentation is **source locked** if:

1. its paths are exactly the selected partial-return paths, not a superlanguage;
2. (2.3) equals the actual core/WAD source cocycle on every path;
3. its terminal colors and ribbon decorations retain every critical, access, side,
   and horizon distinction used later;
4. every proof-used orbit or WAD segment is present up to its last use.

These are hypotheses about extraction from the dynamics. They do not follow from the
formal finiteness of \(X\).

For one block, \(\Gamma\) is finite. A uniform theorem must additionally distinguish
a universally finite **structural token catalog** from declared numerical fields such
as an exact matrix, a corridor length, or a geometric counter increment. Otherwise
an omitted itinerary could be encoded into arbitrarily many token names and the
bounded state count would be vacuous. Numerical fields may vary, but they must have
the declared source semantics and update/endpoint rules used by the proof.

### 2.3 Source-faithful automata

A colored deterministic automaton over the same decorated tokens is
\[
  \mathcal A=(Q,q_\ast,\Gamma,\Delta,\bar o).
\tag{2.6}
\]
It is **source faithful for \(\mathfrak P\)** if:

1. for every token word \(u\), \(u\) is a path from \(q_\ast\) exactly when it is a
   source path from \(x_\ast\);
2. corresponding endpoints have the same terminal color;
3. token decorations, transfer matrices, and hence all products (2.3) are unchanged.

This definition permits several source paths with identical decorated traces to be
identified. It does not permit a new decorated trace.

The accumulated matrix product need not itself be stored in the automaton state when
it does not affect which continuation is dynamically allowed: it is recovered from
the edge labels. `corridor_support_automaton.md` later augments an automaton state by
the Boolean support of the accumulated prefix product for its pumping argument. If
the accumulated numerical product, a critical count, or a remaining-time count
changes future admissibility, however, that quantity belongs in the source
configuration or in an explicitly declared macro parameter; it cannot be silently
discarded.

## 3. The canonical future-equivalence automaton

Define
\[
  x\equiv_{\rm fut}y
  \quad\Longleftrightarrow\quad
  \mathcal F(x)=\mathcal F(y).
\tag{3.1}
\]

### Lemma 3.1 (future equivalence is a right congruence)

If \(x\equiv_{\rm fut}y\), then:

1. \(o(x)=o(y)\);
2. a token \(\gamma\) is enabled at \(x\) if and only if it is enabled at \(y\);
3. whenever \(\gamma\) is enabled,
   \[
     \delta(x,\gamma)\equiv_{\rm fut}\delta(y,\gamma).
   \tag{3.2}
   \]

**Proof.** Item 1 follows from the empty-word entries in (2.5). A token \(\gamma\) is
enabled exactly when \(\mathcal F(x)\) contains a pair whose word begins with
\(\gamma\), proving Item 2. Finally,
\[
  \mathcal F(\delta(x,\gamma))
  =
  \{(u,z):(\gamma u,z)\in\mathcal F(x)\}.
\tag{3.3}
\]
Equality of the two futures gives (3.2). \(\square\)

### Theorem 3.2 (canonical source-faithful quotient)

Let \(\mathfrak P\) be a finite resolved source-locked presentation. Then
\[
  Q_{\min}=X/{\equiv_{\rm fut}},
\qquad
  [x]\xrightarrow{\gamma}[\delta(x,\gamma)]
\tag{3.4}
\]
is a well-defined source-faithful deterministic automaton.

If every state of \(X\) is reachable from \(x_\ast\), this automaton is minimal among
all deterministic colored automata realizing the same decorated trace language.
Consequently, its state count is exactly the number of distinct source futures
\(\mathcal F(x)\).

**Proof.** Lemma 3.1 proves that the transition and terminal color in (3.4) are
independent of the representative.

Every source path projects to a quotient path. Conversely, start with the fixed
representative \(x_\ast\). If a quotient token is enabled, Lemma 3.1 says that it is
enabled at every representative of the current class. Induction therefore lifts
every quotient path to a source path. Terminal colors agree by Lemma 3.1, and the
token sequence is unchanged, so its source matrix product and ribbon data are
unchanged. This proves source faithfulness.

For minimality, let \(x\) and \(y\) be reachable and suppose
\(\mathcal F(x)\ne\mathcal F(y)\). Choose source words \(u,v\) reaching them. If a
deterministic colored automaton reaches the same state after \(u\) and \(v\), its
colored futures after those words are equal, contradicting the chosen difference.
Thus distinct future classes require distinct automaton states. The quotient realizes
one state per class, so it is minimal. \(\square\)

### Corollary 3.3 (finiteness is not uniformity)

Every finite resolved cell presentation has a finite canonical automaton, with at
most \(|X|\) states. A uniform state bound across virtual blocks is equivalent to a
uniform bound on the number of reachable future-equivalence classes.

In particular, the assertion that every individual cell tree is finite does not
prove the virtual support-automaton theorem.

The equivalence (3.1) is the terminal-colored, source-decorated form of the
Myhill--Nerode equivalence. It is deliberately stronger than equality of local tree
shape or equality of the current Boolean transfer support.

## 4. Constructive uniform bounds

### 4.1 Markov-complete signatures

Let
\[
  \theta:X\longrightarrow\Theta
\tag{4.1}
\]
be a finite signature. It is **Markov complete** when, for all
\(\theta(x)=\theta(y)\):

1. \(o(x)=o(y)\);
2. the exact decorated token sets enabled at \(x\) and \(y\) are equal;
3. for every enabled token \(\gamma\),
   \[
     \theta(\delta(x,\gamma))
     =
     \theta(\delta(y,\gamma)).
\tag{4.2}
\]

Because tokens contain their exact matrix, multiplicity, branch, access, and ribbon
decorations, Item 2 is stronger than equality of unweighted support.

### Theorem 4.1 (bounded-signature construction)

If \(\theta\) is Markov complete, the type automaton
\[
  \theta(x)\xrightarrow{\gamma}\theta(\delta(x,\gamma))
\tag{4.3}
\]
is source faithful and has at most \(|\Theta|\) states.

Moreover,
\[
  \theta(x)=\theta(y)
  \quad\Longrightarrow\quad
  x\equiv_{\rm fut}y.
\tag{4.4}
\]

**Proof.** Conditions 1--3 make (4.3) well defined. Induction on word length shows
that equal-type configurations enable exactly the same words and that corresponding
endpoints have equal type and terminal color. This proves (4.4). Projection and
lifting from \(x_\ast\), exactly as in Theorem 3.2, prove source faithfulness. The
state bound is immediate. \(\square\)

A useful auditable signature has the form
\[
  \theta(x)=
  \bigl(
    \text{reduced cell type},
    \text{ribbon side},
    \text{critical/orbit phase},
    \text{return-domain mask},
    \text{core frame},
    \text{WAD future profile}
  \bigr).
\tag{4.5}
\]
If the six catalogs in (4.5) have respective cardinalities
\[
  C_0,\ R_0,\ P_0,\ D_0,\ K_0,\ W_0,
\]
then
\[
  |Q|\le C_0R_0P_0D_0K_0W_0.
\tag{4.6}
\]
For at most \(a_0\) possible resolved branch actions, the crude choice of the entire
enabled-domain mask gives \(D_0\le2^{a_0}\).

Formula (4.6) is a theorem only after the successor and exact token data are proved
to depend on (4.5). Counting local shapes without proving this Markov property does
not suffice.

### Lemma 4.2 (cellular conjugacy certificate)

Suppose every pair \(x,y\) with \(\theta(x)=\theta(y)\) has a marked ribbon
isomorphism between its resolved cell germs such that:

1. the isomorphism preserves the core frame, retained WAD ports, critical/orbit
   labels, terminal color, and oriented access flags;
2. for each branch token \(\gamma\), its selected domain contains the germ at \(x\)
   if and only if it contains the germ at \(y\);
3. whenever \(\gamma\) is defined, the cellular square commutes with a marked ribbon
   isomorphism between the two image germs that preserves every component of
   \(\theta\);
4. the two restrictions have the same exact
   \(\widehat M(\gamma)\), occurrence multiplicity, and discrete decoration.

Then \(\theta\) is Markov complete.

**Proof.** Item 1 gives equal terminal colors. Items 2 and 4 give equal exact
decorated enabled-token sets. Item 3 says the two successors have the same marked
cell signature. These are precisely the three conditions preceding Theorem 4.1.
\(\square\)

The commutative-square clause is stronger than saying the two unmarked stars are
homeomorphic. It checks the partial return domains and their marked images, which is
where future splitting first appears.

### 4.2 A bounded distinguishing-horizon criterion

For \(L\ge0\), let \(\mathcal F_{\le L}(x)\) be (2.5) restricted to words of length
at most \(L\).

### Proposition 4.3 (finite-horizon state bound)

Assume:

1. \(|\Gamma|\le g\) and \(|Z|\le z\);
2. there is a universal \(L\) such that
   \[
     \mathcal F_{\le L}(x)=\mathcal F_{\le L}(y)
     \quad\Longrightarrow\quad
     x\equiv_{\rm fut}y.
\tag{4.7}
   \]

Then
\[
  |Q_{\min}|
  \le
  (z+1)^{\,1+g+\cdots+g^L}.
\tag{4.8}
\]
For \(g=1\), the exponent is \(L+1\).

**Proof.** In a deterministic presentation, each word of length at most \(L\) is
either undefined or ends in exactly one of \(z\) terminal colors. There are
\(1+g+\cdots+g^L\) such words, so there are at most the number of truncated future
tables in (4.8). Hypothesis (4.7) says each table determines one full future class.
\(\square\)

This criterion is often much weaker than a Markov-complete local signature, but it
makes the missing uniformity falsifiable: one must exhibit a uniform distinguishing
horizon, not merely a finite horizon for each block.

## 5. The abstract cell-tree construction theorem

### 5.1 Marked cell-return data

Let \(T\) be a finite ribbon tree with a finite cellular subdivision. Marked objects
may include:

- core/Hubbard edges and their coordinate frames;
- critical and postcritical orbit labels;
- oriented access gates and corridor sides;
- retained WAD ports and support classes;
- block-entry, block-exit, and finite-horizon stops.

Let \(r_a:D_a\to T\) be finitely many selected partial cellular return branches. A
**resolved atom** is a cell, oriented flag, or marked germ after subdividing so that
each \(D_a\), each image, and every proof-used marking is cellular. The configurations
\(X\) are the resolved atoms together with the finite live-marking frame needed to
continue the selected correspondence.

The following hypotheses are sufficient.

This is a theorem for an **exact compiled checkpoint language**, not for the raw
finite-control projection of a counter/stack follower. Exact unbounded return clocks,
nesting words, and endpoint guards must first be treated as in
`virtual_language_memory.md`.

#### `CTM` Exact memory compilation

Every memory-changing run has been replaced by a source-locked parameterized macro,
or the pumping summary includes a finite memory congruence whose repeated classes
act identically on every relevant reachable counter/stack fiber. Consequently, every
accepted finite-control token path is accepted by the complete augmented follower at
the declared trace resolution. Merely omitting the counters or stack does not satisfy
`CTM`.

#### `CT0` Bounded source modules

The core and retained WAD modules have explicitly declared dimensions
\[
  d\le d_0,
  \qquad
  w\le w_0.
\tag{CT0}
\]
For one finite presentation \(d_0,w_0\) may depend on the input. A uniform virtual
theorem must prove that they are universal. Bounded signature catalogs do not imply
these inequalities: a one-state loop labeled by \(I_d\) has one local type for every
\(d\).

#### `CT1` Exact branch resolution

Every selected partial return has been split into deterministic branch tokens. A
source orbit segment determines a unique token path, and every token path is an
actual selected orbit segment.

#### `CT2` Exact source cocycle

Every token carries the actual matrix \(\widehat M(\gamma)\) of (2.1), with core
edge multiplicities and WAD incidence checked before any quotient. The discrete
decoration carries cyclic order, oriented side, critical status, and access identity.

#### `CT3` Markov-complete bounded signature

There is a signature (4.5) satisfying Theorem 4.1, and the catalog product in (4.6)
is bounded independently of satellite period, corridor length, and transition depth.
In particular, every selected return domain is a union of signature fibers. The
structural branch-token catalog is also universally bounded after the declared
matrix, macro-length, counter, and stack fields are separated; none of those fields
is an opaque code for the omitted future word.

#### `CT4` Future-closed WAD compression

If the retained WAD coordinates are obtained from a raw WAD module by a quotient
\(P\), every enabled raw transport satisfies the Markov compatibility equation
\[
  P_{\rm out}R_\gamma=\bar R_\gamma P_{\rm in}
\tag{CT4}
\]
for a declared compressed transport \(\bar R_\gamma\). In addition, the coordinates
satisfy the fixed-family output-observability criterion of Theorem 6.3 below. No
eliminated port or WAD class later separates, acquires a different core itinerary, or
receives a different Value coefficient inside the complete block.

#### `CT5` Terminal and horizon completeness

The terminal color distinguishes every later-used stopping condition. Every
critical-orbit, Wave, Wanderer, WAD, and access segment used by the block lies inside
the selected horizon and appears before its data are discarded.

#### `CT6` Honest treatment of long pure runs

Every unbounded exact clock has first been retained as a declared counter, stack word,
clone length, or weighted-transfer parameter. In the remaining zero-counter
presentation, every unbounded run is treated in one of two ways:

1. its individual cells satisfy the uniformly bounded future-index condition; or
2. it satisfies the pure checkpoint-macro hypotheses of Proposition 5.2.

It is not replaced by a freely repeatable loop merely because its local cell shapes
agree. When Item 2 is used, the declared source presentation is the
checkpoint-to-checkpoint presentation obtained after macro compression; source
faithfulness is asserted at that trace resolution, not for the discarded layerwise
prefix language.

#### `CT7` Source identity

For every core occurrence from source \(\beta\) to target \(\gamma\), the core
cocycle in `CT2` satisfies
\[
  B_{\gamma\beta}=N_{\beta\gamma}.
\]
Thus \(B=N^{\mathsf T}\) for the raw row-source incidence \(N\) occurring in KKL's
Value coordinate sums, and KKL \(v,w\) become the project left and right
eigenweights. The WAD incidence is the actual typed pullback itinerary used by
Value. This clause does not identify \(B\) with the source's orientation-ambiguous
symbol \(T_F\), and the cocycle is not a graph fitted after inspecting a desired
spectral radius.

### Theorem 5.1 (cell-tree-to-automaton theorem)

Under `CTM` and `CT0`--`CT7`, the compiled marked partial return correspondence has a
source-faithful finite core-transfer automaton. Its state count is bounded by (4.6),
its core and WAD dimensions are \(d,w\), and every accepted compiled path has:

1. the exact dynamical admissibility of the selected correspondence at its declared
   full-layer or checkpoint trace resolution;
2. the exact core transfer with multiplicity;
3. the exact retained WAD transport and WAD-to-core incidence;
4. all declared critical, access, ribbon, and terminal data.

If the bounds in `CT0` and `CT3` are universal, then the automaton state, core
dimension, and WAD dimension are universal. `CT4` proves that the chosen WAD
dimension is a compositional output-sufficient quotient; it does not itself bound
that dimension.

The theorem does not construct `CTM` from an arbitrary counter/stack follower.
Source faithfulness of the complete block belongs to the separate memory-safe
checkpoint compilation theorem in `virtual_language_memory.md`; without it,
Theorem 5.1 cannot be invoked.

**Proof.** `CTM`, `CT1`, `CT2`, `CT5`, and `CT7` give a resolved source-locked presentation
as in Section 2. If `CT6(2)` is used, Proposition 5.2 first replaces it by the
source-locked checkpoint presentation. `CT3` supplies the Markov-complete signature,
so Theorem 4.1 produces the exact automaton and the state bound. Lemma 2.1 proves the
product assertion for the core and WAD data. `CT4` proves that the declared finite
WAD coordinates transport compositionally and lose no declared future observable.
`CT0` supplies the separate dimension bounds. `CT6` rules out an unrecorded length
counter. \(\square\)

The theorem is abstract but not vacuous: `CT3`, `CT4`, `CT6`, and `CT7` are exactly
the places where a plausible local quotient can enlarge the language or lose the
source valuation.

### 5.2 Pure checkpoint macros

Consider a path
\[
  x_0\xrightarrow{\tau}x_1\xrightarrow{\tau}\cdots
  \xrightarrow{\tau}x_n
\tag{5.1}
\]
with \(\widehat M(\tau)=\widehat M_\tau\). Call it **checkpoint pure** if:

1. \(x_0\) and \(x_n\) are declared checkpoints with compatible endpoint frames;
2. no edge enters or leaves \(x_1,\ldots,x_{n-1}\) except the two displayed chain
   edges;
3. none of those interior configurations is an initial state, terminal checkpoint,
   critical event, WAD injection/elimination event, access split, or proof-used
   observation;
4. every later argument either works only at \(x_0,x_n\) or explicitly unfolds the
   stored run length \(n\).

### Proposition 5.2 (exact checkpoint macro)

A checkpoint-pure run (5.1) may be replaced by one token
\[
  \tau[n]:x_0\longrightarrow x_n,
  \qquad
  \widehat M(\tau[n])=\widehat M_\tau^n.
\tag{5.2}
\]
where \(\tau[n]\) is a fresh resolved token schema and its endpoint frames are the
declared frames of \(x_0,x_n\).
This gives a bijection between checkpoint-to-checkpoint paths before and after
compression and preserves all checkpoint terminal data and transfer-incidence
products.

It does not preserve the layerwise prefix language.

**Proof.** By Item 1, a path that takes the displayed first edge from \(x_0\) has no
choice inside the run before reaching \(x_n\), and no path can enter or exit in its
interior. Other branches at \(x_0\) are left unchanged. Hence replacing the displayed
chain by one edge gives a bijection of paths whose endpoints are checkpoints.
Equation (2.3) gives the matrix label in (5.2). Item 2 says no declared checkpoint
observation is removed. The words \(\tau,\ldots,\tau^{n-1}\) disappear, so the full
prefix language is not preserved. \(\square\)

The integer \(n\) is edge metadata, not a finite-state variable. Thus a family of
macro tokens \(\tau[n]\) is not a finite alphabet uniform in \(n\). This is harmless
for a matrix-labeled complete-block automaton only if downstream arguments accept
parametric macro labels and analyze \(\widehat M_\tau^n\) exactly. If a downstream
lemma requires every layer as an automaton edge, Proposition 5.2 cannot be invoked.

### 5.3 Four memory mechanisms that must not be conflated

There are four distinct exact models.

#### Layerwise finite language

Every cell crossing is an ordinary decorated token. Terminal admissibility is
recognized by the finite state alone. Theorem 3.2 applies directly, and a universal
model requires a universal future-equivalence index. Proposition 7.1 shows that
prescribed arbitrary exit length violates this requirement.

#### Checkpoint macro with parameter \(n\)

A complete pure run is one parametric token \(\tau[n]\). The integer \(n\) and
\(\widehat M_\tau^n\) are retained on that token. Only checkpoint paths are claimed
to be exact; intermediate prefixes are deliberately absent. This is a compiled
complete-block edge, not a freely iterable one-letter loop.

#### Finite control with additive counters

An augmented configuration has the form
\[
  (q,\boldsymbol\nu),
  \qquad
  q\in Q,\quad
  \boldsymbol\nu\in\mathbb Z^k,
\tag{5.3}
\]
and a transition carries a declared increment
\(\Delta(\gamma)\in\mathbb Z^k\). Exact first returns and corridor exits may be
counter predicates. The finite control \(q\) alone generally accepts a
superlanguage; source faithfulness belongs to the augmented system. The counter must
have declared geometric meaning and cannot be an opaque integer encoding an entire
itinerary.

#### Finite control with a LIFO stack

An augmented configuration has the form
\[
  (q,\omega),
  \qquad
  \omega\in\mathcal T^\ast
\tag{5.4}
\]
for a finite stack alphabet \(\mathcal T\). Transitions may push a declared symbol,
pop a matching top symbol, or leave the stack unchanged. This model is appropriate
only if the selected satellite nesting is proved to unwind in last-in, first-out
order. No such order is inferred from the abstract cell tree or assumed in this
note. If antirenormalization can revisit nesting data in another order, a LIFO stack
is not source faithful and a different memory invariant is required.

The stack word may be arbitrarily long even when \(|Q|\) and
\(|\mathcal T|\) are universal. It is side data, not a homogeneous geometric
coordinate and not part of the finite-state count.

### Lemma 5.3 (counter/stack configuration neutrality)

Suppose each token has an additive counter increment and a partial stack operation.
Let a loop word \(\beta\) return to the same finite-control state. Deleting \(\beta\)
preserves the complete augmented configuration for every admissible entering
counter/stack state if:

1. its total counter increment is zero; and
2. its induced partial stack transformation is the identity on every admissible
   entering stack.

Conversely, if either condition fails, there is an entering augmented state for
which deletion changes the augmented state. It can preserve an endpoint language
only after a separate proof that every later transition and endpoint predicate is
invariant under that specific change.

**Proof.** Counter increments add along the word, so the post-loop counter is
\(\boldsymbol\nu+\Delta(\beta)\). This equals the entering counter for every
\(\boldsymbol\nu\) exactly when \(\Delta(\beta)=0\).

Let \(\Phi_\beta\) be the partial transformation of stack words induced by the loop.
The post-loop stack equals the entering stack for every admissible stack exactly when
\(\Phi_\beta\) is the identity on its admissible domain. If either equality fails,
choose a state witnessing the failure. Deletion changes that augmented state. Equal
finite control and equal Boolean matrix support cannot restore the omitted counter or
stack data. Only an independently proved invariance of the remaining language can
make that particular change irrelevant. \(\square\)

The lemma concerns only the counter/stack configuration. Even a
configuration-neutral loop may emit a nonidentity transfer matrix, critical/WAD
events, Value, error, or shear moments. Those outputs must be retained in the ordered
loop record or separately proved invariant.

Accordingly, Theorem 5.1 and the pumping theorem in
`corridor_support_automaton.md` apply only after `CTM` proves that the pigeonhole
summary itself is a memory congruence, or after exact checkpoint compilation. A
nonzero counter loop remains in its clone, neutral, or weighted transfer equation. A
stack-changing loop remains explicit unless the actual dynamics proves the necessary
stack cancellation and every emitted observable is retained.

## 6. WAD-to-core incidence and future observability

### 6.1 The linear criterion

Let \(U\) be the finite set of uncompressed WAD coordinates in one complete block,
and let
\[
  P:\mathbb R^U\longrightarrow\mathbb R^w
\tag{6.1}
\]
be the proposed compression. Let \(\mathscr O\) contain every future linear
observable used before the block closes, including:

1. every row of every future WAD-to-core incidence map;
2. every outgoing KKL Value coefficient row;
3. every electrode or port-separation weight that is later reopened;
4. every retained linear error or shear moment depending on the WAD weights.

Discrete cyclic order and orientation are not linear observables and must remain in
the finite decorations.

### Lemma 6.1 (exact observability criterion)

The compressed vector \(Pz\) determines \(Oz\) for every \(O\in\mathscr O\) and every
\(z\in\mathbb R^U\) if and only if
\[
  \ker P\subseteq\bigcap_{O\in\mathscr O}\ker O.
\tag{6.2}
\]
Equivalently,
\[
  \operatorname{row}(O)\subseteq\operatorname{row}(P)
  \qquad\text{for every }O\in\mathscr O.
\tag{6.3}
\]

**Proof.** If \(Pz=Pz'\), then \(z-z'\in\ker P\). Thus all \(Oz=Oz'\) exactly when
(6.2) holds. In finite-dimensional linear algebra,
\(\ker P\subseteq\ker O\) is equivalent to every row of \(O\) belonging to the row
space of \(P\), proving (6.3). \(\square\)

### Lemma 6.2 (Markov transport quotient criterion)

Let
\[
  R:\mathbb R^U\longrightarrow\mathbb R^V
\]
be one raw WAD transport, with proposed source and target compressions
\[
  P_{\rm in}:\mathbb R^U\to\mathbb R^w,
  \qquad
  P_{\rm out}:\mathbb R^V\to\mathbb R^{w'}.
\]
There exists a compressed transport \(\bar R\) satisfying
\[
  P_{\rm out}R=\bar R P_{\rm in}
\tag{6.4}
\]
if and only if
\[
  \ker P_{\rm in}\subseteq\ker(P_{\rm out}R).
\tag{6.5}
\]

**Proof.** Equation (6.4) immediately implies (6.5). Conversely, define
\[
  \bar R(P_{\rm in}z)=P_{\rm out}Rz
\]
on \(\operatorname{im}P_{\rm in}\). Condition (6.5) makes this independent of the
representative \(z\). Extend linearly to the remaining target coordinates if
\(P_{\rm in}\) is not surjective. \(\square\)

This condition must hold for every enabled branch and successor compression. Output
observability in Lemma 6.1 does not imply it. For example,
\[
  P=(1\ \ 1),
  \qquad
  R=\begin{pmatrix}1&0\\0&2\end{pmatrix}
\]
has \(PR=(1\ \ 2)\), which does not factor through \(P\), even if every currently
listed terminal observable is zero.

### Theorem 6.3 (coarsest output-safe WAD partition for a fixed family)

Suppose \(P\) is a partition-sum quotient: it replaces all coordinates in each class
\(A_j\subset U\) by their sum. Then \(P\) is future observable if and only if every
row of every \(O\in\mathscr O\) is constant on each \(A_j\).

Consequently, among partition-sum quotients and for the already complete fixed
observation family \(\mathscr O\), the coarsest output-safe partition groups two WAD
coordinates precisely when their future-observation columns agree. Its number of
classes is the number of distinct future profiles.

**Proof.** The row space of a partition-sum matrix consists exactly of rows that are
constant on each partition class. Apply Lemma 6.1. The coarsest equivalence relation
on columns preserving all such rows is equality of their complete observation
profiles. \(\square\)

This is the WAD analogue of future equivalence. A universal WAD dimension \(w\)
requires a universal bound on the number of distinct future profiles. Bounded port
incidence at the current cell does not imply that bound.

### Corollary 6.4 (nonnegative observability witness)

If (6.2) fails, there are two nonnegative WAD vectors \(z_+,z_-\) such that
\[
  Pz_+=Pz_-,
  \qquad
  Oz_+\ne Oz_-.
\tag{6.6}
\]
for some proof-used future observable \(O\).

**Proof.** Choose \(v\in\ker P\) with \(Ov\ne0\). For a sufficiently large strictly
positive vector \(z_0\) and sufficiently small \(\varepsilon>0\), both
\[
  z_\pm=z_0\pm\varepsilon v
\]
are nonnegative. They satisfy (6.6). \(\square\)

Thus failure is not confined to signed formal WADs.

Lemmas 6.1--6.4 concern a linear compression of the raw WAD coordinate vector. They
do not imply that a Schur-eliminated terminal response matrix determines Value or
future incidence: the map from internal conductances to terminal response is
nonlinear and noninjective. For response-state compression, exactness must instead be
checked directly on every fiber of the response map, or the missing raw moments must
be retained as in `bc1_finite_port_response.md` and `bc2_value_feature.md`.

## 7. Exact no-go examples

### 7.1 Prescribed corridor length has unbounded future index

For \(n\ge0\), let
\[
  L_n=\{a^n b\}
\tag{7.1}
\]
over the fixed alphabet \(\{a,b\}\).

### Proposition 7.1 (countdown lower bound)

Any partial deterministic automaton that recognizes exactly \(L_n\) at a terminal
checkpoint has at least \(n+2\) reachable live states.

**Proof.** The \(n+2\) prefixes
\[
  \epsilon,a,a^2,\ldots,a^n,a^nb
\]
have pairwise distinct right futures. For \(0\le i<j\le n\), the suffix
\(a^{n-i}b\) completes \(a^i\) to the accepted word but does not complete \(a^j\).
The accepting prefix \(a^nb\) has the empty accepting continuation and is distinct
from the others. Theorem 3.2 gives the lower bound. \(\square\)

Therefore identical local translation cells do not by themselves yield a uniformly
bounded exact automaton. One must prove genuine repeatability, retain a countdown
whose state size grows with \(n\), or use the restricted checkpoint macro of
Proposition 5.2.

### 7.2 Unsafe representative splicing

Let the actual decorated language be
\[
  \{ab,cd\}.
\tag{7.2}
\]
After reading \(a\), only \(b\) is enabled; after reading \(c\), only \(d\) is
enabled. If those two intermediate configurations are merged because their current
tree shapes or matrix supports agree, the quotient admits both outgoing tokens and
therefore also accepts
\[
  ad,\quad cb.
\]
These words have no source realization. The two intermediate configurations are not
future equivalent.

This is the exact language-enlargement mechanism that `CT3` excludes.

### 7.3 Boolean support loses multiplicity

The one-dimensional transfers
\[
  B_1=(1),
  \qquad
  B_2=(2)
\tag{7.3}
\]
have the same Boolean support and different core multiplicity. If the source
pushforward distinguishes one and two occurrences, a token quotient based only on
support is not source faithful.

Boolean support is valid for the later pumping state only after the exact numerical
matrix has been attached to each source-faithful edge.

### 7.4 Present port equality does not imply future equality

Let two WAD coordinates \(u_1,u_2\) be compressed by
\[
  P=(1\ \ 1).
\tag{7.4}
\]
Suppose a later core incidence observes
\[
  O=(1\ \ 0).
\tag{7.5}
\]
Then \((1,0)\) and \((0,1)\) have the same compressed mass and different future
incidence. The same example applies when the outgoing Value row is
\((\alpha,\beta)\) with \(\alpha\ne\beta\).

This failure persists even if the two coordinates currently use the same pair of
ports.

### 7.5 Bounded local degree does not bound automaton states

Take a path-shaped ribbon tree with all vertices of degree at most two. Put one exit
mark at distance \(n\) from the entry and let the partial return move one edge toward
it. Its local unmarked cells are all isomorphic, but its future residuals are the
countdown residuals of Proposition 7.1. Hence bounded valence, bounded cell shape,
and a finite tree do not imply a universal state count.

### 7.6 A bounded current port count need not bound WAD profiles

For \(U=\{u_1,\ldots,u_n\}\), let a later family of observations contain the coordinate
rows
\[
  O_i z=z_i,\qquad 1\le i\le n.
\tag{7.6}
\]
All coordinates may currently meet the same two geometric ports, but they have \(n\)
distinct future profiles. Theorem 6.3 requires \(n\) output-safe partition classes.

Thus a universal terminal count requires future closure, not merely present
incidence.

### 7.7 Opaque token names make a state bound vacuous

For any finite decorated word \(w\), introduce one new token \([w]\) and one edge
from an entry state to an exit state. This gives a two-state checkpoint automaton for
that single word. As \(w\) varies, however, the token catalog contains the entire
omitted word, and no layerwise event can be recovered unless \([w]\) is unfolded.

Likewise, storing the binary expansion of \(w\) in one unrestricted integer does not
give a one-counter geometric normal form. These encodings prove that state dimension
or counter dimension alone is not a complexity theorem. The structural token
catalog, parameter semantics, update rules, and proof-used internal observations must
also be uniformly controlled.

### 7.8 Bounded signature count does not bound module dimension

For every \(d\), take one reachable configuration, one loop token, no WAD
coordinates, and core label \(B=I_d\). The Markov signature, future quotient, and
structural action catalog each have size one, while \(d\to\infty\). Similarly, with
\(d=1\), \(R=I_w\), and no nonzero declared output, the WAD module dimension can
diverge while the control signature remains constant.

Thus `CT0` is independent of `CT3` and output observability. The
\(s2^{d^2}\) support bound has no uniform content until \(d\le d_0\) is proved.

### 7.9 Topological semiconjugacy does not supply analytic source identity

A monotone quotient may collapse an access-separating continuum while preserving the
abstract tree map. The resulting cellular transition can satisfy `CT1`--`CT3` and
still fail to represent:

- the correct prime-end intervals;
- a proper selected pullback branch;
- the KKL translation marking;
- the WAD restriction itinerary;
- a uniform extremal-width comparison.

The abstract automaton theorem does not repair this analytic failure. It is why the
realization theorem in Section 8 retains the analytic-access and finite-horizon
inflation hypotheses.

## 8. Virtual analytic realization theorem

### Virtual Markov Cell-Tree Realization (`OPEN`)

For every virtual-Molecule complete block, construct an access-complete selected
finite-horizon correspondence and marked ribbon cell tree such that the
counter/stack data of `H2_UNIFORM_COUNTER_FOLLOWER` are explicitly retained and the
chosen checkpoint language satisfies all of the following with universal constants.

1. **Full carrier and cellular extraction.** The carrier and monotone ribbon-tree
   quotient satisfy the fullness, saturation, inactive-component, and marked-leaf
   requirements of `virtual_hull_realization.md`, Section 6.1.
2. **Analytic access realization.** Every declared flag is realized by the required
   prime-end interval and selected proper branch, with the finite-horizon
   correspondence and width control required by
   `finite_horizon_inflation.md`.
3. **Resolved source branches.** The cellular partial returns give `CT1`, and their
   core multiplicities give the exact source cocycle `CT2`.
4. **Uniform source modules.** The core and compressed WAD modules satisfy `CT0`
   with universal \(d_0,w_0\), proved independently of the signature count.
5. **Exact memory compilation.** The checkpoint language satisfies `CTM`: every
   memory-changing run is an exact typed macro, or the pumping summary is a finite
   congruence whose repetitions act identically on the reachable counter/stack
   fiber. The raw finite-control projection is not used.
6. **Uniform Markov signature and action catalog.** The descriptor (4.5), or another
   explicit descriptor, is Markov complete and satisfies a universal bound (4.6).
   The structural token catalog is universal after declared numerical and memory
   fields are separated.
7. **Honest long-run mechanism.** Every exact length remains in its declared
   counter/clone/weighted-transfer equation. Every unbounded zero-counter translation
   run either has universally bounded future index or is checkpoint pure and is
   carried by the parameterized macro mechanism of Proposition 5.2. No freely
   repeatable loop is inserted without a dynamical recurrence theorem.
8. **Source-licensed nesting memory.** If a finite-alphabet stack is used, every
   push and pop is identified with the selected return correspondence and the LIFO
   order is proved. Otherwise the actual nesting word remains uncompressed or is
   carried by the replacement memory invariant.
9. **Transport-compatible, future-closed WAD incidence.** Every enabled raw WAD
   transport obeys (6.4), and the complete fixed family of future core-incidence,
   Value, port, response, error, and shear observations obeys (6.2), with a universal
   number of WAD future profiles.
10. **Source identity.** The resulting \(B\)-cocycle is identified entry by entry as
   \(B=N^{\mathsf T}\) for the raw KKL source-to-target incidence \(N\); the KKL
   \(v,w\) weights are translated to project left/right roles, and the \(R,C\) data
   are the typed WAD pullback itinerary used by Value. No conclusion is based on the
   source's ambiguous \(T_F\) symbol.
11. **Complete horizon.** Every edge, loop, mixing witness, critical branch, access,
   WAD restriction, and Wave/Wanderer pullback used downstream occurs before the
   declared horizon closes.

Under these hypotheses, Theorem 5.1 supplies the source-faithful automaton required
by `corridor_support_automaton.md`. The support-pumping theorem may then be applied
without language enlargement.

No current project document proves Items 1--11 simultaneously. In particular:

- finite cell-tree extraction does not imply Markov completeness;
- analytic access realization does not imply a bounded future index;
- bounded signature count does not imply bounded core or WAD dimension;
- bounded current port incidence does not imply future WAD observability;
- output observability does not imply transport compatibility;
- projecting away counters or a stack does not produce an exact pumping language;
- a long translation corridor does not imply a bounded exact layerwise automaton;
- nested molecule terminology does not prove LIFO unwind order.

## 9. Dependency and proof-ledger suggestions

Theorem 3.2 is the terminal-colored, cocycle-decorated refinement of
`FUTURE_EQUIVALENCE_AUTOMATON`; it is recorded as
`SOURCE_FUTURE_QUOTIENT` so that source-cocycle preservation remains visible.
Proposition 7.1 remains under `FINITE_HORIZON_LANGUAGE_NO_GO`. Lemma 5.3 is recorded
as `COUNTER_STACK_SAFE_LOOP`, depending on the exact counter-fiber statement in
`COUNTER_SAFE_PUMPING`.

The following additional internal obligations are proved here and may be entered as
separate dependency nodes.

1. **`MARKOV_SIGNATURE_AUTOMATON`**: Theorem 4.1, Lemma 4.2, and Theorem 5.1. After
   exact memory compilation (`CTM`), a bounded Markov-complete marked-cell signature
   with the local cellular-conjugacy certificate produces a uniformly finite
   core-transfer automaton with exact decorated compiled language and cocycle.
   Separate `CT0` hypotheses, not the signature, bound the core/WAD dimensions.
2. **`WAD_TRANSPORT_QUOTIENT_CRITERION`**: Lemma 6.2. A proposed compressed WAD
   state is compositional precisely when every enabled raw transport descends
   through its source and target quotients.
3. **`WAD_FUTURE_OBSERVABILITY`**: Lemma 6.1 and Theorem 6.3. For a fixed complete
   observation family, output compression is exact precisely when all observation
   rows factor through it.
4. **`PURE_CORRIDOR_MACRO`**: Proposition 5.2. A checkpoint-pure run admits exact
   parametric macro compression at checkpoints.

The open node **`H2_VIRTUAL_SUPPORT_AUTOMATON`** should depend on:

- `H1_CELL_TREE_EXTRACTION`;
- `H1_ANALYTIC_ACCESS_REALIZATION`;
- `H1_FINITE_HORIZON_INFLATION`;
- `H2_UNIFORM_COUNTER_FOLLOWER`;
- `H2_MEMORY_SAFE_PUMPING_COMPILATION`;
- `H2_UNIFORM_CORE_WAD_DIMENSION`;
- `SOURCE_FUTURE_QUOTIENT`;
- `MARKOV_SIGNATURE_AUTOMATON`;
- `WAD_TRANSPORT_QUOTIENT_CRITERION`;
- `WAD_FUTURE_OBSERVABILITY`;
- `PURE_CORRIDOR_MACRO`;
- `COUNTER_STACK_SAFE_LOOP`;
- `FRAMED_RETURN_SPECTRAL_INVARIANCE`;
- `KKL_TYPED_VALUE_INCIDENCE`;
- `H2_VIRTUAL_CORE_COCYCLE_REALIZATION`.

If response or Value moments are compressed at the same stage, it should also depend
on `H2_RESPONSE_REALIZATION` and `H2_VALUE_FEATURE_REALIZATION`.

No dependency should run in the opposite direction from the abstract automaton
theorems to analytic realization: the former are conditional finite-state results,
not constructions of a virtual hull.

## 10. Adversarial acceptance checklist

A proposed virtual support automaton is not accepted until all of the following tests
pass.

1. **Residual test:** enumerate or characterize the future residuals. Prove their
   number is universal after any declared macro compression.
2. **Splicing test:** for every merged pair of configurations, verify equality of
   enabled decorated tokens and successor classes.
3. **Multiplicity test:** compare exact core matrices, not only Boolean support.
4. **Source test:** tabulate raw incidence \(N\), verify \(B=N^{\mathsf T}\), and
   translate KKL \(v,w\) to project left/right roles before invoking Value. Do not
   rely on the source's ambiguous \(T_F\) label.
5. **WAD kernel test:** verify
   \[
     \ker P\subseteq\bigcap_{O\in\mathscr O}\ker O
   \]
   for the complete future-observation family.
6. **Port reopening test:** prove that no eliminated access later separates inside
   the complete block.
7. **Ribbon test:** retain every cyclic-order and orientation distinction that affects
   a later restriction.
8. **Countdown test:** identify every quantity depending on remaining corridor
   length. It must be a bounded state, a declared external macro parameter, or an
   explicit obstruction.
9. **Counter test:** every additive counter has declared geometric semantics and
   update rules; no nonzero-counter loop is pumped without the exact reachable-fiber
   predicate equality.
10. **Stack test:** every push/pop symbol has a source dynamical meaning, and LIFO
    unwinding is proved rather than inferred from nesting terminology.
11. **Macro-interior test:** verify that no proof-used critical, WAD, access, error, or
   shear event was skipped inside a macro.
12. **Horizon test:** every pumped loop and every mixing witness must lie inside the
    selected analytic horizon.
13. **Language test:** generate short accepted words and lift each one back to an
    actual partial-return path. A single unliftable word falsifies source faithfulness.
14. **Support/numerical separation test:** support pumping may compress the finite
    skeleton, but every numerical entropy or shear loop remains in the transfer
    product.
15. **Token-encoding test:** the structural action alphabet is universally bounded;
    no unique token name or unrestricted integer field encodes the omitted itinerary.
16. **Dimension test:** exhibit independent universal \(d_0,w_0\); do not infer them
    from a bounded signature catalog.
17. **WAD transport test:** verify
    \(P_{\rm out}R_\gamma=\bar R_\gamma P_{\rm in}\) for every enabled branch, in
    addition to Item 5's output test.
18. **Repeated-pair memory test:** prove that the actual pigeonhole summary is a
    memory congruence, or invoke pumping only after exact checkpoint compilation.
19. **Trace-resolution test:** fix layerwise or checkpoint resolution once and use it
    in every downstream theorem.
20. **Emission test:** retain every core, critical/WAD, Value, error, and shear
    emission of a configuration-neutral loop.

These tests turn the virtual support-automaton step into a finite, adversarially
checkable target. They do not by themselves solve the analytic realization problem.
