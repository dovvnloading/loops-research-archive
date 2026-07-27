# Second red-team audit: virtual automaton construction

## Scope and verdict

This audit checks:

- `virtual_support_automaton_construction.md`;
- `virtual_language_memory.md`;
- the claimed handoff to `corridor_support_automaton.md`.

The canonical future quotient, Markov-complete signature theorem, fixed-length
lower bounds, reverse-copy stack example, bounded-memory theorem, bounded-increment
counter count, and the linear WAD observability lemmas are correct in their stated
abstract settings, subject to the wording corrections below.

The documents do **not** construct the virtual dynamical automaton. More
importantly, three present bridge statements are not yet valid:

1. the cell-tree theorem does not derive a universal core/WAD transfer dimension;
2. projecting away counters or a stack does not license the finite support-pumping
   theorem unless memory safety is guaranteed for the repeated pair supplied by
   pigeonhole;
3. future linear observability alone does not construct a compositional compressed
   WAD transport.

These are repairable formulation gaps, but the first two are fatal to using the
current abstract theorem as the claimed input to a uniform corridor induction.

## Fatal/material findings

### F1. `Theorem 5.1` does not prove a universal transfer dimension

The final sentence of the cell-tree theorem says that universal `CT3` and `CT4`
bounds make both the automaton-state and transfer dimensions universal. `CT3`
bounds a catalog of signatures and structural actions. It does not bound the core
dimension \(d\). `CT4` is an observability condition and does not, as written,
bound the number \(w\) of retained WAD coordinates.

Explicit abstract family: for every \(d\), take one reachable configuration, one
loop token, \(w=0\), and core matrix \(B=I_d\). Give the unique configuration one
signature and the unique structural action one action type. All future and
Markov-completeness catalogs have cardinality one, while \(d\to\infty\). Treat
\(I_d\) as the prescribed source cocycle. Nothing in `CT1`--`CT7` excludes this
family. The same example with \(d=1\), \(R=I_w\), and no nonzero future WAD
observable leaves \(w\) unbounded.

Required repair: add separate hypotheses
\[
  d\le d_0,\qquad w\le w_0
\]
uniformly, or prove canonical core and WAD quotient theorems that imply these
bounds. A bounded number of frame *types* is not a bound on the dimension of each
frame. This repair is essential because the support-pumping bound
\(s2^{d^2}\) is useless without a universal \(d\).

### F2. Memory-safe pumping is not supplied by finite-control pigeonhole

`corridor_support_automaton.md` is correct for an exact finite automaton. A
finite-control projection of a counter/stack follower is generally not such an
automaton: it accepts a superlanguage. Requiring “the pumped loop” to be
counter-fiber-safe and stack-neutral does not solve this, because the pigeonhole
argument chooses an arbitrary repeated finite-control/support pair and gives no
reason that its intervening loop is memory neutral.

Explicit counterexample: use one finite-control state, one identity Boolean support,
and the exact augmented language
\[
  \operatorname{Pref}\{a^n b\}.
\]
Each \(a\)-edge changes a countdown or elapsed-time counter. Every pair of
finite-control/support prefixes repeats, but no intervening \(a^j\), \(j>0\), is
counter neutral for the exact exit predicate. Deleting it creates an inadmissible
exit time. The finite-control projection has a one-state \(a\)-loop, but it is not
source faithful.

The same obstruction occurs with a stack word if all repeated projected pairs
enclose a nonidentity push or pop. There need not be any memory-neutral repeated
pair before the horizon.

Consequences:

- the finite support-skeleton theorem cannot be applied to the projected language
  while retaining its conclusion that the shortened skeleton is dynamically
  accepted;
- the bounded bad-support witness theorem cannot be transferred to the augmented
  language;
- a pathwise instruction to “retain unsafe loops” is not enough, because the proof
  obtains the bounded skeleton by deleting loops.

Required repair: prove one of the following stronger statements.

1. Every repetition of the chosen pumping summary induces the identity on the
   relevant reachable counter/stack fiber.
2. Enlarge the pumping summary by a **finite** memory congruence that makes this
   true.
3. Compile every memory-changing run into exact checkpoint macro-edges first and
   prove that the resulting checkpoint language is an exact finite-state language.
4. Replace the accepted-skeleton theorem by a purely algebraic factorization that
   does not claim the shortened word is dynamically admissible, and redo every
   downstream witness argument without that claim.

The current `Lemma 5.3` is a correct criterion for a specified loop. It does not
prove that a suitable loop exists, so it cannot by itself repair the pumping
handoff.

### F3. WAD output observability is not a compositional quotient condition

`Lemma 6.1` and `Theorem 6.2` correctly characterize when the listed linear outputs
\(Oz\) factor through \(Pz\). They do not ensure that the next compressed WAD state
is well defined. For every branch transport \(R_\gamma\), compositional compression
also requires a map \(\bar R_\gamma\) satisfying
\[
  P R_\gamma=\bar R_\gamma P,
\tag{R}
\]
equivalently
\[
  \ker P\subseteq\ker(P R_\gamma).
\]

Explicit counterexample: let
\[
  P=(1\ \ 1),\qquad
  R=\begin{pmatrix}1&0\\0&2\end{pmatrix},
\]
and let all currently declared terminal observables be zero. The observability
criterion is vacuous, but \(PR=(1\ \ 2)\) does not factor through \(P\). Two raw
vectors with the same compressed mass can have different next compressed masses.

Required repair: distinguish:

- terminal/future **output sufficiency**, governed by (6.2); and
- **Markov transport compatibility**, governed by (R) for every enabled branch and
  successor class.

If `CT2` is intended to assume an already constructed exact compressed transport,
state (R) there explicitly. Then `CT4` is an additional output-sufficiency
condition, not the construction of the WAD cocycle.

## Additional material corrections

### M1. `Theorem 2.1` needs a complete-DFA convention

As written, “a deterministic exact automaton with \(s\) reachable states” is
ambiguous in a project that otherwise uses partial deterministic automata. For
\(\mathcal L=\{\epsilon\}\), a partial automaton with one accepting state and no
edges recognizes the language, while right future-equivalence on all words has two
classes: the class of \(\epsilon\) and the empty-future class. Thus the theorem is
false if the absent dead state is not counted.

Required repair: say “a complete deterministic automaton with at most \(s\)
reachable states, including the dead state,” or formulate the partial version in
terms of live residuals and add at most one dead class. “With \(s\)” should also be
“with at most \(s\)” unless exact state padding is intended.

This issue does not invalidate the exponential lower bounds, which count live
residuals.

### M2. The checkpoint macro changes the theorem category

`Proposition 5.2` is correct as graph contraction at checkpoint resolution after
adding these explicit hypotheses:

- \(x_0\) and \(x_n\) are declared checkpoints;
- \(\tau[n]\) is a fresh resolved token/schema;
- all endpoint frames needed to interpret
  \(\widehat M_\tau^n\) are compatible.

But the proposition deliberately loses every interior prefix, and
\(\{\tau[n]\}\) is a parameterized, generally infinite family of labels across
blocks. Therefore it cannot simultaneously discharge a downstream obligation that
requires:

- a literal finite alphabet of exact labels;
- every layer to occur as an automaton edge;
- every interior Wave/Wanderer, WAD, access, error, or shear event to remain
  inspectable.

The support-pumping proof only uses finite \(Q\) and finite \(d\), so it could be
restated for a finite structural edge-schema with numerical parameters. That is a
new typed-automaton statement, not the ordinary finite automaton currently defined.
The chosen trace resolution must be fixed once and propagated through every
downstream lemma.

### M3. The open counter/stack follower is not yet a formal machine class

The open theorem allows “counter/stack predicates” and numerical fields without
specifying what they may inspect. If an endpoint guard may examine an arbitrary
integer encoding or the entire stack word by an arbitrary predicate, finite control
and one stack impose no auditable complexity restriction. Conversely, a standard
pushdown transition sees only the top symbol (plus empty-stack status).

The theorem should lock:

- whether epsilon transitions are forbidden;
- a universal finite set, or a uniformly bounded set, of additive counter
  increments;
- the permitted counter guards (for example zero tests and fixed affine
  inequalities);
- top-only push/pop/no-op stack access;
- the endpoint acceptance form;
- whether macro parameters are read-only inputs rather than encodable memory.

`Proposition 5.3` applies only under its bounded-increment hypothesis \(C<\infty\);
Section 6 currently does not state a corresponding \(C_0\). A semantic instruction
that counters be “geometric” is valuable but is not a mathematical substitute for a
machine definition.

### M4. A neutral memory transformation does not preserve emitted data

`Lemma 5.3` correctly says when a specified loop preserves the entering augmented
counter/stack **configuration**. It does not say deletion preserves:

- the loop's numerical transfer matrix;
- critical or WAD events emitted inside it;
- accumulated error, Value, or shear moments.

The surrounding text mostly respects this by retaining numerical loop products.
The lemma and every citation should consistently say “configuration-neutral,” not
“deletion-safe” without the additional condition that all proof-used emitted
observables are either retained separately or invariant.

### M5. “Coarsest safe WAD partition” is scoped to a fixed observation family

`Theorem 6.2` is correct among partition-sum quotients for the already complete
family \(\mathscr O\). It is not the coarsest quotient among all linear maps, and it
is not safe if a later proof adds a new observation. The ledger should retain both
qualifiers. `Corollary 6.3` would be more accurately titled “nonnegative
observability witness”; it is unrelated to additive counters.

## Theorems that survive this audit

The following arguments are valid after the small convention changes above.

1. `Lemma 2.1`: block incidence composition.
2. `Lemma 3.1` and `Theorem 3.2`: the reachable, terminal-colored future quotient
   of a finite resolved presentation is a canonical minimal partial trace
   automaton.
3. `Theorem 4.1` and `Lemma 4.2`: a genuinely Markov-complete exact signature
   yields a source-faithful quotient.
4. `Proposition 4.3`: a uniform distinguishing horizon gives the displayed crude
   state bound.
5. `Propositions 3.1`, `3.2`, and `7.1`: fixed alphabet and finite horizon do not
   bound exact future index.
6. `Proposition 3.3`: the union of reverse-copy prefix languages is recognized by
   finite control plus a single LIFO stack; this is only an analogy until reverse
   dynamical unwinding is proved.
7. `Theorem 4.1` of `virtual_language_memory.md`: bounded suffix memory gives the
   stated finite automaton.
8. `Lemma 5.1`: for a fixed continuation, equality (5.2) is exactly the endpoint
   counter-predicate criterion; intermediate guards still require separate checks.
9. `Proposition 5.3`: fixed finite control and fixed bounded-increment additive
   counters have only polynomially many length-\(m\) configurations.
10. `Lemmas 6.1`--`6.3`: the fixed-family linear output-observability statements.

These are useful no-go and conditional construction results. They should remain
classified as internal combinatorial infrastructure, not as evidence that the
virtual analytic realization or Master Transition Lemma has been proved.

## Adversarial acceptance tests to add

Before accepting a virtual automaton handoff, require:

1. **Dimension test:** exhibit explicit universal \(d_0,w_0\), separately from the
   state/signature bound.
2. **Repeated-pair memory test:** prove that the pigeonhole-selected repeated
   summary has identity action on the reachable memory fiber, or do not claim an
   accepted shortened skeleton.
3. **Transport quotient test:** verify
   \(P R_\gamma=\bar R_\gamma P\) for every enabled WAD transport.
4. **Typed-alphabet test:** distinguish the finite structural schema from all
   numerical macro parameters and prove the exact theorem used by downstream
   pumping.
5. **Trace-resolution test:** make every downstream lemma declare whether it uses
   layerwise paths or checkpoint paths.
6. **Machine-class test:** mechanically enumerate the permitted counter and stack
   operations and endpoint guards.
7. **Emission test:** a memory-neutral loop must still carry every removed
   numerical and proof-used observable into the retained loop record.

Until F1--F3 are repaired and analytically realized, the virtual support automaton
remains an open obligation and cannot serve as a completed MLC proof step.

## Remediation status

The abstract formulation defects identified here have been repaired; their analytic
realizations remain open.

1. **F1:** `CT0` now imposes independent bounds \(d\le d_0\), \(w\le w_0\).
   `H2_UNIFORM_CORE_WAD_DIMENSION` records the missing virtual theorem.
2. **F2:** `CTM` now requires exact checkpoint compilation or a finite exact memory
   congruence before pumping. `MEMORY_PROJECTION_PUMPING_NO_GO` is proved and
   `H2_MEMORY_SAFE_PUMPING_COMPILATION` remains open.
3. **F3:** every WAD quotient must satisfy
   \(P_{\rm out}R_\gamma=\bar R_\gamma P_{\rm in}\). The exact criterion is ledger
   node `WAD_TRANSPORT_QUOTIENT_CRITERION`.
4. **M1--M5:** the DFA counts its dead state, macro endpoints/frames and trace
   resolution are explicit, the follower machine class has fixed update/guard
   catalogs, memory neutrality is separated from emissions, and WAD
   output-observability is explicitly scoped to a fixed complete family.

These changes validate the conditional finite-state theorems only. They do not
construct the virtual core, prove universal dimensions, or supply memory-safe
compilation for the dynamical family.
