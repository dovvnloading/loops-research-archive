# Formal research task: virtual core cocycle and follower realization

## 1. Status and decisive target

This is the next analytic construction task in the unified MLC program. It does not
assert MLC or a virtual-hull bound.

The finite automaton algebra is no longer the first missing step. Before it can be
used, the virtual hull must supply an exact source-oriented core/WAD cocycle. Only
then can one ask whether its decorated future language has uniformly finite control
after explicit counters and any necessary nesting stack are retained.

The task is deliberately split into four independently auditable theorems:

1. **Virtual Core-Cocycle Realization (`OPEN`)**: construct the exact raw
   finite-horizon dynamical presentation and its core/WAD labels;
2. **Uniform Counter/Stack-Follower Realization (`OPEN`)**: prove a universal
   restricted machine description after all honest unbounded memory is exposed;
3. **Uniform Core/WAD Dimension (`OPEN`)**: prove universal core and compositional
   WAD quotient dimensions independently of any finite signature count;
4. **Memory-Safe Pumping Compilation (`OPEN`)**: compile memory-changing runs into
   exact checkpoint macros, or construct a finite memory congruence on which every
   pumped repetition is exact.

Conflating these steps can hide a nonexistent dynamical branch, an unbounded
follower index, an unbounded transfer module, or a projected loop that is not
dynamically admissible.

### 1.1 Post-spectral-repair critical path

The finite clone spectrum is no longer an open subproblem. Once an exact literal
common-delay graph has been constructed, the corrected theorem supplies its return
operator, multiplier, fixed-template limits, and typed gate eigenvectors. Therefore
the translation-clone branch now reduces to five concrete realization obligations:

1. **complete edge occurrence:** construct the raw finite-horizon core multigraph and
   prove that no critical, immersion, or WAD-relevant branch is omitted;
2. **literal corridor purity:** after bounded endpoint absorption, every interior
   edge is exactly the declared label-preserving chain edge, with no side incidence;
3. **uniform gate data:** prove universal gate dimension \(d\le d_0\) and actual
   maximum first-return edge length \(K\le K_0\);
4. **delay and recurrence:** prove the surviving common delay satisfies \(n>K\), the
   return matrix is non-permutation, and any KKL aperiodicity hypothesis is certified
   separately;
5. **source/WAD activation:** prove \(B=N^{\mathsf T}\) for the realized core,
   realize every WAD itinerary entering Value, prove the coefficientwise domination
   \(Y\le(f^r)^*X+E\) for an actual pullback exponent \(r\ge n\), where \(n\) is the
   literal clone delay, and bound the outgoing error in the same Value units.

Items 1--4 activate the internal factor \(<2^{-1/(2d_0)}\). Item 5 is what makes
that finite graph estimate a dynamical KKL block. Failure of any one item routes the
word away from the clone branch; it may not be repaired by fitting a weighted matrix
afterward.

## 2. Input datum

Fix one virtual-Molecule complete block. Its input must include:

1. the canonical finite portion
   \[
     \mathcal M^{(0)}\supset\mathcal M^{(1)}
     \supset\cdots\supset\mathcal M^{(N)}
   \]
   of the nested satellite-copy chain actually used by the block;
2. the corresponding small-Julia/Cantor carrier and every critical-orbit point
   through the last first return used downstream;
3. every prime-end access, ideal interval, WAD support class, Wave/Wanderer segment,
   and checkpoint used before the block closes;
4. the selected partial returns and their stopping times;
5. the incoming and outgoing core frames, chart type, and port/ribbon order.

The integer \(N\), return times, satellite periods, and marked horizon may be
unbounded. They are input side data, not homogeneous geometric coordinates.

## 3. The raw realization theorem

### Virtual Core-Cocycle Realization (`OPEN`)

For every input datum in Section 2, construct a finite resolved presentation
\[
  \mathfrak P_B=(X_B,x_B,\Gamma_B,\delta_B,o_B,\widehat M_B,\rho_B)
\tag{3.1}
\]
with the following properties.

#### `VC1` Analytic carrier

The proposed connected virtual hull is fullified and subdivided into a marked ribbon
cell carrier. Every declared access is realized by the required prime-end interval,
and every selected return branch is proper on its declared domain through the stated
stopping time.

#### `VC2` Exact branch resolution

Every multivalued pullback correspondence is split into deterministic branch tokens.
Token paths are exactly the selected dynamical paths. No word is accepted merely
because its local cell types concatenate.

#### `VC3` Typed source-column core identity

For each token \(\gamma\),
\[
  B_\gamma:\mathbb R^{E_{\rm in}(\gamma)}
  \longrightarrow\mathbb R^{E_{\rm out}(\gamma)}
\]
is the actual Hubbard/core pushforward, in the convention
\[
  (B_\gamma)_{ij}
  =
  \#\{\text{occurrences from source }j\text{ to target }i\}.
\tag{3.2}
\]
Chronological words use \(B_m\cdots B_1\). The construction supplies an explicit
typed bridge to the KKL Value incidence: if
\[
  N_{\beta\gamma}
  =
  \#\{\text{occurrences from source }\beta\text{ to target }\gamma\},
\]
then \(B=N^{\mathsf T}\), KKL \(v\) is the project left eigenweight, KKL \(w\) is
the project right eigenweight, and Value uses \(v^2w\). It does not rely on the
orientation-ambiguous source symbol \(T_F\), or fit a graph after computing a
desired spectral radius.

#### `VC4` WAD incidence

The upper-right and WAD blocks of
\[
  \widehat M_\gamma=
  \begin{pmatrix}
    B_\gamma&C_\gamma\\
    0&R_\gamma
  \end{pmatrix}
\tag{3.3}
\]
are the actual selected WAD transport and WAD-to-core incidence used by Value.
Every future Value, port, error, and shear observation used before closure is listed.

#### `VC5` Endpoint frame

The initial and terminal frame are part of the presentation. A word is called an
entropy return only if it closes to the same framed state or carries a separately
proved canonical source endpoint identification. Open words receive no intrinsic
spectral classification.

#### `VC6` Horizon completeness

Every critical visit, access split, WAD restriction, mixing witness, and
Wave/Wanderer pullback used later occurs before its information is discarded.
Stagewise forward closure and the selected degree-two factorization are verified
through the same horizon.

This theorem is allowed to have state, alphabet, and WAD dimensions depending on the
finite input horizon. Its purpose is exactness, not uniformity.

## 4. Honest memory factorization

Starting from (3.1), partition the state needed by future admissibility into four
noninterchangeable mechanisms.

1. **Finite decorated control:** local marked-cell mode and a bounded suffix.
2. **Geometric additive counters:** exact clone lengths, return clocks, or depths
   with declared bounded update rules and endpoint guards.
3. **Parameterized checkpoint macros:** a checkpoint-pure run
   \(\tau[n]\) carrying \(n\) and \(\widehat M_\tau^n\); it does not retain layerwise
   prefixes.
4. **Finite-alphabet stack:** an ordered nesting word
   \(\omega\in\mathcal T^*\), allowed only after source dynamics proves matched
   push/pop, LIFO order, no skipping, and predecessor frame/WAD recovery.

An opaque integer encoding of the entire itinerary is forbidden. A depth counter
cannot replace the labeled nesting word unless their decorated future languages are
proved equal. Projecting these mechanisms away does not create an exact finite
automaton: the one-control-state language
\(\operatorname{Pref}\{a^n b\}\) has repeated projected control/support pairs but no
deletable positive \(a\)-loop at the prescribed exit. This is the
memory-projection pumping obstruction in `virtual_language_memory.md`, Section 5.

## 5. The uniform compression package

### Uniform Counter/Stack-Follower Realization (`OPEN`)

There are universal
\[
  a_0,m_0,R_0,k_0,t_0,C_0,g_0<\infty
\tag{5.1}
\]
such that every raw presentation from Section 3 admits a machine with:

1. at most \(k_0\) declared additive counters;
2. an optional stack alphabet of size at most \(t_0\);
3. at most \(m_0\) finite modes and suffix memory at most \(R_0\);
4. a structural token catalog of size at most \(a_0\), after matrix, macro,
   counter, and stack fields are separated;
5. no hidden epsilon computation;
6. counter increments from a fixed catalog with norm at most \(C_0\), and guards
   from a fixed catalog of zero tests and bounded affine/residue predicates;
7. top-symbol/empty-stack push, pop, and no-op only, with no arbitrary full-word
   predicate;
8. read-only numerical macro parameters, a fixed trace resolution, and explicit
   endpoint acceptance using at most \(g_0\) declared guards;
9. exact equality of decorated futures for every merged finite-control pair, while
   every emitted transfer, critical/WAD, Value, error, and shear record is retained.

Counting present cell shapes is insufficient, and one integer with arbitrary
decoding is not a geometric one-counter theorem.

### Uniform Core/WAD Dimension (`OPEN`)

There are universal \(d_0,w_0<\infty\) such that every raw presentation admits:

1. a source-faithful core module of dimension \(d\le d_0\);
2. a retained WAD module of dimension \(w\le w_0\);
3. for every enabled raw WAD transport, quotient maps satisfying
   \[
     P_{\rm out}R_\gamma=\bar R_\gamma P_{\rm in};
   \]
4. output observability for the complete fixed family of future core-incidence,
   Value, port, response, error, and shear observations.

This is independent of the control-state theorem. The family with one state and one
loop \(B=I_d\) has one signature for every \(d\), so bounded signatures do not bound
the core dimension. Likewise, output observability alone does not construct a
compositional WAD quotient.

### Memory-Safe Pumping Compilation (`OPEN`)

At one declared layerwise or checkpoint trace resolution, prove one of:

1. every repeated pumping summary acts identically on every relevant reachable
   counter/stack fiber; or
2. the summary includes a finite memory congruence with that property; or
3. every memory-changing run is compiled into an exact typed checkpoint macro before
   the exact finite-state automaton and support-pumping theorem are invoked.

The theorem must preserve endpoint frames, guards, terminal colors, and all emitted
observables. A configuration-neutral loop is not emission-neutral, and the
pigeonhole argument cannot be instructed after the fact to “choose a safe loop.”

Only after these three open theorems are proved may a Markov-complete signature or
uniform distinguishing-horizon theorem provide the exact finite automaton.

## 6. Closed-return routing

After all parts of Section 5, apply support pumping only to the exact compiled
finite-state language. Preserve the ordered nested insertion history and every
emitted numerical record. Every complete framed return must then be routed to
exactly one of:

1. an exact clone block satisfying all corridor-purity and cross-section clauses;
2. a source-licensed primitive positive-entropy block;
3. transient extinction;
4. pseudo-Siegel/sectorial regularization;
5. a calibrated finite shear state inside a complete block with proved strict
   contraction.

For Item 1, once the literal common-delay graph is proved, the spectral equation is
no longer an additional conjecture: `corrected_clone_theorem_derivation.md` supplies
\[
  H(t)=\sum_k t^{-k}R_k,
  \qquad
  \rho(H(\lambda_n))=\lambda_n^n.
\]
Uniform contraction still requires universal gate dimension and actual return depth,
plus \(n>K\). KKL Value additionally requires its separate WAD/source hypotheses
and an actual pullback exponent at least as large as the graph delay.
Permutation interiors do not by themselves discharge Item 1. A cyclic support
component does not discharge Item 2 unless the return is closed, repeatable, and
source identified.

## 7. Required proof artifacts

Completion requires all of:

1. a cell-by-cell carrier and branch-domain definition;
2. a path-lifting proof in both directions between tokens and selected dynamics;
3. the exact source-column matrix and WAD-incidence formulas;
4. a table of every counter, its semantics, update, reset, and guard;
5. either a proof that no stack is needed or a complete push/pop theorem;
6. the Markov-complete signature and its universal cardinality bound;
7. separate proofs of the universal \(d_0,w_0\) module bounds;
8. every WAD transport-quotient commuting square and the full future-observation
   matrix;
9. the exact memory-congruence or checkpoint-compilation proof;
10. a framed-return/holonomy table for every spectral block;
11. the raw incidence table \(N\), the identity \(B=N^{\mathsf T}\), and the
    left/right Value-weight translation;
12. an independent short-word lifting test and a backward dependency audit.

## 8. Adversarial suite

Any proof must defeat:

1. the copy language \(x\#x\), which has exponential future index;
2. the exact exit language \(a^n b\), which cannot be a free loop;
3. the reverse-copy language \(x\#x^{\rm rev}\), which exposes stack memory;
4. two equal-depth satellite words with different rotations or decorations;
5. an access or WAD class that splits only after the proposed merge;
6. a hidden critical branch entering a nominally pure corridor;
7. a permutation interior with a side edge or a non-cross-sectional gate;
8. an open transfer whose Perron root changes under endpoint relabeling;
9. a transient zero SCC mislabeled as branching;
10. a nonzero counter loop accepted on one fiber but not another;
11. a macro whose discarded interior contains a proof-used event;
12. a number of independent clocks or WAD profiles growing with \(N\);
13. one control state carrying \(I_d\) with \(d\to\infty\);
14. a WAD quotient that preserves present outputs but violates
    \(P_{\rm out}R=\bar RP_{\rm in}\);
15. the KKL clone recurrence with the printed \(+\lambda^k\) exponent on the
    three-vertex counterexample in `kkl_transfer_orientation_audit.md`;
16. a nominal clone with \(n/K\to0\), which defeats any delayed uniform multiplier;
17. a one-sided perturbed transition with unbounded added multiplicity, which
    defeats uniform Perron-cone compactness.

## 9. Success and failure criteria

Success is a checkable proof of all four open theorems with constants independent of
period, molecule depth, and horizon, followed by the closed-return routing of
Section 6.

A valid negative result is an explicit virtual dynamical family for which one of
\[
  k_0,\quad t_0,\quad m_0,\quad R_0,\quad d_0,\quad w_0
\]
must diverge, together with the exact additional memory or geometric invariant
required. Numerical experiments may locate such a family but cannot discharge the
proof.

## 10. Ledger interface

This task directly targets:

- `H2_VIRTUAL_CORE_COCYCLE_REALIZATION`;
- `H2_UNIFORM_COUNTER_FOLLOWER`;
- `H2_UNIFORM_CORE_WAD_DIMENSION`;
- `H2_MEMORY_SAFE_PUMPING_COMPILATION`;
- `H2_VIRTUAL_SUPPORT_AUTOMATON`;
- the source part of `H2_VIRTUAL_CORRIDOR_GRAPH_REALIZATION`;
- the source/frame part of `H2_VIRTUAL_TRANSFER_TRICHOTOMY`.

Its proved abstract inputs are:

- `SOURCE_FUTURE_QUOTIENT`;
- `MARKOV_SIGNATURE_AUTOMATON`;
- `WAD_TRANSPORT_QUOTIENT_CRITERION`;
- `WAD_FUTURE_OBSERVABILITY`;
- `MEMORY_PROJECTION_PUMPING_NO_GO`;
- `PURE_CORRIDOR_MACRO`;
- `COUNTER_STACK_SAFE_LOOP`;
- `FRAMED_RETURN_SPECTRAL_INVARIANCE`;
- `KKL_TYPED_VALUE_INCIDENCE`;
- `KKL_PRINTED_CLONE_EQUATION_NO_GO`;
- `KKL_CLONE_EIGEN`;
- `SUPPORT_AUTOMATON_PUMPING`.

No dependency runs from those abstract inputs to analytic realization. They specify
what must be verified once the virtual dynamics has been constructed.
