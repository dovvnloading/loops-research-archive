# Source research: a finite automaton for the virtual-Molecule hull

> **Post-audit correction (2026-07-23).** A later complete orientation/clone audit
> found that KKL's symbol \(T_F\) has incompatible orientation cues and that the
> printed \(+\lambda^k\) finite-\(n\) clone equation is false under the literal
> definitions on an explicit primitive graph. The safe live source lock is raw
> incidence \(N\), project \(B=N^{\mathsf T}\), KKL \(v,w\) as project
> left/right, and Value \(v^2w\). The abstract clone *definition* and parabolically
> bounded cross-section construction remain useful. The printed spectral bridge is
> still rejected, but `corrected_clone_theorem_derivation.md` independently proves
> the literal \(t^{-k}\) equation, limits, and typed gate-eigenvector convergence.
> Later sections below distinguish this internal theorem from the source claim.

## 1. Question and verdict

This note audits whether the existing literature constructs, or can be quoted to
construct, the finite source-faithful automaton required in
`corridor_support_automaton.md` and `virtual_language_memory.md`.

The short answer is:

> **No source checked proves a uniformly finite, WAD-decorated automaton for
> Dudko's virtual Julia-set hull.**

There is, however, a precise positive model:

1. a prime primitive \(\psi\)-quadratic-like map has a finite Hubbard-tree core
   transition;
2. in KKL's parabolically \(b\)-bounded setting, a bounded part of that tree is a
   cross section;
3. increasing the parabolic corridor length supplies the stated cross-section clone
   syntax;
4. the clone length is retained as an explicit unbounded integer, while the printed
   \(h(\lambda)=\lambda^n\) bridge is replaced by the independently proved
   negative-weight literal-graph equation documented above.

This is the closest source precedent for finite control plus a retained length, but
not a source proof of that spectral equation. The internal theorem is available once
the literal graph is realized. The construction uses the prime primitive
\(\psi\)-ql structure and the parabolic \(b\)-bound. Dudko's virtual hull has
neither structure supplied a priori.

The primary-source audit also gives two important no-shortcut results:

- general postcritically infinite Hubbard trees can be infinite, including for
  complex-admissible quadratic combinatorics;
- even a finite topological Hubbard tree can contain infinitely many distinct
  postcritical points, so "the carrier is a finite tree" does not by itself bound
  the marked postcritical data or prove a bounded follower language.

The correct next theorem is therefore not merely "construct a finite tree." It is
a **decorated counter/stack-follower extraction theorem**: construct a raw
finite-horizon carrier, factor all exact unbounded lengths into universally many
explicit counters, retain any ordered history in a source-faithful
finite-alphabet stack when necessary, and prove a universal bound on the remaining
decorated future-equivalence index.

There is also no source-licensed shortcut from the nested satellite-copy sequence
to a pushdown model. D25 and KKL supply an ordered chain; they do not prove LIFO
antirenormalization, matched push/pop identities, or recovery of a virtual-hull
state after a pop.

This report does not promote MLC or any virtual-hull realization lemma.

## 2. Five assertions that must not be conflated

For one finite-horizon block, the following are distinct.

1. **Finite raw carrier.** A finite tree or finite union of puzzle pieces contains
   the orbit segment used through the declared horizon.
2. **Finite core transition.** A finite graph carries the exact edge-pushforward
   multiplicities of the selected dynamics.
3. **Exact dynamical language.** Every accepted graph concatenation is a permitted
   dynamical concatenation, and dynamically distinct futures are not merged.
4. **WAD/source faithfulness.** Critical branches, accesses, ideal intervals, and
   every WAD-to-core incidence used by Value are outputs of the same transition
   system.
5. **Uniformity.** State dimension, follower index, memory radius, number of
   counters, and defect complexity are independent of the satellite periods,
   virtual-Molecule depth, and finite postcritical horizon.

The checked sources prove useful instances of Items 1--3. KKL proves the needed
core/WAD compatibility in its own prime primitive setting. No checked source proves
Items 1--5 together for the virtual hull.

## 3. Source lock

All TeX line numbers below refer to the files and hashes in this table, retrieved
2026-07-23. The hash, rather than an arXiv abstract, is the controlling source lock.

| ID | Primary source | Locked file | SHA-256 |
|---|---|---|---|
| D25 | D. Dudko, [*On the MLC Conjecture and the Renormalization Theory in Complex Dynamics*](https://arxiv.org/abs/2512.24171) | `main.tex` | `FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454` |
| KKL26 | J. Kahn, A. Kapiamba, M. Lyubich, [*MLC for parabolically bounded primitive renormalization*](https://arxiv.org/abs/2606.27272) | `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| KKL26-D | same | `not-all-good2.tex` | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` |
| K06-H | J. Kahn, [*A priori bounds ... I. Bounded primitive combinatorics*](https://arxiv.org/abs/math/0609045) | `hubbard2.tex` | `3015AC25298F1C22F54F232A726CF4A087DA276CBC6F4534216A3537FE6AE8C6` |
| K06-E | same | `entropy2.tex` | `FDB92C6DE5DF5EAC6EBE66471B2C9587513FC0BB9E3154234DA8061DC97A30AB` |
| KL08 | J. Kahn, M. Lyubich, [*A priori bounds ... II. Decorations*](https://arxiv.org/abs/math/0609046) | `kingdom.tex` | `5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7` |
| KL09 | J. Kahn, M. Lyubich, [*A priori bounds ... III. Molecules*](https://arxiv.org/abs/0712.2444) | `kingdom.tex` | `16E467B6810B69581DFEA1A748191FFBCC25E01DC61556C417F67209C3A7DF43` |
| HS24 | M. Hassler, D. Schleicher, [*Combinatorial Hubbard trees for postcritically infinite unicritical polynomials and exponential maps*](https://arxiv.org/abs/2401.10378) | `H_trees_180124_DS.tex` | `95F59BE5231DE8E51EA8C3E8E666C0DAE44EF5BABD72E4D61D1586D5956D05EC` |
| AF00 | L. Alsedà, N. Fagella, [*Dynamics on Hubbard trees*](https://doi.org/10.4064/fm-164-2-115-141), [official PDF](https://matwbn.icm.edu.pl/ksiazki/fm/fm164/fm16422.pdf) | `fm16422.pdf` | `6BFB2098DE78E80E4CA515559213BBD860B8AF8088A7AB30362589A68C9E8F6E` |

Source-lock identifiers for the audited files are:

- D25: `source-lock/Dudko25`;
- KKL26: `source-lock/KKL26-v1`;
- the remaining sources:
  `source-lock/automaton-sources-20260723`.

## 4. Exact theorem ledger

### 4.1 Dudko: the virtual hull is a proposed strategy, not a construction

**Source locations.** D25 `main.tex`:

- lines 746--746 identify the interpolation obstruction: the postcritical set can
  look dense and its entropy can blow up near the Molecule;
- lines 875--881 define the virtual-Molecule scale interval and its virtual
  bounded-satellite/near-neutral subcases;
- lines 885--889 state Interpolation Problem 4.4 and say the proposed programs
  *should* imply full MLC;
- lines 891--892 propose partially invariant virtual Julia sets as connected hulls
  of Cantor small Julia sets containing the critical orbit through an appropriate
  number of first returns.

**What is available.**

- a canonical nested sequence of satellite copies for the primitive type under
  discussion;
- the proposed carrier and the principle of a partial postcritical horizon.

**What is absent.**

- no definition of a finite graph or transition states;
- no Markov partition or follower-language theorem;
- no bound on the number of first returns required;
- no bound on active branch/access complexity;
- no WAD-to-core incidence construction;
- no proof that the connected hull carries a selected degree-two correspondence;
- no uniform state, memory, or counter bound.

**Ledger status:** `OPEN PROPOSAL`.

### 4.2 Focused stack audit: an ordered chain is not a LIFO theorem

**Verdict.**

> **Neither D25 nor KKL26 proves LIFO antirenormalization for the nested
> virtual-Molecule satellite chain.**

The sources prove or state ordered nesting. D25 also reports a repeatable
one-level antirenormalization mechanism for neutral pseudo-Siegel disks. They do
not define a stack on the virtual chain, identify its frames, or prove matched
last-in/first-out recovery.

#### D25: what the two relevant passages actually say

**Virtual-Molecule passage, D25 `main.tex`, lines 875--892.**

- Lines 875--879 associate to one primitive first quadratic-like
  renormalization a finite canonical parameter-space inclusion chain
  \[
    \mathcal M^{(0)}\supsetneq\mathcal M^{(1)}
    \supsetneq\cdots\supsetneq\mathcal M^{(\nu+1)}.
  \]
  Each successor is a maximal satellite subcopy, and the terminal placement of
  the primitive copy is specified by decorations.
- Line 881 uses this ordered chain to identify the scale interval called the
  virtual Molecule and its two stated subcases.
- Lines 885--892 then pose the Virtual Molecule Near-Degenerate Regime as an
  interpolation problem and propose partially invariant connected hulls through
  an appropriate number of first returns.

This is a canonical *order of nested parameter copies*. The passage does not
define push maps, pop maps, an antirenormalization operator on the virtual hulls,
or an identity recovering the predecessor hull and its critical/access data.

**Neutral-sector passage, D25 `main.tex`, lines 846--867.**

- Theorem `thm:wZ`, lines 846--849, reports uniform pseudo-Siegel bounds for the
  neutral family.
- Lines 851--859 describe nested pseudo-Siegel disks and their index shift under
  sector renormalization.
- Line 862 says that, after regularization,
  \(\widetilde Z^{-1}_{f_n}\) becomes
  \(\widetilde Z^{0}_{f_{n-1}}\) under sector antirenormalization and that the
  procedure can be repeated.
- Line 864 labels the contracting-error discussion informal before pointing to
  the cited neutral theory. Line 867 describes extension of the construction to
  the remaining satellite setting as a strategy and says full realization would
  imply the satellite case of MLC.

Thus line 862 licenses a survey-level, one-step reverse-index mechanism in the
neutral pseudo-Siegel setting. It does **not** assert that the distinct
\(\mathcal M^{(s)}\) of lines 875--879 are pushed and popped by that mechanism.
It does not state no-skipping, matched returns, frame recovery, or compatibility
with the virtual connected hulls of line 892.

#### KKL26: a unique chain and a forward renormalization, but no pop

**Source locations.** KKL26 `waves-with-Misha.tex`:

- lines 299--303 give, for every prime primitive type \(M\), a unique infinite
  sequence \((M_n)\) of nested satellite subcopies, eventually of
  \(1/2\)-type, and define the molecule-depth statistic \(\ell(M)\);
- lines 315 and 326--338 use \(\ell\) to name the virtually-satellite regime and
  list virtual near-Molecule renormalization among the anticipated theories;
- lines 373--381 call these primitive regimes remaining cases and say the
  virtual renormalization is to appear elsewhere and is only briefly sketched in
  D25;
- lines 478--491 define one canonical **forward** \(\psi\)-ql
  renormalization \(\mathcal R F\) under prime primitive hypotheses.

The unique sequence in lines 299--303 is a parameter-space/combinatorial
classification. KKL26 defines no antirenormalization of that sequence and proves
no inverse or predecessor-recovery identity for \(\mathcal R F\). The finite D25
chain and the infinite KKL26 chain are visibly analogous, but neither locked
text states a theorem identifying the former with a particular truncation of the
latter together with compatible dynamical operators.

#### Exact proof obligations for a stack interpretation

For frames \(\sigma_s\) attached to successive satellite levels, a
source-faithful LIFO theorem would at minimum have to construct:

1. a push \(P_s\) that records all proof-relevant data when level \(s+1\) is
   entered;
2. a pop \(A_s\) defined on the resulting virtual hull/chart, with
   \(A_sP_s=\mathrm{id}\) in a specified analytic or combinatorial equivalence;
3. a no-skip/no-permutation statement showing that a depth-\(r\) composition
   pops the frames in the order
   \(\sigma_r,\sigma_{r-1},\ldots,\sigma_1\);
4. recovery after each pop of the critical-orbit horizon, accesses, WAD
   incidences, and the next permitted transition;
5. uniform compatibility at neutral/satellite/primitive chart changes.

No such maps or identities occur in the audited D25 or KKL26 passages.
Set-theoretic nesting supplies a total order but not operational stack semantics.
In particular, depth alone cannot be substituted for the sequence of rotation,
decoration, and return labels without a separate future-equivalence theorem.

**Ledger status:** `ORDERED CHAINS IMPORTED`; `NEUTRAL ONE-STEP MECHANISM REPORTED
IN ITS OWN SETTING`; `VIRTUAL LIFO ANTIRENORMALIZATION OPEN`.

### 4.3 KKL: finite Hubbard-core transition in the prime primitive setting

**Source locations.** KKL26 `waves-with-Misha.tex`:

- lines 439--461 define a \(\psi\)-ql map and its fiber-product iterates;
- lines 478--490 define prime primitive renormalization, the small Julia cycle,
  localization, and the canonical \(\psi\)-ql renormalization;
- lines 512--535 define the Hubbard tree, its vertices and edges, and the
  pushforward \(T_F\);
- lines 542--543 pass to a rational-lamination combinatorial model when the filled
  Julia set is not locally connected.

For a primitively renormalizable, periodically repelling \(\psi\)-ql map, KKL takes
the smallest connected subset of the filled Julia set containing the finite cycle
of small filled Julia sets. Define its raw source-to-target occurrence incidence by
\[
  N_{\beta\gamma}
  =
  \#\{\alpha\in\iota^*\beta:f_*\alpha=\gamma\}.
\]
The Value coordinate sums give
\[
  Nv=\lambda_Fv,\qquad N^{\mathsf T}w=\lambda_Fw.
\]
The project's source-column count map is \(B=N^{\mathsf T}\). The source symbol
\(T_F\) cannot itself be orientation-locked consistently, so it is not used as the
bridge.

This is a genuine typed source incidence for the core transition used by KKL Value.
It is not a theorem about an arbitrary connected hull of Cantor small Julia sets.

**Ledger status:** KKL Value is `IMPORTED` only under the stated prime primitive,
periodically-repelling \(\psi\)-ql hypotheses; the \(N/B\) and left/right translation
is the proved internal node `KKL_TYPED_VALUE_INCIDENCE`.

### 4.4 KKL: abstract finite cross-section cloning

**Source locations.** KKL26 `waves-with-Misha.tex`, lines 2236--2318:

- lines 2240--2244 define a cross section \(E\) of a finite directed graph \(A\);
- lines 2245--2251 define the length-\(n\) clone and separately assume primitivity
  of all cloned graphs;
- lines 2255--2268 construct the finite labeled reduced graph \(\widehat A\) on
  \(E_0\), independent of clone length once \(n>N\);
- Theorem `thm:clone-eigen`, lines 2270--2278, states
  \[
    h(\lambda_n)=\lambda_n^n,\qquad
    \lambda_n\to1,\qquad
    \lambda_n^n\to h(1).
  \]

The printed finite-\(n\) equation does not follow from the literal preceding
definitions. The primitive three-vertex counterexample in
`kkl_transfer_orientation_audit.md`, Section 6.1, satisfies the actual clone equation
\(\lambda_n^{n+3}=\lambda_n+1\), while the printed \(+\lambda^k\) reduction would
force \(\lambda_n^n=\lambda_n^{n+5}\). The limiting behavior still holds for that
example, so the finite-\(n\) source bridge is refuted. The general literal-graph
limit is now independently proved in `corrected_clone_theorem_derivation.md`.

The intended reduced graph is a finite-control model with one explicit length
parameter. That parameter is not pumped away; any corrected spectral equation must
retain it.

The theorem starts with a finite graph, a cross section, and primitive clones. It
does not construct any of them from dynamics.

**Ledger status:** clone definition imported as source data;
`KKL_PRINTED_CLONE_EQUATION_NO_GO` proved internally;
`KKL_CLONE_EIGEN` proved internally by the negative-weight correction.

### 4.5 KKL: dynamical clone realization under parabolic \(b\)-boundedness

**Source locations.** KKL26-D `not-all-good2.tex`:

- Lemma `lem:get-around`, lines 74--105, proves a return bound
  \(N=N(b)\) using at most \(b\) small Julia sets in the critical limb;
- Corollary `cor:cross-section`, lines 107--120, makes
  \(E(\mathcal T)\cap\mathcal L_{b+1}\) a cross section;
- Proposition `prop:eigenweights`, lines 131--157, states that there are finitely
  many parabolically \(b\)-bounded types at the fixed base rotation
  \(q=2b+2\), identifies larger \(q\) with cloning of that tree cross section,
  and applies the clone theorem.

The hypotheses supplying \(b\) are in KKL26 `waves-with-Misha.tex`, lines 661--671:
each limb contains at most \(b\) small Julia components, and critical-limb
components move only into \(O(b)\) neighboring limbs.

This is the strongest positive precedent found. For fixed \(b\), it gives:

- finitely many finite base templates;
- a bounded return/cross-section depth depending on \(b\);
- an exact translation corridor obtained by cloning;
- source identity with the Hubbard transition used for Value.

It does **not** give constants independent of \(b\), nor does it apply to a virtual
hull before a prime primitive \(\psi\)-ql realization has been constructed.

**Ledger status:** `IMPORTED SPECIAL-CASE REALIZATION`.

### 4.6 KKL WAD support is finite relative to topology, not uniformly finite

**Source locations.** KKL26 `waves-with-Misha.tex`:

- lines 1842--1865 permit countable ideal markings;
- lines 1901--1908 bound a WAD support by
  \[
    3|\chi(\mathcal V)|+|\mathcal I|;
  \]
- inner translation marking lines 1004--1018 has
  \(N=2(n+1)p\) intervals with \(p\le b\);
- outer translation marking lines 1040--1048 has cardinality at most \(4bq\).

Consequently the WAD theorem gives a finite support only after the topology and
ideal marking are finite. It does not bound their cardinalities universally. In the
parabolic application, raw marking cardinality is allowed to grow with \(q\).

A translation quotient may compress this growth, but that quotient and its future
faithfulness are additional theorems.

**Ledger status:** `IMPORTED RELATIVE BOUND`; no universal virtual state count.

### 4.7 KKL path itineraries do not give an exact finite language

**Source locations.** KKL26 `waves-with-Misha.tex`, Proposition
`prop:itineraries`, lines 2092--2108.

For one path and one immersion, the proposition produces a finite sequence of
refined ideal intervals describing restrictions of that path. The proposition:

- is existential rather than a unique coding;
- gives no uniform bound on the sequence length;
- ignores pullbacks that are not paths in the refined marking or are subordinate
  to one interval (lines 2096--2097);
- does not assert closure under concatenating two itinerary sequences;
- does not identify a finite right congruence or follower-equivalence relation;
- does not carry the full future WAD output required by the virtual automaton.

The proof of WAD domination at lines 2113--2124 is an extremal-width relation. It is
not a regular-language recognition theorem.

**Ledger status:** `IMPORTED POINTWISE ITINERARY`; `EXACT DECORATED LANGUAGE` remains
open.

An additional caution: KKL26-D lines 705--748 contain a proposed limiting
translation-invariant arc-diagram argument inside a TeX `comment` environment,
including an explicitly labeled proof sketch. It is not an active theorem and is
not imported here.

### 4.8 Kahn 2006: a finite period-\(p\) model, with \(p\)-dependent size

**Source locations.**

K06-H `hubbard2.tex`:

- lines 9--44 replace a primitively period-\(p\) renormalizable quadratic(-like)
  map by a critically periodic superstable model and transfer arcs/WAD
  combinatorics by a Thurston equivalence;
- lines 47--92 construct its Hubbard disked tree with the \(p\) immediate-basin
  disks;
- lines 234--243 define the finite aligned-arc transition matrix and prove
  expansion over \(p\) iterates.

K06-E `entropy2.tex`:

- Theorem `loss-F`, lines 4--19, loses half the horizontal weight after \(8p\)
  iterates;
- lines 43--56 use \(|\operatorname{supp}X^0|\le3p\) to find an invariant support
  by time \(3p\);
- lines 120--123 align the surviving support with the Hubbard tree;
- lines 201--219 complete the entropy estimate.

This gives a finite, exact period-\(p\) combinatorial model and proves useful bounds
linear in \(p\). When relative periods are bounded, it is a valid special-case
finite-complexity model. It does not provide a period-independent automaton for
unbounded \(p\), and its Thurston equivalence starts with one ordinary primitive
renormalization, not Dudko's virtual hull.

**Ledger status:** `IMPORTED SPECIAL CASE`; no virtual uniformity.

### 4.9 Decorations and anti-Molecule results give bounded top puzzles only

#### Decorations

KL08 `kingdom.tex`:

- lines 21--53 construct the top Yoccoz puzzle;
- lines 89--118 encode escape by parameters \((q,n)\); the top piece has \(2^n\)
  vertices and records all relevant preimages through depth \(qn\);
- lines 140--155 give \(2^n\) disjoint univalent pullbacks at those vertices;
- lines 198--220 construct the modified principal nest, whose height and final
  renormalization period are additional data;
- lines 247--257 state that the decoration condition is equivalent to bounded
  \((q_n,n_n)\) along the renormalizations.

A fixed finite family of decorations therefore bounds the top-puzzle templates.
It does not bound arbitrary virtual-Molecule chains, and it does not state a
WAD-decorated finite automaton for the complete principal nest.

#### Molecule condition

KL09 `kingdom.tex`:

- lines 167--204 define the molecule condition by recording qualified primitive
  renormalizations and staying a definite distance from the Molecule;
- lines 206--252 show this is equivalent to bounded combinatorial parameters
  \((r,q,n)\);
- lines 280--284 set the top depth \(k=rqn\);
- lines 382--407 show that the top puzzle through this depth depends on those
  bounded parameters;
- lines 410 onward enter the deeper, return-dependent modified principal nest.

This supplies finite top-level combinatorial types for families uniformly away from
the Molecule. Dudko's virtual-Molecule interpolation problem is precisely the scale
range where anti-Molecule control fails. Allowing the distance \(\eta\to0\) lets the
bounding parameters diverge.

**Ledger status:** `IMPORTED ANTI-MOLECULE SPECIAL CASE`; not a bridge across the
virtual regime.

### 4.10 Classical Hubbard-tree Markov coding is postcritically finite

AF00, p. 130, Theorem 2.9 and Remark 2.10:

- a finite forward-invariant vertex set containing endpoints and branch points
  gives a finite transition matrix for a tree map;
- for a monotone Markov tree map, the entropy is the logarithm of the spectral
  radius;
- the Hubbard-tree restriction in their quadratic Misiurewicz setting is
  semiconjugate to the corresponding subshift of finite type.

This is the clean primary source for the finite-state Markov paradigm. Its setting
is a postcritically finite quadratic Misiurewicz polynomial. It neither constructs
the virtual hull nor attaches KKL WAD/access outputs to the coding.

**Ledger status:** `IMPORTED PCF MARKOV MODEL`.

### 4.11 General postcritically infinite Hubbard trees are not uniformly finite

HS24 supplies the sharpest adversarial boundary.

**Source locations.**

- lines 93--125 construct symbolic Hubbard trees from the full kneading sequence;
  they state that the trees may be infinite and may fail to be reconstructible
  from the dynamical Julia set;
- lines 456--494 construct the finite truncations
  \[
    H_n=\bigcup_{k=0}^{n}\sigma^k(C_\nu);
  \]
- lines 528--535 define the global tree as the infinite union of these
  truncations;
- lines 1028--1034 give a finite topological tree with an infinite postcritical
  orbit;
- lines 1043--1045 give the Feigenbaum interval as another finite-tree,
  postcritically infinite example;
- lines 1050--1059 give complex-admissible internal addresses whose Hubbard trees
  have infinitely many periodic branch orbits and infinitely many endpoints.

Three exact conclusions follow.

1. A finite horizon has a canonical finite **symbolic** raw tree \(H_n\).
2. Its complexity is allowed to grow with \(n\); no uniform quotient is supplied.
3. The full global tree cannot be used as a uniformly finite carrier in general.

Moreover, HS24 lines 105--119 emphasize that the postcritically infinite tree is
constructed combinatorially and need not exist as an embedded invariant tree in the
Julia set. Thus it cannot by itself supply D25's required connected hull, prime-end
accesses, or analytic WAD correspondence.

**Ledger status:** `IMPORTED RAW SYMBOLIC TRUNCATIONS AND NO-GO EXAMPLES`.

## 5. Deductions proved by the source audit

The following are logical consequences of the locked statements. They are not
additional analytic theorems.

### Proposition 5.1 (no global-Hubbard-tree shortcut)

There is no valid proof of the Virtual Support Automaton theorem whose only
complexity input is:

> every quadratic polynomial has a Hubbard tree, so use its edges as finitely many
> states.

**Proof.** HS24 lines 1050--1059 exhibit complex-admissible quadratic
combinatorics with infinitely many periodic branch cycles and infinitely many
endpoints. Such a tree cannot have a finite edge set containing all its branch
data. \(\square\)

This does not rule out a finite-horizon quotient. It rules out the unqualified
global-tree argument.

### Proposition 5.2 (finite topology does not bound marked postcritical data)

A finite topological tree alone does not bound the number of postcritical labels
that a source-faithful construction may have to distinguish.

**Proof.** HS24 lines 1028--1034 give a finite tree containing infinitely many
distinct postcritical points, and lines 1043--1045 give the Feigenbaum interval.
Therefore the number of distinguished postcritical labels is not bounded by the
number of topological branches. Any finite quotient that omits such distinctions
must separately prove that the proof-relevant futures agree or retain the
distinctions as explicit counters. \(\square\)

This proposition does not say that every postcritically infinite tree map lacks a
finite Markov partition. It says that finite topology alone is insufficient to
establish the decorated, postcritical-label bound needed here.

### Proposition 5.3 (finite horizon is only pointwise finiteness)

For each horizon \(h\), HS24's \(H_h\) is finite, but the source gives no constant
bounding its combinatorial complexity independently of \(h\).

**Proof.** Lemma `The finite trees \(H_n\)` proves finiteness separately for each
\(n\). The construction adds a new path when the next critical image is not already
captured (lines 501--525), and the full tree is the union over all \(n\). The source
also supplies examples with infinitely many endpoints, so these additions cannot
stabilize uniformly in general. \(\square\)

### Observation 5.4 (the KKL clone syntax is length-aware, not length-free)

KKL's clone definition and intended finite reduction do not eliminate the unbounded
corridor length.

**Proof.** The reduced labeled graph \(\widehat A\) is intended to become independent
of clone length, while the displayed spectral relation still contains \(n\).
Therefore the source syntax retains \(n\) as part of the transfer datum. The printed
exponent relation itself is quarantined by Section 4.4 and is not used in this
observation. \(\square\)

This directly supports the counter-aware correction in
`virtual_language_memory.md`.

### Proposition 5.5 (existing uniformities are hypothesis-relative)

Every checked finite-complexity bound is controlled by at least one parameter that
is unbounded in the proposed general virtual regime:

| Source mechanism | Controlling parameter |
|---|---|
| K06 Hubbard/WAD model | primitive relative period \(p\) |
| KL08 decorations | finite decoration family, equivalently bounded \(q,n\) |
| KL09 molecules | distance from Molecule, equivalently bounded \(r,q,n\) |
| KKL26 dynamic cross section / clone syntax | parabolic bound \(b\); raw corridor length \(q\) is retained; printed spectral bridge is false, while the literal graph has an independent internal repair |
| HS24 finite truncation | declared symbolic horizon \(h\) |

Thus none can be quoted for constants independent of period, molecule depth, and
horizon without a new reduction theorem.

## 6. What source-faithful language closure would require

For the virtual block, let an atom record:

- the selected core edge and its multiplicity;
- critical/noncritical branch type;
- input and output access/ideal-interval labels;
- WAD class and its incidence with the core edge;
- local Frobenius/support type;
- declared counter increments.

Two prefixes may be merged only when they have the same permitted decorated futures,
modulo the explicit counters. A finite directed graph of current edge types is not
enough if two occurrences have different:

- remaining first-return time;
- future access splitting;
- later critical visit;
- WAD image or error routing;
- endpoint eligibility;
- neutral/primitive chart transition.

AF00 supplies ordinary finite Markov closure in a PCF tree. KKL supplies a finite
parabolically bounded Hubbard cross section and clone syntax. Its printed spectral
closure is unusable, while the internal corrected theorem applies once a literal
clone graph has been realized. No checked source proves this decorated
right-congruence property for D25's partial hull.

## 7. The strongest viable construction route

The sources suggest the following route, but do not complete it.

### Step A: canonical raw finite-horizon symbolic carrier

For the orbit segment actually used by a block, imitate HS24:
\[
  H_h=\bigcup_{j=0}^{h}\sigma^j(C_\nu).
\]
Decorate it with the selected Cantor small-Julia clusters, the critical return
labels, and every access used by Wave/Wanderers/Value.

This is only a **symbolic raw carrier**. A new theorem must relate it monotonically
and access-faithfully to the connected hull inside the dynamical Julia set.

### Step B: exact dynamical realization

Construct the selected finite-horizon \(\psi\)-ql/localization correspondence and
prove that its edge pushforward is the same transition used by KKL Value. This must
include every branch and ideal interval used downstream.

### Step C: split chains from finite control

Identify translation and neutral chains. Retain each exact corridor length,
satellite depth, or return clock as a declared counter, following KKL's treatment of
clone length.

For the nested satellite-copy history, this reduction is itself an open proof
obligation. One must prove either that all future-relevant frame labels compress
to bounded finite control plus finitely many counters, or that there is an exact
LIFO push/pop and recovery theorem over a finite frame alphabet. D25/KKL ordered
nesting proves neither alternative. A depth counter by itself forgets the ordered
rotation/decoration history.

### Step D: quotient only by decorated future equivalence

Quotient the zero-counter remainder by equality of:

- all permitted future atoms;
- all future critical/access outputs;
- all future WAD-to-core outputs;
- terminal chart and endpoint predicates.

Prove that the quotient has at most \(s_0\) classes and matrix dimension at most
\(d_0\), universally.

### Step E: license loops

Show every zero-counter loop is:

- a closed, framed, exact source-licensed primitive core block;
- a transient/extinction block;
- a common-flag shear carried by the augmented moment state; or
- a bounded witness forcing a chart transition.

Nonzero-counter loops must retain their exact clone, neutral
antirenormalization, or weighted-transfer equation.

Steps A--E would prove the source portion of the Uniform Counter/Stack-Follower
Theorem.
Analytic width comparison and error summability remain separate obligations.

## 8. Adversarial tests

Any proposed source construction should be rejected if it fails one of these tests.

| Attack | Why existing sources do not remove it |
|---|---|
| Increasing horizon adds a genuinely new branch | HS24 explicitly permits an infinite increasing union \(H_n\). |
| Finite carrier but infinite postcritical distinctions | HS24 gives finite-tree, postcritically infinite examples. |
| Same core support, different future exit time | KKL retains clone length as a counter; it does not merge exact exits. |
| Same tree edge, different WAD/access future | KKL's itinerary proposition is pointwise and does not prove follower equivalence. |
| Raw ideal marking grows with corridor length | KKL's inner/outer marking cardinalities grow with \(n,q\). |
| Parabolic bound \(b\) drifts | KKL's return and cross-section bounds depend on \(b\). |
| Anti-Molecule distance tends to zero | KL09's bounded \((r,q,n)\) equivalence loses uniformity. |
| Abstract tree is not embedded in the Julia set | HS24 explicitly separates its combinatorial construction from dynamical-plane realization. |
| A topological quotient merges cyclically distinct accesses | None of the tree sources carries KKL prime-end/WAD data through such a quotient. |
| Several nested satellite clocks interact | No checked source bounds the number of independent counters in a virtual block. |
| Nested inclusion is treated as a stack | D25/KKL order the satellite copies, but do not prove matched push/pop, reverse-order antirenormalization, or recovery of virtual-hull/WAD state. |
| Equal depth is treated as equal history | Different rotation/decoration sequences can have the same depth; no audited source proves their decorated futures equivalent. |
| Accepted graph word has no selected dynamical branch | Neither KKL `prop:itineraries` nor a bare transition matrix proves the required decorated language equality. |
| Primitive base loses primitivity after delay | KKL separately assumes primitive clones; delay-robust mixing needs an additional certificate. |

## 9. Exact open theorem exposed by the audit

### Source-Faithful Virtual Counter/Stack Automaton (`OPEN`)

There exist universal constants
\[
  s_0,d_0,w_0,R_0,k_0,t_0,C_0<\infty
\]
such that every finite-horizon virtual-Molecule block admits:

1. an access-faithful raw carrier representing all proof-used Cantor components,
   orbit points, and accesses;
2. a selected \(\psi\)-ql/localization correspondence whose core transition is
   the typed incidence \(B=N^{\mathsf T}\) used by Value, with its left/right
   eigenweight roles;
3. at most \(k_0\) explicit integer counters recording all unbounded exact return,
   corridor, satellite, and neutral lengths, together with an optional stack over an
   alphabet of size at most \(t_0\) whose top-only push/pop rule is source realized,
   all under fixed bounded update and guard catalogs;
4. an exact checkpoint compilation or finite memory congruence before any pumping,
   yielding a decorated follower quotient with at most \(s_0\) states and memory
   radius at most \(R_0\);
5. independently proved core and WAD dimensions at most \(d_0,w_0\), every WAD
   branch descending through its quotient, and the complete fixed future-observation
   family factoring through it;
6. exact equality between accepted words and selected dynamical concatenations,
   including all WAD/access outputs and every loop emission;
7. at most \(C_0\) endpoint/critical defects per corridor family;
8. source-licensed routing of every contextual loop occurrence into a closed framed
   primitive entropy return, transient extinction, neutral regularization, or the
   finite shear state;
9. constants independent of satellite periods, virtual-Molecule depth, and the
   finite postcritical horizon.

Before Item 3 can absorb nested satellite history, one must discharge the stack
audit above: either prove bounded counter compression of the ordered frame
labels, or prove source-faithful LIFO antirenormalization and then show that the
downstream transfer argument is valid for the resulting pushdown memory. Neither
branch follows from canonical set inclusion.

No checked source proves any general implication that would discharge Items 1--9
as a package.

## 10. Imported / proved / open boundary

### Imported

- D25's precise virtual-hull proposal and its status as an interpolation problem.
- D25's finite canonical nested satellite-copy order and KKL26's unique infinite
  molecule sequence, strictly as combinatorial/parameter-space chains.
- D25's reported one-step neutral-sector pseudo-Siegel antirenormalization
  mechanism, restricted to that setting.
- KKL's prime primitive Hubbard transition and Value source identity.
- KKL's abstract cross-section and clone definitions, but not the inconsistent
  printed finite-\(n\) spectral bridge.
- KKL's parabolically \(b\)-bounded dynamic cross-section/clone construction,
  combined only with the separate internal literal-clone spectral theorem.
- KKL's relative WAD support bound and pointwise itinerary proposition.
- K06's period-\(p\) superstable Hubbard/WAD model.
- KL08/KL09 bounded top-puzzle results under decoration/anti-Molecule hypotheses.
- AF00's finite PCF Hubbard-tree Markov/SFT model.
- HS24's finite symbolic truncations and finite/infinite global-tree examples.

### Proved in this report

- the global Hubbard tree cannot be used as a blanket finite-state shortcut;
- finite topological tree complexity does not bound marked postcritical data;
- finite horizon provides only pointwise, not uniform, finiteness;
- KKL's successful compression is explicitly counter-aware;
- canonical nested satellite-copy order does not by itself supply LIFO
  antirenormalization or matched state recovery;
- every located state-complexity bound depends on a parameter not uniformly
  controlled in the full virtual regime.

These are source-scope deductions, not complex-analytic advances.

### Open

- dynamical realization of a finite-horizon carrier inside D25's virtual hull;
- a universal bound on decorated future-equivalence after counters are split off;
- a universal bound on the number of necessary counters;
- exact WAD/access language closure;
- LIFO antirenormalization, matched frame recovery, and chart compatibility for
  the D25 virtual-Molecule chain, or a proof that its full ordered history
  compresses to bounded finite control plus finitely many counters;
- source identity between the virtual transition and KKL Value;
- uniform defect, gate, and active-core bounds;
- analytic access realization and width comparison;
- all subsequent Master Transition and MLC obligations.

## 11. Final assessment

The literature supports a disciplined blueprint, not the missing theorem.

The best source-faithful starting point is:

\[
\boxed{
\text{HS24 finite-horizon raw tree}
\;+\;
\text{KKL finite core/cross section with explicit length}
\;+\;
\text{corrected typed clone recurrence}
\;+\;
\text{new decorated follower-index theorem}.
}
\]

The essential new work is the last term, together with the analytic embedding of the
raw symbolic carrier into Dudko's connected virtual hull. Any argument that jumps
directly from "connected hull" or "finite tree" to a uniformly finite automaton
misses precisely the postcritical-memory and WAD/access obstructions exposed above.
