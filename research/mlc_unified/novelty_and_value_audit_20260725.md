# Novelty, mathematical value, and MLC-impact audit

Date: 2026-07-25  
Status: completed internal audit; publication priority remains subject to expert
review and author confirmation

## 1. Correction of the earlier rapid assessment

The earlier project-level answer was produced too quickly to justify a novelty
judgment. It combined previous repository audits with one dependency query; it
was not a fresh theorem-by-theorem comparison with the primary literature. That
answer is withdrawn as an evidentiary basis.

This document records the replacement audit. It separates four questions that
must not be conflated:

1. **Correctness:** does the proof establish the statement under its stated
   hypotheses?
2. **Novelty:** is the statement or proof absent from the existing literature?
3. **Relevance:** does the result concern the missing virtual or unbounded
   renormalization geometry?
4. **Gate effect:** does the result discharge an open dependency of MLC rather
   than merely state a conditional implication or reject a shortcut?

The principal conclusion is:

> The repository is not entirely low-value material. It contains one strong
> candidate-original source correction, one modest candidate-original
> first-scale construction cluster, and a useful catalogue of exact
> counterexamples. Most of its volume, however, is classical mathematics,
> conditional proof engineering, source reconstruction, or negative
> diagnostics. No global MLC gate, Dudko Problem 4.3 or 4.4, or new MLC
> parameter class has been closed.

## 2. Audit method and reproducibility

The audit used the following independent checks.

1. Parsed every entry in `proof_obligations.json`.
2. Classified every one of the 209 internally proved obligations by
   mathematical role.
3. Read the complete proof sections behind every plausible originality
   candidate.
4. Checked the current public Kahn--Kapiamba--Lyubich arXiv v1 source, including
   Appendix C, against the source-locked local TeX.
5. Re-derived the delayed-clone equations directly from the block incidence
   matrix and reproduced the finite counterexample.
6. Compared the direct-decoration construction with the Kahn--Lyubich
   Decorations paper and with established shift-coding constructions.
7. Compared the connector, response, and symbolic compactification results
   with their classical topological, Sobolev, spectral, and automata
   antecedents.
8. Computed the full dependency closure below `MLC` and audited every remaining
   global gate.
9. Ran the proof-ledger validator and the complete diagnostic regression suite.
10. Commissioned three independent internal reviews: theorem classification,
    primary-literature comparison, and dependency/gate impact.

Machine-readable classification and its validation are in:

- `novelty_classification_20260725.json`;
- `novelty_classification_20260725_validation.md`.

The validation found exactly 209 distinct classification records for the 209
ledger entries marked `proved`, in exact ledger order, with no missing, extra,
or duplicate ID. No proof status was changed.

The commands rerun during this audit reported:

```text
ledger: valid (295 obligations)
statuses: imported=23, proved=209, open=63
target: MLC [open]
diagnostic transfer regressions: all passed
```

These scripts check graph consistency and finite diagnostics. They do not
certify analytic truth or publication novelty.

## 3. Classification of the 209 internally proved nodes

| Mathematical role | Count | Share |
|---|---:|---:|
| Standard or classical mathematics | 71 | 34.0% |
| Direct formal corollary or compiler | 85 | 40.7% |
| Finite or source diagnostic | 8 | 3.8% |
| Negative counterexample or no-go | 41 | 19.6% |
| Potentially original positive construction | 3 | 1.4% |
| Substantive but novelty unresolved | 1 | 0.5% |

The three candidate-positive entries are not three independent breakthroughs.
They are consequences of one direct-decoration rooted-end construction:

- `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`;
- `DIRECT_DECORATION_GAP_CELL_ATLAS`;
- `DIRECT_DECORATION_FINITE_PROTECTED_CARRIER`.

The unresolved entry is `KKL_CLONE_EIGEN`. Its companion
`KKL_PRINTED_CLONE_EQUATION_NO_GO` is classified by role as a negative
counterexample, although it may be the most externally valuable result in the
repository.

The raw number `209 proved` therefore must not be used as a percentage-complete
measure of MLC. In particular, a conditional theorem can be perfectly correct
while assuming the missing analytic object in its statement.

## 4. Strongest candidate-original contribution: the KKL clone correction

### 4.1 Public source statement

The current public version is Kahn--Kapiamba--Lyubich,
*MLC for parabolically bounded primitive renormalization*,
arXiv:2606.27272v1, submitted 2026-06-25:

<https://arxiv.org/abs/2606.27272>.

Appendix C:

1. replaces a cross section \(E\) by a directed delay chain
   \(E_0\to E_1\to\cdots\to E_n\);
2. prints a self-referential eigenvector identity;
3. assigns the reduced edge with delay label \(k\) the positive weight
   \(\lambda^k\); and
4. asserts the finite-\(n\) equation
   \(h(\lambda_n)=\lambda_n^n\).

The relevant public HTML passage is Appendix C of:

<https://arxiv.org/html/2606.27272v1>.

### 4.2 Exact literal counterexample

Let the base directed graph have vertices \(e,a,b\) and edges

\[
e\to a,\qquad a\to e,\qquad a\to b,\qquad b\to e,
\]

with cross section \(E=\{e\}\). The base is primitive because it is strongly
connected and has cycles of lengths \(2\) and \(3\).

The length-\(n\) literal clone has cycles of lengths \(n+2\) and \(n+3\).
Its Perron root therefore satisfies the renewal equation

\[
\lambda_n^{n+3}=\lambda_n+1.
\tag{4.1}
\]

The reduced graph specified by the printed definition has one vertex and two
loops with labels \(2\) and \(3\). The positive-weight definition gives

\[
h_+(\lambda)=\lambda^2+\lambda^3.
\tag{4.2}
\]

If the printed finite-\(n\) equation were valid, then

\[
\lambda_n^n
=\lambda_n^2+\lambda_n^3
=\lambda_n^2(1+\lambda_n)
=\lambda_n^{n+5},
\]

using (4.1). Since \(\lambda_n>1\), this is impossible. Transposing the
incidence matrix preserves the Perron root and does not repair the exponent
sign.

### 4.3 Correct reduction

Write the row-source base incidence in blocks

\[
N_0=
\begin{pmatrix}
Q&C\\
D&0
\end{pmatrix},
\]

where the complement of the cross section has nilpotent incidence \(Q\).
Eliminating the active coordinates of the literal clone gives the exact
first-return operator

\[
H(t)
=t^{-1}D(tI-Q)^{-1}C
=\sum_{j\ge0}t^{-(j+2)}DQ^jC.
\tag{4.3}
\]

Thus a first-return walk of length \(k\) has weight \(t^{-k}\), and the exact
clone equation is

\[
\rho(H(\lambda_n))=\lambda_n^n.
\tag{4.4}
\]

For the three-vertex graph,

\[
H(t)=t^{-2}+t^{-3},
\]

so (4.4) is exactly (4.1). The internal proof also establishes, under its
fixed-cross-section hypotheses,

\[
\lambda_n\to1,\qquad
\lambda_n^n\to\rho(H(1)),
\]

together with the correctly typed gate-normalized Perron-vector limits and a
finite gate-dimension multiplier bound.

The finite numerical regression was rerun for \(1\le n\le20\), but the proof
is the block elimination above; the computation is only a diagnostic.

### 4.4 Novelty and impact judgment

No public erratum or independent discussion of this defect was found in the
targeted search, and arXiv currently lists only v1. Because the paper is very
recent, the explicit source correction is plausibly original. Absence of a
search result does not establish priority.

The Schur/renewal mechanism in (4.3) is standard spectral mathematics. The
candidate-original contribution is the precise diagnosis of this public
preprint, the literal counterexample, the source-convention audit, and the
complete repair.

This should be described as:

> A printed finite-\(n\) bridge in KKL v1 fails under its literal definitions;
> the negative-delay Schur reduction repairs the bridge and preserves the
> intended fixed-template asymptotics.

It should not be described as a refutation of KKL's main restricted MLC
theorem. The corrected theorem appears to restore the asymptotic multiplier
and eigenweight facts used later in the paper. Author confirmation and an
independent expert convention check are required before public priority or
correctness claims.

Relevant project proofs:

- `kkl_transfer_orientation_audit.md`;
- `corrected_clone_theorem_derivation.md`.

## 5. Candidate-original first-scale construction

The direct-decoration work starts from actual Kahn--Lyubich data: a puzzle
disk \(P\), two disjoint degree-one pullback pieces \(Q_0,Q_1\), and univalent
inverse branches of \(g=f^q\). See:

<https://arxiv.org/abs/math/0609046>.

The project constructs:

1. finite preterminal continua \(K_w=\phi_w(K_0)\);
2. nested end fibers
   \(E_\omega=\bigcap_m Q_{\omega|m}\);
3. a compact planar rooted-end union;
4. its exact connected-component decomposition;
5. the partial shift and actual univalent branch action;
6. gap cells isolating finite fibers; and
7. finite protected carriers preserving selected prime-end chains.

The exact package was not located in the Kahn--Lyubich source. Its core,
however, is close to standard graph-directed inverse-branch and shift coding;
compare Petersen:

<https://arxiv.org/abs/0912.4181>.

The defensible novelty claim, if expert review confirms it, is therefore the
specific decorated-puzzle rooted-end package and its protected-cell
consequences, not the symbolic coding principle.

Important limitations are explicit:

- the end fibers are not identified as the intended virtual small Julia sets;
- no second virtual scale or next satellite marking is constructed;
- all-depth physical contact closure is open;
- trace welding and analytic response compactness are open;
- no period-independent width estimate follows;
- no new MLC class follows.

There is also a source-risk requiring expert review: the project uses strong
closed-Jordan-piece and closed-boundary separation hypotheses. Puzzle pieces
in related settings may share rays or vertices, so these hypotheses must be
checked against the exact source realization rather than inferred from open
component disjointness.

Relevant project proof:

- `virtual_cantor_pullback_compactification.md`.

The correct current label is **promising internal first-scale lemma, medium
confidence, novelty unverified**.

## 6. Valuable negative and quality-control results

The counterexample catalogue is a legitimate output even when it does not
advance the positive proof. Particularly useful entries include:

1. `QUADRATIC_PROTECTED_ACCESS_COLLISION`: an actual critical-value-free
   branch of \(z^2\) shows that absorbing a pulled-carrier excess can erase a
   protected prime-end access.
2. `PULLED_EQUIPOTENTIAL_SERIAL_RECTANGLE_NO_GO`: exact Böttcher angular
   scaling rejects a proposed serial-collar identification.
3. `WOT_WELDING_ALGEBRA_NO_GO`: bilateral shifts show that weak-operator
   compactness does not preserve graph constraints or welding composition.
4. Scalar-neck, independent-port-gauge, topology-only-width, finite-memory,
   and unmarked-hull counterexamples reject several tempting but invalid
   compressions.

These results add adversarial and proof-hygiene value. Most refute internally
proposed shortcuts rather than published theorems, and their underlying
mathematics is generally elementary or classical. They should be presented
as a failure map, not as cumulative evidence that MLC is nearly proved.

## 7. Material that is mostly standard or scaffolding

The following large families are mathematically useful but have low novelty:

- proper-map degree and factorization lemmas;
- planar tree, fullness, Jordan-neighborhood, and prime-end transport lemmas;
- extremal-length monotonicity and serial-annulus estimates;
- Sobolev trace gluing, Dirichlet-to-Neumann response, and Schur complements;
- Perron--Frobenius, finite graph, and matrix-cone estimates;
- automata pumping, follower equivalence, Stone/product compactification;
- conditional Wave, tame, corridor, and transport compilers;
- record, Lyapunov, and conditional endgame reductions.

The future-observable compactification, for example, is a routine product
completion of frozen observables and is closely related to established
compact-automata constructions; compare:

<https://arxiv.org/abs/1306.1468>.

It compactifies symbolic records. It does not prove that a limit is an
analytic renormalization tower.

The protected regulated connector is a useful bespoke formulation, but it is
assembled from classical nonseparation, Alexander duality, planar-tree, and
prime-end functoriality. Its hard dynamical input--the simultaneous free-port
certificate for actual virtual-Molecule atoms--remains open.

## 8. Exact effect on the MLC dependency graph

The ledger contains 295 nodes. The dependency closure of `MLC` contains 259:

| Status in MLC closure | Count |
|---|---:|
| Imported | 15 |
| Internally proved | 185 |
| Open, including `MLC` | 59 |

Thus 58 unresolved obligations lie below the final open statement.

The four decisive direct gates remain:

| Gate | Status | Missing substance |
|---|---|---|
| `H1_MARKED_CONSTRUCTION` | open | actual all-scale marked carriers and analytic access realization |
| `MBTT` | open | universal backward transition on the realized geometric state |
| `H3_COERCIVITY` | open | analytic marked precompactness from bounded potential |
| `H4_RIGIDITY` | open | qc pullback, no-line-field application, and shrinking parameter neighborhoods |

All six direct prerequisites of `MBTT` are open:

- `H1_MARKED_CONSTRUCTION`;
- `H2_CALIBRATION`;
- `H2_FORWARD_CONTRACTION_CALIBRATION`;
- `H2_CONE_CALIBRATION`;
- `H2_SUMMABILITY`;
- `H2_ENTROPY_DICHOTOMY`.

The graph-minimal open nodes are:

1. `DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE`;
2. `DIRECT_DECORATION_END_PRIME_END_COFINALITY`;
3. `H1_CELL_TREE_EXTRACTION`;
4. `MAPPING_TELESCOPE`;
5. `VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION`;
6. `VIRTUAL_WAVE_DEMAND_SCHEMA`.

They are not “the last six lemmas.” The longest unresolved chain from a
minimal open node to MLC contains roughly twenty-five further open
transitions.

No internal result establishes:

- a new a-priori bound in a previously open class;
- a uniform unbounded-satellite estimate;
- a virtual-Molecule return atlas through all scales;
- a positive/zero-entropy interpolation theorem;
- bounded puzzle Teichmüller diameter for the missing mixed class;
- a new rigidity theorem or shrinking parameter basis; or
- a new parameter class at which MLC follows.

The recent Cheraghi--Shishikura, Levin, Elephant-Eyes, and BLOT imports refine
the literature map, but the newly added side-source imports are outside the
current `MLC` dependency closure. They do not shrink the universal target
quantifier in the present architecture.

## 9. Circularity and overstatement risks

The following risks must remain visible.

1. `H4_RIGIDITY` already asks for shrinking connected relative parameter
   neighborhoods. The implication from H1--H4 to MLC is correct but close to
   an endgame restatement.
2. UPTCR-6 similarly includes parameter equality, singleton fibers, and
   shrinking neighborhoods. `UPTCR_IMPLIES_MLC` is a valid conditional
   implication, not a reduction of that hard clause.
3. Several compiler theorems assume actual bases, branches, proof-complete
   horizons, properness, and access compatibility. Those are the analytic
   problem, not bookkeeping supplied by the compiler.
4. Compactifying every declared future observable gives a formal symbolic
   compactum. It cannot be used as analytic coercivity without proving that
   its boundary points are admissible towers.
5. “All future proof-used data” and prefix-local canonical construction are
   repeatedly required together, but no theorem proves a uniformly finite
   state satisfying both.
6. The proposed invariant has repeatedly expanded from one scalar width to
   vectors, response forms, Value moments, counters, stacks, flags,
   attachment traces, contact atoms, and welding cocycles. The project has
   not proved that this enlargement terminates in a uniformly finite state.

The last point is a structural warning: the current protected-tower invariant
may need replacement rather than additional bookkeeping.

## 10. Verdict on the side-research material

The side-research intake was not wholly wasted. It:

- corrected invalid response and welding claims;
- retained several exact narrow lemmas;
- improved the known-subclass map;
- supplied adversarial counterexamples; and
- prevented false ledger promotions.

Its positive retained lemmas are mostly standard and do not close a project
gate. Several proposed claims were false and were correctly rejected. The
main value is quality control and source triage, not progress toward a global
renormalization theorem.

## 11. Research decision

Further broad framework expansion should stop. The project should be split
into three honest outputs:

1. **KKL correction note.** Extract the counterexample and corrected
   negative-delay theorem into a short standalone manuscript. Obtain an
   independent expert check and contact the KKL authors before making a
   public correction claim.
2. **First-scale construction note.** Isolate the direct-decoration rooted-end
   and protected-carrier package. Have a complex-dynamics expert check the
   closed-piece boundary hypotheses and the prime-end exposure argument.
3. **MLC research dossier.** Retain the dependency graph and obstruction
   catalogue as a map of what remains open, without presenting node count or
   conditional UPTCR as evidence of proximity to MLC.

A future result should count as forward MLC progress only if it does at least
one of the following:

- proves a theorem on actual quadratic return domains with source-verified
  branches and period-independent constants;
- closes a previously open parameter subclass;
- discharges one of H1, MBTT, H3, or H4 without encoding its conclusion in
  the hypotheses; or
- gives an exact analytic counterexample showing that the proposed
  finite-state protected-tower architecture cannot work and identifies a
  replacement invariant.

Until then, `VAAPC-I`, UPTCR, MBTT, coercivity, rigidity, Dudko Problems 4.3
and 4.4, and MLC remain open.
