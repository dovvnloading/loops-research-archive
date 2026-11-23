# Source-grounded Lean risk register and proof contracts (2026-11-23)

> **Update to this dated snapshot.** The attachment rank algebra from #111 is on main. The covering-space endpoint equivalence and variational width implication now have separate Lean modules. Source-specific KL maps, admissible foliations and all-child metrics still require independent realizations. [Current model-to-physical register](PHYSICAL_BRIDGES.md)

**Base revision:** `7df9b19ab8d87983a7a2c89160235d0576dbcb66`
(2026-11-23). **Toolchain:** Lean 4.32.0; Mathlib v4.32.0 in
`formalization/weighted`.

**Purpose:** rank places where a kernel-checked model statement could be
incorrectly promoted to a geometric, analytic, or global-dynamical statement.
The relevant failure is generally *semantic adequacy*, not a failure of
Lean's kernel. This is an actionable *internal* source audit, not an
independent peer review or a claim that a theorem does not exist anywhere
else in Lean/Mathlib.

## Baseline and interpretation

- `ledger.json`: 465 obligations, 34 imported, 316 documentary proved,
  115 open. `ResearchLedger.lean` proves the *encoded metadata*
  (counts, DAG acyclicity and ordering), not the mathematics of its 316
  documentary-proved claims. It records 14 conditional documentary proofs
  with explicit open hypotheses.
- There are 20 open ledger nodes with no *open ordinary dependency*.
  This is a work queue, not a claim of readiness or analytic provability.
- Using ordinary `deps` edges only (not separate conditional hypothesis
  edges), 94 of the 115 open nodes are ancestors of the `MLC` target.
  These are graph metrics, not probabilities or estimated time-to-proof.
- The full delayed-clone strict eigenvalue gap and positive root for every
  delay are **already formalized** in
  `formalization/weighted/FullCloneStrictGap.lean` and related files;
  real period-27 center existence, uniqueness in the specified interval,
  and exact period are likewise already formally proved. Do not reopen
  them merely because older prose predates newer Lean work.
- `ResearchGates.lean` correctly represents the global implication as
  conditional on source-defined same-carrier H1–H4, a complement theorem
  and a terminal geometric bridge. Its explicit countermodels are
  proof-theoretic safeguards. H1–H4, universal protected-tower closure
  and MLC remain open.

## Priority ranking (logical impact, not predicted difficulty)

| Priority | Exact missing bridge / target | Reason and source | Lean completion contract |
|---|---|---|---|
| P0 | Physical KKL marking and all-path Wave class agreement | `REFEREE_REPORT.md` F1/F2; actual ideal boundary, proper-path/sidedness, immersion and cover markings need not agree with chosen finite 10/20 atom tables. | Construct **source-defined** spaces, path groupoids, marked ideal-end sets and a proven equivalence with the finite model. Derive actual all-path class inclusion and properness. Then prove the analytic extremal-width inequality under independently proved metric/foliation hypotheses. |
| P0 | Non-locally-connected selected geometric continuum lift | `KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT` is open and lies upstream of 49 open nodes in the ordinary dependency DAG. | Establish source-defined lift/continuum and its marked two-level naturality, not just an abstract sheet-incidence table. Prove actual image/fiber equalities and boundary access preservation. |
| P0 | Proof-used predecessor selection | `KKL_STATIONARY_PROOF_USED_PREDECESSOR_SELECTION` is open, upstream of 48 open nodes. | Distinguish existence of *some* predecessor from selection of the exact physical predecessor for every required stage. Preserve same source, marking, and depth. |
| P0 | Physical separator realization | `KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION` is open, upstream of 45 open nodes. | Prove the named physical separation theorem for actual Julia/tree carriers; finite graph separation alone is not sufficient. |
| P1 | KL physical covering and sheet/coset identification | `formalization/weighted/LocalizationSheetKernel.lean` proves the general nonnormal-coset algebra; issue #62 needs source-defined path groupoid and prescribed connector deck words. | Prove a fiber-to-coset correspondence for the actual connected based covers, the endpoint-lift test for `f_*`, and compatibility with the separately typed immersion `ι^*`. Supply a **physical** defect word before using the abstract collision theorem. |
| P1 | KKL exceptional attachment/edge incidence | Issue #40 requires actual boundary components, cyclic order, open/closed endpoints, proper corridors and source-defined `T_F` rows. | Construct prime-end/access atlas and establish exhaustive component incidence; derive all finite rows *from the same atlas*. Eliminate countermodels where identical matrices hide different collapsed fibers. |
| P1 | Planar fullification on compacta | `ProtectedCarrierLogic.lean` assumes an extensive, monotone, idempotent total `Fullifier (α)` on **all** sets. Actual planar fill is defined by bounded complementary components of compact sets. | Choose a type/structure carrying compactness (or a precisely justified extension of fill), prove existence of the unique unbounded complementary component and compactness/extensivity/monotonicity/idempotence, and instantiate the existing generic closure theorem. Do not silently instantiate a compacta operation on arbitrary unbounded sets. |
| P1 | Paper 3 Čech MV / Alexander-duality geometric interface | Paper 3 `separation_budget.tex` uses compact-pair Čech MV, Alexander duality, and component-to-rank identification. | Define the actual cohomology groups and connecting/restriction maps, prove exactness and finite-rank/component identities. Then specialize `AttachmentDefectLedger.lean`, whose purely rational finite-dimensional rank algebra is now kernel-checked in draft PR #111. |
| P1 | H1 finite cell-tree extraction to actual carriers | `H1_CELL_TREE_EXTRACTION` is open and upstream of 34 open nodes; the universal same-carrier problem remains open. | Prove existence/naturality of the actual monotone quotient and lifted marked prime-end carrier. Keep parameter/stage/return domains identical across all H1–H4 interfaces. |
| P2 | All-period near-(-2) real-tip analytic realization | `REFEREE_REPORT.md` M3/M5/M6; finite signed-chart and rational margin code does not establish the infinite-p family or physical nested quadratic-like maps and Wave support. | First formalize the p≥13 analytic tail estimates with uniform quantifiers, correct p versus 3p return types, and orbit-order/complex-collar derivations. Separately prove proper degree-two source-domain hypotheses; local chart uniqueness is **not** global-window uniqueness. |
| P2 | Paper 2 rooted-end compactification | Existing `PhaseTower*.lean` and `PhaseFuture*.lean` prove finite phase/memory assertions, not topological end realization. | Construct the actual compactified end space, prove topological continuity and dynamics, and give source-level maps relating its points to symbolic phase clocks. |
| P2 | Finite-to-infinite protected-carrier stability | Paper 3 `separation_budget.tex` supplies a Hausdorff-limit trace-birth example; finite fullness and singleton attachment are not enough for a limit. | Prove a nested compact decreasing-envelope theorem **with nonempty connected limiting traces** or an explicit limit countermodel. Avoid assuming arbitrary Hausdorff limits preserve fullness/port access. |

### Actual upstream reach (ordinary dependency DAG)

| Open node | Open descendants |
|---|---:|
| `KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT` | 49 |
| `KKL_STATIONARY_PROOF_USED_PREDECESSOR_SELECTION` | 48 |
| `KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION` | 45 |
| `KKL_NATIVE_WAVE_WANDERERS_QUERY_SCHEMA_BOUNDARY_MAP` | 37 |
| `H1_CELL_TREE_EXTRACTION` | 34 |

Counts are transitive, can overlap, and were computed from the pinned
`ledger.json` ordinary `deps` graph. They exclude conditional `hyp`
edges and do not imply any theorem follows just by closing a node.

## PR #111: substantive verified increment, precise scope

New module:
`formalization/weighted/AttachmentDefectLedger.lean`.

Its `short_exact_finrank` theorem combines actual maps `i : U →ₗ[ℚ] V`
and `r : V →ₗ[ℚ] W`, injectivity, surjectivity and
`i.range = r.ker` to derive
`finrank(V)=finrank(U)+finrank(W)`.
Then `attachment_balance` uses *two* short exact sequences
(`Contact→New→Defect` and `Defect→Old→Trace`) to obtain

`finrank(New) + finrank(Trace) = finrank(Old) + finrank(Contact)`.

With `finrank(Contact)+1=components`, the component formula is

`finrank(New) = finrank(Old)+components-1-finrank(Trace)`.

The module includes the strictly decreasing rank consequence for a
connected trace with nonzero first-cohomology rank and a finite arithmetic
anti-monotonicity check. It does **not** identify abstract rational
vector spaces with physical Čech groups, construct the long exact sequence,
or discharge the topological premises. The branch is draft, not merged.

The weighted-Lake default target and CI proof-hole scanner were updated.
The initial build failed on two rank-nullity rewriting details and was
corrected; **the next push build at commit `6a3bac5` passed**:
[GitHub Actions #45258094941](https://github.com/dovvnloading/loops-research-archive/actions/runs/45258094941).

## Formalization acceptance policy

**A theorem counts as a source-level mathematical discharge only if:**

1. Its Lean statement is linked to the exact numbered source assertion.
   Every sourced dynamical object, quantifier and mark is represented.
2. All model-to-physical identification maps are constructed, not simply
   declared as hypotheses with the same name as the desired conclusion.
3. Nontrivial hypotheses are either independently proved or clearly
   recorded as *assumed*, and cannot be hidden inside a `structure`.
4. A pinned Lean build succeeds and `#print axioms` shows no `sorryAx`
   or unreviewed nonstandard axioms for the claimed theorem.
5. A negative test/countermodel checks at least one plausible false
   strengthening (wrong coset convention, omitted `-σ(T)`, noncanonical
   marking, non-coattained suprema, a bad limit, etc.).
6. The research ledger is updated only for the *exact* discharged claim,
   without upgrading H1–H4, UPTCR or MLC on the strength of a finite
   model or a conditional implication.

## CI / maintainability risks

- The root `.github/workflows/lean-proofs.yml` uses a long,
  explicit handwritten proof-file list for its placeholder scan and
  path filters; future files can be silently omitted. Give it an
  all-root-source discovery/registration check analogous to the
  *weighted workflow's repair in this PR*.
- This PR repairs two weighted-workflow blind spots: the placeholder
  and axiom scanner now covers **every** direct
  `formalization/weighted/*.lean` file, and a Python/TOML guard
  requires each such source to appear both as a Lake library and
  in the default build targets. It also triggers the weighted build
  on root `*.lean` changes, so changes to imported root modules get
  a same-commit integration check.
- A green finite-computation verifier or a successful formal proof of
  `assumptions → conclusion` is *not* a verification that analytic
  hypotheses are true. Report the categories separately in PR checks.
- The research ledger's `.ledgerProved` status is documentary, as
  `ResearchLedger.lean` itself explicitly warns. Do not count those
  nodes as Lean theorems.

## Recommended order of attack

First complete the finite/high-confidence proof kernels, particularly
the rank ledger (this PR), exact coset-convention adapters and data-derived
source-incidence checks. Next build the actual compact-planar hull and
covering/prime-end bridges. Only after those source objects exist should
the all-path KKL Wave analytic inequalities be treated as candidates
for geometric closure. Last, tackle uniform all-period estimates,
nested infinite-horizon compactness and same-carrier H1–H4 rigidity.

**No current theorem in this audit proves Mandelbrot local connectivity.**
