# Research map

This map connects the mathematical dependency structure to the public files. The canonical route through the project is the paper sequence, the main manuscript, the proof ledger, and `research/mlc_unified/`. Dated push bundles preserve the development record and remain addressable because ledger entries cite them.

## Mathematical dependency spine

| Stage | Public object | Status at 2026-07-27 | What it supplies | What it does not supply |
|---|---|---|---|---|
| 1. Localization correction | [Paper 1](./papers/paper1_canonical_localization/paper1_forced_noninjectivity_sheet_kernel_v1.1_visual.pdf) | Version 1.1 Visual Edition | Forced canonical collision, canonical covering/embedding resolution, infinite sheet kernel, winding quotient, and exact propagation on the complementary-cover locus | Decoration-stage alignment, a priori bounds, rigidity, MLC |
| 2. One-scale compactification | [Paper 2](./papers/paper2_rooted_end_compactification/paper2_direct_decoration_rooted_end_compactification_v1.1_visual.pdf) | Version 1.1 Visual Edition | Direct-decoration realization of the binary rooted-end compactification, exact component quotient, shift dynamics, stable replacement, and protected accesses | Cross-scale transitions, end-fiber renormalization, analytic nondegeneration, MLC |
| 3. Finite protected carriers | [Paper 3](./papers/paper3_protected_carriers/paper3_draft3_visual.pdf) | **Draft III Visual Edition · QA audited** | Finite protected routing, exact recognition and packet audits, attachment separation ledger, and sharp Hausdorff-limit failure/stability tests | Virtual carrier construction, Wave horizon, analytic correspondence, uniform incidence control, MLC |
| 4. Marked construction | `H1_MARKED_CONSTRUCTION` in [`ledger.json`](./ledger.json) | Open | The complete marked state and transition object consumed by the reduction | — |
| 5. Calibration | `H2_CALIBRATION` | Open | Quantitative comparison with source extremal-width observables | — |
| 6. Coercivity | `H3_COERCIVITY` | Open | Analytic nondegeneration and compactness of the marked state | — |
| 7. Rigidity | `H4_RIGIDITY` | Open | The rigidity input required at the terminal limit | — |
| 8. Universal closure | `UNIVERSAL_PROTECTED_TOWER_CLOSURE` | Open | Uniform closure of the protected-tower program | — |
| 9. Terminal implication | `UPTCR_IMPLIES_MLC` | Proved conditional implication | MLC from the universal compactness-and-rigidity proposition | A proof of UPTCR itself |

The main manuscript integrates all nine stages and states the hypotheses consumed at each transition.

## Canonical public layers

### 1. Orientation

- [`README.md`](./README.md): research thesis, paper sequence, novelty, status boundary, attribution, and reading path.
- [Project page](https://dovvnloading.github.io/loops-research-archive/): visual overview, mathematical atlas, references, and searchable ledger.
- [`CONTRIBUTING.md`](./CONTRIBUTING.md): standards for mathematical review and additions.

### 2. Manuscripts

- [`marked_width_mlc_manuscript.pdf`](./marked_width_mlc_manuscript.pdf): 225-page global synthesis and conditional reduction.
- [`papers/README.md`](./papers/README.md): paper index, status, PDFs, and source roots.
- [`papers/paper1_canonical_localization/`](./papers/paper1_canonical_localization/): Paper 1 PDF, LaTeX source, extracted theorem packets, certificates, and assembly tooling.
- [`papers/paper2_rooted_end_compactification/`](./papers/paper2_rooted_end_compactification/): Paper 2 PDF and LaTeX source.
- [Paper 2 primary-source realization audit](./research/independent_audits/paper2_decorations_source_realization_20261105.md): checks the Kahn–Lyubich shallow and deep closed-pullback hypotheses, proves the primitive-orbit fixed-point exclusion, and records exactly which dynamical time and root-arrow statements must change in a deeper branch variant; no MLC gate is promoted.
- [Exact two-level **real** quadratic return certificate](./research/independent_audits/real_quadratic_3_9_restrictive_certificate_20261105.md): uniquely certifies an algebraic critical-period-27 real quadratic with nested period-3/9 restrictive intervals, disjoint physical phase windows and a 9-to-3 phase quotient. An exact dyadic interval program plus a core-Lean phase lemma verify the arithmetic and transport logic. The superattracting center **fails Paper 2 H3**, and no complex renormalization or MLC gate is claimed.
- [Complex two-scale first-failure certificate](./research/independent_audits/two_scale_complex_window_obstructions_20261105.md): exact outward integer bounds prove that the existing |c'-c*|<2^-26 collar disk has an attracting exact period-27 cycle and, more strongly, **every** parameter in the eightfold-larger |c'-c*|<2^-23 disk fails **Paper 2 H3 (K(f)=J(f))**; they also rule out using equal-width thin stadiums as proper first-return preimage domains at the center. This does **not** rule out other polynomial-like domains, prove a KL atlas, or affect the global H3_COERCIVITY ledger gate.
- [Certified **complex two-scale quadratic-like returns**](./research/independent_audits/complex_two_scale_quadratic_like_certificate_20261105.md): a separate exact outward-integer certificate plus Rouché/Riemann–Hurwitz argument constructs proper connected degree-two restrictions of f_c^3 and f_c^9 on explicitly nested disk-preimage domains, uniformly for every complex |c-c*|<2^-32. All nine inner complex phase images are separated and refine the three outer phases by physical inclusion, with K9 ⊂ K3. **Source limit:** these parameters remain attracting and fail Paper 2 H3 (K(f)=J(f)); no KL rays, prime ends, sheet/coset atlas, H1–H4 gate or MLC result is promoted.
- [Exact three-scale **candidate** angle and real Markov atlas](./research/independent_audits/period27_three_scale_symbolic_marking_20261105.md): outward-integer orbit signs and exact rational-doubling arithmetic verify that twice applying the airplane substitution (0→011, 1→100) gives matching orientation-normalized critical kneading at physical return times 1/3/9 (angular periods 27/9/3). A deterministic 26-edge invariant real Markov graph and full machine-readable data are committed in [`results/period27_symbolic_marking.json`](./results/period27_symbolic_marking.json). **Boundary:** this does not identify actual parameter rays or supply the source KL prime-end/sheet atlas; all global MLC gates remain open.
- [Exact real period-27 kneading-angle and 27-point twisted permutation](./research/independent_audits/period27_kneading_angle_permutation_source_audit_20261105.md): signed-dyadic orbit data independently yield the classical kneading angle 59914011/(2^27−1), while the Baker–Chen–Li–Qian twisted-shift construction produces all 27 physical orbit ranks exactly. Classical tuning identifies these angles as *root rays of the specified twice-tuned airplane component*, not rays landing at the superattracting center. The outstanding source bridge is identifying that tuned component with the one containing the certified parameter, then transporting dynamical-plane accesses and sheets.
- [Actual exterior 9-to-3 inverse-ray pullback and sectorwise trace lift](./research/independent_audits/period27_exterior_ray_pullback_20261106.md): applies the classical global Böttcher conjugacy to the **physical** certified period-27 polynomial, proving a sharp 64-to-1 projection from 512 escaping inverse-ray points to eight, with six necessary branch bits and a normalized 64-branch direct-sum \(\dot H^{1/2}\) trace identity. The [exact regression](./research/independent_audits/verify_period27_exterior_pullback.py) checks the dyadic angles; it does **not** identify restrictive KL puzzle sheets, Julia-ray landings, source prime-end markings, or width calibration.
- [Certified nonattracting 3/9 Misiurewicz tip, parameter/dynamical rays and access collision](./research/independent_audits/period27_misiurewicz_tip_ray_access_20261106.md): exact \(2^{-128}\)-bracket for the root of \(P_{18}(c)+P_9(c)\), strict derivative, critical preperiod 10/eventual period 9 with a repelling cycle, two nested *real* restrictive return intervals, Zakeri-identified preperiodic parameter rays and four dynamical ray accesses at the critical point. The \(f^6\) exterior ray map is nonfaithful on an explicitly identified pair. [Exact regression/manifest](./research/independent_audits/verify_period27_misiurewicz_tip.py). **Not** the complete source-defined KL puzzle/prime-end/sheet transport; no MLC gate promotion.
- [Nonattracting complex quadratic-like two-scale realization](./research/independent_audits/nonattracting_tip_complex_two_scale_20261106.md): at the exact real Misiurewicz tip (where K=J), certified proper degree-two 3/9 complex returns, connected nested little filled Julia sets and physical phase routing, using new [Lean-recomputed signed-dyadic margins](./TipComplexMargins.lean), an [independent integer checker](./research/independent_audits/verify_tip_complex_domains.py) and explicitly imported Rouché/Riemann–Hurwitz. This supplies Levin (p1); its formerly missing Green-level condition (p2) is now addressed by the [uniform Carathéodory lemma](./research/independent_audits/levin_tip_p2_carathéodory_two_scale_20261106.md). The KL source ray/access/sheet atlas is still open.
- [Levin's connected-quadratic renormalization ray interface](./research/independent_audits/levin_tip_ray_correspondence_20261106.md): nine actually landed real-tip ray pairs and a Lean-checked 18-angle unlinked portrait. The conditional angular collision is now made **source-defined** by the [new (p2) proof and exact two-scale ray comparison](./research/independent_audits/levin_tip_p2_carathéodory_two_scale_20261106.md): Π9 sends 114/511 and 397/511 to 0, whereas Π3 sends them to 5/7 and 2/7. This is not a KL sheet groupoid or the unmarked ambient f^6 exterior-ray map.
- [Source-level KL first puzzle and actual 3/9 localization obstacles](./research/independent_audits/kl_tip_primitive_puzzle_and_localization_20261106.md): two actual q=2, n=1 top puzzles for f and the internal quadratic-like G=f³, with separate 3/9 physical critical first returns, rational first-level landed vertices and certified second-level internal vertex bounds; [TipKLPuzzle.lean](./TipKLPuzzle.lean) and [the independent checker](./research/independent_audits/verify_tip_kl_puzzle.py) certify strict inverse-preimage brackets at both 3 and 9 and the disjoint complex phase bounds. Kahn's one-scale based coset collisions now have concrete realizations at both periods. **First failure:** a∈B₃\\B₉ is fixed by f⁶, so naive 9→3 source/target complement maps are undefined. Does not construct the requested fully marked KL *inter-scale* sheet/groupoid functor; Issue #29 and global MLC status stay open.
- [Lean kernel-check of the complete period-27 dyadic and symbolic certificate](./research/independent_audits/lean_period27_kernel_arithmetic_20261105.md): root-bracket endpoint bounds at 2^-144, a strictly negative parameter derivative, all 26 strict orbit signs and all 27 real ranks are recomputed in Lean from the integer recurrence; a second module kernel-checks the kneading/tuning identity, full 27-state twisted shift and a conditional 9-to-3 marking-memory obstruction. The prior coarse 2^-128 endpoint-sign computation is explicitly recorded as inconclusive. Analytic interval soundness, actual KL rays/sheets and MLC gates are not promoted.
- [Lean-proved signed interval arithmetic and rational 27-step semantic soundness](./research/independent_audits/period27_rational_interval_soundness_20261105.md): **three new Lean 4.32 modules** prove outward floor/ceiling, four-corner signed multiplication, zero-crossing squaring and exact rational add/double/mul/square enclosures for arbitrary denominators. An induction then proves the actual quadratic orbit is enclosed for every rational parameter, with true positive/negative P27 endpoint signs. A separate joint recurrence proves the exact *algebraic parameter-derivative recurrence* is negative at every rational parameter in the entire source bracket. **Still open:** real IVT/MVT and equality to the calculus derivative, exact real-root existence/uniqueness in the Lean kernel, component-root rays, KL marking/sheets and global MLC gates.
- [`papers/paper3_protected_carriers/`](./papers/paper3_protected_carriers/): Paper 3 Draft III Visual Edition, modular and assembled source, deterministic build/QA tooling, change record, research assessment, and release audit.

### 3. Claim-status system

- [`ledger.json`](./ledger.json): canonical machine-readable status map.
- [`ledger.js`](./ledger.js): browser-consumable ledger data.
- [Interactive ledger](https://dovvnloading.github.io/loops-research-archive/#ledger): filterable public interface.

At the source lock the ledger contains 465 obligations: 34 imported, 316 proved, and 115 open. A count does not determine mathematical importance; the dependency graph and terminal open gates do.

### 4. Canonical research record

[`research/mlc_unified/`](./research/mlc_unified/) is the primary working record behind the manuscripts and ledger. Its entry point is [`research/mlc_unified/README.md`](./research/mlc_unified/README.md). Major classes of material include:

- source and notation locks;
- theorem and dependency ledgers;
- adversarial audits and counterexamples;
- proof-obligation packages;
- finite-state, transfer, carrier, Wave, and compactification investigations;
- novelty and value audits;
- numerical and structural validations;
- chronological research logs.

When a dated audit reports a smaller proved-node count than the current ledger, treat it as a snapshot of the state on its stated date, not as the current total.

### 5. Historical research increments

Directories named `research/mlc_research_push_*` record earlier research increments. They are not the preferred orientation layer, but they remain part of the evidentiary chain because manuscript and ledger entries point to exact artifacts within them. Use `research/mlc_unified/` for the consolidated state and the push bundle named by an evidence pointer for historical reconstruction.

### 6. Computation and figures

- [`code/`](./code/): reproducible exploratory programs.
- [`results/`](./results/): generated numerical records.
- [`figs/`](./figs/): public visual diagnostics.
- [`research/mlc_unified/figures/`](./research/mlc_unified/figures/): figure-generation manifests and proof-safety statements.

Computational output can motivate, test, falsify, or illustrate a statement. It is not classified as a proof unless a manuscript provides a separate rigorous argument.

## Research interfaces

The program is organized around interfaces rather than a single undifferentiated proof attempt.

| Interface | Question | Current record |
|---|---|---|
| Localization | What data are lost when canonical localization is treated as embedded? | Paper 1; sheet-kernel and winding data |
| End compactification | Can an exact address compactification be realized in one dynamical plane? | Paper 2; one-scale theorem |
| Protected planar routing | When can selected atoms be joined while preserving frozen obstacles and accesses, and when does that control survive a limit? | Paper 3 Draft III Visual Edition; audited finite theory and compactness gate |
| Virtual construction | Can the finite planar package be realized uniformly in the virtual carrier? | Open H1 layer |
| Quantitative transport | Does the constructed state carry the required extremal-width inequality with controlled loss? | Open H2 and stationary-Wave subgates |
| Compactness | Does the compactified state avoid analytic degeneration? | Open H3 layer |
| Rigidity | Does the limiting control imply the required dynamical rigidity? | Open H4 layer |

## Claim verification route

For any claim:

1. identify the exact theorem or ledger ID;
2. read its declared status and hypotheses;
3. inspect each dependency rather than inferring closure from a nearby theorem;
4. follow the evidence path to the cited source or internal artifact;
5. verify that source hypotheses, orientations, normalizations, and quantifiers match the use;
6. check whether a later adversarial audit narrows or repairs the statement;
7. distinguish finite, one-scale, conditional, and global conclusions.

## High-value contribution targets

The highest-leverage public targets are the open interfaces that connect the finite papers to the global reduction:

- a stage-alignment theorem connecting the Paper 1 localization model to the relevant decoration stages;
- virtual realization of the protected carrier and complete marked packet;
- pointwise two-path breaking and measurable final fixed-component exit for the stationary Wave repair;
- typed bounded-degree pushforward with the exact state data retained;
- quantitative calibration between the marked state and the source extremal-width observable;
- coercive compactness preventing degeneration of the future-observable state;
- the terminal rigidity theorem.

Contributions should follow [`CONTRIBUTING.md`](./CONTRIBUTING.md) and name the exact interface or ledger ID they address.

## Version policy

- Released papers carry explicit versions in their filenames and front matter.
- Paper 3 Draft III Visual Edition is the current public research preprint; later revisions must update the draft label, PDF link, and audit record together.
- The ledger source lock states the date to which aggregate counts and frontier summaries refer.
- Historical evidence paths remain stable even after their conclusions are consolidated into `research/mlc_unified/`.
