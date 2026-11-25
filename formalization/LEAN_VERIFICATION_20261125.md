# Lean verification audit — 25 November 2026

**Baseline:** `1ca308c90b8bd3a4bb5ab4230986ea6f053f5a9f`.
**Toolchain:** repository-pinned Lean 4.32.0, with the pinned Mathlib
project under `formalization/weighted`.

The baseline formalization builds successfully. This audit found no
uncovered Lean source file or source-level proof hole. It also identified
specific written results whose finite or algebraic parts are now proved in
Lean. A successful build establishes the formal statements with their
declared hypotheses; it does not turn every written theorem, imported
source result, or open physical identification into a Lean proof.

## 1. Inventory and evidence boundary

The baseline contains **95 Lean files**: **37 root modules**, **53 weighted
modules**, and **five standalone audit modules**. The source/contract scan
finds **842 named public theorems and lemmas** across **39 registered
contracts**. The files are covered by the root, weighted, or standalone
CI build commands. These counts describe source coverage, not progress
toward MLC or the number of independently established physical theorems.

In particular, `ResearchLedger.lean` checks documentary structure and
finite ledger facts. The ledger's **316 archive-internal proofs** are not
316 Lean formalizations of their mathematical content. Read the
[ledger evidence crosswalk](LEDGER_EVIDENCE_CROSSWALK.md), the
[physical bridge register](PHYSICAL_BRIDGES.md), and the
[theorem index](physical_bridge_index.json) for the respective meanings.

No `sorry`/`admit` proof hole, ad hoc axiom declaration, or orphan Lean
file was identified by the baseline source scan. Source scanning is a
guard against omissions; exact-revision compilation and declared axiom
dependencies supply the separate kernel evidence. Standard foundational
dependencies must be reported accurately rather than described as
axiom-free merely because a source file contains no `axiom` command.

## 2. New verification work

### Complete finite native-mark grammar

[`NativeMarkSaturation.lean`](../NativeMarkSaturation.lean) extends
[`ImmersionMarkFinite.lean`](../ImmersionMarkFinite.lean) to the complete
grammar used by the [November 24 native-mark audit](../research/independent_audits/native_mark_attack_20261124/NOTE.md):
100 open arcs including ten punctured circles, 90 proper closed arcs,
and one complete circle. Distinct entries represent distinct states.
All 191 inputs reach the full circle within five pushes, and the exact
open-atom first-saturation times are `[2,4,4,5,4,3,4,5,4,4]`.

The module also checks the four exact-turn endpoint regressions,
the `q=2,b=2` finite limb census, and conditional logical propagation to
the no-chain conclusion. The final source includes a one-step closure
theorem ensuring that successors remain within the same grammar.
It has **17 public theorems**, each with an axiom-dependency printout.

This formalizes finite contour bookkeeping. The native-action
identification still uses the explicitly imported KKL Propositions
6.5–6.6; the physical descendant propagation uses A.14. The actual
proper-path/homotopy arguments and full independent `MARK` obligation
retain their stated status. See the
[component and native-action contract](PHYSICAL_BRIDGES_CONTRACTS.md#native-component-refinements).

### Clone characteristic polynomial and spectrum

The modules [ClonePolynomialRoots.lean](weighted/ClonePolynomialRoots.lean),
[FullCloneCharpoly.lean](weighted/FullCloneCharpoly.lean), and
[FullCloneGapCollapse.lean](weighted/FullCloneGapCollapse.lean) close the previously written
simplicity/Vieta and matrix-characteristic-polynomial steps in the
[clone spectral audit](../research/independent_audits/clone_strict_spectrum_and_no_uniform_expansion_20261107.md).
They prove separability and the modulus product of
`X^(2n+5)-X-1`, and equality with the characteristic polynomial of the
**actual** complexified graph adjacency matrix.

The matrix proof reuses the existing root-to-eigenvector theorem in
[FullCloneRenewal.lean](weighted/FullCloneRenewal.lean), which already checks
the actual adjacency rows. Separability, equal degree, and monicity then
identify the characteristic polynomial with algebraic multiplicities.
The new module states the literal determinant identity, semisimplicity,
and the spanning of the whole complex vector space by eigenspaces.

For every delay and its positive root, the gap module supplies an actual
nonleading eigenvalue with `0<t_n-‖μ‖<1/(n+2)`. It proves absolute and
relative nonuniformity for every positive tolerance. The proof erases the
simple leading root from the exact modulus product, forces another root
of modulus at least `1/t_n`, and combines the existing strict separation
and root-excess bounds. It does not assume the characteristic polynomial
or a maximum-modulus bound as a hypothesis. The newer cubic asymptotic
remains written, and no native KL edge realization is supplied.

### Complete compilation and axiom enforcement

The final source inventory is **99 Lean files** (38 root, 56 weighted,
five standalone) and **880 named public theorems/lemmas** in the existing
contract index. The four new modules contain 38 public theorem declarations.

The [coverage guard](../code/verify_lean_coverage.py) checks all source
assignments, Lake targets, matching pinned toolchains, and prohibited
proof/trust tokens after masking strings and nested comments. Its compiled
audit selects declarations by their actual module provenance, including
definitions and private helpers. It calls Lean's `collectAxioms` and
accepts only `propext`, `Classical.choice`, and `Quot.sound`.
Every selected module must contain declarations and theorems, preventing
an empty selection from passing. At the verified proof revision the audit
checks **3,112 declarations**: 1,625 in the root project, 1,401 in the
weighted project, and 86 in the five standalone files. These counts include
private helpers and compiler-generated declarations; they are distinct from
the 880 named public theorems and lemmas.

The five standalone research files are compiled in the same root workflow,
then checked with the same axiom policy. Ten Python adversarial regressions
exercise the source/coverage guard. Four actual Lean fixtures require a
clean theorem to pass and custom-axiom, native-evaluation, and empty-module
cases to be rejected for the expected audit reason. This is separate from
the [physical bridge checker](../code/verify_physical_bridges.py), which
enforces the source-to-contract references and status discipline.

## 3. What remains outside these formalizations

The [bridge register](PHYSICAL_BRIDGES.md) distinguishes written,
imported, conditional, and open claims. The following boundaries survive
the new finite/algebraic checks:

| Interface | Exact remaining work |
|---|---|
| `DEFECT` | The rank algebra in `AttachmentDefectLedger.lean` does not construct the actual reduced Čech groups or prove their Mayer–Vietoris exactness and planar-duality interpretation. See [two-scale bridges](TWO_SCALE_PHYSICAL_BRIDGES.md). |
| `SHEETS`, `ENDS`, `SLIT-CLASSES` | General covering-fiber results do not instantiate a named KL cover, its peripheral defect loop, the direct-decoration end compactification, or the actual slit prime ends. See [cover and end contracts](TWO_SCALE_PHYSICAL_BRIDGES.md). |
| `VARIABLE-EXIT`, `BUFFER-ZERO` | Finite endpoint-cover algebra does not establish Borel exit existence, conformal modulus additivity, peripheral degree geometry, slit-ring embeddings, or the hyperbolic collar estimates. See [width contracts](PHYSICAL_BRIDGES_WIDTH.md). |
| `RENEWAL-GAP` | A characteristic polynomial and finite nonuniform-gap estimate do not prove selection of the first subleading conjugate pair or the limit `D³(1-r/t) → π²/2`. The analytic branch and remainder argument remain [written](../research/independent_audits/clone_renewal_clock_20261123.md). |
| H1–H4, UPTCR, MLC | Universal construction, calibration/transport, nondegenerate analytic compactness, and rigidity on the same physical tower remain open. [`ResearchGates.lean`](../ResearchGates.lean) proves their logical composition under its inputs. |

The buffered-width theorem is specifically for the selected whole-component
marking and periods `p≥10`; neither refined markings nor `p≤9` follow.
Conditional statements should retain their hypotheses, and imported
theorems should retain their source attribution.

## 4. Ranked next Lean tasks

1. **Actual real Markov spectrum and return counts.** Formalize the
   26-edge characteristic-polynomial factorization and all-horizon
   Fibonacci return counts in
   [`period27_real_markov_bridge_20261123.md`](../research/independent_audits/period27_real_markov_bridge_20261123.md),
   using the existing `weighted/Period27RealMarkov.lean` and
   `weighted/Period27FiniteFibers.lean`. This is a concrete algebraic
   extension of an already formal physical interval-map bridge.
2. **Clone stationary law and renewal asymptotic.** First formalize the explicit positive stationary probability and
   cylinder law retained as premises by `weighted/FullCloneCorrelation.lean`.
   Then formalize root ordering, the analytic implicit branch, and a controlled expansion in
   [`clone_renewal_clock_20261123.md`](../research/independent_audits/clone_renewal_clock_20261123.md).
   Keep the exact stationary law and physical clock explicit.
3. **Selected prime-end and component bridge.** Formalize
   [`IDEAL_BOUNDARY.md`](../research/independent_audits/marked_slit_path_bridge_20261123/IDEAL_BOUNDARY.md)
   and the component results in
   [`native_mark_attack_20261124/NOTE.md`](../research/independent_audits/native_mark_attack_20261124/NOTE.md).
   Preserve path occurrences, traces, homotopy classes, and endpoint
   inclusions; the new finite grammar does not identify them.
4. **Actual modulus transfer.** Formalize the Borel-support and
   cyclic-cover theorems in
   [`maximal_exit_transfer_20261123/NOTE.md`](../research/independent_audits/maximal_exit_transfer_20261123/NOTE.md)
   before connecting `weighted/StationaryEndpointCover.lean` to physical
   extremal widths. Exit existence remains a separate research premise.
5. **All-class buffered exclusion.** Transfer the exact certificates and
   slit-ring/collar proof in
   [`canonical_width_attack_20261124/NOTE.md`](../research/independent_audits/canonical_width_attack_20261124/NOTE.md)
   to analytic Lean statements, preserving its period and marking scope.
6. **Čech attachment and infinite carriers.** Supply the topological
   hypotheses behind `weighted/AttachmentDefectLedger.lean`, and then
   address the protected infinite-limit interfaces documented in
   [`TWO_SCALE_PHYSICAL_BRIDGES.md`](TWO_SCALE_PHYSICAL_BRIDGES.md).
   These require substantial topology rather than more finite tables.

## 5. Reproduction and CI evidence

Run from the repository root with the pinned toolchain:

```sh
python3 -B code/verify_lean_coverage.py
python3 -B code/verify_physical_bridges.py
python3 -B code/verify_lean_frontier_sync.py
python3 -B code/verify_lean_coverage.py --self-test
lake build
python3 -B code/verify_lean_coverage.py --test-kernel-audit
python3 -B code/verify_lean_coverage.py --audit root
python3 -B code/verify_lean_coverage.py --audit standalone
cd formalization/weighted
lake build
cd ../..
python3 -B code/verify_lean_coverage.py --audit weighted
```

Standalone audit modules are also compiled by the
[Lean workflow](../.github/workflows/lean-proofs.yml). The coverage guard
checks source/build wiring and compiled axiom dependencies. The physical
bridge checker separately verifies the theorem/contract index.

| Revision / scope | Evidence |
|---|---|
| Baseline root project and Python regressions | [Successful run 45703478395](https://github.com/dovvnloading/loops-research-archive/actions/runs/45703478395) |
| Baseline weighted project | [Successful run 45703478308](https://github.com/dovvnloading/loops-research-archive/actions/runs/45703478308) |
| First 16 native-mark theorems, `0822271` | [Successful core job](https://github.com/dovvnloading/loops-research-archive/actions/runs/45704703096/job/139523573654) |
| Complete proof and audit revision `a9dcbb89f6a6105f36610de0be930002b01f25bb` | [Root, standalone, and Python checks](https://github.com/dovvnloading/loops-research-archive/actions/runs/45707763753) · [Weighted build and axiom audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45707763695) |


AI assistance: OpenAI GPT-6 Astra Pro performed source review, proof
construction, and verification integration. This audit does not assert
independent human specialist review or a proof of MLC.
