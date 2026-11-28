# Validation record

## Exact proof inputs

The final proof sources are the following Git blobs. Documentation-only commits do not change these inputs.

| Source | Git blob SHA | Indexed public theorems |
|---|---|---:|
| `formalization/weighted/QuadraticTwinReal.lean` | `c3e79d5516135af2fef576bb856e82461b0d36c2` | 4 |
| `formalization/weighted/QuadraticTwinSemiconjugacy.lean` | `d1156ad7f07b41c8290ca8b7ccccdd8a0498fbd8` | 6 |
| `formalization/weighted/QuadraticTwinMLC.lean` | `6fcc6941bcbafcf47a2062246f7c3c3ed0bfbb1e` | 13 |
| `formalization/weighted/QuadraticTwinDiscontinuous.lean` | `e118c915119b7bca5ae90d202e101a72f83236d2` | 9 |

These four sources are present together at [source commit a39323b7cd0fda2f646d4f78090ad778354333a0](https://github.com/dovvnloading/loops-research-archive/commit/a39323b7cd0fda2f646d4f78090ad778354333a0). The branch incorporates main at `1e010c5255523faf29b09cf545eef8c948b3dce8`, preserving all of its additions. The only shared-file edits made by this packet register its sources, public theorems, and default build targets.

Toolchain: Lean 4.32.0. Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997` from the repository's existing lockfile. No toolchain, dependency, workflow, audit script, ledger, or existing theorem is changed by this packet.

## Acceptance checks

The [PR checks](https://github.com/dovvnloading/loops-research-archive/pull/277/checks) record the final exact-head outcomes. The PR description also records the final weighted run and source revision after successful completion. The acceptance checks are the existing repository gates, including:

1. `Weighted spectral mathlib proofs`: full registered Mathlib build and transitive declaration audit.
2. `Research validation`: root and standalone Lean checks, metadata and research dependency checks.
3. `Model-to-geometry coverage`: every public theorem and source is registered.
4. `Contribution intake`: the contribution note and scope conform to the repository's rules.

Local Lean is not installed in the execution environment, and the scratch filesystem could not hold a checkout. The repository explicitly permits CI to be the compiler in this case. No local Lean compilation is claimed.

## Reproduction

From the repository root:

```sh
python3 -B code/verify_lean_coverage.py
```

From `formalization/weighted`:

```sh
lake build
```

Back at the repository root:

```sh
python3 -B code/verify_lean_coverage.py --audit weighted
```

The build includes the endpoint `QuadraticTwinMLC.locallyConnectedAt_of_twin`, the exact characterization `QuadraticTwinMLC.twinParameters_iff`, and the supporting discontinuity theorem. The source checker rejects placeholders and prohibited proof escapes; the transitive audit permits only `propext`, `Classical.choice`, and `Quot.sound`. No new axioms are introduced.

## Development history

- The candidate and classical screen were recorded in commits `12d4434316d33ebbc864815dbbae6c694dbdf38d` and `bcc4cf53923482f6c5b42250cf104e8480077c1d`, before the first Lean source commit.
- [Run 46138258781](https://github.com/dovvnloading/loops-research-archive/actions/runs/46138258781), source commit `a549bf31334050f3a4d93c08a93a28c2b453feb3`, built all three original core modules and emitted `AXIOM_AUDIT_PASS weighted: 298 modules, 7767 declarations`. It also reported allowed dependencies for each new module. The overall run was superseded by the next source push, so it is not described as a green final run.
- [Run 46138955032](https://github.com/dovvnloading/loops-research-archive/actions/runs/46138955032), source commit `b2709bd30b1a2206dc2aa95638e335e9ae4cea51`, found two elaboration errors in the new supporting additions: an equality required explicit composition, and a case split removed a variable name. The core parameter theorem continued to build.
- Commit `a39323b7cd0fda2f646d4f78090ad778354333a0` repairs those two proof-script errors without changing any statement or hypothesis.

Compilation and the dependency audit establish correctness of the stated implications. They do not establish worldwide literature priority, construct a canonical Mandelbrot quotient, or construct the intertwiners from shared combinatorics.
