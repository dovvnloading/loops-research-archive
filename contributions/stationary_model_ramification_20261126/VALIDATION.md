# Lean validation

Audited at `2026-11-26T20:54:58.928709-05:00` (America/New_York).

## Toolchain and scope

The three new modules compiled locally with Lean **4.32.0**, compiler commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, using the repository's weighted
Lean project and its pinned dependency versions. Mathlib is pinned to
`81a5d257c8e410db227a6665ed08f64fea08e997`; all nine dependency revisions
were checked against `formalization/weighted/lake-manifest.json`.

The focused transitive audit uses the repository's unmodified
`code/verify_lean_coverage.py::audit_command`, selecting declarations by
module provenance. Every selected declaration, including private and generated
declarations, was checked with `Lean.collectAxioms`. Every transitive axiom
belongs to the allowed set `propext`, `Classical.choice`, `Quot.sound`.
The audit rejected no declaration and exited with status 0.

| Module | All declarations | Theorem declarations |
|---|---:|---:|
| `StationaryRamificationCensus` | 22 | 16 |
| `StationaryModelRamification` | 13 | 13 |
| `StationaryModelBranchLocus` | 9 | 9 |
| **Total** | **44** | **38** |

The theorem counts include private and generated kernel declarations; they are
not a count of new mathematical claims or public theorem names.

## Audited source hashes

SHA-256 was recorded before the audit. Both source hashes and compiled-object
hashes were checked again afterward to confirm that the audited inputs did
not change during the run.

| Source | SHA-256 |
|---|---|
| `formalization/weighted/StationaryRamificationCensus.lean` | `227e3b2f6c0be3f513488ae2679d65677e56528afa49fe7700bc54b230a03f5d` |
| `formalization/weighted/StationaryModelRamification.lean` | `72690212f97cab4b3c731c02fcd0f2bc267705468568dad63ea6a455efe0ccc6` |
| `formalization/weighted/StationaryModelBranchLocus.lean` | `2c12ba3a18c43bdca4ca358a357beb3b877df4f1d914e275fac76096122f1500` |

## Exact focused audit output

```text
AXIOM_AUDIT stationary-model-ramification-final StationaryRamificationCensus: 22 declarations, 16 theorems; allowed axioms only
AXIOM_AUDIT stationary-model-ramification-final StationaryModelRamification: 13 declarations, 13 theorems; allowed axioms only
AXIOM_AUDIT stationary-model-ramification-final StationaryModelBranchLocus: 9 declarations, 9 theorems; allowed axioms only
AXIOM_AUDIT_PASS stationary-model-ramification-final: 3 modules, 44 declarations
```

## Registration and source trust checks

Both commands exited with status 0:

```text
python -B code/verify_lean_coverage.py
python -B code/verify_physical_bridges.py
```

The source guard reported **193 registered Lean files**: 38 root, 150 weighted,
and 5 standalone, with no prohibited proof or trust escapes. The bridge checker
reported 90 bridge rows, 466 indexed sources, and 1,831 named theorems/lemmas,
with evidence paths and public statuses consistent.

## Reproduction and CI

From the repository root, the standard project checks are:

```bash
python -B code/verify_lean_coverage.py
python -B code/verify_physical_bridges.py
(cd formalization/weighted && lake build)
python -B code/verify_lean_coverage.py --audit weighted
```

The final command audits the complete weighted project, including these three
modules. The focused local audit above is a subset of that CI gate.

CI results and their exact commit association are recorded in the pull request's
Checks tab. The proof-bearing commit `70453d86e253398ae3b3d8f17b663371ccbc528d`
triggered the
[weighted Lean workflow](https://github.com/dovvnloading/loops-research-archive/actions/runs/45925257334)
and the
[research validation workflow](https://github.com/dovvnloading/loops-research-archive/actions/runs/45925257335).
This local report does not infer a workflow conclusion; use those run records
and the latest PR checks for the CI verdict.
