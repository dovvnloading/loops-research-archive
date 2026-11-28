# Validation record

The workspace has no installed Lean compiler. Validation uses the unchanged
repository workflows and pinned Lean 4.32.0 / Mathlib project.

## Successful source revision

- Source commit: `432da2bd3593b3751a9a22177d3a6f093a4d118c`.
- [Full weighted build and audit, push run](https://github.com/dovvnloading/loops-research-archive/actions/runs/46135348714).
- [Full weighted build and audit, pull-request run](https://github.com/dovvnloading/loops-research-archive/actions/runs/46135353086).
- [Contribution intake](https://github.com/dovvnloading/loops-research-archive/actions/runs/46135352946).
- [Research validation](https://github.com/dovvnloading/loops-research-archive/actions/runs/46135352858).

The successful push run reports:

    Built QuadraticRotationRigidity (4.9s)
    Built QuadraticRotationMLC (3.2s)
    Build completed successfully (9270 jobs).
    AXIOM_AUDIT weighted QuadraticRotationMLC: 14 declarations, 11 theorems; allowed axioms only
    AXIOM_AUDIT weighted QuadraticRotationRigidity: 17 declarations, 17 theorems; allowed axioms only
    AXIOM_AUDIT_PASS weighted: 297 modules, 7770 declarations

The declaration totals include compiler-generated declarations, so they exceed
the 24 explicitly named public theorems registered for the two new sources.

The source is checked against forbidden proof escapes. The compiled audit
selects declarations by their actual originating module, then applies
Lean.collectAxioms to every declaration, including definitions. It accepts only
propext, Classical.choice and Quot.sound. It does not merely inspect namespace
names or the public theorem index. The audit script is byte-for-byte unchanged
from baseline.

The exact main conclusions are:

- LoopsQuadraticRotationRigidity.parameter_eq_of_quarter_turn_conjugacy
- LoopsQuadraticRotationRigidity.map_eq_id_of_quarter_turn_conjugacy
- LoopsQuadraticRotationMLC.fiber_eq_singleton_of_quarter_turn
- LoopsQuadraticRotationMLC.nontrivial_fiber_obstructs_quarter_turn
- LoopsQuadraticRotationMLC.locallyConnectedAt_of_quarter_turn

## First proof submission and repair

- Initial proof commit: `f01886a5d2c9830259fb23c0b0318d5e9f342797`.
- [Initial weighted run](https://github.com/dovvnloading/loops-research-archive/actions/runs/46135106529).
- Contribution intake and source coverage passed.
- The weighted build compiled the algebra and periodic boundedness helpers,
  then reported one failed simplification in the final polynomial-bound step.
- The repair transports the already proved identity with congrArg norm in an
  explicit calculation. It also replaces a redundant field_simp/ring calculation
  by the pinned cancellation lemma mul_div_cancel₀.
- No theorem statement or hypothesis was weakened.

## Reproduction

With the pinned Lean toolchain installed, from the repository root:

    cd formalization/weighted
    lake exe cache get
    lake build QuadraticRotationRigidity QuadraticRotationMLC
    cd ../..
    python3 -B code/verify_lean_coverage.py --audit weighted

The unchanged CI builds the entire weighted default-target set before auditing.
The final documentation-only revision preserves exactly the successful Lean
sources and registration files. Its CI runs are visible in the PR checks.

Compilation establishes the formal statements under their displayed hypotheses.
It does not certify mathematical priority or establish the existence of the
quarter-turn-compatible intertwiners for unresolved combinatorial fibers.
