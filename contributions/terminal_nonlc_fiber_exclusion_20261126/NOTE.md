---
ledger: TERMINAL_NONLC_HUBBARD_CARRIER_PROPER
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="terminal-nonlc-fiber-exclusion-20261126"></a>

# Terminal non-LC carrier: fiber exclusion without full-preimage equality

## Claim

Verified first-checkpoint Lean result: for a finite family of compact connected physical marks and a least compact connected physical carrier, a fiber over a noncut model point with path-connected complement is excluded from the carrier exactly when it is excluded from all marks. In a compact physical space with a continuous surjective monotone semiconjugacy onto a locally path-connected Hausdorff model, a physical noncut fixed point whose full fiber is singleton is therefore excluded from the least carrier of disjoint cyclic marks. The final theorem specializes to the genuine quadratic filled set. The first six declarations passed CI at the checkpoint recorded below.

## Evidence

[TerminalFiberExclusion.lean](../../formalization/weighted/TerminalFiberExclusion.lean) contains six public theorems:
- `fixed_fiber_avoids_cycle`
- `finite_marks_compact_bridge`
- `model_puncture_path_connected`
- `least_carrier_fiber_exclusion_iff`
- `terminal_cycle_least_carrier_proper`
- `quadratic_terminal_least_carrier_proper`

The finite compact bridge is assembled from the model images of the marks and finitely many paths in the punctured model. Its full inverse is compact and connected by closed monotone quotient transport. Leastness places the physical carrier in this inverse. A singleton fiber at a fixed model point cannot intersect disjoint successive physical marks. The image of the physical puncture equals the model puncture, so the latter is connected and, by local path connectivity, path connected.

The local shell lacks Lean and networked git; the weighted workflow is the compilation and dependency-audit judge. Reproduce with `cd formalization/weighted && lake build TerminalFiberExclusion` and `python3 -B code/verify_lean_coverage.py --audit weighted` from the repository root.

## Dependencies

KKL_NATIVE_TERMINAL_HUBBARD_TREE, TERMINAL_LC_NATIVE_HUBBARD_CARRIER_PROPER. StationaryMonotoneGeometry.preconnected_preimage_closed_fibers and StationaryFiberDynamics.quadratic_filled_compact (qualified by their Loops namespaces). Mathlib compactness, connectedness and path connectivity.

## Boundary

The result does not identify KKL's named natural quotient or actual physical carrier with a least compact connected carrier, does not establish its actual fixed-point fiber is singleton, nor does it assert the carrier is saturated. The physical noncut point and model local path connectivity are explicit hypotheses. The source-level identification, the polynomial-like transport, and all ledger gates remain open. No claim of literature priority.

## Attribution

Builds on Kahn–Kapiamba–Lyubich's terminal Hubbard construction, Kiwi's rational-lamination model (see the archive's kkl_stationary_n2_kiwi_model_identification_audit_20260727.md), and the archive's earlier geometric quotient theorems.

## Verified checkpoint and stronger follow-up

Commit [2d243ab](https://github.com/dovvnloading/loops-research-archive/commit/2d243ab45ce3b4399cb63c32c3d730538c885f90) passed both push and [pull-request weighted Lean CI](https://github.com/dovvnloading/loops-research-archive/actions/runs/45875889290), including the full transitive axiom audit: 6 declarations, 6 theorems in TerminalFiberExclusion; 75 modules, 2046 declarations overall. Contribution intake passed as well.

The follow-up adds a compact connected neighborhood lemma and an exact avoidance criterion for an arbitrary closed forbidden set: the compact marked image must lie entirely within one complementary component. This removes the path-connectivity requirement and any finiteness restriction on the compact marked subset in that criterion. The terminal-cycle and actual-quadratic corollaries then require only a locally connected Hausdorff model and connected least carrier. Follow-up Lean verification is pending; see this PR's head CI. The named KKL physical carrier still needs a proof of leastness and the precise source identification.

### Invariant carrier existence follow-up

The first stronger CI attempt ([run 45876549132](https://github.com/dovvnloading/loops-research-archive/actions/runs/45876549132)) rejected two elaboration details, now corrected: explicitly changing preimage membership into membership in the model envelope, and restoring the nonempty witness after destructuring. The new work also formalizes inclusion-minimality implying leastness in a hereditarily unicoherent compact space, actual filled-set reflection and surjectivity, and existence of a proper forward-invariant least carrier of the primitive marked cycle when one phase contains the critical point. This combines the earlier verified least-carrier existence and critical-preimage results with the new exclusion mechanism, discharging invariance, compactness, surjectivity, reflection, and existence of the carrier rather than assuming them all. Hereditary unicoherence, the monotone model, the singleton noncut fixed-point fiber, and the physical primitive cycle are hypotheses; identity with the named KKL lift is still not proved. These additions are pending weighted CI.

The next weighted build ([run 45876848014](https://github.com/dovvnloading/loops-research-archive/actions/runs/45876848014)) confirmed that the two local-connectivity errors had been repaired, and reported one remaining rewrite-pattern error in actual filled-set surjectivity: a lambda application needed an explicit beta-reduced equality. This is corrected in the next commit. The full new result is not counted until its build and transitive audit both pass.
