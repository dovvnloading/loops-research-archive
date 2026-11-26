---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="univalent-telescope-collars-20261126"></a>

# Univalent open collars of actual quadratic telescope cores

## Claim

Work in progress. The target is to prove in Lean that an actual finite quadratic
iterate, injective on a compact selected pullback component and with no
preterminal critical encounter there, is injective on an open neighborhood of
that component. Combining this with the existing proper-component perturbation
theorem should give open univalent selected restrictions over sufficiently small
target collars. No result is claimed until its Lean theorem compiles in CI and
passes the repository's transitive axiom audit.

## Evidence

The first proof-development checkpoint contains registered Lean source for:

1. `QuadraticUnivalentNeighborhood`: separate the compact intermediate images
   from their negatives; inductively construct one open injective domain for the
   actual quadratic iterate, inside a prescribed open ambient set.
2. `TelescopeUnivalentCollars`: characterize exactly when compact injectivity
   extends to an open neighborhood, then construct actual full selected
   pullback collars with compact closure, injectivity on the closure,
   prescribed ambient containment, properness and full target surjectivity.
3. `TelescopeConformalInverse`: construct an analytic inverse on the whole
   target, its reciprocal derivative, and compatible inverse restriction and
   chronological concatenation identities.

These are candidate proofs pending local and CI compilation at this checkpoint.
The exact pinned Lean 4.32.0 toolchain and Mathlib revision are available locally;
no toolchain, dependency or workflow changes are proposed. Reproduction:

```sh
cd formalization/weighted
lake build QuadraticUnivalentNeighborhood TelescopeUnivalentCollars TelescopeConformalInverse
cd ../..
python code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

The final packet will include the successful full build, transitive axiom audit,
and the exact remaining geometric boundary. Candidate declarations are not
counted as proved results while that validation is pending.

## Dependencies

Research target: MAPPING_TELESCOPE. Existing formal inputs:
TelescopeCollarRecognition, TelescopeRamification, SaturatedTelescope, and the
pinned Mathlib. The ledger prerequisites PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER,
RELATIVE_COVER_LIFT, and STAGE_FORWARD_CLOSURE describe the research context;
their documentary status will not be imported as mathematical assumptions.

## Boundary

This work addresses a conditional actual-map collar construction. The native
virtual-molecule core, its univalence and critical avoidance, compatible cyclic
Jordan domains, marked relative-cover lifts, and complete deck-phase route
remain to be constructed. No closure of MAPPING_TELESCOPE, H1, or MLC is claimed,
and no ledger status change is requested. No priority claim over classical
complex analysis or topology is intended.

## Attribution

Builds on contributions/saturated_telescope_20261126 and
contributions/telescope_ramification_order_20261126, especially the actual
proper-component upper semicontinuity theorem in TelescopeCollarRecognition.
Proof development and adversarial review are AI-assisted; no human review.
