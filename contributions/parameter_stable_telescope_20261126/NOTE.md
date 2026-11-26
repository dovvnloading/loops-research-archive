---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="parameter-stable-telescope-20261126"></a>

# Parameter stability of actual quadratic telescope collars

Ledger statement being addressed:

> Every actual finite virtual stage cycle admits compatible selected relative-cover lifts that are embedded on relatively compact Jordan cores, preserve the full component and deck-phase route, and retain the propagated critical value after the unique quadratic stage, so that the planar critical-spine compiler produces a closed degree-two selected return.

## Claim

Work in progress. This draft claims the parameter-stability subproblem: strengthen the existing fixed-parameter compact univalence theorem for actual iterates of z ↦ z²+c to a common parameter neighborhood and a common phase collar, and derive stable inverse-branch consequences. No mathematical result is claimed before the corresponding Lean theorem compiles and passes the existing kernel audit.

## Evidence

The first proof source is committed in QuadraticParameterUnivalence.lean. It gives the exact divided-difference factorization, derives nonvanishing from compact injectivity and critical avoidance, and uses compactness to construct common parameter and phase neighborhoods with a positive inverse-distance bound. Compilation and audit are pending.

The proof development is placed in the existing Mathlib Lean project under formalization/weighted/ and registered with code/contribute.py lean-add. Checkpoints will be committed to this pull request. The existing QuadraticUnivalentNeighborhood, TelescopeUnivalentCollars, and TelescopeConformalInverse modules provide the starting point.

## Dependencies

The contribution extends the existing formal compact-univalence and finite telescope results. The exact dependency list and theorem statements will be recorded with the completed proof.

## Boundary

MAPPING_TELESCOPE remains open. Parameter stability of an independently supplied compact injective critical-free itinerary does not construct the native marked itinerary, Jordan cores, relative-cover lifts, or the unique critical stage. No claim is made about H1–H4, UPTCR, or MLC, and no status record is changed.

## Attribution

This work builds on the existing repository Lean developments and their cited sources. The final note will identify the exact reused theorems and the increment proved here.
