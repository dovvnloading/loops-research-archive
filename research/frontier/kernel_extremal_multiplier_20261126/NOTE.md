# Kernel target: extremal quadratic multiplier rigidity

<a id="quadratic-extremal-multiplier"></a>

Target: H4_RIGIDITY (open), [MISIUREWICZ.md §7](../sharp_boundary_frontier_20261126/MISIUREWICZ.md). Develop the actual quadratic bounded-orbit radius bound, multiplier bound and its equality rigidity, with quantitative strengthening if possible. Use the existing `QuadraticEscape` definitions. Distinguish genuine orbit statements from model estimates. No global gate or novelty claim.

Acceptance: pinned weighted Lake build and transitive axiom audit at the exact PR head. Until those succeed, declarations are candidates only. Local Lean is unavailable in this session. AI assistance: ChatGPT GPT-6.2; no independent specialist review.

First proof commit: growth outside max(2,|c|), critical-parameter radius two, bounded-orbit radius two, the sharper squared bound, and a derivative recurrence for actual iterates. [Lean source](../../../formalization/weighted/QuadraticExtremalMultiplier.lean). CI pending.
