# Kernel target: extremal quadratic multiplier rigidity

<a id="quadratic-extremal-multiplier"></a>

Target: H4_RIGIDITY (open), [MISIUREWICZ.md §7](../sharp_boundary_frontier_20261126/MISIUREWICZ.md). Develop the actual quadratic bounded-orbit radius bound, multiplier bound and its equality rigidity, with quantitative strengthening if possible. Use the existing `QuadraticEscape` definitions. Distinguish genuine orbit statements from model estimates. No global gate or novelty claim.

Acceptance: pinned weighted Lake build and transitive axiom audit at the exact PR head. Until those succeed, declarations are candidates only. Local Lean is unavailable in this session. AI assistance: ChatGPT GPT-6.2; no independent specialist review.

First proof commit: growth outside max(2,|c|), critical-parameter radius two, bounded-orbit radius two, the sharper squared bound, and a derivative recurrence for actual iterates. [Lean source](../../../formalization/weighted/QuadraticExtremalMultiplier.lean). CI pending.

## Quantitative strengthening

Candidate statement: whenever |c|, |f_c(z)|, and |f_c²(z)| are at most 2, then |c+2|² ≤ 288(4−|z|²). The parallelogram identity gives |f_c(z)+c|² ≤ 8(4−|z|²), and the next radial deficit is at most four times the present one. Write w=f_c(z), u=f_c(w). The exact identity c(c+2)=(c+w)(c−w)+(u+c) gives |c||c+2| ≤ 4|w+c|+|u+c|. For |c|≥1, squaring and using (2|w+c|−|u+c|)²≥0 gives the constant 288; for |c|<1 the claim follows from |z|²≤2+|c| and |c+2|≤3. The constant is explicit but not claimed optimal.

Consequently on every bounded orbit at a critical-bounded parameter, the squared norm of the actual n-fold complex derivative is bounded by (16−|c+2|²/72)^n, for every n≥0. This supplies a per-iterate exponential gap uniformly on parameter regions separated from −2, not merely a pointwise strict inequality for each fixed period. Equality at a positive iterate forces c=−2, and the fixed point 2 at that parameter attains the bound. No periodicity or repelling assumption is required for the estimate. The earlier source's qualitative equality case is written; the quantitative strengthening is new to this PR, without a literature priority claim. No conformal-radius asymptotic or global H4 conclusion follows without the separate missing analytic interfaces. Exact-head kernel and axiom validation pending.

## Compiler repair

Weighted run [45848689610](https://github.com/dovvnloading/loops-research-archive/actions/runs/45848689610) rejected the first quantitative candidate at the derivative identity/addition API, numeral-square normalizations, one implicit norm type, a non-targeted power rewrite, and the multiplicative cancellation lemma name. These are Lean elaboration failures, not a validated proof. This revision uses a function-level derivative identity with the derivative of a constant, explicit numeral normalization and typed arguments, the correct targeted power expansion and the pinned cancellation lemma. The theorem statements, trust guards, and proof scope are unchanged. The earlier source-registration repair passed the Model-to-geometry coverage and main Research validation jobs. The new exact-head weighted build and audit must pass independently.
