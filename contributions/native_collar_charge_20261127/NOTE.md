---
ledger: KKL_STATIONARY_UNIFORM_COLLAR_EXIT_CHARGE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; research, proof search, Lean implementation and adversarial review
human_review: none
---

# Native stationary collar-charge investigation

Ledger statement being addressed:

> For every proof-used horizon h<=b+2, prove either that the optimized prefix-compatible collar conductance is at most C_b(W(U minus T)+1), together with measurable source first-exit selection, or directly that the sum of marked route-exit conductances is at most that quantity. C_b must be independent of satellite period, rotation denominator, route depth within the fixed horizon, and the individual block. Qualitative collar existence and Kahn's response in the larger full width W(F) are insufficient.

## Claim

Work in progress. No new theorem, counterexample, or closure is claimed at this checkpoint. The partial designation is provisional intake metadata, not a claim of completed progress.

The target is the actual quantitative comparison between the full filled-set collar and the stationary tree or route-exit width. The archived z^2 countermodel fails the periodically repelling native hypothesis, so reproducing it would not count as progress here.

## Evidence

The initial attack is to test whether shrinking actual equipotential neighborhoods around a periodically repelling primitive-renormalizable quadratic can force optimized full-carrier collar conductance to grow faster than the vertical tree conductance. This requires proving the actual dynamical category and quantitative energy estimate; neither is assumed.

Any result counted by this investigation must be a theorem in the repository's existing Lean project, compiled by the unchanged CI with no proof holes or new axioms. Exploratory reductions and failed routes will be distinguished from such results.

## Dependencies

- KKL_STATIONARY_COLLAR_EXIT_OVERFLOW.
- KAHN_QUALITATIVE_COLLAR_VERTICAL_CHARGE_NO_GO.
- The exact native hypotheses and collar/route definitions in research/mlc_unified/kkl_stationary_uniform_collar_charge_attack.md and research/mlc_unified/kkl_stationary_route_exit_invariant.md.

## Boundary

The full obligation remains open. No new mathematical result is established at this initial checkpoint. In particular, harmonic-measure or external-uniformization assertions are not supplied as unproved Lean assumptions to disguise the missing estimate. If the attack produces no genuine new result, this draft will be closed to release the claim.

## Attribution

The existing qualitative collar analysis, z^2 countermodel and exact distinction between full width and vertical width belong to the prior archive. The native pseudo-quadratic-like and stationary Wave theory is due to Kahn, Kapiamba and Lyubich and its cited predecessors. No claim of mathematical priority or independent human review is made.
