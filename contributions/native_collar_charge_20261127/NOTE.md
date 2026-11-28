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

Closed unsuccessful investigation. No new theorem, counterexample, or closure was established. The partial designation records the original draft intake only; this packet is not submitted as mathematical progress.

The target is the actual quantitative comparison between the full filled-set collar and the stationary tree or route-exit width. The archived z^2 countermodel fails the periodically repelling native hypothesis, so reproducing it would not count as progress here.

## Evidence

The initial attack is to test whether shrinking actual equipotential neighborhoods around a periodically repelling primitive-renormalizable quadratic can force optimized full-carrier collar conductance to grow faster than the vertical tree conductance. This requires proving the actual dynamical category and quantitative energy estimate; neither is assumed.

Any result counted by this investigation must be a theorem in the repository's existing Lean project, compiled by the unchanged CI with no proof holes or new axioms. Exploratory reductions and failed routes will be distinguished from such results.

### First adversarial checkpoint: the two alternatives cannot be conflated

The tentative equipotential construction would address only the first alternative. For an ordinary inclusion model with source at escape level t/2^h, the h-fold polynomial covering still maps the complement of the complete pullback of T to the target complement of T with degree 2^h. Consequently a comparison for outer-boundary exits can remain available even if every collar surrounding the whole filled set has much larger conductance. A failure of the full-carrier collar route is not a counterexample to the disjunctive ledger statement.

The stronger analytic estimate under investigation is a thin-equipotential capacity asymptotic: t times the capacity of (T,{g_K<t}) should tend to 2*pi times the equilibrium harmonic measure of T. This is an unproved research route, not a Lean theorem or a novelty claim. A cutoff times a flattened Green ramp suggests the upper bound, while radial energy in exterior coordinates suggests the lower bound. Establishing those coordinates, energy transformations, flux convergence and competitor regularity is essential; none may be inserted as an assumption and then counted as a solution of the original problem.

There is also a native-category obstruction to using the existing real examples immediately. Their dividing rotation denominator is two. The high-type stationary setting and its bound on little Julia sets per limb require a separate source-category check. A real postcritically finite example alone does not settle that check.

These observations reject two premature claims: that the existing actual real-tip modules already provide a native stationary counterexample, and that a hypothetical full-collar counterexample closes the route-exit obligation. No new theorem is established at this checkpoint.

## Dependencies

- KKL_STATIONARY_COLLAR_EXIT_OVERFLOW.
- KAHN_QUALITATIVE_COLLAR_VERTICAL_CHARGE_NO_GO.
- The exact native hypotheses and collar/route definitions in research/mlc_unified/kkl_stationary_uniform_collar_charge_attack.md and research/mlc_unified/kkl_stationary_route_exit_invariant.md.

## Boundary

The full obligation remains open. No new mathematical result was established. In particular, harmonic-measure or external-uniformization assertions are not supplied as unproved Lean assumptions to disguise the missing estimate. The draft is closed to release the claim, as required by AGENTS.md for an investigation without a genuine new result.

## Attribution

The existing qualitative collar analysis, z^2 countermodel and exact distinction between full width and vertical width belong to the prior archive. The native pseudo-quadratic-like and stationary Wave theory is due to Kahn, Kapiamba and Lyubich and its cited predecessors. No claim of mathematical priority or independent human review is made.
