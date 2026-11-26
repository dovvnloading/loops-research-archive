# Extended CS dividing-multiplier locus

**Verdict: INCONCLUSIVE (preregistered; computation not yet performed).**

## Limits
Finite sampled evidence only, even when local root enclosures are rigorous. No certified wake/mark identification unless separately proved, no whole-copy upper bound, no infinite-tail assertion, no Theorem D extension or MLC/JLC claim.

## Preregistration (before new numerical computation)
For f_c(z)=z²+c, q=3,4,5,..., P_i=product of the first i denominators and P_0=1, use the actual absolute-period P_{i-1} dividing multiplier rho_i and the attachment-continued logarithm z_i=log(rho_i)/(2*pi*I), CS arXiv:1509.07843v1 printed p.52 (31)–(32), as in merged #139. Prediction: the scaled norms q_i |z_i| stay in [0.9,1.2] at the next levels q=8 (P=20160), and q=9 (P=181440) if feasible. Test on linked child centers, attachment roots, and deterministic interior child multiplier chart samples including the original four directions; use nested angular grids at radii 0.95 and 0.99 where feasible, reporting actual completed densities, maxima and any failed points. Retain ancestor observations where feasible. The observed maximum is a lower estimate of the whole-copy supremum, not an upper bound. Compare independent 50- and 80-decimal-digit runs (or higher); require agreement of reported scaled norms within 1e-10, numerical period/linkage/mark tests inherited from #139, and local interval inclusion plus proper-period exclusions for centers, parent attachment solutions and dividing cycles at centers where possible. Root anchors alone cannot pass.

Decision: PREDICTION FAILS if a numerically linked, converged non-anchor sample lies outside [0.9,1.2] by more than 1e-10 (state certification separately); PREDICTION HOLDS (finite sampled evidence only, list certified levels) if q=8 completes both precisions, passes inherited linkage checks, center and all accepted primary chart samples are inside the interval with margin 1e-10, no required primary sample fails, and q=9 either passes the same tests or is explicitly infeasible under the resource budget. Primary chart samples are the four original directions (0.99, -0.95, +0.95i, -0.95i); any accepted denser-grid violation also fails. Otherwise INCONCLUSIVE, including unresolved precision/mark checks or ambiguous log branch. Report interval certification separately from numerical linkage and coverage. Do not extrapolate a pass to the full copy or infinite tail. A certified algebraic periodic orbit is not by itself a certified dividing mark.

## Inputs
Merged #139: ../cs_multiplier_locus_numerics_20261126/NOTE.md and measure.py; independent review https://github.com/dovvnloading/loops-research-archive/pull/139#issuecomment-7183305806. Prior audit #136; no modification to either.

Status: OPEN / METADATA; GPT-6.2 assisted research, human specialist verification not performed.
