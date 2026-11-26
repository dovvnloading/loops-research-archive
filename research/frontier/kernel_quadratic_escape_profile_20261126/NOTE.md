# Kernel target: uniform quadratic escape profiles

<a id="quadratic-escape-profile"></a>

Target: H4_RIGIDITY (open), specifically the uniform escape-potential passage in [MISIUREWICZ.md, section 4](../sharp_boundary_frontier_20261126/MISIUREWICZ.md). This draft targets actual quadratic iterates, not a synthetic clock. [Lean module](../../../formalization/weighted/QuadraticEscape.lean).

## Statement and proof strategy

For c,z in the complex plane, set S(z)=max(1,|z|), L(z)=log S(z), f_c(z)=z²+c, and a_n(c,z)=2^(-n)L(f_c^n(z)). The triangle inequality in both directions gives S(f_c(z)) ≤ (1+C) S(z)² and S(z)² ≤ (1+C) S(f_c(z)) whenever |c|≤C. Therefore the candidate uniform one-step defect bound is log(1+C), attained at z=1 and c=C≥0. Telescoping gives the explicit finite-tail bound (2^(-n)−2^(-n-k))log(1+C), and completeness gives the limiting escape rate g(c,z) with absolute approximation error at most 2^(-n)log(1+C). These are all-starting-points estimates, including at the cutoff and at zero.

The module also proposes the genuine functional identity g(c,f_c(z))=2g(c,z), the equivalence g(c,z)=0 iff the orbit is bounded (indeed bounded by 1+|c|), a finite threshold criterion for strictly positive escape rate, and joint continuity in c,z. With G(c)=g(c,c)=2g(c,0), the exact physical normalization is 2^m (2^p)^n G(c)=2g(c,f_c^(m+pn)(0)). Hence if c_n→c_* and the actual critical iterates f_(c_n)^(m+pn)(0)→w, then (2^p)^n G(c_n)→2^(1-m)g(c_*,w). This is the analytic transfer in the source's section 4; the critical-iterate convergence is an explicit premise, not silently assumed.

## Boundary and validation

This is a draft of actual polynomial escape-potential theorems, not a proof of Misiurewicz transversality, Koenigs/Poincaré linearization, harmonicity, convergence of equipotential domains, the conformal-radius law, H4, or MLC. The source's written argument is classical; no priority claim is made. No ledger status is changed. CI must build the pinned weighted Lake default target and audit transitive axioms using the existing coverage checker; a green documentary check alone is not proof. Local Lean is unavailable in this session. AI assistance: ChatGPT GPT-6.2; no independent human specialist review yet.

Status: candidate theorem declarations submitted, exact-head kernel check pending.
