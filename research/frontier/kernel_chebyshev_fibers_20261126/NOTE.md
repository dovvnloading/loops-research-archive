# Kernel frontier: exact Chebyshev fibers (H1/H4 input)

Base main: `433a120f44472eec0d351b19a92ff495fb39d9ae`. Draft investigation, no newly verified theorem yet.

<a id="chebyshev-fibers"></a>

Target: at the actual quadratic parameter c = -2 (the Misiurewicz example in `research/frontier/sharp_boundary_frontier_20261126/MISIUREWICZ.md`), formalize the Joukowski semiconjugacy, bounded-orbit classification and sharp two-sheet boundary fibers. This is a direct dynamical model with actual complex points, not a freely chosen finite carrier. It tests the distinction between a singleton planar point and multiple boundary addresses. Do not identify these algebraic fibers with a general physical KL prime-end chain, nor infer H1/H4/MLC closure. The separate open transversality and escape-potential PRs are not assumed merged.

Acceptance: registered default Lean target, exact-head successful CI, transitive axiom audit using the existing coverage checker; no proof holes, no new axioms or trust-guard changes. Classical Chebyshev/Joukowski identities are not a world-priority claim. AI assistance: OpenAI ChatGPT GPT-6.2 (proof search, code and audit); no independent human specialist review.

## Candidate proof and first CI diagnostics

[Lean module](../../../formalization/weighted/ChebyshevFibers.lean). For nonzero w, write J(w)=w+1/w. Every z has a reciprocal pair w,v via a square root of z²−4. The identity f(J(w))=J(w²) iterates exactly. A reciprocal lift of modulus greater than one has orbit norm at least |w|^(2^n)−1, ruling out boundedness. On the unit circle the inverse is conjugation, hence J is real and lies in [−2,2]; the real interval is forward invariant. Thus the actual filled bounded-orbit set equals the segment. Factoring the equation J(w)=J(v) shows that the only ambiguity is inversion. A putative equivariant section at the fixed planar point −1 would require a nonzero fixed square-root address w²=w, forcing w=1 and J(w)=2, a contradiction.

First Lean run [45846004992](https://github.com/dovvnloading/loops-research-archive/actions/runs/45846004992) reached the module but failed on four simplification/cast goals, now addressed. Coverage run [45846004810](https://github.com/dovvnloading/loops-research-archive/actions/runs/45846004810) required an index entry, supplied without promoting the status of either gate. Exact-head build and axiom audit still required.

## All-return-clock extension

The candidate general obstruction is stronger than the single fixed point: for each p>0, a primitive complex root of unity of order 2^p+1 has a planar point J(w) of least period p. Its return is inversion, w^(2^p)=1/w, with distinct addresses. For 0<k<p neither 2^k−1 nor 2^k+1 is a positive multiple of 2^p+1. Hence no earlier planar return is possible. In general the least lift period is the least planar period or twice it: every lift return projects, and a swapping return squares to an address return. The factor two is attained at every positive period. Consequently no fixed positive iterate admits a global single-valued equivariant address selection on the actual filled segment, even without continuity. This is an exact all-period statement about a single actual polynomial, not a universal geometry claim; classical primitive roots of unity are supplied by Mathlib. CI and transitive axiom checks remain the acceptance test.
