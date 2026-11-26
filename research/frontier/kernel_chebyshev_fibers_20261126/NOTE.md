# Kernel frontier: exact Chebyshev fibers (H1/H4 input)

Base main: `433a120f44472eec0d351b19a92ff495fb39d9ae`. Draft investigation, no newly verified theorem yet.

Target: at the actual quadratic parameter c = -2 (the Misiurewicz example in `research/frontier/sharp_boundary_frontier_20261126/MISIUREWICZ.md`), formalize the Joukowski semiconjugacy, bounded-orbit classification and sharp two-sheet boundary fibers. This is a direct dynamical model with actual complex points, not a freely chosen finite carrier. It tests the distinction between a singleton planar point and multiple boundary addresses. Do not identify these algebraic fibers with a general physical KL prime-end chain, nor infer H1/H4/MLC closure. The separate open transversality and escape-potential PRs are not assumed merged.

Acceptance: registered default Lean target, exact-head successful CI, transitive axiom audit using the existing coverage checker; no proof holes, no new axioms or trust-guard changes. Classical Chebyshev/Joukowski identities are not a world-priority claim. AI assistance: OpenAI ChatGPT GPT-6.2 (proof search, code and audit); no independent human specialist review.
