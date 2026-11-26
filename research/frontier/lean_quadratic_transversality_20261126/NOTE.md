# Quadratic critical-relation transversality (Lean development)

Target: H4_RIGIDITY, specifically the classical Douady–Hubbard transversality input to [MISIUREWICZ.md §2](../sharp_boundary_frontier_20261126/MISIUREWICZ.md). This draft is opened before substantive proof commits. It does not claim a new classical complex-dynamics theorem or promote any global gate.

Let P_0(c)=0, P_(j+1)(c)=P_j(c)^2+c. The goal is to show that at an actual strictly preperiodic quadratic critical orbit the first collision polynomial has nonzero parameter derivative, by an algebraic parity argument over algebraic integers rather than by assuming analytic transversality. The candidate proof is to use the signed predecessor collision, reduce its derivative divided by two modulo two, and rule out 2 being invertible in the ring of algebraic integers. The center case is the corresponding odd derivative. The source's holomorphic continuation and linearization are separate interfaces.

Acceptance: the pinned Lean 4 project must build the actual theorem and pass its existing transitive axiom audit on the exact PR head; no unproved declarations, no new assumptions masquerading as axioms, no status changes. The mathematical target above is not yet a verified result. AI assistance: ChatGPT GPT-6.2; no human specialist review.
