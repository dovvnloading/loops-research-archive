---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI GPT-6.2
human_review: none
---

<a id="quadratic-critical-window-20261126"></a>

# Actual quadratic critical-window obstruction and exact local ramification

Ledger statement being addressed:

> After an actual target base is typed or uniquely selected, every demanded finite-cylinder branch image must have the open pullback component forced by INTERIOR_PULLBACK_COMPONENT_FORCING, and that reached localized component, or the globally identical component justified by the Jordan-disk component lemma, is one of the declared equal-depth target cylinders at every proof-used intermediate iterate with complete metadata and enlargement stability.

## Claim

For the actual complex map f(z)=z²+c, every finite iterate has local polynomial vanishing order exactly 2^k at a point z, where k counts encounters with 0 at times 0,...,n-1. For any N-step inverse section of an open root A containing 0, and each 0<j≤N, every set containing the j-step reached image fails injectivity under the N-step projection. These are candidate formal statements pending exact-head kernel verification; no global gate promotion.

## Evidence

The new registered module [QuadraticCriticalWindow.lean](../../formalization/weighted/QuadraticCriticalWindow.lean) imports the archive's actual complex return orbit, which is already identified with the genuine function iterate.

1. Let P_n(X)=f^n(z+X), a complex polynomial. The recursive count k_n increments precisely when f^n(z)=0. The identity P_(n+1)-P_(n+1)(0)=(P_n-P_n(0))(P_n+P_n(0)) shows that the order doubles at a critical encounter and otherwise stays unchanged. The explicit residual polynomial U_n is squared in the first case and multiplied by P_n+P_n(0) otherwise. Its value at zero is never zero, by induction.
2. The resulting polynomial identity P_n-P_n(0)=X^(2^k_n) U_n is sharpened by showing that the next power of X does not divide: cancel the nonzero power of X in the polynomial domain and evaluate at zero. This supplies exact algebraic multiplicity, not only a derivative obstruction.
3. Every open root A containing 0 contains t and -t for some t≠-t. If the residual map f^(N-j) sends U onto A, choose preimages u and v of t and -t; they are distinct. Since j>0, f^j is even, hence f^N(u)=f^N(v). If phi is an N-step inverse section on A, U=f^j(phi(A)) has precisely the surjectivity needed by this argument. Any target containing U therefore cannot be univalent under f^N. No analyticity or inverse-branch construction is assumed beyond the actual stated section identity.

Public declarations: `shiftedOrbit_eval`, `criticalCount_eq_zero_iff`, `localUnit_eval_zero_ne`, `shiftedOrbit_factor`, `shiftedOrbit_exact_order`, `local_factorization`, `orbit_add`, `positive_iterate_even`, `open_contains_reflected_pair`, `reached_projection_collision`, `central_window_no_univalent_cylinder`.

Reproduce: from formalization/weighted, run `lake build QuadraticCriticalWindow`; from the repository root, run `python3 -B code/verify_lean_coverage.py` and `python3 -B code/verify_lean_coverage.py --audit weighted`. The registered default target is built and axiom-audited by the existing weighted workflow. Local Lean is unavailable in the session; CI must establish compilation and allowed transitive dependencies. This packet is not verified until the exact head succeeds.

## Dependencies

Ledger context: DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, INTERIOR_PULLBACK_COMPONENT_FORCING. The formal statements use the actual complex orbit in QuadraticCriticalTransversality and Mathlib polynomial ring and metric-space lemmas, not any assumed virtual cylinder theorem.

## Boundary

This is a partial result targeting the same-clock univalence failure; the local order formula is an all-parameter, all-point, all-horizon refinement of the derivative argument. It does not establish target authorization, actual virtual block realization, complete demand exhaustion, equality of geometric components or enlargement stability. A ramified target, or a retimed univalent target, is not ruled out. No MLC, H1–H4, global width estimate, or change to the ledger is asserted. No claim of world-first priority is made for classical local multiplicity.

## Attribution

Builds on the archive's [reached-cylinder audit](../../research/independent_audits/virtual-reached-clock_20261126/NOTE.md), especially §4.1(iii), and the existing critical-transversality module. The classical algebra of local multiplicities is not new; the contribution is an exact formal certificate in this project's actual dynamics and the direct reflected-pair proof for its cylinder obstruction.
