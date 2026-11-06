# Independent mathematical and evidence audits

This directory contains reproducible audits of research claims in the archive. It is **not** a proof of Mandelbrot local connectivity and does not change the status of any open obligation.

## New mathlib-backed real center verification

- **[lean_period27_real_center_20261105.md](lean_period27_real_center_20261105.md)**: kernel-checked real calculus, IVT and strict MVT uniqueness for the actual period-27 quadratic parameter, plus exact minimal period from all 26 early orbit enclosures. These are finite real-polynomial results; no global MLC or KL geometric gate is closed.

## Contents

- **clone_spectral_referee_note.md**: self-contained calculation checking a delayed-cross-section clone formula against the convention printed in Kahn–Kapiamba–Lyubich, arXiv:2606.27272v1, Appendix C. It includes two-sided finite-clone estimates and a second-order fixed-template asymptotic. Specialist confirmation of the source interpretation and novelty is still required.
- **verify_clone_spectral.py**: standalone finite-matrix numerical regressions for the clone formula, including an independently constructed whole adjacency matrix and a two-gate example.
- **evidence_audit_20261104.md**: baseline of unresolved proof-evidence pointers in the 465-entry proof ledger as found on November 4, 2026.
- **audit_ledger_evidence.py**: standard-library-only diagnostic of the ledger's dependency wiring and plain Markdown proof pointers. It checks *traceability*, not theorem correctness.
- **two_scale_complex_window_obstructions_20261105.md**: precise proofs that the original complex collar parameter disk is uniformly attracting of exact period 27, an eightfold larger disk also fails Paper 2 H3, and equal-width stadium/preimage domains fail compact containment at both real restrictive levels.
- **verify_complex_window_obstructions.py**: exact (2^{-224})-dyadic recurrence checks for the attracting disk, lower-period exclusion, and stadium first-failure thresholds; depends only on the earlier exact real two-scale certificate engine.
- **complex_two_scale_quadratic_like_certificate_20261105.md**: explicit uniform complex parameter-disk construction of nested quadratic-like degree-two period-3 and period-9 returns, with actual phase inclusion and connected filled Julia sets; retains Paper 2 H3 and MLC limitations.
- **verify_complex_quadratic_like_3_9.py**: no-float outward signed-integer certificate of Rouché boundary margins, precritical avoidance, connected-return trapping, nine-phase separation and 9-to-3 complex phase nesting.
- **period27_three_scale_symbolic_marking_20261105.md**: exact candidate 3/9/27 rational ray-angle kneading match, orientation-adjusted real return kneading, source-facing first-failure checklist, and a strictly real 26-edge Markov partition.
- **verify_period27_symbolic_atlas.py**: standard-library-only signed-dyadic/rational-integer audit of angle periods, substitution, internal addresses, real orbit order, all three kneading matches and byte-for-byte reproduction of `results/period27_symbolic_marking.json`.
- **period27_kneading_angle_permutation_source_audit_20261105.md**: source-level separation of Baker–Chen–Li–Qian's real-center kneading angle, their lexicographic twisted-shift permutation, and Douady–Hubbard/Zakeri *root* parameter-ray tuning; records the still-open parameter-component and KL sheet/access bridge.
- **verify_period27_kneading_angle_permutation.py**: exact all-27-sign kneading-angle reconstruction, modular doubled-angle admissibility, and independent lexical versus real-rank 27-cycle comparison.
- **lean_period27_kernel_arithmetic_20261105.md**: sources, strict scope and reproduction for two core-Lean modules that recheck the parameter bracket at 2^-144, derivative, orbit order and symbolic kneading/rank correspondence; explicitly distinguishes kernel finite computation from nonformalized interval soundness and ray geometry.
- **period27_rational_interval_soundness_20261105.md**: genuine Lean proof of generic signed-dyadic floor/ceiling, four-corner products and zero-crossing squares for **arbitrary rational fractions**, plus induction for all quadratic orbit steps and joint derivative recurrence; proves exact rational endpoint P27 signs and rational-bracket algebraic derivative negativity, while real IVT/MVT and complex source geometry remain open.
- **Period27IntervalSound.lean** (root): generic signed interval arithmetic, including correctness of outward rounding for arbitrary rational numerators/positive denominators.
- **Period27RationalTrace.lean** (root): exact rational quadratic recurrence, arbitrary-length semantic enclosure theorem and certified positive/negative *true* period-27 rational endpoint iterates.
- **Period27RationalDerivative.lean** (root): arbitrary-length joint orbit/algebraic parameter-derivative recurrence and negativity for all rational parameters within the source bracket.
- **Period27Dyadic.lean / Period27Kneading.lean** (root): new default Lean targets checked by GitHub Actions without native_decide or proof holes.

## Run locally

From the repository root:

    python -m pip install numpy
    python research/independent_audits/verify_clone_spectral.py
    python research/independent_audits/verify_real_nested_3_9.py
    python research/independent_audits/verify_complex_window_obstructions.py
    python research/independent_audits/verify_complex_quadratic_like_3_9.py
    python research/independent_audits/verify_period27_symbolic_atlas.py --check-manifest
    python research/independent_audits/verify_period27_kneading_angle_permutation.py
    lake build Period27IntervalSound Period27RationalTrace Period27RationalDerivative
    python research/independent_audits/audit_ledger_evidence.py . --strict

The last command is **expected to exit nonzero** until broken source pointers are repaired or the actual source files restored. Do not change an entry from open to proved or redirect evidence simply to make this check pass.

## Scope and review rule

An internal proof, a deterministic test, a correct citation, and independent expert verification are distinct forms of evidence. New entries in this directory preserve that distinction. No external mathematical priority, publication acceptance, or institutional endorsement is asserted.

Baseline from GitHub main at 2026-11-04; this branch was created after the repository was unarchived.
