# Independent mathematical and evidence audits

This directory contains reproducible audits of research claims in the archive. It is **not** a proof of Mandelbrot local connectivity and does not change the status of the source-locked global ledger obligations. The finite issues resolved here have their own explicit acceptance criteria and proof boundaries.

## Independent boundary-spectrum route (November 2026)

- [Fejér criterion and critical Sobolev regularity](mlc_boundary_spectral_program_20261111.md) derives the uniformly Cauchy criterion, distinguishes ordinary boundary sums from continuous radial traces, and gives finite estimates away from the circle.
- [Inverse-log-cubed area-tail obstruction](mlc_logarithmic_area_tail_barrier_20261112.md) derives the lower bound $\limsup_j j^3 E_{2^j-1}\ge \pi^2/(12\log 2)$ from the published landing sequence and Gronwall's area identity. MLC remains open.
- [Coefficient verifier](verify_mlc_spectrum_extended.py) and [512-coefficient manifest](../../results/mlc_spectrum_exact_511_20261112.json) record nine complete dyadic packets. The published OEIS prefix is a table cross-check. The verifier also checks the critical-orbit polynomial identity against the finite coefficient series.
- [Lean certificates](../../MandelbrotSpectrum.lean) cover finite summation by parts with both endpoint terms, its square-weight specialization, the five-coefficient energy and residual, the radius-two squared error budget, and the arithmetic of the first Fejér difference. Run `lake build MandelbrotSpectrum` from the root. The analytic inequalities and asymptotic obstruction have written proofs.

## Issue 29: source-defined collision resolution

The [five-objective resolution record](issue29_source_defined_collision_resolution_20261106.md) identifies the actual canonical map, the infinite fine-sheet fiber and the native KL boundary joints where the displayed whole-mark comparison fails. This satisfies the issue's explicit collision alternative; it does not assert faithful all-scale or protected transport.

- **[tip_iterated_direct_canonical_localization_embedding_20261106.md](tip_iterated_direct_canonical_localization_embedding_20261106.md)**: a correctly marked `K9` morphism gives a strict open embedding of the iterated 3-then-3 canonical target into the direct period-nine target. Its fine-to-coarse projection has the full coset fiber and all-path naturality. A native coarse-stage KL pseudo-piece immerses into the fine surface; its deck orbits identify actual fine-sheet collisions, and the composite fails at its `lambda/xi` and `lambda/eta` joints. No whole-native-tile embedding or separately identified fine prime-end image is assumed.
- **[tip_interval_root_and_marked_morphism_obstruction_20261106.md](tip_interval_root_and_marked_morphism_obstruction_20261106.md)**: `K9=[x9,x18]`, all nine fine phases are exact real intervals, and `K3` contains a four-arm star. Compactness, the open mapping theorem and local star pullbacks exclude every holomorphic marked morphism with full source root `K9` and full target root `K3`. The [exact checker](verify_tip_root_topology.py) verifies the finite inputs and [interval-phase manifest](../../results/tip_root_interval_geometry.json); the general morphism theorem is a written analytic proof.
- **[tip_kl_pseudopiece_side_atlas_20261106.md](tip_kl_pseudopiece_side_atlas_20261106.md)**: exact ordinary source sides for all 24 tiles of `P,QL,QR,V0,W` at the two stages; based seams, ambient endpoint representatives, integer winding and same-stage side/interior collisions. The [checker](verify_tip_kl_side_atlas.py) regenerates the [side atlas](../../results/tip_kl_side_atlas.json). Holomorphic localization and ideal-boundary interpretation are separately proved.
- **[tip_localization_access_lifts_and_germ_alignment_20261106.md](tip_localization_access_lifts_and_germ_alignment_20261106.md)**: finite-modulus annular target, exact two-interval boundary extension, integer-valued access lifts and finite physical/canonical germ alignment. Lifting the earlier annular comparison to a universal target tile is a biholomorphism; its fibers alone were insufficient to identify a KL tile collision.
- **[tip_kl_marking_source_types_20261106.md](tip_kl_marking_source_types_20261106.md)**: version-locked primary sources, corrected printed page locators, actual KL `O/xi/eta` definitions, marked-root typing, and the scope of the native collision. No source-locked manuscript or ledger is rewritten.

## New mathlib-backed real center verification

- **[lean_period27_real_center_20261105.md](lean_period27_real_center_20261105.md)**: kernel-checked real calculus, IVT and strict MVT uniqueness for the actual period-27 quadratic parameter, plus exact minimal period from all 26 early orbit enclosures. These are finite real-polynomial results; no global MLC or KL geometric gate is closed.

## Contents

- **[tip_kl_terminal_first_child_20261106.md](tip_kl_terminal_first_child_20261106.md)**: both source KL modified principal nests terminate at their first children, with `E0=int Y3`, `E1=int Y6`, `chi=1`, primitive stage period three and physical periods three/nine. The proof identifies the terminal filled sets with the old complex certificates and checks Paper 2's local standing hypotheses. The [exact checker](verify_tip_kl_terminal_first_child.py) verifies finite interval, boundary and clock inputs; these are distinct from the global ledger gates.

- **[tip_localization_refinement_peripheral_monodromy_20261106.md](tip_localization_refinement_peripheral_monodromy_20261106.md)**: an actual based holomorphic 9→3 comparison on the common exterior, with trivial pullback subgroup, countably infinite sheet fibers and naturality for every path. It proves the opposite inclusion has no lift between canonical target covers, and a deck-limit obstruction prevents extension over the entire conformal ideal circle. Its formerly missing source-side identification is handled by the distinct native construction above; arbitrary protected-boundary compatibility remains open. These are all-word covering-space proofs, not a finite enumeration or a new Lean formalization.

- **[period27_center_tuning_identification_20261106.md](period27_center_tuning_identification_20261106.md)**: resolves the separate old-center component identity: the certified period-27 center is the center of `A*A*A`. Buff–Floyd–Koch–Parry's exact center-to-root-ray assertion and Zakeri's tuning/unique-root-component statements supply the analytic bridge; the [checker](verify_period27_center_tuning_identification.py) verifies every sign, source convention and tuning angle. The center still fails Paper 2's `K=J` hypothesis.

- **[tip_puzzle_ray_tree_20261106.md](tip_puzzle_ray_tree_20261106.md)**: analytic slit-branch proof and complete ambient alpha-ray table through depth six (64 vertices, 128 rays), including the nonreal first-child vertices and strict Jordan containment of `Y^6` in `Y^3`. The [exact checker](verify_tip_puzzle_ray_tree.py) regenerates the [full manifest](../../results/tip_puzzle_ray_tree.json); complex landing and polynomial-like germ uniqueness are written analytic inputs.

- **[tip_internal_puzzle_ambient_lifts_20261106.md](tip_internal_puzzle_ambient_lifts_20261106.md)**: actual ambient rays `2/9,7/9` at the dividing fixed point of `G=f^3`, with forced Levin images `2/3,1/3`, and all ambient lifts of its internal alpha puzzle through depth six. The [exact checker](verify_tip_internal_ray_lifts.py) verifies central eight-to-two pullbacks, every finite angle correspondence and the [manifest](../../results/tip_internal_ray_lifts.json). This supplies the ray/access labels used by the separate source-side atlas above.

- **[kl_tip_primitive_puzzle_and_localization_20261106.md](kl_tip_primitive_puzzle_and_localization_20261106.md)**: source-aligned successive top KL puzzles for the ambient f and the polynomial-like return G=f³ (both q=2, n=1, with distinct physical first returns p=3 and 9), exact landed α/α′/critical puzzle vertex ray-access table, and *two actual scale-specific Kahn localization coset collisions* based on exact off-cycle real preimages of 0. A separate point-level witness shows identity and f⁶ do **not** map the nine-scale deleted surfaces into the three-scale ones. This earlier note did not construct the interscale map; the canonical comparison above now supplies the issue's explicit collision alternative. Companion [TipKLPuzzle.lean](../../TipKLPuzzle.lean) and [verify_tip_kl_puzzle.py](verify_tip_kl_puzzle.py) check finite arithmetic, not source geometry.

- **[tip_kl_top_puzzle_and_localization_complement_20261106.md](tip_kl_top_puzzle_and_localization_complement_20261106.md)**: first source-level Kahn–Lyubich top-puzzle identification at the nonattracting tip (dividing q=2, first escape n=1, P=Y¹, V⁰=Y³), rational ray-vertex candidates, and a **certified obstruction** to the *naïve physical* 9→3 localization target-complement inclusion at z=31/1024. The separate based KL sheet/groupoid transport remains open. New [Lean arithmetic](../../TipKLPuzzle.lean) and [independent exact checker](verify_tip_kl_puzzle.py).

- **[levin_tip_p2_carathéodory_two_scale_20261106.md](levin_tip_p2_carathéodory_two_scale_20261106.md)**: exact source (p2) quantifiers; a uniform positive ambient Green-level margin via Milnor's subhyperbolic Julia-local-connectivity theorem and Carathéodory ray landing; actual Levin Π9 collision at 0 and distinct Π3 angle pair 5/7 vs 2/7. Analytic theorems imported, not Lean-formalized; no numerical b or KL sheet groupoid. **[verify_tip_levin_transport.py](verify_tip_levin_transport.py)** independently checks the finite angle enumeration.
- **[nonattracting_tip_complex_two_scale_20261106.md](nonattracting_tip_complex_two_scale_20261106.md)**: nonattracting 3/9 complex polynomial-like realization from exact inequalities and classical analytic steps. Lean 4.32 recomputes 3/9 Rouché margins, phase disjointness, critical exclusion and 9-to-3 containment, including a failed old-radius negative control. Its formerly open Levin (p2) gate is supplied by the **subsequent** Carathéodory audit above; KL marking remains open.
- **[TipComplexMargins.lean](../../TipComplexMargins.lean)**, **verify_tip_complex_domains.py**, and [exact JSON manifest](../../results/tip_complex_domains.json): finite arithmetic and reproducibility; analytic topology is a separately written theorem, not kernel formalized.

- **[levin_tip_ray_correspondence_20261106.md](levin_tip_ray_correspondence_20261106.md)**: a missing source connection (Levin, Theorems 1–3), the needed (p1)/(p2) hypotheses, actual period-nine ray landing along the Misiurewicz tip's repelling cycle, and a conditional forced noninjective renormalization-angle fiber.
- **[TipRayPortrait.lean](../../TipRayPortrait.lean)**: core Lean theorems checking 18 primitive-period-nine distinct angles, unlinked chords and the semiconjugacy collapse implication.
- **verify_tip_ray_portrait.py**: independent exact rational arithmetic regression and comparison against [manifest](../../results/period27_tip_ray_portrait.json).

- **[period27_misiurewicz_tip_ray_access_20261106.md](period27_misiurewicz_tip_ray_access_20261106.md)**: exact nonattracting real postcritically finite parameter with real period-3/9 restrictive returns; imported Zakeri theorem identifies genuine parameter and dynamical ray landings, and critical-point rays yield a first explicit physical \(f^6\) access collision. No KL prime-end/sheet atlas or MLC gate is claimed.
- **verify_period27_misiurewicz_tip.py**: deterministic standard-library signed-integer/fraction certificate, with exact published JSON manifest [results/period27_misiurewicz_tip.json](../../results/period27_misiurewicz_tip.json); this checks finite recurrence and angles, not the imported landing theorem.

- **[period27_exterior_ray_pullback_20261106.md](period27_exterior_ray_pullback_20261106.md)**: physical escaping-basin Böttcher inverse-ray theorem for the certified period-27 center. The 9-to-3 map is exactly 64-to-1 on distinct ray/equipotential points; a separate 64-branch homogeneous trace direct-sum formula has exact \(1/8\) normalization. These statements do **not** identify KL restrictive-domain sheet cosets or ray landing.
- **verify_period27_exterior_pullback.py**: dependency-free exact audit of all 512 dyadic ray labels, the 64-fold projection and lifts, collision witnesses and trace-scale coefficients; it does not verify the imported Böttcher theorem.

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
    python research/independent_audits/verify_tip_root_topology.py --check-manifest
    python research/independent_audits/verify_tip_kl_side_atlas.py --check-manifest
    lake build Period27IntervalSound Period27RationalTrace Period27RationalDerivative
    python research/independent_audits/audit_ledger_evidence.py . --strict

The last command is **expected to exit nonzero** until broken source pointers are repaired or the actual source files restored. Do not change an entry from open to proved or redirect evidence simply to make this check pass.

## Scope and review rule

An internal proof, a deterministic test, a correct citation, and independent expert verification are distinct forms of evidence. New entries in this directory preserve that distinction. No external mathematical priority, publication acceptance, or institutional endorsement is asserted.

Baseline from GitHub main at 2026-11-04; this branch was created after the repository was unarchived.
