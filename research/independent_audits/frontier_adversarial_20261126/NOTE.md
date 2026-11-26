# Adversarial frontier investigation (2026-11-26)

Base: `47806d64c64688bdf27c817f036cfdbfa85ce1d5`. PR [#172](https://github.com/dovvnloading/loops-research-archive/pull/172).

## Findings, in proof-dependency order

| Record | Result | Scope |
|---|---|---|
| [CYCLIC_SATURATION](CYCLIC_SATURATION.md) | Least anchored saturation on finite directed graphs, with countable closure and explicit critical-value discontinuity accounting | Actual quadratic, connected empty-interior filled set; supplied physical seeds |
| [CYCLIC_RIGIDITY](CYCLIC_RIGIDITY.md) | Recognition and uniqueness of one-quadratic cyclic carriers | Actual saturated cyclic pullbacks at a fixed physical time |
| [PERIOD_INTERSECTION](PERIOD_INTERSECTION.md) | Intersection/lcm rule, period divisibility, primitive comparability; native decoration obstruction | Actual admissible quadratic-like periods; no general satellite/satellite comparability assertion |
| [SHARP_CLOCK_DEGREE](SHARP_CLOCK_DEGREE.md) | Fixed-time critical-word rigidity and intersection; subgroup forcing of critical stages; sharp degree bound | Actual cyclic carriers; exact 3/9 tip for sharpness |
| [COMPLETE_RETURN_SPECTRUM](COMPLETE_RETURN_SPECTRUM.md) | Every connected polynomial-like filled set through the critical point at the certified tip is one of X, K3, K9, with exact divisibility and degree formulas | One specified algebraic Misiurewicz parameter, all positive physical return times and all degrees |

The full native second-decoration inventory cannot be accommodated by a degree-two physical return at times 6 or 9. In fact its possible filled sets are X and K3 only, with respective degrees 2^m and 2^(m/3) (the latter when 3 divides m). At time 9 the unrestricted degree spectrum through the critical point is {2,8,512}; the full inventory excludes 2. The intrinsic period-nine restriction is not being denied.

## Exact arithmetic and reproducibility

From the repository root:

```sh
python -B research/independent_audits/frontier_adversarial_20261126/check_clock_arithmetic.py
python -B code/verify_physical_bridges.py
```

The first command was run locally under Python 3.13.5, with outward-rounded integer intervals at 256 bits and 512 deterministic residue regressions. The committed file's Git blob is `f112e7a9d58118ade698a9b9cdc61549f4adb981`. Root endpoint signs [1,-1], exact critical preperiod 10, period 9; strict Rouché margin exceeds 0.127132476 and phase separation exceeds 0.927889313. See the complete-spectrum record for the mathematical use of these inequalities. Finite regression tests are not proofs of all-period theorems. The diagnostic is registered as METADATA, not as a proof of a ledger gate. The accompanying read-only workflow runs both commands. Full checkout/validator execution was not possible locally because github.com did not resolve in the execution environment; the GitHub connector was used for repository operations.

## Gate accounting

The pinned ledger's `MAPPING_TELESCOPE` requires actual virtual-stage relative-cover lifts on relatively compact Jordan cores, with deck-phase route and critical-value retention, yielding a degree-two selected return. `H1_CELL_TREE_EXTRACTION` requires a universal finite cell-tree quotient of dynamically relevant Cantor carriers with atomic/gate incidence and partial cellular dynamics. `H1_MARKED_CONSTRUCTION` additionally requires entropy-clock checkpoints, access-faithful skeletons, selected factorizations and bounded active cores/resolved carriers.

All three remain **open**. The results apply to actual saturated physical carriers, not automatically to an arbitrary selected virtual loop or to a relative-cover return. In particular, a virtual construction may avoid the obstruction by using distinct carriers, partial arrows, or a return not identified with a closed physical iterate; its access incidence, deck phase and analytic core still require proof. The identification of the native decoration inventory with its real hull uses the earlier repository source audit. The classification of the polynomial itself does not depend on that identification.

No global MLC, H1, H2 or subsequent gate is promoted. No claim of priority over the research literature is made. This is AI-assisted research (OpenAI GPT-6.2), with written proofs and executable arithmetic, not Lean formalization or independent human peer review. Primary external inputs are identified in the proof records. Review the hypotheses of every cited theorem and the physical/virtual distinction before using the results downstream.
