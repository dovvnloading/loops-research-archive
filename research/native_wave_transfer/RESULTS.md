# Native Wave Transfer Laboratory — PR #68 physical regression

**Case:** ordinary degree-two `G=f_{c_*}³:V3→D(0,1/4)` and actual tree
inclusion; source lock is `source_contracts/LOCK.json`. **Not** the
unrestricted canonical KKL localization or PR #67's duplicated KL tiles.

| Observable | Recomputed (exact symbolic/interval unless noted) | Dependency |
| --- | --- | --- |
| Inner target ideal atoms | `10` from five ordered physical cuts and upper/lower/tip accesses | KKL Appendix A.1 and physical induced-marking choice |
| Inner covering-source atoms | `20`; independent inverse-branch isolation yields `f_*(S_s)=I_(s mod 10)` | physical degree-two source, KKL §6.1 |
| Complete tree attachment census | `T=[x6,x3]`, `Tprime=[-x3,x3]`; one attachment `[-x3,x6)` rooted at `x6`, source attachment atoms `S19,S0,S1` | **conditional** on the prior complex degree-two theorem / dendrite |
| Actual immersion pullback `iota^*` | cyclic block lengths `5,2,1,1,3,1,3,1,1,2`; all end-proper; only `P0` not proper | KKL Prop. 6.5, not identification with `f_*` |
| Filtered marked source paths | crossing: `(3,1),(19,17)` → push `(3,1),(9,7)`; avoiding `(3,17)` → push `(3,7)` | rational endpoints; KKL A.1/A.3.2 rules |
| Same target ideal endpoints | both `(I1,I9)`; restriction counts `2` and `1` | rational circle homotopy; prime-end topology cited |
| Whole closed-disk bounds | small `|G(B)| < 1/20`, larger `< 21/100`; clearance > `1/5` and > `1/25` | exact rational ball enclosures |
| Wave | `-9/64` center, `3/256<r<1/64`; target base `(I9,I0,I1)`, pushed bases `(I1,I2,I3)`, `(I7,I8,I9)` | exact whole-range inequalities, KKL marking |
| Symbolic width equality | `W=log(4/3)/(2π)`; each child and push `log(4/3)/π = 2W`; harmonic-series **equality** | exact fraction algebra **plus** analytic rectangle/conformal invariance argument |

## Epistemic boundary

**Machine-certified conditional arithmetic:** strict dyadic orbit and cut
orders at scale `2^-256`; isolated negative inverse branches with 78 rational
bisection steps; nonoverlap and sided source labels; finite block partition,
refinement and both marking filters; entire complex-disk bounds (not boundary
samples); all radii in the wave interval; equality of rational *coefficients*
in the symbolic harmonic-series formula. The immutable manifest also checks
its own byte-for-byte canonical form, code hash, source blobs and the
independent projection against `results/tip_KKL_tree_marked_breakage_20261109.json`.

**Written analytic assumptions, not proved by Python:** parameter's
algebraic identity and Julia interval descriptions from prior certificates;
physical source component has degree two; dendrite characterization and
*complete* complex preimage of the tree; prime-end identification and the
induced ideal marking; KKL's pullback/attachment theorem and restriction
semantics; relative-ideal-endpoint homotopy; analytic extremal widths,
conformal invariance and injectivity on this wave support. The program
checks compatible exact bounds but does not independently prove those facts.

**Numerical-only claims:** none in the committed result. No floating-point
computation or plotted sample is used as a certificate; the strings containing
`log` and `pi` are exact *symbolic* expressions, not decimal approximations.

**Open:** arbitrary canonical-localized path groupoids, the other connector
words, selected-geodesic behavior, general/nonlocally-connected attachment
censuses, uniform Wave gain / H1–H4, UPTCR, and MLC. No claim is made that
the authors' theorem is contradicted, or that a local equality provides
strict amplification. This lab validates *one implementation at one source-
locked physical representative*, not a general theorem.

## Audit protocol

`regenerate.py --check` is read-only and fails on code/input/source/manifest
or reference drift. `test_regenerate.py` supplies independent hard-coded
oracles and adversarial failures. The CI workflow executes both, the legacy
PR #68 manifest check (without importing it into the new code), and a Lean
`TipKKLTreeMarking` build. Because the existing *Research validation* and
*Actual KKL tree marking* workflows have path filters that do not include
this new directory, the new workflow explicitly runs their relevant checks;
any skipped old workflow must not be misreported as a passing run.
