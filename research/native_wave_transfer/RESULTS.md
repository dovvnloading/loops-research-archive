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

## Physical comparison — primitive outer period 3 versus period 4

The second, independent input is
[`physical_examples/primitive4_tip12.json`](physical_examples/primitive4_tip12.json),
with source-specific field citations and strict
[parameter certificate](physical_examples/primitive4_tip12_parameter.json).
It uses the same finite marking/proper-restriction algorithms, **not**
different mathematical definitions. The original `tip_pr68` code, data,
contract, lock and manifest have not been changed. The new source lock and
[immutable manifest](experiment_manifests/primitive4_tip12.json)
are checked by `regenerate_period4.py --check`.

| Observable | `tip_pr68`: physical `p=3` | `primitive4_tip12`: physical `p=4` |
| --- | --- | --- |
| Parameter | `c≈-1.7865105445443248`; pinned `2^-128` bracket, `x18=-x9` | `c≈-1.9425541714947619053`; unique root `x24=-x12` in adjacent `2^-160` bracket, strict signs and derivative |
| Physical return and degree | `G=f^3`, global 8, central 2; `U3=D(0,1/4)` | `G=f^4`, global 16, central 2; `U4=D(0,1/16)` with strict Rouché margin `>1/25` |
| Primitive/inner geometry | real three-phase inner period-9 tip, existing analytic central restriction | primitive period-four physical return with four pairwise disjoint phase balls; inner period-12 central degree-two Rouché margin `>1/100` |
| Marked tree | `T=[x6,x3]`; `Tprime=[-x3,x3]` | `T=[x8,x4]`; `Tprime=[-x4,x4]` |
| Inner ideal atom counts | 10 target, 20 source; one outer-component atom | 10 target, 20 source; one outer-component atom |
| Complete attachment census | one `[-x3,x6)` rooted at `x6`, atoms `S19,S0,S1` | one `[-x4,x8)` rooted at `x8`, atoms `S19,S0,S1` |
| `f_*` covering | `S_s → I_(s mod 10)` | `S_s → I_(s mod 10)` independently bisected and computed |
| `iota^*` immersion | block sizes `5,2,1,1,3,1,3,1,1,2`; `P0` only nonproper | identical block sizes; `P0` only nonproper; attached sides land in target interior |
| Proper restrictions, same endpoint class | crossing `(S3,S1),(S19,S17)` (2); avoiding `(S3,S17)` (1) | crossing `(S3,S1),(S19,S17)` (2); avoiding `(S3,S17)` (1) |
| Cover-pushed restrictions | crossing `(I3,I1),(I9,I7)`; avoiding `(I3,I7)` | same independently calculated covering images |
| Old real edge incidence | `[[0,0,1],[1,0,1],[1,1,0]]` (existing issue-40 native edge audit) | `[[0,0,1],[1,0,1],[1,1,0]]`, derived from three mapped physical edges **once each** |
| Exact Perron root | `phi=(1+sqrt(5))/2` | `phi=(1+sqrt(5))/2`; polynomial `t^3-2t-1`, positive left weights `(phi,1,phi)` |
| Zero-old-edge crest sectors | `I0,I2,I5,I8`; actual Wave parent/children `I0,I2,I8` all zero | `I0,I2,I5,I8`; actual Wave parent/children `I0,I2,I8` all zero |
| Parent Wave width | `log(4/3)/(2*pi)` | `log(3/2)/(2*pi)` |
| Each child and pushed width | `log(4/3)/pi` | `log(3/2)/pi` |
| Harmonic-series test | **equality**, not strict gain | **equality**, not strict gain |

The p=3 edge and zero-old-edge rows are pinned to the source-side
[physical issue-40 audit](../independent_audits/issue40_native_attachment_edge_incidence_20261115/NOTE.md),
which explicitly counts each real edge once and distinguishes whole atomic
open intervals from closed Wave crests. The new p=4 output derives its own
matrix and all three distinct zero-edge sets from *physical* real
segments, both inverse sheets, and separate cover/inclusion operations.
Both cases have a genuine two-versus-one marked breakage. This remains a
finite, source-dependent prime-end interpretation, not a general KKL result.

**What depends on `p`.** The polynomial and dyadic parameter, global
iterate degree `2^p`, physical phase-ball separation, source/target scale,
critical orbit labels, available closed-disk margin, and the concrete
rational Wave radius interval change. In these two cases the *inner*
three-phase kneading order is the same, so the induced cut/attachment
**combinatorics**, old-edge matrix, 2/1 path multiplicities, and zero-crest
types agree. The different log ratio (`4/3` versus `3/2`) is chosen
from the two allowed Wave radius ranges, **not** forced by `p`.
In particular no statement that these finite counts or widths are
functions of return time alone is justified.

### Certification boundary of the comparison

**Certified by machine-exact arithmetic:** The period-four parameter is
the unique root in its stated dyadic interval (opposite rigorous endpoint
signs and a strict derivative sign); degree-two central `f^4` and
`f^12` domains follow by strict complex Rouché enclosures; all four
physical phase balls are disjoint; the real interval factors, cut orders,
two inverse sheets, 10/20 atom counts, one attachment over all
central degree-two fibers, finite subordination filters, full-disk bounds,
entire Wave gate range, three old-edge incidence rows, exact Perron
algebra, zero-edge atom census, and rational harmonic coefficients are
independently checked. Existing `tip_pr68` exact checks are unchanged and
regenerated byte-identically.

**Conditional on stated mathematics:** Identification of the real
Chebyshev-tip little Julia interval and the native full Hubbard-tree
marking; physical slit prime ends, KKL Propositions 6.5–6.6, its
short-multi-interval and proper-restriction notions, relative ideal-access
homotopy, and the analytic identification of log-rectangle coefficients
with extremal widths under the stated conformal maps. In particular,
a finite `2/1` comparison does **not** establish a new general path theorem.
The p=3 complex quadratic-like assumption remains imported from its prior
source; the p=4 central degree-two domains are newly Rouché-certified.

**Numerical-only:** None. Approximate parameter displays in the table
are illustrative, not certificates, and no floating-point eigenvalue or
wave-width approximation is used as a proof.

**Open:** Nonlocally connected canonical-localized KL maps and complete
general attachment/prime-end gate censuses; arbitrary path-level and
**closed-crest** Wave transport; zero-old-edge **subsector** escape and a
same-path edge-charge-to-extremal-width bridge; any general strict
harmonic inequality, H1–H4, UPTCR or MLC. The exact harmonic equality
in *both* physical cases rules out inferring strict gain merely from
a larger physical iterate or from the old-edge Perron root.
