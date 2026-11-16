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

## Satellite comparison — real period-doubling return, specification refusal

**Status: source-valid satellite candidate, exact quadratic-like certificate,
but *not representable* as the unchanged v1 physical interval-marking record.**
Following the explicit refusal rule of this laboratory, no fake
`PhysicalExample`, satellite `f_*` / `iota^*` table, or Wave width is
asserted. See the [negative physical input](physical_examples/satellite2_period4_obstruction.json),
[exact executable](regenerate_satellite2.py),
[adversarial tests](test_satellite2.py), and
[immutable obstruction manifest](experiment_manifests/satellite2_period4_obstruction.json).
The existing two primitive code paths, data records, source contracts, and
manifests are still byte-identical; the new tests check the original seven
input/code/manifest Git blob identities.

### Choice of parameter, return, and first structural difference

Let `f(z)=z^2+c`, `x0=0`, and `x(k+1)=x(k)^2+c`.
Choose the **unique** real zero of `x4=0` in the adjacent
`2^-128` dyadics with numerators

`[-446008997123623373135743845318053032736,
  -446008997123623373135743845318053032735]`.

This is approximately `c=-1.31070264133683288356`, the
period-four superattracting center in the real doubling cascade.
The code certifies **strict** endpoint signs `x4(lo)<0<x4(hi)` and
`d(x4)/dc>0` over the entire bracket; it verifies `x2 in (2/5,1/2)`,
`x1<-1`, `x3<-1`. Thus the original critical orbit has exact
period four. Take **physical return p=2**, `G=f^2`, of global degree four,
not the physical `p=4` return of `primitive4_tip12`.

Use `U2=D(0,4/5)` and `V2=component(G^-1(U2),0)`.
The **exact** identity
`G(z)=z^4+2*c*z^2+(c^2+c)` gives, on `|z|=4/5`,

`|2c|*(4/5)^2 - |c^2+c| - (4/5)^4 - 4/5 > 3/50 > 0`.

Rouché therefore yields **exactly two preimages inside
D(0,4/5) for every w in U2** (not two globally: G has degree four).
The critical point 0 lies in their central component; the other critical
points of G are outside the disk. Consequently
`G:V2 -> U2` is a proper degree-two quadratic-like return with
`V2` compactly contained in `U2`, and the postcritical orbit stays
in `V2`. This is a genuine renormalization, not a schematic Markov map.

The real fixed point `alpha=f(alpha)` lies strictly between
`-3/4` and `-7/10` by exact sign bounds. Monotonicity of `G` on
both halves of `[-3/4,1/2]`, together with exact endpoint bounds,
places the **entire** interval in the same central preimage component.
Hence `alpha in K(G)` and `alpha=f(alpha) in f(K(G))`.
The two phase sets are distinct, since `f(0)=c` lies outside `U2`.
Their **nonempty contact** is proved here; the classical **simple
satellite period-doubling** (in particular the uniqueness of the
phase-contact point) uses Douady–Hubbard tuning/Julia topology, rather
than being inferred from sampled disks. See the [primitive/satellite
definition](https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/on-invariant-measures-of-satellite-infinitely-renormalizable-quadratic-polynomials/AF8B693630F2234A9CA96C55A4F39852)
and the [doubling renormalization background](https://www.math.stonybrook.edu/~mlyubich/book.pdf).

**First incompatible field: `MarkedHubbardTree.small_julia_intervals`
(via `ExperimentOutputs.marked_tree`).**
At this exact parameter, `G(0)=x2`, `G(x2)=0` and `G'(0)=0`.
The exact *whole-complex-disk* enclosure further gives
`f^4(D(0,1/64)) subset D(0,1/128)` and
`f^2(D(0,1/64)) subset U2`. The real bridge places `x2` in `V2`;
by connectedness, the whole image `G(D(0,1/64))` lies in that central
component. Repeated `G^2` contracts the disk, so
**`D(0,1/64) subset K(G)` is certified**, not merely inferred
from a derivative calculation.
Thus `G^2` has a superattracting fixed point at 0, and the small
filled Julia set `K(G)` contains a **nonempty complex Fatou interior**.
A real interval cannot represent `K(G)`. In contrast, the v1
specification requires *three small Julia intervals*, a real hull and
its single slit interval pullback; the two primitive examples realize
precisely that real Chebyshev-tip structure. Replacing this satellite
Julia set with the real postcritical segment `[-3/4,1/2]` would
alter the meaning of the marking.

Downstream, `PhysicalExample.marking.induced_from` presumes that
three-interval marking, `AttachmentCensus.components[].interval`
stores one-dimensional half-open attached segments,
`IdealBoundaryIntervals.target_real_cuts` and
`ImmersionPullback.connected_blocks` rely on two-sided real slit
prime ends, and `SheetPathFamily` / `WaveFamily` rely on the resulting
one- or two-semicircle filtration. No unchanged v1 definition
guarantees these represent the **planar satellite** accesses.
The covering `f_*` and inclusion pullback `iota^*` remain
different mathematical operations; neither was replaced with the other
or assigned a guessed satellite table.

### Side-by-side native observables

Here **N/C** means *not certified or not meaningfully defined by the
unchanged v1 marking*, **not** zero and **not** a failed width
inequality. The two primitive columns are their pre-existing,
byte-identical outputs.

| Observable | `tip_pr68` (primitive, p=3) | `primitive4_tip12` (primitive, p=4) | period-four center (satellite, **p=2**) |
| --- | --- | --- | --- |
| Parameter | `c≈-1.7865105445`; pinned tip bracket | `c≈-1.9425541715`; `x24=-x12` certified | `c≈-1.3107026413`; unique `x4=0` root in adjacent `2^-128` bracket |
| Return degree | `f^3`: global 8, central 2 | `f^4`: global 16, central 2 | `f^2`: global 4, **central 2 proved**, Rouché margin `>3/50` |
| Little Julia geometry | three real inner intervals | three real inner intervals, primitive phase separation | **interior-filled little Julia set**; distinct physical phase sets meet at `alpha` |
| Inner target/source atoms | **10 / 20**, outer atom 1 | **10 / 20**, outer atom 1 | **N/C**: no v1 prime-end atom census |
| Complete new attachment | one `[-x3,x6)` rooted at `x6`; `S19,S0,S1` | one `[-x4,x8)` rooted at `x8`; `S19,S0,S1` | **N/C**: planar attachment / accesses unresolved |
| Immersion filtered blocks | `5,2,1,1,3,1,3,1,1,2`; only `P0` nonproper | same, only `P0` nonproper | **N/C**: no `iota^*` partition |
| Proper restrictions | **2 crossing / 1 avoiding** | **2 crossing / 1 avoiding** | **N/C**: cannot assert 2/1 or any multiplicity |
| Real-edge matrix, each edge once | `[[0,0,1],[1,0,1],[1,1,0]]` | `[[0,0,1],[1,0,1],[1,1,0]]` | **N/C**: no canonical three-old-edge model |
| Perron root | `(1+sqrt(5))/2` | `(1+sqrt(5))/2` | **N/C**: matrix not constructed |
| Zero-old-edge atom types / Wave crests | `I0,I2,I5,I8` / `I0,I2,I8` | `I0,I2,I5,I8` / `I0,I2,I8` | **N/C**: no certified crest gates |
| Exact parent Wave width | `log(4/3)/(2*pi)` | `log(3/2)/(2*pi)` | **N/C** |
| Exact each child / pushed width | `log(4/3)/pi` | `log(3/2)/pi` | **N/C** |
| Harmonic-series test | **equality**, not strict | **equality**, not strict | **undetermined**: neither equality, failure nor strictness established |

**Quantitative answer.** The first real structural difference is satellite
phase contact and a non-interval little Julia set, *before* the primitive
slit/atom and proper-restriction counts can be formed. It **blocks
transfer of the primitive quantitative width certificate**, but it is
**not** evidence of decreased satellite width, failure of harmonic
equality or strict improvement. Those are genuinely open under the
unchanged specification. In particular the Perron root in the primitive
three-edge model must not be copied into the satellite case.

### Certification / numerical / open boundary

**Machine-certified exact:** uniqueness of the period-four center in
the printed dyadic bracket; period-four critical orbit and period-two
central return; strict uniform Rouché degree-two enclosure; the real
bridge and fixed-point phase contact; nonempty complex interior of
`K(G)`; refusal at the first typed v1 interval field; negative mutation
tests and immutable byte-canonical manifest. All checks use standard
library integer/rational interval arithmetic, with **no floating-point
certificate**.

**Cited/conditional:** identification with the classical simple
period-doubling satellite tuning and the uniqueness of phase contact;
the KKL full Hubbard-tree and prime-end marking framework for
non-interval satellite sets. No path/width theorem is imported as
if numerically verified.

**Numerical-only:** the displayed decimal `c≈-1.3107026413` is
orientation only; no claimed result depends on that rounding.

**Open:** native satellite attachment and planar access census,
separate `f_*` and `iota^*` tables, sheet/path filtration, old-edge
incidence and spectral radius, zero-edge closed crest transport,
satellite parent/child extremal Wave widths and any strict harmonic gain.
Only the named two primitive examples retain their exact 2/1, edge
and harmonic-equality certificates. The satellite obstruction is a
**scope limitation**, not a theorem refuting KKL or proving a
quantitative loss.

## Real period-two satellite Misiurewicz tip: exact return, *semantic* v1 refusal

**This is a different obstruction from the superattracting period-four center.**
The previous `satellite2_period4_obstruction` record and every primitive
output are left byte-for-byte unchanged. The new independent input
`physical_examples/satellite2_misiurewicz_tip_refusal.json` is deliberately
a **negative compatibility record, not a fabricated v1 `PhysicalExample`**.
Its executable and immutable output are
`regenerate_satellite2_tip.py` and
`experiment_manifests/satellite2_misiurewicz_tip_refusal.json`.

Write `P(c)=c^3+2c^2+2c+2`, let `c_*` be its unique real root,
and put `a=c_*^2+c_*`. The exact adjacent dyadic isolator has denominator
`2^128` and numerators
`[-525290151028706361181936933686549192168,
-525290151028706361181936933686549192167]`.
The endpoint values of `P` have strict opposite signs, and
`P'(c)=3(c+2/3)^2+2/3>0` globally. Consequently the
critical orbit is **exactly** `0 -> c -> a -> -a -> -a`
(`f(a)+a=c P(c)=0`), with `4a^2>2` for the terminal
`f^2` multiplier. The decimal `c≈-1.5436890126920764`
is orientation only, **not** a numerical certificate.

For `G=f^2=z^4+2cz^2+a`, choose `U=D(0,1)` and
`V=component(G^-1(U),0)`. On the entire circle `|z|=1`,
uniformly for `|w|<=1`, the Rouché comparison with `2cz^2`
has the explicit, strictly certified lower margin
`2|c|-|a|-1-|w| >= -2*c_high-a_high-2 > 1/5`.
The only critical point of `G` inside `U` is `0`;
the other two are `±sqrt(-c)`, strictly outside `U`.
Rouché counts **two**, not four, roots in `U` for every `w`
in the closed target disk. Thus `G:V -> U` is a
proper degree-two quadratic-like restriction with `V` compactly
contained in `U`. This is a physical return certificate,
not merely a real one-dimensional mapping.

Its real invariant inner interval is `K0=[-a,a]`:
`G(0)=a`, `G(±a)=-a`, and
`G'(x)=4x(x^2+c)` has only the central turning point
there. For `y∈K0`, the inverse formula
`z^2=-c±sqrt(y-c)` has an inner branch
`0<=z^2<=a^2` and an outer branch
`z^2>=-c+a>1`; hence
`G^-1(K0)∩V=K0`, giving `Tprime=T=K0` and
**zero new attachments**. Identification of the *entire*
small filled Julia set with that real interval uses the standard
backward-density theorem for repelling points of a quadratic-like
map and the absence of bounded complementary components when its
Julia set lies in a real line. It is an analytic argument with exact
algebraic hypotheses, not a claim that finite samples prove Julia
topology.

But `f(K0)=[c,-a]` **touches** `K0` at
the repelling endpoint `-a`, whereas KKL
[arXiv:2606.27272v1 §§2.3–2.5](https://arxiv.org/abs/2606.27272)
defines the tree/edge construction here for **primitive** renormalization
with disjoint small filled Julia sets. This model has only *one*
`G`-inner Julia interval, not the three distinct inner intervals
specified by the current executable v1 contract. The first semantic
incompatibility is therefore
**`MarkedHubbardTree.small_julia_intervals`**. A one-element JSON
list passes the generic list *type*, but does **not** satisfy the
source-locked three-phase construction. It would be misleading to
invent two additional inner intervals from the touching *ambient*
`f`-phases. **Stop the v1 record here**; do not emit atomic
`f_*` or `iota^*` tables, sheet/path counts, or Wave widths.
The maps remain distinct: `f_*` comes from the degree-two
covering `G`; `iota^*` comes from physical inclusion. They are
not interchangeable, even though there is no extra inverse-tree
attachment.

| Observable | Primitive `p=3` tip | Primitive `p=4` tip | Satellite `p=2` tip |
| --- | --- | --- | --- |
| Small inner Julia intervals / tree attachments | 3 / 1 | 3 / 1 | **1 / 0** |
| Target / covering-source inner atoms in locked primitive v1 marking | 10 / 20 | 10 / 20 | **not defined by that marking** |
| Filtered restrictions (crossing / avoiding) | 2 / 1 | 2 / 1 | **not evaluated:** no new attachment |
| Old edges counted once per *real* edge | 3 | 3 | 0 (one vertex = `K0`) |
| Old-edge matrix | `[[0,0,1],[1,0,1],[1,1,0]]` (same three-phase inner kneading; not separately frozen in the `p=3` manifest) | `[[0,0,1],[1,0,1],[1,1,0]]` (independent certified once-edge audit) | formally empty `0×0` graph matrix (**not** a source-defined KKL Perron operator) |
| Perron root of old-edge matrix | `(1+sqrt(5))/2` under the same old-edge convention | `(1+sqrt(5))/2` | **undefined**, not `0` or `1` |
| Zero-old-edge closed Wave crests | not separately frozen for `p=3`; analogous three-phase geometry | `I0,I2,I8` all zero-edge | **not defined:** no v1 Wave marking |
| Parent symbolic Wave width | `log(4/3)/(2*pi)` | `log(3/2)/(2*pi)` | **not defined** |
| Each child and pushed symbolic width | `log(4/3)/pi` | `log(3/2)/pi` | **not defined** |
| Harmonic series | conditional analytic **equality** | conditional analytic **equality** | **no verdict**: neither strictness nor failure established |

Because touching of small Julia sets is the defining satellite
obstruction to *primitive* separation, choosing another genuine real
period-doubling satellite tip cannot restore the KKL §2.5 primitive
hypothesis. A different inner tuning could change its number of marked
intervals but would require a satellite-specific replacement contract.

**First structural difference and quantitative meaning.** The satellite
touching of two ambient `f`-phases violates the primitive separation
hypothesis and collapses the three-interval inner tree to a single
vertex, *before* any sheet filtration or Wave comparison. The
lack of a nonempty old-edge Perron operator or a two-child Wave is
**not evidence of quantitative width loss**. The primitive 2-versus-1
breakage and harmonic equality are not transferable by assertion;
the satellite extension of the induced ideal marking and its analytic
Wave width remain open. Neither `f_*` nor `iota^*` is replaced by
a synthetic table.

### Certification / numerical / open boundary for this tip

**Exact, executable:** uniqueness of the real parameter root in the
adjacent dyadic bracket; critical orbit identities; strict repelling
multiplier; uniform complex Rouché margin `>1/5`; degree two and
compact containment; exact monotone real interval and inverse-branch
inequalities; contact of two `f`-phases; absence of additional *real
tree inverse branches within the full complex central source*; and
the empty attachment census. Baseline primitive results are read
from immutable, blob-locked files.

**Analytic, explicitly cited/conditional:** the standard
quadratic-like Julia/backward-orbit argument upgrading the invariant
interval to the entire small filled Julia set, the definition
and hypothesis of primitive KKL Hubbard-tree/ideal marking, and
analytic identification of the *primitive* example's symbolic
rectangle expressions with extremal Wave widths.

**Numerical only:** the displayed decimal approximation of `c_*`;
it is never used for a sign, branch, degree or width conclusion.

**Open / deliberately unasserted:** any satellite-native ideal-boundary
atom and attachment-sector atlas outside this real interval,
filtered proper restrictions, independent `f_*` / `iota^*`
atomic maps on such an atlas, old-edge Wave crest census, actual
parent/child extremal widths, and strict/equal/failed harmonic
transfer. This is a **source/contract limitation** and does not
claim a counterexample to a theorem for primitive maps.

Read-only reproduction:
`python research/native_wave_transfer/regenerate_satellite2_tip.py --check`
and `python -m unittest discover -s research/native_wave_transfer -p 'test_*.py' -v`.


## v2 satellite contact certificate: period-two Misiurewicz tip (additive)

**Contract:** [`SPECIFICATION_v2_satellite.md`](SPECIFICATION_v2_satellite.md);
field-by-field [`source_contracts/satellite_v2_field_sources.json`](source_contracts/satellite_v2_field_sources.json);
computed [`experiment_manifests/satellite2_misiurewicz_v2.json`](experiment_manifests/satellite2_misiurewicz_v2.json).
The original v1 refusal above and **all existing source files, code, tests and
manifests remain byte-identical**. The new `regenerate_satellite_v2.py`
is independent and uses only exact integers/rationals and symbolic identities.

### What the satellite record actually represents

For \(P(c)=c^3+2c^2+2c+2\), unique real root \(c_*\), and
\(a=c_*^2+c_*\), retain the v1 **physical** central return
\(G=f_{c_*}^2:V\to D(0,1)\), **restricted degree two**, not global degree
four. It has **one** Chebyshev inner interval \(K_0=[-a,a]\), and
\(G^{-1}(K_0)\cap V=K_0\). Its ambient \(f\)-images are the **two**
touching phases \(K_0\) and \(K_1=f(K_0)=[c_*,-a]\);
\(K_0\cap K_1=\{-a\}\). The shared point \(q=-a\) is fixed under
\(f\), its multiplier \(-2a\) is negative and repelling, and the two
real incident arms exchange (arm rotation \(1/2\)). This is a
period-two satellite **bouquet**, as defined in
[Avila–Lyubich §2.10](https://www.numdam.org/item/10.1007/s10240-011-0034-2.pdf)
and [Lyubich, *Dynamics of Quadratic Polynomials*, Part II §9.1](https://www.math.stonybrook.edu/~mlyubich/Archive/Selected/puzzle.pdf).
It is not an additional \(G\)-little Julia interval or a new attachment.

The **return-tree** attachment count remains **zero**:
\(T=T'=K_0\). Replace the v1 primitive attachment list by a separate
phase-contact vertex census \(\{q\}\), without treating it as a component
of \(T'\setminus T\). The central-return slit has one tip access at
\(-a\); the ambient bouquet interval has upper/lower local side
accesses at that same interior point. They are **not** interchangeable
prime-end markings. This is local topological bookkeeping, not a fully
constructed satellite ideal atlas [KKL v1 §§2.3–2.5, Appendix A.1](https://arxiv.org/abs/2606.27272v1).

Modulo \(P(c)\) the exact identity
\(G(z)+a=(z^2-a^2)(z^2-c_*^2)\) gives **two unramified central
covering endpoint lifts** of the return slit tip, at \(-a\) and \(+a\)
(each local degree one); the actual inclusion \(\iota\) has **one
local endpoint germ**, at \(-a\) (degree one). The covering
\(f_*\) and immersion pullback \(\iota^*\) remain **separate typed
operations**, not guessed complete atomic tables. A path passing
*through* the deleted point \(q\) is not a proper path of the slit
complement, so it has zero admissible through-contact crossings.
The **global** filtered KKL restriction multiplicities are **undefined**,
not the local `2/1` germ count. Cf.
[KKL §6.1 Props. 6.5–6.6, Appendix A.1/A.3.2](https://arxiv.org/abs/2606.27272v1);
[Dudko–Lyubich–Selinger §§2.1–2.2](https://doi.org/10.1090/jams/942)
supplies pacman sectors, *not* a KKL full-path rule here.

### Computed invariants and honest primitive comparison

| Observable | Primitive \(p=3\) tip (unchanged) | Primitive \(p=4\) tip (unchanged) | Satellite \(p=2\) tip v2 |
| --- | --- | --- | --- |
| Central \(G\)-inner intervals / new return-tree attachments | 3 / 1 | 3 / 1 | **1 / 0**; two touching ambient \(f\) phases |
| Phase contacts / local rotation | primitive disjoint | primitive disjoint | **1 contact** \(q=-a\); \(1/2\) under \(f\) |
| Full filtered crossing/avoiding proper restrictions | **2 / 1** | **2 / 1** | **undefined**; through-\(q\) crossing not proper |
| Local slit-tip covering/immersion endpoint lifts | not this v1 observable | not this v1 observable | **2 / 1**, both unramified; *not* full-path counts |
| Old-edge KKL \(G\)-matrix and Perron root | \(3\times3\), \(\varphi=(1+\sqrt5)/2\) | \(3\times3\), \(\varphi\) | **undefined** (no \(G\)-old edges) |
| **Ambient** \(f\)-Hubbard-tree Markov matrix | not compared in this convention | not compared in this convention | \(\left[\begin{smallmatrix}0&1&1\\1&0&0\\1&0&0\end{smallmatrix}\right]\), \(\rho=\sqrt2\) |
| Parent symbolic Wave width | \(\log(4/3)/(2\pi)\) | \(\log(3/2)/(2\pi)\) | **undefined**, not zero |
| Each child and pushed symbolic Wave width | \(\log(4/3)/\pi\) | \(\log(3/2)/\pi\) | **undefined**, not zero |
| Harmonic width transfer | conditional analytic equality | conditional analytic equality | **undetermined**: neither preservation, loss nor forced degradation established |

For the **ambient** real Hubbard tree \(H=[c_*,a]\), the exact
vertex partition \(c_*<-a<0<a\) yields
`E0=[c*,-a]`, `E1=[-a,0]`, `E2=[0,a]` with images
`E0 -> E1,E2`, `E1 -> E0`, `E2 -> E0`.
Counting each physical edge once (output rows, input columns)
gives \(M=\bigl[\begin{smallmatrix}0&1&1\\1&0&0\\1&0&0\end{smallmatrix}\bigr]\),
\(\chi_M(t)=t(t^2-2)\), and \(\rho(M)=\sqrt2\).
This is the **Hubbard-tree Markov operator** of the type described
in [Dudko–Schleicher §2, Lemma 2.3](https://doi.org/10.1007/s40598-020-00134-y),
not the KKL primitive old-edge operator; their spectral radii do
**not** compare satellite Wave widths.

### Evidence boundaries and immutable reproduction

* **Certified exact by the executable:** strict rational parameter enclosure
  and phase order; reduction of contact/fixed-point and factor identities
  modulo \(P\); the return-degree and no-new-attachment facts via locked
  v1 exact certificates; local covering/inclusion germ counts, distinct
  map types, image-edge incidence, \(M^3=2M\) and Perron root \(\sqrt2\);
  v1 primitive manifests checked by immutable Git-blob identities.
* **Cited but not independently formalized:** identification of the whole
  central filled Julia set with \([-a,a]\); bouquet/arm rotation
  interpretation and full complex prime-end access identifications.
  The cited literature supplies the satellite topology but does *not*
  establish a KKL satellite Wave family in this setting.
* **Numerical-only:** **none** in v2's deductions. The decimal approximation
  of \(c_*\) elsewhere in the unchanged v1 refusal remains orientation only.
* **Open:** full satellite ideal-atom and \(\iota^*\) atlas, globally
  filtered proper contact paths, a non-vacuous satellite KKL old-edge
  operator, parent/child **extremal** Wave widths and whether a genuine
  transfer inequality is preserved, lost, or must degrade. Neither
  pacman moduli nor ambient \(\rho(M)\) substitutes for this missing
  analytic theorem.

Read-only reproduction:
`python research/native_wave_transfer/regenerate_satellite_v2.py --check`
and `python -m unittest discover -s research/native_wave_transfer -p 'test_*.py' -v`.
The new CI step explicitly checks the immutable v2 manifest and
source-to-field contract, while every existing job is retained.
