# Native Wave Transfer Laboratory — executable specification v1

**Scope.** An independent executable restatement of the *physical*, ordinary
quadratic-like PR #68 example, not a definition of the unrestricted canonical
KKL localization and not a theorem about arbitrary waves. Primary source:
Kahn–Kapiamba–Lyubich (KKL), [arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272v1),
§§2.1, 2.5, 6.1 (Propositions 6.5–6.6), Appendix A.1, A.3.2–A.3.4.
Physical case proof: [`tip_KKL_native_tree_marking_and_marked_wave_breakage_20261109.md`](../independent_audits/tip_KKL_native_tree_marking_and_marked_wave_breakage_20261109.md), §§1–5;
original phase/parameter inputs: [`results/tip_root_interval_geometry.json`](../../results/tip_root_interval_geometry.json).

## 1. Types, sources and records

`source_contracts/record_fields.json` is the machine-readable, versioned field
registry. Its `records` define field paths, scalar/list/ref types, and a **mandatory
source ID for every field**; `sources` expands those IDs to a specific KKL
section/proposition or pinned repository file and section. `[]` means every
array member, `*` an instance ID, and nested dots indicate JSON objects.
`source_contracts/LOCK.json` binds the source files to their Git blob SHA-1
identities, and cites a **specific preprint version**. SHA-256 is separately
used for the executable, input, contracts, lock and calculated outputs.

The records and their keys (full per-field types and citations in the registry):

| Record | Required content | Definition |
| --- | --- | --- |
| `PolynomialParameter` | `family`, `critical_point`, exact dyadic `parameter_bracket.{lower_numerator,upper_numerator,denominator_power_of_two}`, `orbit_index_range` | tip root source, KKL §2.1 |
| `PhysicalReturn` | physical iterate 3, global degree 8, *central restricted* degree 2 | source for the physical `G=f_c^3`, KKL §2.1 |
| `DomainPair` | `V3 = component(G^-1(U3),0)`, degree 2; `U3=D(0,1/4)` | PR #68 §1 |
| `MarkedHubbardTree` | three small Julia intervals, minimal connected hull `T`, `Tprime`, `alpha` | KKL §2.5, PR #68 §1 |
| `AttachmentCensus` | `components[]` with interval, attaching root, source boundary atoms, **actual** immersion destination; completeness conditional on degree 2 | KKL §6.1 Prop. 6.5, PR #68 §1–2 |
| `IdealBoundaryIntervals` | ordered target/source cuts and atom lists, terminal/upper/lower conventions, one outer-component atom | KKL App. A.1, PR #68 §2 |
| `CoveringFStar` | degree and `source_to_target` atom function under `f_*` | KKL §6.1, PR #68 (2.2) |
| `ImmersionPullback` | distinct `iota^*` source-to-**pullback** labels, maximal cyclic blocks, end-properness and nonproper cells | KKL §6.1 Props. 6.5–6.6 |
| `SheetPathFamily` | exact real circle coordinates, ideal endpoint atoms, source restrictions, both map outputs, filter flags, relative-endpoint homotopy | KKL App. A.1/A.3.2–A.3.4, PR #68 §§3–4 |
| `WaveFamily` | concentric open radius interval, whole endpoint ranges, base/crest, pushed bases, symbolic widths and series-law equality | KKL App. A.3.2 Lemma A.11, PR #68 §5 |
| `PhysicalExample`, `ExperimentOutputs`, `ExperimentManifest` | source-locked input, ten calculated records, immutable code/input/output/proof-status envelope | this specification |

**Representation rules:** Fractions are reduced strings like `"-5/32"`; never
binary floating point. Bounds are inclusive `Box(low, high)` on the integer
lattice `2^-256`. Physical tree intervals use symbolic orbit labels, because
an exact root is *not* replaced by a rounded decimal. `target_width` and
`each_child_and_pushed_width` are **symbolic identities** in `log(r1/r0)` and
`pi`, not claimed numerical interval approximations to transcendental values.
The manifest is byte-canonical UTF-8 JSON: sorted keys, two-space indent,
newline, `ensure_ascii=True`. `--check` is the default; only explicit `--write`
may re-freeze after a reviewed source or algorithm change. The committed
manifest records code SHA-256, file SHA-256s, input Git blob IDs, every output,
its SHA-256 and proof-status categories. The new workflow never writes it.

## 2. Physical model and two operations

Let `f(z)=z²+c_*`, `x_k=f^k(0)` and `G=f³`. The exact *input*
parameter bracket and `x18=-x9` relation come from the pinned root source.
The native three-cycle is `K0=[x9,x18]`, `K1=[x12,x3]`,
`K2=[x6,x15]`; `T=[x6,x3]`, and on the degree-two central source
`Tprime=[-x3,x3]`. There is **one** new attachment
`Tprime\T=[-x3,x6)` with root `x6`; the assertion that there are no
additional complex preimages inside `V3` uses the previously proved
quadratic-like degree-two representative. It is not a consequence of interval
sampling alone. The real branch monotonicity follows from
`G'(z)=8*z*f(z)*f²(z)` and exact interval signs.

The two maps MUST have separate types and separate output fields:

* **Covering** `g=G:V3\Tprime -> U3\T` induces `f_* : S_s -> I_j`.
  The ten preimages of the five target cuts are isolated by monotone inverse
  interval bisection. An oriented real-sided atom sample is then mapped by
  `G`, with its side orientation reversed on the positive branch. This yields
  twenty covering atoms (two over each target atom).
* **Immersion** `iota:V3\Tprime -> U3\T` is the actual inclusion and
  induces the set-valued KKL **pullback marking** `iota^*`.
  A source atom attached left of `x6` is **not** assigned a genuine target
  ideal-boundary image: those sides go to target **interior**. Its source
  *pullback-block label* is `P0` under Prop. 6.5. The rest uses the physical
  inclusion and side placement. This yields ten cyclic blocks
  `[18,19,0,1,2], [3,4], [5], [6], [7,8,9], [10],
  [11,12,13], [14], [15], [16,17]` with only `P0` nonproper; all ten
  blocks are end-proper.

The whole source-cut census is derived from inverse *branches*, not cloned
from a saved twenty-entry table. The exact orbit identities label the
resulting increasing cuts `-x12,x6,x15,-alpha,x9,x18,alpha,-x15,-x6,x12`.
Canonicalizing `-x9` as `x18` is justified by the source's exact root identity.
The target cuts are `x15,x9,x18,alpha,x12`; their side/tip atoms are indexed
`I0..I9` as in PR #68 §2. These finite identifications use KKL's
induced-marking rule and the prime-end interpretation as cited inputs.

## 3. Path, sheet and Wave algorithms

A `paths[]` record specifies rational `q,w`, where the proper target arc is
`gamma_w(t)=(q+w)/2+(q-w)/2 * exp(2*pi*i*t)`, `0<t<1`. Its right-hand
endpoint carries separate upper/lower **ideal accesses** even though both
have physical impression `q`. The two real intersections alone decide the
restriction components because the entire circle lies in `V3` and the
physical `Tprime` is a slit. A crossing `w in (-x3,x6)` splits into two
semicircles; an avoiding `w < -x3` leaves one. Only surviving paths count:
exclude short source multi-intervals (KKL A.1), then paths subordinate to a
single `P_i` (KKL A.3.2). Push survivors by **the separately computed**
`f_*`, not by `iota^*`. For PR #68, this yields `(S3,S1),(S19,S17)` versus
`(S3,S17)`, with pushforward `(I3,I1),(I9,I7)` versus `(I3,I7)`.

Closed rational complex-ball arithmetic propagates
`B(d,r) -> B(d²+c_mid, 2|d|r+r²+c_rad)` three times.
`|G(B)| < 1/20` (crossing) and `< 21/100` (avoiding) prove the **whole**
disks map strictly inside `U3`. Their centers lie in the native source tree;
connectedness therefore selects the component `V3`. For Wave leaves with
center `-9/64` and `3/256 < r < 1/64`, exact **endpoint interval** tests
place every left crossing in the attachment and every right endpoint in the
same target base atoms. The small closed-disk bound covers all leaves.

The angular interval is `2*pi` for the target log-rectangle and `pi` for
both pieces. With exact `r1/r0=4/3`, algebra of rational coefficients gives

`W(S) = log(4/3)/(2*pi)`, `W(S'_+) = W(S'_-) = log(4/3)/pi`, and
`1/W(S) = 1/W(S'_+) + 1/W(S'_-)`.

This computes the symbolic rectangle identity; the analytic identification
with extremal width and conformal pushforward is cited from PR #68 §5 and
KKL Lemma A.11. Joint injectivity holds because the inclusion is an
embedding; injectivity of `G` on the negative-half-plane wave support uses
the cited physical degree-two dynamics. No general wave-gain theorem follows.

## 4. Reproducibility, refusal conditions, and negatives

Run at repository root:

```sh
python research/native_wave_transfer/regenerate.py --check
python -m unittest discover -s research/native_wave_transfer -p 'test_*.py' -v
python research/independent_audits/verify_tip_KKL_tree_marked_breakage.py --check-manifest
lake build TipKKLTreeMarking
```

The program neither imports the old verifier nor reads its **code** for
results. It checks its *blob ID* as provenance and independently computes
its own table; only **after** computation does it compare a defined projection
against the pinned PR #68 result JSON. It fails on an input/code/source hash
mismatch, a failed strict arithmetic inequality, an ambiguous cut, disconnected
pullback cell, short/one-cell path, symbolic width drift, or a changed
reference projection. Unit tests deliberately mutate the return time,
marking, action separation, disk margin, Wave endpoint range, parameter, and
one reference table cell. These are regression tests of an *implementation*
under fixed analytic inputs, not formal proofs of prime ends, dendrites,
KKL Propositions 6.5–6.6, or the extremal-width lemma.

## 5. Source-locked primitive period-four configuration (inner period-12 tip)

The existing `tip_pr68` source records, `regenerate.py`, contracts, lock
and immutable manifest remain **byte-identical**. A second executable
`regenerate_period4.py` imports the same exact `Box`, cyclic atom,
proper-restriction, and canonical-manifest primitives, but recomputes from its
own parameter and geometric data. The separate
`source_contracts/primitive4_record_fields.json` supplies source-specific
IDs for the *same record grammar*, plus typed domain, old-edge and zero-edge
certificates. Its lock pins the parameter file and the pre-existing
physical old-edge convention audit. Run
`python research/native_wave_transfer/regenerate_period4.py --check`;
only explicit `--write` can re-freeze its own canonical manifest.

**Parameter.** Put `x0=0` and `x(k+1)=x(k)^2+c`. The parameter is the
**unique** real zero of `x24+x12` in the adjacent `2^-160` dyadic bracket
in `physical_examples/primitive4_tip12_parameter.json`. The left endpoint
is strictly positive, the right strictly negative, and the interval derivative
is strictly negative, all certified by outward `2^-256` arithmetic. The
exact relation `x24=-x12` implies `x36=x24`, by evenness of `f^12`.
This is not the period-four superattracting center: `G=f^4` is global
degree 16 with a *central quadratic-like degree-two* restriction.

**Complex source and target.** Set `U4=D(0,1/16)`. For the entire circle
`|z|=1/16` write `G(z)=d+A z^2+E(z)`; propagate the exact rational tail
bound `E_next <= 2|d| E + (|A|rho^2+E)^2`. The Rouché margin
`|A|rho^2 - |d| - E - 1/16 > 1/25` guarantees a proper degree-two
`V4=component(G^-1(U4),0)`, compact in `U4`; the central critical point
exhausts both preimages. The same calculation for `f^12` on
`|z|=3/256`, target `D(0,1/128)`, has margin `>1/100`. Exact complex
balls enclosing `f^j(V4)` for `j=0,1,2,3` are pairwise disjoint.
Thus the physical period-four renormalization is **primitive**, rather
than a period-doubling satellite. Real derivative-factor signs on
`[0,x24]`, together with `x24=-x12`, make `f^12` send
`[x12,x24]` onto itself with one critical minimum. Identifying this
real interval with the full inner Chebyshev-tip Julia set uses the
standard analytic backward-density/straightening argument and is not
claimed as a conclusion of finite interval sampling alone.

**Marked Hubbard tree and both operations.** The three small intervals are
`K0=[x12,x24]`, `K1=[x16,x4]`, `K2=[x8,x20]`;
their certified order is
`x8<x20<x12<0<x24<alpha<x16<x4`, where the fixed
`alpha=G(alpha)` is isolated by strict interval bisection.
The native hull is `T=[x8,x4]` and its *complete* real inverse in the
degree-two central source is `Tprime=[-x4,x4]`. Both monotone branches
account for all inverse fibers, ruling out additional complex inverse
tree components in `V4`. The single new attachment
`[-x4,x8)` has root `x8` and boundary atoms `S19,S0,S1`:
they map by actual **immersion inclusion** to target interior, not to a
target boundary atom. The target cuts are `x20,x12,x24,alpha,x16`,
and the independently isolated ordered inverse cuts are
`-x16,x8,x20,-alpha,x12,x24,alpha,-x20,-x8,x16`.
The ten target inner atoms and twenty source inner atoms have separate
maps `f_*` (covering, two copies of ten) and `iota^*` (immersion pullback,
ten cyclic blocks). The one whole outer-boundary atom is not asserted
to have end-proper immersion behavior.

**Paths and entire Wave families.** The common right target ideal endpoint
is `q=-7/256`. The left crossings `w=-5/128` and `w=-3/64` are,
respectively, inside the new attachment and outside the source slit.
The entire corresponding closed disks satisfy
`|G(B)|<1/32` and `|G(B)|<1/20`, strictly within `U4`.
The original A.1 short-span and A.3.2 one-pullback filters produce
proper source restrictions `(S3,S1),(S19,S17)` versus
`(S3,S17)`, and **cover** outputs `(I3,I1),(I9,I7)` versus
`(I3,I7)`. Equality of relative *ideal-endpoint* homotopy classes
still depends on the usual prime-end identification, not on identical
real impressions. The concentric positive-width Wave has center
`-17/512`, all `1/256<r<3/512`, target base `(I9,I0,I1)`
and pushed child bases `(I1,I2,I3)`, `(I7,I8,I9)`;
the endpoint/gate inequalities hold for the *whole radius interval*.
Exact rectangle coefficients give parent width `log(3/2)/(2*pi)` and
both child widths `log(3/2)/pi`, hence **harmonic-series equality**.
The analytic extremal-width/conformal-invariance identification remains
an explicit cited assumption.

**Old-edge and zero-edge guard.** The three real **old** edges
`E20=(x20,x12)`, `E0a=(x24,alpha)`, `Ea1=(alpha,x16)`
map as `E20 -> (E0a,Ea1)`, `E0a -> Ea1`,
`Ea1 -> (E0a,K0,E20)`; `K0` is a vertex interval *gap*,
not an old edge. Count each real physical traversal **once**, not once
per upper/lower boundary side. With output rows and input columns,
`T_F=[[0,0,1],[1,0,1],[1,1,0]]`, characteristic polynomial
`t^3-2t-1`, Perron root `phi=(1+sqrt(5))/2`, positive left
weights `(phi,1,phi)` and strictly positive fourth power.
The zero-old-edge target atom types are `I0,I2,I5,I8`; the distinct
source-inclusion and covering-pushforward zero lists are frozen in the
second manifest. In particular **all three actual Wave closed crests**
`I0,I2,I8` have *zero* old-edge incidence. No Perron edge growth or
finite whole-atom saturation is misreported as a closed-crest Wave gain.

**Trust boundary:** the dyadic parameter, complex Rouché and phase balls,
finite real cut/attachment/edge arithmetic, whole-disk and full-radius
bounds, and symbolic harmonic coefficient equality are certified.
The inner Julia identification, slit Carathéodory marking, KKL attachment
and proper-path definitions, homotopy, and analytic extremal widths are
conditional on cited mathematics. There is **no numeric-only certificate**.
Canonical non-LC attachments, zero-edge subsector transport and a general
strict Wave inequality remain open. The difference in *physical* iterate
`p=4` changes polynomial, global degree, scale and domain certificates;
this example intentionally retains the same three-phase *inner* kneading,
so the finite 10/20 counts, edge matrix and breakage multiplicities need
not vary with `p` alone.
