# Selected slit widths, fine landing angles, and a corrected rigidity endgame

**2026-11-23.** Base: `ed64c7ad839dcc8b799d53379434f892fdc92a2c`.
This packet supplies written local geometric results, repairs an exact-arithmetic
under-enclosure, and identifies the remaining native restriction and global
rigidity obligations. MLC, UPTCR and the global H1–H4 package remain open.

## Results and their dependencies

| Result | Evidence | Exact scope |
|---|---|---|
| Every intrinsic A.1 path class on the selected finite slit surfaces is identified, with all winding retained. | [IDEAL_BOUNDARY.md](IDEAL_BOUNDARY.md), §§1–4 | Actual target and covering-pulled source markings; complete ideal circles and slit accesses. The full immersion-pulled marking remains open. |
| The selected independent unbuffered parent/child defect is strictly greater than 1/100 for every p≥3. | [WIDTH_TRANSFER.md](WIDTH_TRANSFER.md), §§1–5 | Actual finite surfaces and every eligible leaf in the specified independent classes. A common optimizing parent and an iterated amplification are not supplied. |
| The actual fine-cycle external-angle set and each full phase set have Hausdorff and both box dimensions exactly 1/3; no original W ideal interval is wholly boundary-valued in the fine localization. | [Exact rational upper bound](../issue62_landing_angle_bound_20261123/NOTE.md) and [matching entropy lower bound](../issue62_landing_angle_bound_20261123/EXACT_DIMENSION.md) | The normalized G external-angle metric, with actual landing, sector and Chebyshev-return inputs. The result supplies no literal F9 connector words or conformal-width equality. |
| The valid terminal rigidity implication uses hybrid uniqueness. | [RIGIDITY_AND_REMAINING_GAP.md](RIGIDITY_AND_REMAINING_GAP.md), §§1–2 | Given the global QC conjugacy and NILF input, K=J and Douady–Hubbard uniqueness imply c=c′. The construction of those inputs and parameter neighborhoods remains open. |

The current register derives `SLIT-CLASSES` from `SELECTED` and `PERIOD-TWO`,
then uses it for `ALL-PATHS` and `GAIN`. `MARK` remains open and is not an
input to the independent-width theorem.

The angular upper bound uses the actual fine cycle, landing map and complete
sector exhaustion to construct exact survivor covers. The matching lower
bound uses the actual Chebyshev return, an onto factor and Furstenberg's
theorem. Both arguments concern the same parameter and the same landing sets.
The corresponding code checks certify the stated finite arithmetic; they do
not replace the analytic proofs.

## The arithmetic error and its repair

The upstream normalized cut estimate contains

\[
\left(30\cdot15246+\frac{88(4^j-1)}3\right)4^{-p}.
\]

The old limiting-gain verifier divided the first term by three as well.
Its input intervals were therefore narrower than the stated theorem permits.
The old executable could return PASS without detecting that mismatch.

Correcting the coefficient alone does not preserve the old p=13 box proof:
the corrected broad parent-width interval is
`(0.658663060, 0.749148532)`, whose lower endpoint is below 2/3.
The repaired proof instead uses the existing exact root-isolation routine for
the actual p=13 parameter, giving
`(0.701260568, 0.701260571)`. The corrected uniform box starts at p=14,
giving `(0.690181183, 0.712667273)`; the explicit `4^-p` factor proves
all later boxes are contained in it. Both cases establish the required floor.

The regression compares the parent inputs with the independently implemented
upstream child cut bounds. It also preserves the failed broad p=13 check as
a negative test and checks the successful actual p=13 and uniform p=14 cases.

## What the continuum proof adds

The explicit Joukowski collar accounts for every inner access. Finite-modulus
annular uniformization identifies both actual KKL ideal circles. A proper
path is subordinate to a proper inner arc precisely when its two lifted
endpoints lie in the same lift of that arc. This retains its actual winding;
shortest cyclic atom distance is not a general substitute.

The parent lower bound uses a full embedded quadrilateral foliation, with
its minimal three-atom base and closed crest. The universal child upper
metric has the exact Euclidean formula

\[
\rho(z)^2=\sum_{\Pi(w)=z}\frac{\sigma(w)^2}{|\Pi'(w)|^2}.
\]

The Jacobian is essential. Length domination holds on every selected lift,
and Tonelli plus conformal change of variables gives the energy. The omitted
box lies outside the **entire** physical source inverse image, so its energy
can be subtracted without removing length from another eligible winding.
The limiting plane-slit model is separately corrected: infinity is a cusp,
not an outer KKL ideal-circle atom. The finite-annulus proof is unaffected.

The resulting exact margins are:

| Periods | Parent floor | Each child cap | Defect floor |
|---|---:|---:|---:|
| 3 | 49/100 | 487/500 | 300/23863 > 1/100 |
| 4 | 511/1000 | 197/200 | 7400/100667 > 7/100 |
| 5–12 | 581/1000 | 247/250 | 43500/143507 > 3/10 |
| 13, and the uniform tail from 14 | 2/3 | 63/50 | 11/126 > 1/100 |

## The rejected outer-marking argument is retained as a gap

An attempted proof of the outer pullback counted temporal source excursions
and used a tiny loop to assert a unique proper restriction. Independent review
found that the archive explicitly admits additional proper paths in the
geometric inverse trace, including retracing paths. The uniqueness assertion
therefore does not follow. [IDEAL_BOUNDARY.md, §§5–6](IDEAL_BOUNDARY.md)
records the exact source conflict. No narrower restriction convention is
silently adopted, and the full `MARK` row remains open.

The independent width estimates operate on one surface at a time and use its
universal cover. They do not require that rejected step. A theorem involving
the restriction of one common parent, however, must resolve the native
geometric-trace problem before invoking the corresponding KKL comparison.

## Current area results and the remaining global problem

The rigidity companion checks the current Petersen and Lim preprints against
their primary versions. Nullity of a critical end, or of every component of a
core, does not give nullity of an uncountable union or locate the nonzero
Beltrami support. The exact entry-time tightness criterion in that note
isolates one possible uniformity requirement. Positive-area Feigenbaum Julia
sets show that this requirement cannot be imposed on the entire Julia set.
The missing support localization, global QC construction, arbitrary-tower
transport and parameter-neighborhood construction are substantive open inputs.

## Reproduction

From the repository root:

```sh
python -B -m unittest discover -s research/independent_audits/tip_family_limiting_wave_gain_20261116 -p 'test_verify.py' -v
python -B research/independent_audits/tip_family_finite_p_wave_gain_20261116/verify.py
python -B research/independent_audits/issue62_landing_angle_bound_20261123/verify.py --check-certificate
python -B code/verify_physical_bridges.py
python -B code/verify_physical_bridge_routes_test.py
```

The width regression has 11 passing tests. The finite width verifier checks
p=3…12 and invokes the corrected tail argument. The new graph verifier checks
the 96 vertices, 144 edges, complete grid-endpoint exclusion, exact all-horizon
recurrence and every field of the committed certificate. These checks are
included in the Research validation workflow. No Lean source was changed or
new Lean proof claimed in this packet.

## Attribution and review

Classical inputs are credited at theorem level in the individual notes:
Kahn–Kapiamba–Lyubich for the ideal/path category, conformal uniformization
and Schwarz–Christoffel theory for the metric comparisons, Furstenberg for
entropy and dimension, and McMullen and Douady–Hubbard for the corrected
rigidity endgame. The archive's earlier physical parameter, tree, landing
and sector theorems remain indispensable inputs.

Prepared with OpenAI GPT-6 Astra Pro for source inspection, proof development,
exact arithmetic, implementation and independent adversarial review. Several
initial claims were narrowed or rejected during that review. No human
specialist review has occurred; this packet makes no claim of a global MLC
proof or of a new general entropy–dimension theorem.
