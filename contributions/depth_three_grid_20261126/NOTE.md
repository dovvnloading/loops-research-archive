---
ledger: NOV26_OPEN_26_TRIPLES
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="depth-three-grid-20261126"></a>

# The complete depth-three finite arithmetic grid

Ledger statement being addressed:

> Remaining depth-three finite triples: The (3,3,3) exact packet does not check the other 26 triples in {3,4,5}^3.

## Claim

The submitted Lean statements supply the missing 26 finite arithmetic packets, together with the archived `(3,3,3)` case as a regression, for every word in `{3,4,5}^3`. Each packet contains an isolated actual real collision-polynomial root, the two signed suffix itineraries, all three ancestor disk margins, phase separation and nesting, real connectors, terminal cut and fixed-point brackets, the separate terminal three-return margin, entire round-gate containment, and checked rational logarithm/Taylor/AGM envelope witnesses.

**Draft validation status:** all four new core modules have compiled locally, including exhaustive coverage, pairwise chart separation, and all 27 geometry and rational width certificates. Their transitive dependency audit checked 575 declarations and accepted only the repository's permitted logical foundations. The core Lean and Python CI jobs have passed, and both the Mathlib real-root/trace module and the complete complex-remainder module have compiled in CI. The final grid synthesis is undergoing compilation and CI validation; this checkpoint does not yet request a ledger status change.

The target is exactly the finite arithmetic omission named in `NOV26_OPEN_26_TRIPLES`. The physical and arbitrary-depth obligations are kept separate in the Boundary below.

## Evidence

### 1. Actual recurrence and the selected charts

Put

\[
f_c(z)=z^2+c,\quad x_0(c)=0,\quad x_{j+1}(c)=x_j(c)^2+c,
\]

\[
D_0(c)=0,\quad D_{j+1}(c)=2x_j(c)D_j(c)+1,
\]

and let `A_0=0`, `A_1=1`, and `A_(j+1)=2*x_j*A_j` for `j>=1`. For the word `(p,q,r)`, the three return times are `p`, `p*q`, and `n=p*q*r`. Its collision polynomial is

\[
P_n(c)=x_{3n}(c)+x_{6n}(c).
\]

Every parameter chart is an explicitly listed dyadic interval with common scale `S=2^512`. `data.json` contains the integer endpoints, three positive rational radii, the bracket for the normalized dividing fixed point, the two distinct suffix reference charts, and the rational width witnesses. `DepthThreeGrid.lean` contains the corresponding literal Lean terms.

The certificates check strictly opposite signs at the exact chart endpoints and a strict single-sign derivative enclosure throughout the entire chart. `DepthThreeReal.certified_unique_real_root` (full namespace `LoopsDepthThreeReal`) uses the actual real polynomial and its calculus derivative, then applies Mathlib's intermediate-value and strict-monotonicity results. It establishes a unique real root strictly inside the chart. The rounded numerical seed is never asserted to be a root.

The generated theorem `parameterChartsSeparated` checks that all 27 closed charts are pairwise strictly separated. `remainingCount`, `remainingWordsNodup`, and `remainingComplete` account for exactly the 26 previously missing words. They exclude the original `(3,3,3)` row explicitly.

### 2. Correct branch and suffix data

A root of `P_n` alone does not select the desired chart. Every packet also checks the first primitive real prefix, the signs of all three quadratic coefficients, the terminal preperiodic branch, and two different signed suffix itineraries:

- The `p`-return is compared with the archived depth-two `(q,r)` reference, through `6*q*r` steps.
- The `p*q`-return is compared with the archived depth-one `r` reference, through `6*r` steps.

The independent verifier locks those reference intervals to the exact archived values. The Lean theorem computes the comparisons with those same literal reference intervals. This is a finite signed itinerary assertion; identification with a Douady–Hubbard tuning construction is not silently inferred from it.

The outer real connector now includes the entire `6*q*r` horizon. This is stronger than the shortened connector check in the original `(3,3,3)` packet.

### 3. Whole-disk inequalities

For each return, the checker starts from the exact recurrence

\[
f_c^j(z)=x_j(c)+A_j(c)z^2+R_j(c,z)
\]

and propagates the complete error majorant

\[
T_1=0,\qquad
T_{j+1}=2|x_j|T_j+(|A_j|\rho^2+T_j)^2.
\]

This bounds every higher term on the entire closed disk, without a sampled-circle test or a truncated unbounded remainder. `DepthThreeReal.trace_enclosed` interprets all three stored trace coordinates on every real parameter in its chart. `DepthThreeRemainder.errors_sound` connects the integer error recursion to the norm of the actual complex residual for every `|z|<=rho`.

The disk-gap numerator is the exact denominator-cleared form of

\[
|A_j|\rho^2-|x_j|-T_j-\rho>0.
\]

`positive_margin_quadratic_comparison` turns this into the actual Rouché-ready inequality on the complete boundary circle,

\[
\left|f_c^j(z)-A_j(c)z^2\right|+\rho
  < |A_j(c)z^2|\qquad(|z|=\rho).
\]

`grid_packet_boundary_comparison` supplies this inequality for all three ancestor return circles of every grid packet, uniformly throughout its real parameter chart. Its proof extracts the positive margins directly from the computed geometry certificate and supplies the trace and error bounds; callers need not assume those analytic estimates.

The arithmetic packet further checks the complete phase disk separation and containment inequalities, their real connectors, the O1/O2 cut ordering, a strict fixed-point bracket, and the independent `3n`-return. The latter retains the normalized margin `>1/8`; it is not substituted by the `n`-return check. The whole closed radial gate is checked by a disk-image majorant, including its center connector.

These are the finite inequalities used by the original packet. The topological and marked-family interpretation of them is distinguished from the inequalities themselves.

### 4. Rational width-envelope witnesses

`DepthThreeWidth.lean` checks each logarithmic, inverse-cosine, complementary-square-root, and AGM witness with exact rational arithmetic. The logarithmic input is tied to the same packet's gate endpoints. The inverse-cosine witnesses are checked against the degree-34 cosine polynomial with the symmetric remainder `t^36/36!`. Every square-root bracket is verified by positive rational square inequalities. All ten AGM steps are checked; a final asserted numerical answer cannot bypass those steps.

For each packet the checked rational lower and upper expressions satisfy

\[
\frac14<L_{\rm rat}<Q_{\rm rat,lower},\qquad
Q_{\rm rat,upper}<\frac{31}{40}.
\]

The smallest generated lower expression is approximately `0.251600738016327`; the largest upper expression is approximately `0.774316277696401`. These decimal displays are not proof inputs. The strict rational inequalities and all supporting witnesses are the Lean statements in `DepthThreeWidthGrid.lean`.

The final closure theorem combines `RootCertificate`, `GeometryCertificate`, and `WidthCertificate`; a width witness alone is not treated as a complete packet. The generic rational checker does not itself assert a theorem about a physical KKL extremal-width supremum.

### 5. Formal declarations and reproduction

The primary proposed closure statement is

`LoopsDepthThreeClosure.remaining_twenty_six_closed`.

`complete_depth_three_grid` includes the regression row. For each quantified word these statements supply a matching explicit packet, its geometry and rational envelope certificates, and a unique actual real root of `P_(p*q*r)` in the certified open parameter chart. The complex residual theorem is uniform over every real parameter in each closed chart and every point of the relevant closed disk.

The proof inputs are generated by `emit_core.py` and `emit_width_lean.py`. Both are untrusted source generators: Lean recomputes their certificate predicates with `decide +kernel`. No Python return value, numerical continuation result, or opaque externally computed theorem is accepted as a proof.

```sh
python -B contributions/depth_three_grid_20261126/verify_grid.py
python -B contributions/depth_three_grid_20261126/check_rejections.py
python contributions/depth_three_grid_20261126/emit_core.py
python contributions/depth_three_grid_20261126/emit_width_lean.py
lake build DepthThreeGrid DepthThreeWidthGrid
(cd formalization/weighted && lake exe cache get && lake build DepthThreeClosure)
python -B code/verify_lean_coverage.py --audit root
python -B code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

The numerical search script is included to explain discovery and permit regeneration. It is not a verifier. Sixteen adversarial controls test the actual failure modes: a shifted chart, two other genuine roots that pass isolated-root tests but fail branch or kneading, the rejected child radius `1/200`, invalid fixed-point and suffix data, false log/cosine/square-root/AGM witnesses, omitted or duplicated words, and overlapping charts.

## Dependencies

- `NOV26_DEPTH3`, the original finite `(3,3,3)` certificate, in `research/independent_audits/tip_family_all_depths_20261116/NOTE.md` and its `verify.py`.
- The nine depth-two suffix reference charts and the depth-one tips in `research/independent_audits/tip_family_renormalization_depth_20261116/verify.py`.
- The repository's generic signed-interval arithmetic and rational recurrence modules, especially `Period27Dyadic.lean`, `Period27IntervalSound.lean`, and `Period27RationalDerivative.lean`.
- The actual critical-orbit calculus in `formalization/weighted/Period27RealCenter.lean`, and the complex quadratic orbit in `QuadraticEscape.lean`.
- Lean `v4.32.0` and the repository-pinned Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997` for real/complex arithmetic, continuity, differentiation, intermediate values, and monotonicity.

No new axioms are declared. The repository's compiled dependency audit permits only its standard logical foundations: `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

The proposed status change is closure of **the finite arithmetic census** `NOV26_OPEN_26_TRIPLES`, after the final Lean and CI checks pass. The ledger itself is unchanged for maintainer review.

The result does not identify these signed charts with designated tuning copies by a new formal straightening theorem. It does not formalize the subsequent Rouché/topological degree-two construction, KKL prime-end marking, extremal-length/logarithm/cosine/AGM interpretation, or the elliptic full-slit width formula as a physical KKL theorem. The original packet explicitly lists those external identifications separately from its finite arithmetic certificate; this extension preserves that distinction.

Consequently `NOV26_OPEN_DEPTH_GATES`, whole-marked QC correspondence, canonical optimal-width attainment/convergence, arbitrary periods or depths, H1–H4, UPTCR, and MLC remain outside this result. The physical width statement `1/4 < W* < 31/40` is not asserted as a new unconditional Lean theorem. What is certified here is the exact finite data, their real-root and complex-remainder semantics, and every rational inequality in the finite packet schema.

## Attribution

This work extends the archive's November 16 depth-three and depth-two packets and its existing interval-soundness and quadratic-dynamics formalizations. The new contributions are the 26 missing charts, complete finite census, their exact certificates, the formal semantic connections needed to validate those certificates, and adversarial rejection checks. The original `(3,3,3)` row is retained only as a regression. Classical tuning, straightening, KKL, and extremal-length results are neither rebranded as new research nor added as axioms. OpenAI ChatGPT, GPT-6 Astra Pro performed the search, formalization, independent checker review, and validation. Human review: none.
