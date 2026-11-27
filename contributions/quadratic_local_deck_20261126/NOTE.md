---
ledger: VIRTUAL_RETURN_BASE_ATLAS
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-local-deck-20261126"></a>

# Cyclic local sheets and constructive monodromy for every quadratic iterate

Ledger statement being addressed:

> Every actual virtual-Molecule block and finite provisional root package has source-defined open nice return localizations and actual atomic branch components with integer iterates, complete critical and degree words, exact component, parent, obstacle, localization, sheet, and protected-access phase data, together with exact enlargement morphisms and demand-bijective no-birth maps wherever complete language stability is claimed.

## Claim

For every complex parameter `c`, anchor `x`, and finite time `n`, this contribution
constructs a physical analytic chart for the actual polynomial iterate
`F = orbit c n`. Put

\[
k=\#\{j<n:f_c^j(x)=0\},\qquad m=2^k.
\]

On one constructed open neighborhood `U` containing `x`, the full collection of
continuous fiber-preserving self-maps is a cyclic group of exactly `m` distinct
source restrictions. Its phase is the derivative at `x`. Continuity is required
only on `U \ {x}`; analyticity, continuity at the anchor, and bijectivity are
conclusions. The chart exists unconditionally for all `c`, `x`, and `n`, including
repeated critical encounters and the unramified cases `m = 1` and `n = 0`.

The same chart gives the unique continuous lift of a full circular target loop
through any noncentral source point. One target turn applies the primitive cyclic
generator, and the lift returns after `j` full turns if and only if `m` divides `j`.
If `k > 0`, no continuous right inverse landing in this `U` exists on any full
punctured disk about `F x`.

**Validation status at this checkpoint:** all generic proofs compile locally;
production CI has already compiled `PowerMapRigidity` and `QuadraticLocalDeckAction`
at the preceding checkpoint. Corrected rigidity integration and the new monodromy
module are now submitted for complete production compilation and the compiled
proof-dependency audit. No result is counted as validated under the requested
standard until those CI steps pass.

## Evidence

### 1. Actual objects and the source chart

`exists_quadratic_powerChart` in
`formalization/weighted/QuadraticLocalDeckAction.lean` wraps the existing
`quadratic_power_disk_chart` theorem without adding a hypothesis. It constructs
`C : PowerChart (orbit c n) x (2^criticalVisits c x n)` with:

- a nonzero complex coefficient `a`, positive real radius `r`, and open `U` containing `x`;
- mutually inverse analytic coordinates `coord : U -> ball 0 r` and
  `inv : ball 0 r -> U`, both onto their indicated domains;
- `coord x = 0` and derivative `coord' x = 1`;
- the exact identity `F z - F x = a * (coord z)^m` on all of `U`.

The underlying factorization and analytic normal form were already established in
`TelescopeRamification.lean` and `QuadraticPowerNormalForm.lean`. The local inverse
count was already in `QuadraticLocalFiberCensus.lean`. Those are dependencies,
not results newly claimed by this PR.

### 2. An actual cyclic action, not only a fiber count

For each `zeta^m = 1`, define

\[
\tau_\zeta(z)=\operatorname{inv}(\zeta\operatorname{coord}(z)).
\]

A root of unity has modulus one, so every phase acts on the same physical source
`U`. `deck_mem`, `deck_analytic`, `deck_preserves`, `deck_mul`, and
`deck_deriv_center` prove source preservation, analyticity, exact preservation of
`F`, the composition law, and `tau_zeta'(x) = zeta`.

`same_fiber_iff_deck` proves

\[
F(w)=F(z)\quad\Longleftrightarrow\quad
\exists\zeta^m=1,\ w=\tau_\zeta(z)
\qquad(z,w\in U).
\]

`deck_phase_unique` makes the phase unique when `z != x`; `deck_fixed_iff` says
that a nonidentity phase fixes only `x`. `map_eq_center_iff` proves that the fiber
of `F x` inside this source is exactly `{x}`.

The explicit phase

\[
\xi=\exp(2\pi i/m)
\]

is primitive. `deck_eq_generator_iterate` expresses every phase map as an iterate
of `tau_xi`, while `generator_period_iff` proves the exact pointwise order

\[
\tau_\xi^j(z)=z\quad\Longleftrightarrow\quad m\mid j
\qquad(z\in U,\ z\ne x).
\]

### 3. Exhaustion of every continuous sheet choice

`PowerMapRigidity.lean` proves punctured complex disks are preconnected, using
four overlapping convex half-disks. For `m > 0`, `power_preserving_rigidity`
proves that any map `g` continuous on the punctured disk and satisfying
`g(z)^m = z^m` on the disk is one constant root rotation. Indeed, `g(z)/z` has
preconnected image contained in the finite set of `m`th roots of unity, so its
image is a singleton. The central fiber equation forces `g(0) = 0` without an
extra continuity assumption.

`continuous_fiber_preserver_eq_deck` in `QuadraticLocalDeckRigidity.lean`
applies this to `coord o T o inv`. Its exact premises are:

1. `ContinuousOn T (U \ {x})`;
2. `MapsTo T U U`;
3. `F (T z) = F z` for every `z in U`.

Its conclusion is a **unique** `zeta^m = 1` with `T = tau_zeta` on `U`.
`continuous_fiber_preserver_analytic_bijective` derives analyticity and `BijOn`;
`continuous_fiber_preserver_deriv` identifies this unique phase with `deriv T x`.

The finite object `deckMaps` consists of restrictions `U -> complex`, so arbitrary
behavior outside `U` is not counted. `deckMaps_card` proves its cardinality is
exactly `m`, and `mem_deckMaps_iff` proves that this finite list exhausts exactly
the continuous, source-preserving, fiber-preserving restrictions.

`quadratic_local_deck_classification` supplies this chart and classification for
every actual quadratic iterate with the orbit-derived multiplicity `2^k`.

### 4. Constructive monodromy and uniqueness of the lifted path

`QuadraticLocalMonodromy.lean` defines, for every real `t`,

\[
\gamma_z(t)=\operatorname{inv}
 \left(e^{2\pi i t/m}\operatorname{coord}(z)\right).
\]

`circularLift_continuous`, `circularLift_mem`, and `circularLift_image` prove
that this is a continuous physical trajectory in `U` and that

\[
F(\gamma_z(t))=F(x)+(F(z)-F(x))e^{2\pi i t}.
\]

For `z != x`, both the lifted trajectory and its target avoid their respective
centers. The target circle is formally nondegenerate. `circularLift_zero` and
`circularLift_one` identify the starting point and the endpoint after one turn:

\[
\gamma_z(0)=z,\qquad \gamma_z(1)=\tau_\xi(z).
\]

`circularLift_unique` proves that **every** continuous lift on `[0,1]` with that
target trajectory, starting at `z` and staying in `U`, agrees with this formula.
For a competing lift `lambda`, the quotient

\[
\frac{\operatorname{coord}(\lambda(t))}
 {e^{2\pi i t/m}\operatorname{coord}(z)}
\]

is continuous, takes values in a finite root set, and equals one at `t = 0`.
Connectedness of the interval forces it to remain one.

`circularLift_nat_eq_self_iff` proves that the constructed lift returns after
`j` complete turns exactly when `m` divides `j`. This is transport along an
actual specified loop in the target plane, not merely an abstract permutation
of a finite fiber. `quadratic_local_circular_monodromy` constructs this entire
package for the actual polynomial iterate at every anchor and time.

### 5. Obstruction to a continuous single-sheet inverse

`power_no_continuous_section` proves that every complex power of degree greater
than one has no continuous right inverse on an entire punctured disk of any
positive radius. No bound on that section's image is assumed. Composing a
putative section with the power map would give a power-preserving map, hence a
nonzero constant rotation. A nontrivial root-of-unity rotation preserves the
power map, contradicting the injectivity of that constant rotation.

`ramified_no_continuous_section` in `QuadraticLocalInverseObstruction.lean`
transfers the obstruction through the affine target coordinate and analytic
source coordinate. `quadratic_critical_local_no_continuous_section` concludes:
if `criticalVisits c x n > 0`, there is an open `U` containing `x` such that for
**every** `epsilon > 0` there is no `S` satisfying all three clauses

- `ContinuousOn S (ball (F x) epsilon \ {F x})`;
- `MapsTo S (ball (F x) epsilon \ {F x}) U`;
- `F (S w) = w` throughout that punctured target disk.

The source restriction is essential. A critical value can have other regular
preimages elsewhere in the plane; this theorem concerns the constructed ramified
local source.

### 6. Reproduction and proof audit

Pinned versions: Lean `leanprover/lean4:v4.32.0`; Mathlib `v4.32.0` from the
existing project manifest. No toolchain, dependency, workflow, or audit policy
is changed.

From the repository root:

```sh
python code/contribute.py check
cd formalization/weighted
lake exe cache get
lake build PowerMapRigidity QuadraticLocalDeckAction QuadraticLocalDeckRigidity QuadraticLocalInverseObstruction QuadraticLocalMonodromy
```

The existing **Weighted spectral mathlib proofs** workflow builds the whole
weighted project and runs:

```sh
python3 -B code/verify_lean_coverage.py --audit weighted
```

That audit calls `Lean.collectAxioms` for every compiled project declaration and
allows only `propext`, `Classical.choice`, and `Quot.sound`. All new sources and
all public theorem names are registered using `code/contribute.py lean-add`.
There are no proof placeholders, new postulates, native-evaluation shortcuts, or
changes to the allowed dependency set.

Exact final-head CI evidence will be recorded here after the pending production
build and audit complete. Local generic probes are debugging evidence only;
they do not replace the production build of the actual quadratic wrappers.

## Dependencies

- Addressed ledger row: `VIRTUAL_RETURN_BASE_ATLAS`, which remains open.
- Source-level branch record and missing global selection/enlargement clauses:
  `research/mlc_unified/virtual_return_base_atlas.md`, Sections 3.3, 8, 9, and 11.
- Existing archive Lean proofs: `TelescopeRamification.lean`,
  `QuadraticPowerNormalForm.lean`, and `QuadraticLocalFiberCensus.lean` and their
  unchanged transitive imports.
- Pinned Mathlib: complex exponentials and roots of unity, analytic calculus,
  finite polynomial root sets, continuity, convexity, and connectedness.
- No external research theorem is imported as an unproved Lean premise.

## Boundary

1. **Local actual dynamics.** The chart and every stated orbit equation concern
   the actual map `z -> z^2+c` and its finite iterates. No symbolic surrogate is
   substituted for that map. The source is a constructed local neighborhood,
   not an arbitrary global return component.
2. **The virtual selector is still missing.** This does not construct a nice
   return base for every virtual-Molecule scale, an entire branch atlas, a
   source-faithful Wave demand inventory, or enlargement/no-birth morphisms.
3. **Intrinsic phases are not the native external marking.** The phase supplied
   here is an intrinsic local derivative and is realized by a specified small
   circular target loop. Its identification with the native external-angle,
   relative-cover, or protected prime-end phase remains unproved.
4. **Exact scope of the inverse obstruction.** A full punctured target disk and
   image contained in the selected ramified source are required. The theorem
   does not exclude an inverse branch on a slit disk or in a different source
   sheet elsewhere in the plane.
5. **No unjustified uniformity.** No uniform lower bound for the source radius
   is proved across parameters, return times, or virtual blocks.
6. **Status.** The result is `partial`. No ledger status change is proposed.
   H1--H4, universal protected-tower closure, and MLC remain open. No worldwide
   originality claim is made for the classical mathematics or its formalization.
7. **Review.** No human mathematical review has occurred. Independent AI proof
   development and statement review supplement, and do not replace, Lean/CI.

## Attribution

The local power-map description, root-of-unity symmetries, connected-image
rigidity argument, and cyclic monodromy are classical complex analysis. This PR
extends the archive's formal coverage from analytic normal forms and local fiber
counts to exhaustive continuous symmetry classification, explicit uniquely lifted
circular transport, and a continuous inverse-selection obstruction.

The prior arbitrary-multiplicity normal forms and fiber counts came from the
archive's local-degree-saturation work (PR #224). The existing one-critical
`TelescopeDeckInvolution.lean` and concurrent global degree-two return work in
PR #226 are related predecessors. The regular inverse-atlas work in PR #228
addresses a different part of the branch problem. None of those results is
rebranded as new here. The source boundary audit builds on the earlier-work
references returned by `code/contribute.py show VIRTUAL_RETURN_BASE_ATLAS`.
