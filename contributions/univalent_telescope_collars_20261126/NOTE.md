---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="univalent-telescope-collars-20261126"></a>

# Constructing univalent open collars and one-critical returns from actual compact cores

## Claim

**Proof-development checkpoint: local and CI validation pending.** All claims
below are candidate Lean theorems until the complete kernel build and transitive
axiom audit succeed. The research contribution is partial for MAPPING_TELESCOPE.

Write `f(z) = z^2+c` and `F_n = f^n`, using the archive's actual complex orbit
`QuadraticEscape.orbit`. For every compact set C, an open neighborhood on which
F_n is injective exists **if and only if** F_n is injective on C and
`F_j(z) != 0` for all z in C and all j < n. The terminal time is excluded.
The compact set need not be connected, full, locally connected, or nonempty.

For a compact connected target K and an anchor x with F_n(x) in K, let C be the
full connected component of the actual inverse image F_n^{-1}(K) containing x.
If this compact core satisfies the criterion, then every prescribed open
neighborhood W of C contains the compact closure of an open selected pullback
U over a constructed open connected neighborhood V of K. F_n is injective on
closure U, maps U properly onto all of V, and has an analytic inverse g on V.
Moreover `g '' K = C` exactly. A single positive target margin works for all
sufficiently close open target neighborhoods, not just one chosen exhaustion.

The main extension constructs compatible open stages for a return with one
critical step. Start with the actual compact components

- D0: the component of F_b^{-1}(K) through c;
- B0: the component of f^{-1}(D0) through 0;
- A0: the component of F_a^{-1}(B0) through x, where F_a(x)=0.

Assume K is compact and connected, F_b(c) belongs to K, and the **compact**
prefix A0 and suffix D0 satisfy injectivity and preterminal critical avoidance
for F_a and F_b respectively. Open injective domains are not hypotheses.
The theorem constructs an open connected target V and its actual selected
stages D, B, A, proves compact closure and prescribed ambient control, and
proves that A is the entire selected component of F_{a+1+b}^{-1}(V). The return
is onto V and proper, and for **every** v in V the sum of Mathlib analytic
multiplicities over its complete A-fiber is exactly two. This includes the
propagated critical value, where cardinality alone would give the wrong count.

## Evidence

### 1. Compact injectivity extends precisely when critical encounters are absent

[QuadraticUnivalentNeighborhood.lean](../../formalization/weighted/QuadraticUnivalentNeighborhood.lean)
contains `quadratic_step_univalent_neighborhood`,
`quadratic_compact_univalent_neighborhood`, and
`quadratic_compact_univalent_neighborhood_within`.

For a single quadratic step, compact injectivity and exclusion of zero imply
that C and -C are disjoint. Separate these two actual compact plane sets by
open sets and intersect one with the reflected other; the exact quadratic
collision factorization then proves injectivity on this open neighborhood.
For a finite iterate, induct on its length, extending the prefix and the
last-step image and intersecting with the appropriate continuous preimage.
This constructs neighborhood injectivity instead of assuming it.

The converse in `compact_univalent_neighborhood_iff` reuses the already proved
`orbit_injOn_no_critical_visits`: an earlier critical encounter makes an open
intermediate image contain a reflected pair, hence makes the final iterate
noninjective. Critical avoidance is necessary, including when compact
injectivity alone is vacuous on a singleton critical core.

### 2. Actual selected collars, with closure and core control

[TelescopeUnivalentCollars.lean](../../formalization/weighted/TelescopeUnivalentCollars.lean)
contains the exact criterion and the construction:

- `selected_univalent_collar_margin` first chooses a compactly contained open
  neighborhood inside the univalent domain and the requested ambient set.
  The existing proper-component upper semicontinuity then supplies a uniform
  target margin. Connectedness of the closure puts the entire pullback closure
  in the selected component over the closed target thickening. Thus injectivity
  and ambient containment hold on the closure, not just in the interior.
- `connected_open_target_neighborhood` selects one component of a metric
  thickening. Connectedness of K proves that this component contains all of K.
- `selected_univalent_open_collar` combines that construction with the actual
  orbit's open and proper map theorems. Surjectivity onto the whole target and
  a homeomorphism of the actual subspaces are outputs.
- `selected_inverse_exact_core` uses connectedness of the inverse image of K
  under the constructed continuous inverse and maximality of the anchored
  connected component to prove the exact compact-core identity.
- `selected_univalent_analytic_collar` assembles the collar, analytic inverse,
  reciprocal derivative and exact compact-core image into one theorem.

### 3. Analytic inverse and physical branch compatibility

[TelescopeConformalInverse.lean](../../formalization/weighted/TelescopeConformalInverse.lean)
contains `orbit_deriv_ne_zero_iff`, `orbit_conformal_of_open_injective`,
`orbit_conformal_inverse`, `orbit_inverse_restriction_agreement`, and
`orbit_inverse_concatenation`.

The actual derivative is nonzero exactly in the absence of preterminal
critical encounters. Define the inverse by `Function.invFunOn` on the actual
open source. Its left-inverse identity holds in a neighborhood of every source
point. The analytic inverse-function theorem makes that same chosen inverse
analytic at every target point, with derivative `1 / deriv(F_n)(g(y))` and
conformality. Uniqueness proves agreement under restriction and reversed-order
composition under chronological concatenation. No target simple connectivity,
ray landing, or boundary extension is assumed.

### 4. Construct the compatible open one-critical return

[TelescopeCompactReturn.lean](../../formalization/weighted/TelescopeCompactReturn.lean)
contains `compact_one_critical_return_collar`. The margins are selected in a
specific, noncircular order:

1. Compact prefix conditions give a target margin around B0.
2. Properness of the quadratic step gives a margin around D0 forcing its
   selected critical pullback B inside the prefix margin.
3. Apply the suffix collar theorem with ambient neighborhood intersected with
   that D0 margin; its compact closure both remains univalent and forces the
   critical pullback into the correct B0 neighborhood.
4. Choose the connected open target V once, after all margins are fixed.
   The three selected components are now compatible by their actual definitions.
5. Apply the existing `selected_saturated_return_full_degree` to the constructed
   stages. Its open prefix/suffix injectivity assumptions have been discharged
   from compact-core data, not repeated as hypotheses of the new theorem.

The additional `compactly_contained_one_critical_return` records the stronger
conclusion available if A0 is independently known to lie in the interior of K:
then closure A lies in V. This extra hypothesis is not derived from compact
saturation and does not apply to an empty-interior Julia target.

### Reproduction and validation

The local toolchain is the exact repository-pinned Lean 4.32.0, with the exact
pinned Mathlib revision. No toolchain, dependency, workflow, validator, or
canonical status record changes are made. Every public theorem is registered
by the repository's `lean-add` command under the existing CONSTRUCT route.

```sh
cd formalization/weighted
lake exe cache get
lake build QuadraticUnivalentNeighborhood TelescopeConformalInverse TelescopeUnivalentCollars TelescopeCompactReturn
lake build
cd ../..
python code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

The existing CI workflow performs the full weighted build and audits the
transitive dependencies of every declaration. Only the repository's standard
foundational allowlist (`propext`, `Classical.choice`, `Quot.sound`) is accepted.
No `sorry`, `admit`, new axioms, native evaluation, unsafe declarations, or
implementation overrides are introduced. Successful CI links will be recorded
before this draft is marked ready.

## Dependencies

Research target: MAPPING_TELESCOPE. Its ledger prerequisites
PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER, RELATIVE_COVER_LIFT, and
STAGE_FORWARD_CLOSURE describe the research context; no documentary ledger
status is used as a proof premise.

Formal inputs are the actual orbit definition in QuadraticEscape;
SaturatedTelescope's quadratic collision and component composition results;
TelescopeRamification's analytic order and critical-encounter results;
TelescopeCollarRecognition's properness, component upper semicontinuity and
weighted-degree theorem; QuadraticExtremalMultiplier's actual derivative;
QuadraticCylinderRamification's open restriction homeomorphism; and the pinned
Mathlib's compact separation, connected components, analytic inverse-function
theorem, and complex conformality. All other mathematical steps are checked in
the new Lean modules.

## Boundary

This is an actual-map, finite-stage construction conditional on explicit compact
core geometry. It does not establish the compact prefix/suffix hypotheses for
every native virtual-Molecule block. It constructs open connected domains and
compact closures; their Jordan boundaries and simple connectivity are not
proved. It does not construct the source's marked relative-cover lifts or
complete basepoint/deck-phase route, prove compatible cyclic Jordan domains,
or obtain parameter-uniform collar radii or analytic bounds. The compactly
contained corollary requires its additional interior-containment hypothesis.

Therefore MAPPING_TELESCOPE, H1, and MLC remain open, and no ledger status change
is requested. This formalizes a further construction in the archive; it makes
no priority claim over classical complex analysis or topology.

## Attribution

Builds on [the saturated telescope contribution](../saturated_telescope_20261126/NOTE.md),
[the ramification and proper-collar contribution](../telescope_ramification_order_20261126/NOTE.md),
and [the written cyclic pullback audit](../../research/independent_audits/h1_mapping_telescope_20261126/NOTE.md).
The source-facing residual is [critical chronology, section 15.3](../../research/mlc_unified/critical_chronology_and_retimed_telescope.md#153-relative-cover-and-marked-telescope).
The new step is the quantified existence of open univalent stages from compact
actual-core data, with the exact analytic inverse and weighted full return;
the prior formal degree theorem assumed those open univalent stages.
Proof development, integration and adversarial review are AI-assisted.
No independent human review has occurred.
