---
ledger: H1_CELL_TREE_EXTRACTION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-component-conjugacy-20261126"></a>

# Exact binary dynamics on escaping quadratic components

Ledger statement being addressed:

> Every virtual-molecule block admits a monotone finite cell-tree quotient of its dynamically relevant Cantor carrier with universal atomic and gate incidence and compatible partial cellular dynamics.

## Claim

For every complex quadratic parameter with escaping critical point, this packet
constructs a binary itinerary whose fibers are exactly the connected components
of the actual filled set. The induced component dynamics is topologically
conjugate to the one-sided full binary shift. Exact periodic-component counts,
density of periodic components, and topological exactness follow from this
conjugacy. The validation section records the compiler checkpoint; development
checkpoints remain explicitly provisional until they pass Lean and its dependency
audit.

Write

\[
f_c(z)=z^2+c,\quad G_c(z)=\operatorname{escape}(c,z),\quad
K_c=\{z:G_c(z)=0\},\quad a_c=G_c(0)>0.
\]

The archive already proves that `K_c` is the actual bounded-orbit set. Let
`F_c` denote the continuous action of `f_c` on the actual connected-component
quotient `pi_0(K_c)`, and let `sigma(omega)(k)=omega(k+1)`. The new conclusions are:

1. There is a continuous surjective itinerary `iota:K_c -> {0,1}^N` with
   `iota(f_c(z))=sigma(iota(z))` and

   \[
   \iota^{-1}(\iota(z))=\operatorname{Component}_{K_c}(z).
   \]

   Connectedness of every full itinerary fiber is proved from the actual
   positive escape sublevels; it is not supplied as an assumption.
2. There is a homeomorphism

   \[
   E:\pi_0(K_c)\simeq\{0,1\}^{\mathbb N},\qquad E\circ F_c=\sigma\circ E.
   \]

   Thus the earlier surjective component factor is strengthened to an exact
   classification of components by binary itineraries.
3. For every positive integer `n`, precisely `2^n` components are fixed by
   `F_c^n`. This count includes components whose minimal period is a proper
   divisor of `n`. Separately, every positive `n` occurs as a minimal component
   period, and periodic components are dense in the quotient topology.
4. For every nonempty open family `U` of components, there is `N` such that

   \[
   F_c^n(U)=\pi_0(K_c)\quad\text{for all }n\ge N.
   \]

   Consequently every such family eventually meets every nonempty target
   family under all later iterates. No parameter-independent or
   neighborhood-independent bound on `N` is claimed.

These statements concern genuine quadratic components at every escaping
critical parameter. They formalize classical dynamics and topology; no
mathematical priority beyond this archive's formalization is claimed.

## Evidence

### Registered Lean modules

| Module | Principal declarations |
|---|---|
| [ConnectedBinaryCoding.lean](../../formalization/weighted/ConnectedBinaryCoding.lean) | `cylinder_mem_iff`, `address_fiber_image`, `address_fiber_preconnected`, `address_fiber_connected`, `component_eq_address_fiber`, `component_conjugacy` |
| [QuadraticComponentConjugacy.lean](../../formalization/weighted/QuadraticComponentConjugacy.lean) | `filled_coherent_branch_system`, `quadraticComponentMap_mk`, `filled_component_image`, `filled_binary_component_model`, `filled_component_conjugacy` |
| [BinaryShiftPeriodic.lean](../../formalization/weighted/BinaryShiftPeriodic.lean) | `shift_periodic_card`, `periodic_extension`, `shift_has_exact_period`, `shift_periodic_dense` |
| [BinaryShiftExactness.lean](../../formalization/weighted/BinaryShiftExactness.lean) | `shift_open_eventually_onto`, `conjugate_open_eventually_onto`, `conjugate_eventual_intersection` |
| [QuadraticComponentDynamics.lean](../../formalization/weighted/QuadraticComponentDynamics.lean) | `quadratic_component_periodic_card`, `quadratic_component_has_exact_period`, `quadratic_periodic_components_dense`, `quadratic_component_open_eventually_onto`, `quadratic_component_eventual_intersection` |

All public theorems are registered in the existing theorem and source indices;
all five modules are default targets of the existing weighted Lake project.
No workflow or canonical status record is changed.

### Construction and proof

**1. Choose one geometric splitting.** Put `X=S_c(a_c)`, where
`S_c(t)={z:G_c(z)<=t}`. The existing critical-height connectivity theorem
proves that `X` is connected, including at the critical height itself. It is
compact. Use the established actual splitting once, at height `a_c/2`:

\[
S_c(a_c/2)\simeq\{0,1\}\times X.
\]

Compose each inverse section with the inclusion into `X` to obtain continuous
branches `b_0,b_1:X -> X`. Their joint map `(i,x) -> b_i(x)` is injective,
so their full images are disjoint. They satisfy the genuine polynomial and
escape-height equations

\[
f_c(b_i(x))=x,\qquad 2G_c(b_i(x))=G_c(x).
\]

The splitting is fixed once for all depths. Independently chosen labelings
at successive heights would not supply the coherence used below.

**2. Restrict the same branches to the actual filled set.** The height equation
shows that both branches preserve `K_c`. Conversely every point of `K_c`
comes from exactly one branch, since the positive-height splitting exhausts
the full inverse image and its second coordinate is the actual polynomial.
The resulting continuous bijection from `{0,1} x K_c` to `K_c` is a
homeomorphism by compactness. Its inverse, denoted `e`, has second
coordinate `f_c`. This constructs the coherent zero-height splitting rather
than assuming compatibility with an unrelated binary coding.

**3. Construct every finite cylinder geometrically.** For an infinite address
`omega`, define compact subsets of `X` by

\[
C_\omega(0)=X,\qquad
C_\omega(n+1)=b_{\omega(0)}(C_{\sigma\omega}(n)).
\]

Continuity preserves compactness and connectedness; inclusion under the
branches proves nesting. The exact height equation gives

\[
2^nG_c(z)\le a_c\quad(z\in C_\omega(n)).
\]

If a point belongs to every cylinder, positivity of its escape height would
contradict unboundedness of `2^n`. Therefore the whole intersection lies in
`K_c`; the limit-containment hypothesis of the generic theorem is proved
for the physical quadratic system.

**4. Identify entire fibers, without selecting one point per address.** Let
`j:K_c -> X` be the actual inclusion. Joint branch injectivity and the
coherence identity

\[
j(e^{-1}(i,y))=b_i(j(y))
\]

give, by induction, that `j(y)` lies in the depth-`n` cylinder exactly when
its first `n` itinerary symbols agree with `omega`. Hence

\[
j(\iota^{-1}(\omega))=\bigcap_n C_\omega(n).
\]

The archive's compact directed-intersection theorem makes the right side
connected. The inclusion is a topological embedding, so the entire itinerary
fiber is connected. Existing compact binary coding realizes every address,
which also proves nonemptiness. Conversely a connected component has a
constant itinerary because binary sequence space is totally disconnected.
The two containments identify the fiber with the component exactly.

**5. Descend and retain the physical map.** The existing continuous component
coding is now injective as well as surjective. A compact-to-Hausdorff
continuous bijection is a homeomorphism. The equality between its induced
step and `quadraticComponentMap` is proved on every component representative;
that map was defined directly from the genuine polynomial and contains no
choice of symbolic labeling. This proves the component conjugacy.
The separate `filled_component_image` theorem proves that the actual polynomial
maps each entire component onto its parent component. Thus return of a component
under the quotient action has its literal setwise meaning.

**6. Derive the dynamical consequences.** Restriction to the first `n` symbols
is an explicit equivalence between addresses fixed by `sigma^n` and binary
words of length `n`, whose cardinality is `2^n`. A word with one marked
symbol has minimal period `n`. Every finite prefix has a periodic extension,
so periodic addresses meet every basic open cylinder. Finally, after a shift
has removed a finite prescribed prefix, its remaining tail can be any target
address. This proves eventual surjectivity of every nonempty open set.
Each conclusion is transported through the homeomorphism to actual components;
none is inferred from the older surjective factor alone.

### Reproduction and validation

The repository pins Lean `v4.32.0` and Mathlib `v4.32.0` at commit
`81a5d257c8e410db227a6665ed08f64fea08e997`.

```sh
python -B code/contribute.py check
python -B code/verify_lean_coverage.py
cd formalization/weighted
lake exe cache get
lake build ConnectedBinaryCoding QuadraticComponentConjugacy BinaryShiftPeriodic BinaryShiftExactness QuadraticComponentDynamics
lake build
cd ../..
python -B code/verify_lean_coverage.py --audit weighted
```

Development is in [PR #220](https://github.com/dovvnloading/loops-research-archive/pull/220),
opened as a draft before implementation. The claim and subsequent proof
checkpoints are committed in that PR. All five new modules compile locally
with the pinned Lean/Mathlib project. The full dependency build for
`QuadraticComponentDynamics` completed successfully with 8,679 jobs.
The existing compiled audit, restricted locally to the five new modules,
reported `AXIOM_AUDIT_PASS component_checkpoint: 5 modules, 71 declarations`.
This includes private and generated declarations, not only the named public
theorems. Local contribution, source-registration, and theorem-index checks
also pass. The full repository CI build and audit remain the final acceptance
gate and are recorded in the pull request before it is marked ready.

The permitted logical dependencies are only `propext`, `Classical.choice`,
and `Quot.sound`. The existing CI compiles the full project and audits the
compiled declarations; source scans alone are not treated as validation.

## Dependencies

The one target is `H1_CELL_TREE_EXTRACTION`. Its existing ledger prerequisites
`TREE_NERVE_FULLNESS` and `TOPOLOGY_REPLICATION_NO_GO` are unchanged. Neither is
used to assume an identification of the virtual-molecule carrier.

This packet extends
[the earlier escape-component packet](../quadratic_escape_component_tree_20261126/NOTE.md),
which explicitly left connectedness and uniqueness of itinerary fibers open.
It uses `sublevel_split`, `quadratic_escape_sublevel_compact`,
`quadratic_escape_sublevel_connected_of_critical`, `escape_step`,
`quadratic_filled_compact`, and `quadraticFilledMap`, together with the existing
`CompactBinaryCoding` itinerary and component-factor results.
`LoopsLeastCarrier.directed_carrier_preconnected` supplies the compact
nested-connected-limit theorem. These are compiled repository proofs, not
new research assumptions.

Pinned Mathlib supplies compact-to-Hausdorff embeddings and homeomorphisms,
connected-component quotients, product topology, natural-number periodicity,
and finite cardinal arithmetic. Relevant source files include
`Mathlib/Topology/Connected/TotallyDisconnected.lean`,
`Mathlib/Topology/Constructions.lean`,
`Mathlib/Topology/Homeomorph/Defs.lean`,
`Mathlib/Data/Nat/Periodic.lean`, and
`Mathlib/Dynamics/PeriodicPts/Defs.lean`.

Source registration uses `METADATA`; it does not promote an existing
model-to-physical bridge or alter a canonical ledger status.

## Boundary

The component quotient is identified with binary sequence space. This packet
does not prove that every component is a singleton, that cylinder diameters
shrink, or that the filled set itself is conjugate to the shift. The periodic
objects counted are components; existence or uniqueness of periodic points
inside those components is not inferred. Topological exactness concerns the
component quotient, not a uniform analytic expansion or distortion bound.

The escape sublevels and their components are not identified with the
source-defined virtual-molecule Cantor carrier, small-Julia atoms, gates,
access markings, or protected return system. Universal atomic incidence,
gate incidence, and compatibility with that source system remain open.
Thus `H1_CELL_TREE_EXTRACTION` remains open; no status change is proposed.
H1-H4, UPTCR, and MLC remain open, and no new MLC case is asserted.

## Attribution

This builds on Matthew Robert Wesney's archive and its existing Lean proofs
of quadratic escape potentials, full sublevels, physical inverse branches,
and binary coding, as well as Mathlib's topology and dynamics library.
The mathematical setting belongs to classical polynomial dynamics developed
by Fatou, Julia, Douady, Hubbard, and their successors. The contribution
advances the archive's formalization; it makes no worldwide priority claim.

OpenAI ChatGPT, GPT-6 Astra Pro assisted with proof design, independent
hypothesis review, implementation, and compiler-directed repair. No human
specialist review has been performed. The contribution follows the
repository's CC0 terms; cited mathematicians and tool providers are not
represented as reviewers or endorsers.
