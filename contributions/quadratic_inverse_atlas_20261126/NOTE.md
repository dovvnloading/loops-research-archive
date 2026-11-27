---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-inverse-atlas-20261126"></a>

# Complete local quadratic inverse atlases and actual-cylinder transport

## Claim

For the actual quadratic map \(f_c(z)=z^2+c\), construct and coordinate all inverse branches of each finite iterate over a regular simply connected target. The branches exhaust the full physical pullback components, are compatible with changes of anchor, clock splitting, and regular target enlargement, and determine all continuous lifts from a nonempty preconnected source. A second construction continues every root of one regular fiber simultaneously in both parameter and target, with a complete root census on a common closed target disk and compact, pairwise disjoint component closures over its interior.

This is a partial result toward `VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION`. It constructs a complete family of actual components; identifying that family with the native authorized marked cylinders remains a separate obligation.

Write \(F_{c,n}=f_c^{\circ n}\), including \(F_{c,0}=\mathrm{id}\), and

\[
 C_{c,n}(V,a)=\operatorname{Comp}_a(F_{c,n}^{-1}(V)).
\]

This is the full ambient connected component, represented in Lean by `connectedComponentIn`; it is not an assumed or prescribed source domain. The finite regularity condition on a target is

\[
 F_{c,k}(c)\notin V\qquad(0\leq k<n).
\]

### 1. Complete static analytic atlas

Suppose \(V\subset\mathbb C\) is open and simply connected, satisfies that regularity condition, and \(y\in V\). For each actual root \(a\in I_{c,n,y}:=\{a:F_{c,n}(a)=y\}\), define `inverseBranch c n V a` by `Function.invFunOn` on \(C_{c,n}(V,a)\). Only its restriction to \(V\) is used. The new theorems prove:

- This restriction is analytic, conformal, and a two-sided inverse of \(F_{c,n}\) on the entire component. Its image equals that component.
- Its derivative is \(b_a'(w)=1/F_{c,n}'(b_a(w))\) throughout \(V\).
- The actual fiber \(I_{c,n,y}\) is in bijection with the connected components of the full preimage \(F_{c,n}^{-1}(V)\). Both have cardinality \(2^n\).
- The branch ranges are pairwise disjoint and their union is the full preimage. For every \(w\in V\) and \(z\in\mathbb C\), \(F_{c,n}(z)=w\) holds exactly when a unique \(a\in I_{c,n,y}\) satisfies \(b_a(w)=z\).
- Changing the target anchor transports actual fibers by an equivalence. These transports satisfy identity and composition laws, and rebasing a branch preserves its entire restriction to \(V\).

The explicit equivalence `fiberComponentEquiv` and the theorems `inverseBranch_fiber_exhaustion`, `inverseBranch_ranges_cover`, `inverseBranch_reanchor`, and `fiberTransport_trans` record these assertions. No branch maps, selected source domains, or component exhaustion are supplied as inputs.

### 2. Classification of entire continuous lifts

Let \(X\) be any preconnected topological space, choose \(x_0\in X\), and let \(\gamma:X\to V\) be continuous. Evaluation at \(x_0\) is a bijection

\[
 \{\Gamma:X\to\mathbb C\text{ continuous}:F_{c,n}\circ\Gamma=\gamma\}
 \simeq I_{c,n,\gamma(x_0)}.
\]

Thus there are exactly \(2^n\) complete continuous lifts. A chosen inverse point determines one unique lift, given everywhere by the corresponding analytic branch composed with \(\gamma\). Distinct lifts differ at every source point. No local path connectivity or simple connectivity of \(X\) is assumed; its preconnectedness and the chosen point are the source hypotheses. The result applies in particular to paths.

The equivalence is `liftFiberEquiv`. Existence, uniqueness, cardinality, and pointwise separation are proved by `continuous_map_lift_exists_unique`, `liftAnchor_bijective`, `continuous_lifts_card`, and `continuous_lifts_pointwise_distinct`.

### 3. Actual component and clock compatibility

For \(F_{c,p+q}(a)\in V\), clock splitting gives

\[
 C_{c,p}(C_{c,q}(V,F_{c,p}(a)),a)=C_{c,p+q}(V,a).
\]

For open \(V\), the prefix image is the entire residual component:

\[
 F_{c,p}(C_{c,p+q}(V,a))=C_{c,q}(V,F_{c,p}(a)).
\]

Under the regular simply connected hypotheses at depth \(p+q\), the inverse branches satisfy the corresponding prefix identity and exact concatenation through that constructed intermediate component. These are `inverseComponent_split`, `inverseComponent_prefix_image`, `inverseBranch_prefix`, and `inverseBranch_concatenation`.

For nested open simply connected targets \(V\subset W\), with \(W\) regular through depth \(n\) and \(F_{c,n}(a)\in V\), enlargement preserves the branch on \(V\), and

\[
 C_{c,n}(W,a)\cap F_{c,n}^{-1}(V)=C_{c,n}(V,a).
\]

These are `inverseBranch_target_restriction` and `inverseComponent_target_restriction`. The hypotheses exclude merger of old sheets inside the enlarged regular simply connected target.

Same-clock transport is separate from residual-clock splitting. Retain that \(V\) is open, simply connected, and regular through depth \(n\), with \(F_{c,n}(a)\in V\). If \(F_{c,j}(V)\subset W\), connectedness forces

\[
 F_{c,j}(b_{V,a}(V))\subset C_{c,n}(W,F_{c,j}(a)).
\]

The target-component containment is derived from base-image containment and one actual anchor. It is not assumed. This containment theorem does not require regularity or simple connectivity of \(W\). If \(W\) is also open, simply connected, and regular through the same depth \(n\), it yields

\[
 F_{c,j}\circ b_{V,a}
   =b_{W,F_{c,j}(a)}\circ F_{c,j}\quad\text{on }V.
\]

If the base image equals \(W\), the reached image equals the entire selected target component. These are `inverseBranch_reached_component`, `inverseBranch_commuting_lift`, and `inverseComponent_commuting_image`. Both cylinder maps use depth \(n\); the intermediate iterate uses \(j\). The residual depth \(q\) in a split clock \(p+q\) is treated separately.

### 4. One common parameter atlas from a single regular fiber

The main theorem `quadratic_parameter_inverse_atlas` assumes only \(c,y\in\mathbb C\), \(n\in\mathbb N\), and

\[
 F_{c,k}(c)\ne y\qquad(0\leq k<n).
\]

It constructs \(\varepsilon,\delta>0\) and functions \(g_a(d,w)\), indexed by the actual base roots \(a\in I_{c,n,y}\), with all of the following properties on the same neighborhoods:

1. \(g_a(c,y)=a\).
2. Each \(g_a\) is jointly complex analytic on neighborhoods of every point of \(B(c,\varepsilon)\times\overline B(y,\delta)\).
3. For every \(d\in B(c,\varepsilon)\), \(w\in\overline B(y,\delta)\), and \(z\in\mathbb C\),

   \[
   F_{d,n}(z)=w\quad\Longleftrightarrow\quad
       \exists!\,a\in I_{c,n,y},\ g_a(d,w)=z.
   \]

4. The image over the open target disk is the full actual pullback component:

   \[
   g_a(d,B(y,\delta))=C_{d,n}(B(y,\delta),g_a(d,y)).
   \]

   Its closure is compact, and \(F_{d,n}\) is injective on that closure.
5. The closures of distinct branch images are pairwise disjoint.
6. Every nearby parameter satisfies \(F_{d,k}(d)\notin\overline B(y,\delta)\) for all \(k<n\).
7. Throughout the closed target disk, every inverse derivative is \(1/F_{d,n}'(g_a(d,w))\), and every branch is conformal.

Items 4–7 hold for every \(d\) in the open parameter ball. Closure disjointness is asserted at each fixed parameter, and conformality is in the target variable \(w\). These are simultaneous existence conclusions. The theorem assumes no moving inverse family, source-component family, exhaustive nearby root list, or persistence of postcritical exclusion. Closed-disk analyticity includes neighborhoods across the target boundary. The component identity concerns the interior open disk.

### 5. A formal boundary obstruction

`punctured_plane_component_obstruction` treats the actual map at \(c=0\). Its private helper `zero_parameter_iterate` and local proof establish, at every depth,

\[
 F_{0,n}(z)=z^{2^n},\qquad
 F_{0,n}^{-1}(\mathbb C\setminus\{0\})=\mathbb C\setminus\{0\}.
\]

The public obstruction theorem exports that the punctured plane is open and connected and avoids all relevant postcritical values, its pullback has exactly one connected component, and the fiber over \(1\) has exactly \(2^n\) points. `punctured_plane_component_count_ne_degree` proves the failure of the component-count conclusion for every \(n>0\). Consequently, simple connectivity cannot be dropped from the static theorem in general. This does not claim that every nonsimply connected target fails or that no alternative univalence hypothesis can replace it.

## Evidence

The contribution registers 43 public theorems in four modules:

| Module | Public theorems | Main content |
| --- | ---: | --- |
| [QuadraticRegularInverse.lean](../../formalization/weighted/QuadraticRegularInverse.lean) | 14 | Canonical actual-component inverse and general continuous lift uniqueness |
| [QuadraticInverseBranches.lean](../../formalization/weighted/QuadraticInverseBranches.lean) | 17 | Exhaustive atlas, component and lift equivalences, reanchoring, explicit obstruction |
| [QuadraticInverseTransport.lean](../../formalization/weighted/QuadraticInverseTransport.lean) | 10 | Clock splitting, enlargement, equal-depth reached-component transport |
| [QuadraticParameterAtlas.lean](../../formalization/weighted/QuadraticParameterAtlas.lean) | 2 | Critical-visit exclusion and the complete common parameter atlas |

Proof status at this draft checkpoint: all four modules and all 43 public theorems have compiled locally without diagnostics. The repository's transitive audit also passed all 75 declarations in the four modules, including private and generated declarations, with only `propext`, `Classical.choice`, and `Quot.sound` permitted. The unchanged full CI build and dependency audit remain the acceptance gate; the final evidence record will identify the exact proof commit and successful CI run.

The pinned versions are Lean `v4.32.0` and Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. Local compilation used a selective dependency cache and temporarily narrowed import headers in six existing ancestors to fit the workspace. All six original headers were restored; no ancestor proof, dependency pin, audit rule, or workflow was changed. Full CI validates the committed project with its original imports.

### Proof architecture

For the static atlas, the earlier component-ramification theorem supplies injectivity of the actual iterate on each actual component. The global component-image theorem supplies surjectivity. The existing analytic inverse theorem constructs an analytic inverse, and injectivity identifies it with the canonical `invFunOn` function. Connectedness forces every continuous lift into its anchor's component. A regular fiber intersects each component in exactly one point, giving the explicit equivalence and exact component count. Applying this classification to continuous maps gives the equivalence of whole lift spaces with one actual fiber.

For the parameter theorem, regularity of the terminal value first excludes every preterminal encounter with zero along every inverse orbit (`inverseFiber_no_critical_visits`). The exact fiber census makes the base fiber finite of size \(2^n\). Finite Hausdorff separation gives pairwise disjoint open source neighborhoods around its roots. Apply the archive's compact parameter inverse-family theorem separately to each singleton root inside its own source neighborhood. Finite intersections give common parameter and target neighborhoods; choose a smaller target disk whose closure remains inside every local inverse chart.

All branches stay in separated source neighborhoods, so their values are distinct for every nearby parameter and every point of the closed target disk. They provide \(2^n\) actual inverse points. The exact polynomial-degree census therefore excludes every additional inverse point anywhere in \(\mathbb C\). Equality in the critical-fiber census proves that no nearby postcritical value lies in the closed target disk. The open-component recognition theorem identifies each analytic image with its entire ambient pullback component and puts its compact closure inside the corresponding separated source neighborhood. This proves closure disjointness and injectivity on closures. The local inverse theorem supplies joint analyticity and the derivative formulas.

The obstruction uses the exact power formula at \(c=0\), connectedness of the complex punctured plane, and the regular-fiber census. It is an exact theorem without numerical approximation.

## Dependencies

The ledger prerequisites are `DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`, `FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS`, and `INTERIOR_PULLBACK_COMPONENT_FORCING`. The source-facing statement is [finite-cylinder commuting lift, sections 4–5](../../research/mlc_unified/finite_cylinder_commuting_lift.md).

The formal proof builds on these existing archive results:

- [QuadraticCylinderRamification.lean](../../formalization/weighted/QuadraticCylinderRamification.lean): `quadratic_iterate_univalent_component`, `quadratic_global_component_image`, and `quadratic_prefix_component_image`.
- [QuadraticCriticalFiberCensus.lean](../../formalization/weighted/QuadraticCriticalFiberCensus.lean): `globalFiber_full_card_iff` and `globalFiber_card_exact`.
- [QuadraticCylinderCensus.lean](../../formalization/weighted/QuadraticCylinderCensus.lean): `quadratic_full_degree_census`.
- [TelescopeConformalInverse.lean](../../formalization/weighted/TelescopeConformalInverse.lean): `orbit_conformal_inverse`, `orbit_inverse_restriction_agreement`, and `orbit_inverse_concatenation`.
- [QuadraticParameterInverse.lean](../../formalization/weighted/QuadraticParameterInverse.lean): `quadratic_compact_parameter_inverse_family`.
- [QuadraticInverseOpen.lean](../../formalization/weighted/QuadraticInverseOpen.lean): `quadratic_inverse_open_component`.

Earlier work reviewed includes the [single-fiber exhaustion](../cylinder_fiber_exhaustion_20261126/NOTE.md), [critical-fiber census](../critical_fiber_census_20261126/NOTE.md), [critical-window obstruction](../quadratic_critical_window_20261126/NOTE.md), [cylinder ramification](../quadratic_cylinder_ramification_20261126/NOTE.md), and [component fiber degree](../quadratic_component_fiber_degree_20261126/NOTE.md) packets. The last already gives component degree and an enlargement test without simple connectivity. The present work uses stronger regular target geometry to construct a coordinated analytic atlas and common parameter family; it does not replace that more general ramified component theory.

Mathlib supplies connected-component quotients, elementary complex topology, finite-type and cardinality infrastructure, and analytic and derivative interfaces. All mathematics used in the new proof scripts is imported and checked inside the pinned Lean project.

## Boundary

The ledger row remains open. In particular:

- The static construction requires an actual open simply connected target and exclusion of its first \(n\) postcritical values. It does not prove that every demanded native virtual stage supplies this geometry.
- Labels are actual inverse points and actual connected components. The proofs do not identify them with authorized marked words, choose between target bases, or establish cross-base ownership.
- No native obstacle, access, prime-end, collar, localization, or ordered critical-chronology metadata is reconstructed. Actual component and branch identities do not supply those identifications.
- The parameter neighborhood and target disk depend on the fixed finite data \((c,n,y)\) and source separation. There is no uniform radius over increasing depths, near-critical limits, or native stages, and no global continuation in parameter space.
- Enlargement requires the larger target to remain regular and simply connected. The proof does not establish those hypotheses for every native enlargement.

No MLC, H1–H4, UPTCR, or full native reached-cylinder exhaustion conclusion is claimed. This contribution extends the repository's formally checked construction and compatibility results; it makes no priority claim over classical complex dynamics or the literature.

## Attribution

Builds on the archive's actual quadratic component, census, ramification, parameter-inverse, and open-component proofs and on Mathlib. Proof development, compiler repair, and independent scope review were performed by AI agents. Human review: none. The contribution is released under the repository's CC0 terms.
