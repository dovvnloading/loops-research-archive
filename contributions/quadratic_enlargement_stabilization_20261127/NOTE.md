---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-enlargement-stabilization-20261127"></a>

# Eventual naturality for increasing actual quadratic targets

Ledger statement being addressed:

> After an actual target base is typed or uniquely selected, every demanded finite-cylinder branch image has the open pullback component forced by INTERIOR_PULLBACK_COMPONENT_FORCING, and that reached localized component, or the globally identical component justified by the Jordan-disk component lemma, is one of the declared equal-depth target cylinders at every proof-used intermediate iterate with complete metadata and enlargement stability.

## Claim

For every actual quadratic polynomial \(f_c(z)=z^2+c\), every finite iterate horizon \(H\), and every increasing sequence \(U_0\subseteq U_1\subseteq\cdots\) of nonempty connected open subsets of \(\mathbb C\), there is one stage after which all actual pullback-component addresses through depth \(H\) agree with their addresses over the entire union. The stage is uniform across every component, every point of every later target, and every depth through \(H\). The same eventual naturality holds for actual prefix images, intrinsic reflection ranks, and every distinct-point inverse fiber, including fibers over critical values.

There is no uniform bound on that stage, even for the fixed polynomial \(z^2\), depth one, a fixed regular target value, and strictly increasing disks with compact closures inside the next disk, the same initial disk, and the same bounded limiting disk.

This is partial progress on the named ledger obligation. It does not identify the actual components with the source's authorized virtual-cylinder family or construct its marked metadata. No ledger closure is requested.

## Evidence

### 1. Exact geometric theorem

Write
\[
U_\infty=\bigcup_{m\ge0}U_m,\qquad
C_{k,m}(x)=\operatorname{cc}_x(f_c^{-k}(U_m)),
\quad
C_{k,\infty}(x)=\operatorname{cc}_x(f_c^{-k}(U_\infty)).
\]
The component is taken in the literal complex-plane inverse image. It is not a declared symbolic cylinder or an abstract finite-tree class.

The main theorem is
\[
\exists N\ \forall m\ge N\ \forall k\le H\
\forall x\in f_c^{-k}(U_m),\qquad
C_{k,\infty}(x)\cap f_c^{-k}(U_m)=C_{k,m}(x).
\tag{1}
\]
The quantification over all stage points is essential. Stabilization of a preselected component alone would not give (1). The targets may have holes; simple connectivity and univalence are not assumed. A common anchor \(y\in U_0\) is supplied in the Lean statements, and it may be postcritical.

The main theorem **quadratic_finite_horizon_component_stabilization** in
[QuadraticEnlargementStabilization.lean](../../formalization/weighted/QuadraticEnlargementStabilization.lean)
proves (1). Its finite-anchor precursor is quadratic_finite_horizon_anchor_stabilization.

Every final component meets the initial anchor fiber because the actual iterate is proper and open and its component maps onto the connected target. Thus the theorem concerns all actual components, including components reached by points which first enter much later in the exhaustion. It neither assumes a whole-domain component census nor substitutes the global degree for a critical fiber's actual cardinality.

### 2. Why an infinite enlargement chain reduces to finitely many witnesses

[IncreasingComponentStabilization.lean](../../formalization/weighted/IncreasingComponentStabilization.lean)
provides the supporting topology.

For increasing open sets \(S_m\) in a locally connected ambient space and an initial anchor \(a\in S_0\),
\[
\operatorname{cc}_a\!\left(\bigcup_m S_m\right)
=\bigcup_m\operatorname{cc}_a(S_m).
\tag{2}
\]
The proof does not assume that the inverse-image sets \(S_m\) are connected. The union of their anchored components is open. To prove it relatively closed in the final component, take a closure point \(z\), choose a finite stage containing \(z\), and use that stage's open component as a neighborhood. It meets an earlier anchored component. Both lie inside the stage indexed by the maximum of the two indices, so \(z\) already belongs to that finite-stage anchored component. Connectedness of the final component gives (2).

Apply (2) to \(S_{k,m}=f_c^{-k}(U_m)\). For each \(k\le H\), take the actual finite inverse fiber
\[
A_k=\{a\in\mathbb C:f_c^k(a)=y\}.
\]
Every pair in \(A_k\) which is connected over \(U_\infty\) is connected at some finite stage. A finite maximum over the pairs and over \(0\le k\le H\) gives one common \(N\). This is finite_family_anchor_relations_stabilize; the single-family and finite-subset forms are also registered.

To upgrade the pair relation to (1), fix an arbitrary old component and choose one anchor in it using the existing component-surjectivity theorem. Every other inverse point over \(y\) in its final component is a pair in the finite census, and therefore already belongs to the old component at stage \(m\ge N\). The old and final component fibers are equal. The existing theorem quadratic_enlargement_no_merger_iff_fiber_eq converts that finite equality into the full geometric intersection identity.

The general component-union and finite-maximum arguments are infrastructure. The new archive-level conclusion is the simultaneous actual-quadratic theorem (1), with its infinite-union quantifier and all-component/all-prefix scope.

### 3. Later stages and actual prefix maps

For every \(r\ge m\ge N\), the final-component sandwich in (1) gives
\[
C_{k,r}(x)\cap f_c^{-k}(U_m)=C_{k,m}(x).
\tag{3}
\]
This is quadratic_finite_horizon_tail_naturality.

For every split \(k+j\le H\), exact prefix transport in the existing archive combines with (1) to give
\[
f_c^j\!\left(C_{k+j,\infty}(x)\right)
\cap f_c^{-k}(U_m)
=
f_c^j\!\left(C_{k+j,m}(x)\right).
\tag{4}
\]
The theorem quadratic_finite_horizon_prefix_naturality proves (4). Here \(j\) is the actual forward iterate and \(k\) is the remaining inverse depth. This is an identity of planar sets and actual polynomial images, not only a commuting diagram of labels.

### 4. Reflection and critical fibers

[QuadraticStableReflection.lean](../../formalization/weighted/QuadraticStableReflection.lean)
first proves that, at positive depth, a pullback component is invariant under \(z\mapsto-z\) exactly when it contains the reflected anchor. The actual iterate is even, so the reflected anchor stays over the old target. Equation (1) therefore preserves the reflection flag at each residual depth. Induction preserves the whole intrinsic reflection rank.

The theorem quadratic_finite_horizon_fiber_and_rank_stabilization then gives, at the same eventual stage,
\[
R(c,U_m,k,x)=R(c,U_\infty,k,x)
\]
and, for every \(z\in U_m\),
\[
\{a\in C_{k,m}(x):f_c^k(a)=z\}
=
\{a\in C_{k,\infty}(x):f_c^k(a)=z\}.
\tag{5}
\]
The second identity is equality of the archive's actual finite root sets. It includes postcritical target values and recurrent critical orbits. No regular-value substitution or generic-parameter hypothesis is introduced.

### 5. Sharpness with fixed initial and final geometry

[QuadraticDelayedMerger.lean](../../formalization/weighted/QuadraticDelayedMerger.lean)
establishes the elementary geometric separation used by the stronger example: the roots \(1,-1\) of \(z^2=1\) lie in different components over the right half-plane. If a preconnected pullback set joined them, its real-part image would pass through zero. But \(\operatorname{Re}(z^2)>0\) forbids \(\operatorname{Re}z=0\). The selected inverse fiber is exactly \(\{1\}\), and over the whole plane it is exactly \(\{1,-1\}\).

[QuadraticDelayedDiskMerger.lean](../../formalization/weighted/QuadraticDelayedDiskMerger.lean)
removes any reliance on repeated domains or an unbounded final target. For each chosen delay \(D\in\mathbb N\), define
\[
r_D(m)=\frac{2m+D+1}{m+2(D+1)},\qquad
U_m^{(D)}=D(1,r_D(m)).
\tag{6}
\]
Lean proves all of the following:

- \(r_D(0)=1/2\), \(r_D(m)>0\), and \(r_D(m)<2\).
- The radii and disks are strictly increasing.
- Every disk closure is compact and contained in the next disk.
- The initial target is always \(D(1,1/2)\), and the union is always \(D(1,2)\).
- The critical value \(0\) enters, and the actual inverse roots first join, precisely when \(m>D+1\).
- The complete selected fiber is \(\{1\}\) for \(m\le D+1\) and \(\{1,-1\}\) afterward.

Before the threshold the target disk lies in the right half-plane. After it, its radius exceeds one, and the real segment \([-1,1]\) joins the two roots inside the actual quadratic inverse image. Algebra shows there are no other roots over \(1\).

Thus the merger can be postponed beyond any proposed stage while preserving the polynomial, iterate depth, regular anchor, initial disk, limiting disk, strict nesting, and compact closure condition. **no_uniform_precompact_disk_stabilization_stage** formalizes that impossibility. A bounded number of possible component mergers does not provide a bound on their time, and a long observed plateau is not a certificate of future stability.

### 6. Validation

The five modules are registered in the existing weighted Lake project, source index, and public-theorem index. No workflow, ledger, status record, checker, or dependency pin is changed.

Validation is performed by the repository's existing Lean 4.32.0 CI. Local Lean is unavailable, and the workspace disk was too full to install it or clone the entire project. The source scan, contribution intake, and theorem-registration checks run unchanged. The weighted workflow builds all default targets and then audits the transitive dependencies of every declaration, allowing only propext, Classical.choice, and Quot.sound.

The first proof checkpoint compiled the increasing-union topology and the half-plane delayed-merger module. CI identified one application mismatch in the reflection proof; the next commit supplied the reflected point explicitly without changing the theorem statement. The four-module proof checkpoint f2b6814d1ae98ff9ce039685930a9a5898b41200 passed [weighted CI run 45961015015](https://github.com/dovvnloading/loops-research-archive/actions/runs/45961015015): 9,056 build jobs and 190 modules / 4,379 declarations audited, with allowed dependencies only. The stronger strict-disk module is added in this checkpoint and awaits the same complete audit; this draft does not count that extension as validated until it passes.

Reproduce from the repository root:

~~~sh
cd formalization/weighted
lake build IncreasingComponentStabilization QuadraticStableReflection QuadraticEnlargementStabilization QuadraticDelayedMerger QuadraticDelayedDiskMerger
cd ../..
python3 -B code/verify_lean_coverage.py --audit weighted
python3 -B code/verify_lean_coverage.py
python3 -B code/contribute.py check
~~~

No numerical experiment is used as proof.

## Dependencies

- Target: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION.
- Source context: DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, and INTERIOR_PULLBACK_COMPONENT_FORCING.
- Existing QuadraticCylinderCensus.lean: actual polynomial openness/properness, component surjectivity, and finite local inverse fibers.
- Existing QuadraticCriticalFiberCensus.lean: the finite actual global inverse fiber, including critical targets.
- Existing QuadraticCylinderRamification.lean: exact actual prefix-component images.
- Existing QuadraticComponentFiberDegree.lean: the critical-value-compatible no-merger criterion, reflection rank, and intrinsic degree interpretation.
- Existing QuadraticEnlargementDegree.lean: the previously archived finite enlargement census and degree conservation.
- Mathlib's connected-component, local connectedness, finite-set, complex-number, convexity, and compact-ball theorems, through the project's pinned Mathlib revision.

Earlier work read includes the packets on single-fiber exhaustion, component fiber degrees, cylinder ramification, and enlargement degree conservation, together with [finite-cylinder commuting lifts](../../research/mlc_unified/finite_cylinder_commuting_lift.md) and the source-facing [residual-clock audit](../../research/independent_audits/virtual-reached-clock_20261126/NOTE.md).

## Boundary

The ledger obligation remains **open**. Equations (1)-(5) settle a new actual-quadratic enlargement theorem after an increasing target sequence has been supplied. They do not construct an authorized virtual-Molecule exhaustion, prove a proof-use-complete source horizon, identify every reached component with an authorized equal-depth cylinder, or provide prime-end/access, collar, sheet, deck-phase, obstacle, or terminal-return metadata.

The stage \(N\) is existential and may depend on the entire exhaustion, parameter, and finite horizon. The proof is not an algorithm that recognizes stabilization from a finite observed prefix. The fixed-disk counterexample rules out a universal stage even when both endpoint targets and the polynomial are fixed.

The statements concern finite iterate horizons and open planar components. They do not assert an all-depth common stage, boundary-impression stabilization, or convergence of marked end fibers. Existing source obstructions involving ramified reached components and univalent authorized cylinder lists remain in force.

No claim is made that H1-H4, UPTCR, or MLC has been proved. The ledger and public status records are unchanged.

## Attribution

Kahn-Lyubich decoration theory supplies the motivating source program; this contribution uses the archive's precise finite-cylinder formulation rather than importing any unformalized geometric conclusion from that source. The cited earlier archive packets supply the actual quadratic component, prefix, fiber, and rank theorems. General topology and algebra are supplied by Mathlib.

The simultaneous infinite-enlargement result and the fixed-initial/fixed-final strict-disk sharpness example are the contribution here. No literature-priority claim is made. The work and proof audit were performed by ChatGPT, GPT-6 Astra Pro; no independent human review has occurred.
