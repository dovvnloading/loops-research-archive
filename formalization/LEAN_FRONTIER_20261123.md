# Lean frontier: canonical sheet kernels and protected-carrier audits

**Subsequent proof at the planar-fill interface.** The [planar realization](PHYSICAL_BRIDGES.md#planar-fill) constructs the filled hull on the complex plane, proves compactness for compact inputs, and specializes the finite-packet theorem. The [current proof index](PHYSICAL_BRIDGES.md) also links the verified period-27 sign and order results. The rankings below describe their stated base revision.

**Repository snapshot:** `main` commit `4840f628c25ef7a3ae91686ddf5ffb57dc0548b4` (2026-11-23).
**Toolchain:** Lean 4.32.0; Mathlib v4.32.0 via `formalization/weighted/`.
**Status discipline:** "Not formalized" below means **not identified in the
repository's existing 60 Lean files**. It is *not* a verified claim that nobody
anywhere has ever proved the mathematical result in Lean. Classical theorems
are not new just because the Lean transcription is new.

## Newly introduced kernel statements

The main branch already has 60 Lean files. In particular the period-27
real-root existence/uniqueness and exact period are proved in
`formalization/weighted/Period27Real{Center,Uniqueness,ExactPeriod}.lean`.
The full delayed-clone complex spectral gap is in
`formalization/weighted/FullCloneStrictGap.lean`. These should not be
misclassified as open Lean opportunities merely because older commentary
in `RESEARCH_MAP.md` still mentions a pre-bridge status.

1. **`LocalizationSheetKernel.lean`** extracts a reusable, group-theoretic
   form of Paper 1's canonical sheet resolution (D-resolution, Theorems
   `sheet-resolution` and `unique-intermediate`). It uses genuinely
   nonnormal subgroup cosets, *not* quotient groups. It proves canonical
   coarsening, exact kernel equivalence, a defect-element collision witness,
   injectivity iff source and pullback subgroups match, injectivity of the
   resolved target leg and equality/uniqueness of intermediate subgroups
   determined by sheet kernels. The group-theoretic interface is
   parameterized over any group homomorphism `φ`, and does not postulate
   existence of a physical peripheral loop.

2. **`ProtectedCarrierLogic.lean`** extracts Paper 3's fixed-packet
   fullification and finite negative-certificate framework (sections
   `E-audit`, `B-no-least`). Every extensive, monotone, idempotent
   fullifier satisfies absorption, repeated completion equals one-shot
   completion, and arbitrary list permutations preserve the result. The
   same module proves persistent merger, localization escape, and
   blocked-port certificates, intersections of closed/fixed hulls,
   and a generic two-carrier no-least theorem with a finite diamond
   path-skeleton countermodel.

The above are **mathematical algebra/order-theory cores**, not proofs of all
geometric content of Papers 1 or 3. In particular the diamond graph is not
a plane continuum, and a `Fullifier` is an *assumed* closure operator;
the physical planar full-hull construction is not yet supplied.

## Ranked next opportunities

| Priority | Precise missing Lean theorem / interface | Benefit and important prerequisites | Status |
|---|---|---|---|
| **1: High** | **Actual planar fullification** for compact sets in `ℂ`: define filling by adjoining bounded complementary components and prove extensivity, monotonicity and idempotence, then instantiate `Fullifier ℂ`. | Promotes Paper 3 packet-completion identities from abstract closure algebra to the genuine geometric operation. Requires robust plane-complement components, compactness, and separation results; **not** completed by this PR. | Open interface |
| **2: High** | **Physical sheet/coset bridge**: given connected based covers, an embedding `a`, a lift `A`, and a proved correspondence between fibers and subgroup cosets, identify the geometric fiber collision with `LocalizationSheetKernel.original_defect_collision`. Formalize the covering-classification and endpoint-lift criterion. | Upgrades Paper 1's algebraic factorization to its full topological assertion without silently converting an immersion into an embedding; actual KL peripheral-loop construction is a separate, complex-dynamics goal. | Algebra core supplied; topological bridge open |
| **3: High** | **Paper 3 attachment defect ledger**: under explicit compact-pair Čech Mayer–Vietoris/Alexander duality hypotheses, prove its short exact sequence and finite-rank identity `σ(Bᵢ)=σ(Bᵢ₋₁)+c(Tᵢ)-1-σ(Tᵢ)`. | The correction term `-σ(Tᵢ)` is essential; this would rigorously protect the program against a false monotone-hole-count rule. An abstract short-exact-sequence rank lemma is a tractable intermediate step; full Čech cohomology is substantially deeper. | Unformalized in archive |
| **4: High** | **Paper 3 protected free-component criterion** (same frozen forbidden inventory, singleton ports to every atom) and persistence of *geometric* separators; formalize the finite ribbon-routing certificate and its realization. | Would directly connect discrete audits to actual protected plane continua. Requires planar topology, arcs, local path connectivity of the free domain, and prime-end-safe access conventions. | Only certificate logic supplied |
| **5: High** | **Canonical physical marking hypothesis M / KKL wave interface**, proving the actual slit-side prime-end census and compatibility of covering `f_*` versus immersion `ι^*`, then inequalities for the actual extremal width rather than an auxiliary round annulus. | Central unresolved bottleneck of the 2026-11 tip-family program, with real impact on validation. Existing `NativeWaveGate.lean` handles finite arithmetic but not analytic physical identification. KKL’s analytic theorems are imported in the source and would need formal interfaces and/or proofs. | Open analytic interface |
| **6: Medium** | **All-period `p≥13` selected real primitive-tip realization**: transfer the published signed-chart estimates and strict orbit order to genuine real/complex Lean claims, with a distinguished chart parameter and direct proper-degree-two returns. | Extends the excellent period-27 and finite discrete formalization to an infinite selected family; technically demanding real/complex interval bounds. Does not imply maximal-window uniqueness. | No such all-period kernel proof identified |
| **7: Medium** | **Paper 2 rooted-end compactification**: topology of the direct-decoration inverse-limit/end model and continuity of its shift or extension, then a source-level link to the existing phase/memory Lean modules. | Ensures the algebraic phase/finite-memory checks correspond to actual compactified topological states rather than just symbolic clocks. | Topological realization open |
| **8: Research-level** | **Nested-envelope full-carrier limit theorem and Hausdorff defect birth** from Paper 3. | Closes the finite-to-infinite stability boundary needed for coherent protected carriers. Existing finite closure lemmas do not assert connectedness of intersections or preservation of protected prime-end collars. | Open Lean target; mathematical hypotheses must remain explicit |

### Do *not* silently promote to a theorem

The README and `RESEARCH_MAP.md` explicitly leave H1 (marked construction),
H2 (calibration), H3 (coercivity), H4 (rigidity), universal protected-tower
closure, and MLC open. A Lean implication with one of those as a hypothesis
does **not** settle it. A physical ray landing, holomorphic proper map, or
KKL extremal-width inequality cannot be obtained just from a finite word,
integer incidence table, graph model or abstract packet-closure structure.

This frontier document is an **internal repository coverage audit**, not an
assertion of worldwide originality or a claim that Mathlib lacks every
ingredient. The group/coset and order-theory tools may already have more
general analogues in Mathlib; the contribution here is the *project-specific*
theorem statements, exact logical factorization and connection to its source.
