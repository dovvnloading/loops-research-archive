import Mathlib

/-!
# Paper 3: the algebraic attachment-defect ledger

Source: `papers/paper3_protected_carriers/extracted/G_separation/separation_budget.tex`,
Theorem `separation-budget`, equations `G-attachment-exact` and
`G-step-ledger`.

This file checks the *finite-dimensional linear-algebra implication*
of TWO consecutive short exact sequences:

  0 → H̃⁰(T) → H¹(B_new) → ker(r) → 0,
  0 → ker(r) → H¹(B_old) → H¹(T) → 0.

The maps, exactness, finite dimensionality, and the comparison of H̃⁰(T)
with (number of connected components - 1) are HYPOTHESES, not derived
from planar compacta. In the paper they require compact-pair Čech
Mayer–Vietoris, Alexander duality and the physical attachment hypotheses.
The rational vector spaces here model finite rank after rationalization;
there is no unproved automatic identification with actual Čech groups.

A key consequence is the *negative* trace correction term. In particular,
one connected but separating attachment trace can reduce separation.
A naive monotone "number of holes can only increase" rule is not valid.
There are no axioms, proof holes or external solvers in this module.
-/

namespace LoopsFormal.AttachmentLedger

/-- Rank additivity of a genuine short exact sequence of finite-dimensional
rational vector spaces. Both injectivity and surjectivity are checked as
hypotheses; exactness is equality of the actual range and kernel. -/
theorem short_exact_finrank
    {U V W : Type*}
    [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (i : U →ₗ[ℚ] V) (r : V →ₗ[ℚ] W)
    (hi : Function.Injective i) (hr : Function.Surjective r)
    (hexact : i.range = r.ker) :
    Module.finrank ℚ V = Module.finrank ℚ U + Module.finrank ℚ W := by
  have hkernel : i.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
  have hrange : r.range = ⊤ := LinearMap.range_eq_top.mpr hr
  have hleft0 := LinearMap.finrank_range_add_finrank_ker i
  rw [hkernel] at hleft0
  simp at hleft0
  have hleft : Module.finrank ℚ (↥i.range) = Module.finrank ℚ U := hleft0
  have hright0 := LinearMap.finrank_range_add_finrank_ker r
  rw [hrange] at hright0
  simp at hright0
  have hright :
      Module.finrank ℚ W + Module.finrank ℚ (↥r.ker) =
        Module.finrank ℚ V := hright0
  rw [← hexact, hleft] at hright
  omega

/-- The two actual short exact sequences from Paper 3's bookkeeping.
`Contact` is the rationalized reduced H⁰ of the attachment trace;
`Defect` is ker(r); `Old` and `New` are rationalized H¹ groups.
Constructing these maps from planar compacta is NOT proved here. -/
theorem attachment_balance
    {Contact New Defect Old Trace : Type*}
    [AddCommGroup Contact] [Module ℚ Contact] [FiniteDimensional ℚ Contact]
    [AddCommGroup New] [Module ℚ New] [FiniteDimensional ℚ New]
    [AddCommGroup Defect] [Module ℚ Defect] [FiniteDimensional ℚ Defect]
    [AddCommGroup Old] [Module ℚ Old] [FiniteDimensional ℚ Old]
    [AddCommGroup Trace] [Module ℚ Trace] [FiniteDimensional ℚ Trace]
    (connecting : Contact →ₗ[ℚ] New)
    (projection : New →ₗ[ℚ] Defect)
    (inclusion : Defect →ₗ[ℚ] Old)
    (restriction : Old →ₗ[ℚ] Trace)
    (hconnect : Function.Injective connecting)
    (hproject : Function.Surjective projection)
    (hexactNew : connecting.range = projection.ker)
    (hinclude : Function.Injective inclusion)
    (hrestrict : Function.Surjective restriction)
    (hexactOld : inclusion.range = restriction.ker) :
    Module.finrank ℚ New + Module.finrank ℚ Trace =
      Module.finrank ℚ Old + Module.finrank ℚ Contact := by
  have hnew := short_exact_finrank connecting projection
    hconnect hproject hexactNew
  have hold := short_exact_finrank inclusion restriction
    hinclude hrestrict hexactOld
  omega

/-- A trace cannot have more rational cohomological rank than the old
connector when the actual restriction map is surjective. -/
theorem trace_rank_le_old
    {Old Trace : Type*}
    [AddCommGroup Old] [Module ℚ Old] [FiniteDimensional ℚ Old]
    [AddCommGroup Trace] [Module ℚ Trace] [FiniteDimensional ℚ Trace]
    (restriction : Old →ₗ[ℚ] Trace)
    (hrestrict : Function.Surjective restriction) :
    Module.finrank ℚ Trace ≤ Module.finrank ℚ Old := by
  have hrange : restriction.range = ⊤ :=
    LinearMap.range_eq_top.mpr hrestrict
  have h := LinearMap.finrank_range_add_finrank_ker restriction
  rw [hrange] at h
  simp at h
  omega

/-- The *subtraction-free* exact contact ledger. The extra hypothesis
`finrank Contact + 1 = components` represents the degree-zero Čech
component-count theorem under the finite-component assumption. -/
theorem attachment_component_balance
    {Contact New Defect Old Trace : Type*}
    [AddCommGroup Contact] [Module ℚ Contact] [FiniteDimensional ℚ Contact]
    [AddCommGroup New] [Module ℚ New] [FiniteDimensional ℚ New]
    [AddCommGroup Defect] [Module ℚ Defect] [FiniteDimensional ℚ Defect]
    [AddCommGroup Old] [Module ℚ Old] [FiniteDimensional ℚ Old]
    [AddCommGroup Trace] [Module ℚ Trace] [FiniteDimensional ℚ Trace]
    (connecting : Contact →ₗ[ℚ] New)
    (projection : New →ₗ[ℚ] Defect)
    (inclusion : Defect →ₗ[ℚ] Old)
    (restriction : Old →ₗ[ℚ] Trace)
    (hconnect : Function.Injective connecting)
    (hproject : Function.Surjective projection)
    (hexactNew : connecting.range = projection.ker)
    (hinclude : Function.Injective inclusion)
    (hrestrict : Function.Surjective restriction)
    (hexactOld : inclusion.range = restriction.ker)
    (components : ℕ)
    (hcomponents : Module.finrank ℚ Contact + 1 = components) :
    Module.finrank ℚ New + Module.finrank ℚ Trace + 1 =
      Module.finrank ℚ Old + components := by
  have h := attachment_balance connecting projection inclusion restriction
    hconnect hproject hexactNew hinclude hrestrict hexactOld
  omega

/-- Under the same precise assumptions the conventional natural-number
subtraction form of Paper 3's formula is justified (with no truncation
artifact). This proves the correction `-σ(T)`, not just a positive term. -/
theorem attachment_defect_formula
    {Contact New Defect Old Trace : Type*}
    [AddCommGroup Contact] [Module ℚ Contact] [FiniteDimensional ℚ Contact]
    [AddCommGroup New] [Module ℚ New] [FiniteDimensional ℚ New]
    [AddCommGroup Defect] [Module ℚ Defect] [FiniteDimensional ℚ Defect]
    [AddCommGroup Old] [Module ℚ Old] [FiniteDimensional ℚ Old]
    [AddCommGroup Trace] [Module ℚ Trace] [FiniteDimensional ℚ Trace]
    (connecting : Contact →ₗ[ℚ] New)
    (projection : New →ₗ[ℚ] Defect)
    (inclusion : Defect →ₗ[ℚ] Old)
    (restriction : Old →ₗ[ℚ] Trace)
    (hconnect : Function.Injective connecting)
    (hproject : Function.Surjective projection)
    (hexactNew : connecting.range = projection.ker)
    (hinclude : Function.Injective inclusion)
    (hrestrict : Function.Surjective restriction)
    (hexactOld : inclusion.range = restriction.ker)
    (components : ℕ)
    (hcomponents : Module.finrank ℚ Contact + 1 = components) :
    Module.finrank ℚ New =
      Module.finrank ℚ Old + components - 1 - Module.finrank ℚ Trace := by
  have hbal := attachment_component_balance connecting projection
    inclusion restriction hconnect hproject hexactNew hinclude
    hrestrict hexactOld components hcomponents
  have hle := trace_rank_le_old restriction hrestrict
  omega

/-- A *connected* trace has reduced H⁰-rank zero. If it also has
positive H¹-rank, the two exact sequences FORCE a strict loss of holes.
This is a formal obstruction to the false monotonicity shortcut. -/
theorem connected_separating_trace_forces_strict_drop
    {Contact New Defect Old Trace : Type*}
    [AddCommGroup Contact] [Module ℚ Contact] [FiniteDimensional ℚ Contact]
    [AddCommGroup New] [Module ℚ New] [FiniteDimensional ℚ New]
    [AddCommGroup Defect] [Module ℚ Defect] [FiniteDimensional ℚ Defect]
    [AddCommGroup Old] [Module ℚ Old] [FiniteDimensional ℚ Old]
    [AddCommGroup Trace] [Module ℚ Trace] [FiniteDimensional ℚ Trace]
    (connecting : Contact →ₗ[ℚ] New)
    (projection : New →ₗ[ℚ] Defect)
    (inclusion : Defect →ₗ[ℚ] Old)
    (restriction : Old →ₗ[ℚ] Trace)
    (hconnect : Function.Injective connecting)
    (hproject : Function.Surjective projection)
    (hexactNew : connecting.range = projection.ker)
    (hinclude : Function.Injective inclusion)
    (hrestrict : Function.Surjective restriction)
    (hexactOld : inclusion.range = restriction.ker)
    (hconnected : Module.finrank ℚ Contact = 0)
    (hseparating : 0 < Module.finrank ℚ Trace) :
    Module.finrank ℚ New < Module.finrank ℚ Old := by
  have hbal := attachment_balance connecting projection inclusion restriction
    hconnect hproject hexactNew hinclude hrestrict hexactOld
  omega

/-- An arithmetic stress test, not a geometric construction: the
rank counts from the annulus-plus-disk example satisfy the exact ledger,
but violate any proposed nondecreasing-hole-count rule. -/
theorem finite_rank_monotonicity_counterexample :
    (0 : ℕ) + 1 + 1 = 1 + 1 ∧ ¬ ((1 : ℕ) ≤ 0) := by
  decide

#print axioms short_exact_finrank
#print axioms attachment_balance
#print axioms attachment_component_balance
#print axioms attachment_defect_formula
#print axioms connected_separating_trace_forces_strict_drop

end LoopsFormal.AttachmentLedger
