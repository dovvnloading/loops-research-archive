import ThreeReturnParent
import ThreeReturnContraction

/-!
# The topology of the actual ambient p-return domain

The ambient source is the central component of the complete p-return
pullback of the fixed control disk.  Its exact signed fibers and properness
give a punctured covering, and lifting a contraction of the control disk
proves that the whole ambient source is contractible.
-/

namespace ThreeReturnParentTopology

open Set Function Metric
open scoped Topology
open LimitingCrestQuadraticReturn NearTwoShooting NearTwoTip
open QuadraticCrestDividedDifference ThreeReturnCovering ThreeReturnContraction
open ThreeReturnDomain ThreeReturnParent

noncomputable section

/-- The constructed ambient p-return source is contractible under
the same complete-disk collision certificate used to define its sheets. -/
theorem parent_contractible_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0) (hparent : ParentRestriction c p)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 23/20 → ‖w‖ ≤ 23/20 →
      (normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w)) :
    ContractibleSpace (parentSource c p) := by
  let H := normalizedReturn c p
  let W := parentSource c p
  let V : Set ℂ := ball 0 (23/20)
  have hproper := normalized_return_proper c p hd
  have hopen := normalized_return_open c p hd
  have hnorm {z : ℂ} (hz : z ∈ W) : ‖z‖ ≤ 23/20 := by
    have h : ‖z‖ < 23/20 := by
      simpa using hparent.closure_inside (subset_closure hz)
    exact h.le
  have hcoll : ∀ {z w : ℂ}, z ∈ W → w ∈ W → (H z = H w ↔ z = w ∨ z = -w) :=
    fun hz hw => hcollision (hnorm hz) (hnorm hw)
  have hm : MapsTo H W V := connectedComponentIn_subset _ _
  have hrest : IsProperMap (MapsTo.restrict H W V hm) := hparent.proper
  have hsym := parent_source_symmetric c p hp hd
  have honto : SurjOn H W V := by
    intro y hy
    exact hparent.image_eq.symm ▸ hy
  have hcover := (signed_two_sheet_cover H W V hparent.isOpen_source isOpen_ball
    hm hproper.continuous hopen hrest hcoll hsym honto).2.2
  let f : C(W, V) := ⟨MapsTo.restrict H W V hm, hrest.continuous⟩
  let x₀ : W := ⟨0, hparent.zero_mem⟩
  apply contractible_of_punctured_cover V (convex_ball _ _) f x₀ hrest.isClosedMap ?_ hcover
  intro x hx
  apply Subtype.ext
  have he : H x = H 0 := congrArg Subtype.val hx
  simpa using (hcoll x.property hparent.zero_mem).mp he

/-- Multiplication by the actual nonzero return scale preserves the
contractibility of the physical ambient source. -/
theorem physical_parent_contractible_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0) (hparent : ParentRestriction c p)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 23/20 → ‖w‖ ≤ 23/20 →
      (normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w)) :
    ContractibleSpace (physicalParentSource c p) := by
  letI := parent_contractible_of_bounds c p hp hd hparent hcollision
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  let e := Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC
  have he : parentSource c p ≃ₜ physicalParentSource c p :=
    e.isEmbedding.homeomorphImage (parentSource c p)
  exact he.symm.contractibleSpace

private theorem actual_collision {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w := by
  have hband := parameter_band hp hc.1
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  exact normalized_return_collision_iff c p (by omega)
    ⟨hband.1, by linarith [hband.2]⟩ hc.2.1 hsmall hc.2.2.2.1 hz hw

/-- The actual analytic-tail ambient restriction has contractible source. -/
theorem actual_parent_contractible {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ContractibleSpace (parentSource c p) :=
  parent_contractible_of_bounds c p (by omega) hc.2.1.ne'
    (actual_parent_restriction hp hc) (fun hz hw => actual_collision hp hc hz hw)

/-- Simple connectivity holds for the actual ambient restriction. -/
theorem actual_parent_simplyConnected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsSimplyConnected (parentSource c p) := by
  letI := actual_parent_contractible hp hc
  change SimplyConnectedSpace (parentSource c p)
  infer_instance

/-- The same contraction is transported into the original dynamical plane. -/
theorem actual_physical_parent_contractible {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ContractibleSpace (physicalParentSource c p) :=
  physical_parent_contractible_of_bounds c p (by omega) hc.2.1.ne'
    (actual_parent_restriction hp hc) (fun hz hw => actual_collision hp hc hz hw)

end

end ThreeReturnParentTopology
