import ActualTipItinerary
import ActualFirstReturnSeparation
import ActualCriticalPreperiod
import ActualTipMultiplier

/-!
# Exact physical return portrait of the constructed near-minus-two tips

The positive inverse itinerary is produced with the parameter.  It
discharges every intermediate-return exclusion used by the physical
phase and exact critical-portrait theorems.  All clauses below concern
one literal quadratic map and its already constructed canonical domains.
-/

namespace ActualPrimitiveReturn

open Set Function
open LimitingCrestQuadraticReturn NearTwoTip NearTwoShooting
open ThreeReturnCollar ThreeReturnParent UniformThreeReturn
open UniformThreeReturnRenormalization ActualFirstReturnSeparation
open ActualFullCycle ActualCriticalPreperiod ActualTipMultiplier

noncomputable section

/-- The entire physical parent lies in the small disk on which the
constructed positive itinerary proves first-return exclusion. -/
theorem actual_parent_in_control_disk {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalParentSource c p ⊆
      {z : ℂ | ‖z‖ ≤ (23/20 : ℝ)*criticalValue c p} := by
  rintro z ⟨w,hw,rfl⟩
  have hb := (actual_parent_restriction hp hc).closure_inside (subset_closure hw)
  have hn : ‖w‖ < (23/20 : ℝ) := by simpa using hb
  change ‖(criticalValue c p : ℂ)*w‖ ≤ (23/20 : ℝ)*criticalValue c p
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.2.1]
  nlinarith [hc.2.1]

/-- Intermediate-time noncollision is a proved property of the actual
parent, once the retained construction witness is supplied. -/
theorem actual_parent_first_return_disjoint {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c)
    (hshoot : shooting (p-2) (criticalValue c p) c = 0)
    (r : ℕ) (hr : 0 < r) (hrp : r < p) :
    Disjoint (physicalParentSource c p)
      (((quadraticMap c)^[r]) '' physicalParentSource c p) := by
  have hsub : physicalParentSource c p ⊆
      Metric.closedBall 0 ((23/20 : ℝ)*criticalValue c p) := by
    intro z hz
    simpa using actual_parent_in_control_disk hp hc hz
  exact (actual_early_image_disjoint hp hc hshoot (by omega) hrp).mono
    hsub (image_mono hsub)

/-- The canonical physical source has a full cycle of 3p disjoint
open phase domains. All intermediate-time hypotheses are discharged. -/
theorem constructed_full_open_cycle {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c)
    (hshoot : shooting (p-2) (criticalValue c p) c = 0)
    (i j : ℕ) (hi : i < 3*p) (hj : j < 3*p) (hij : i ≠ j) :
    Disjoint (((quadraticMap c)^[i]) '' physicalSource c p)
      (((quadraticMap c)^[j]) '' physicalSource c p) :=
  actual_full_open_cycle_disjoint (by omega) (Or.inr ⟨hp,hc⟩)
    (actual_parent_first_return_disjoint hp hc hshoot) i j hi hj hij

/-- The actual critical point has least preperiod 3p+1 and exact
eventual physical period 3p. No separation premise remains. -/
theorem constructed_critical_portrait {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c)
    (hshoot : shooting (p-2) (criticalValue c p) c = 0) :
    ExactPortrait (quadraticMap c) 0 (3*p+1) (3*p) :=
  actual_critical_portrait (by omega) (Or.inr ⟨hp,hc⟩)
    (actual_parent_first_return_disjoint hp hc hshoot)

/-- Every return index at least seventeen supplies one actual parameter
with the physical canonical renormalization, all 3p disjoint phase
domains, the exact critical portrait, the complete orbit census, and
a uniformly repelling terminal cycle. -/
theorem exists_actual_primitive_portrait (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧
      shooting (p-2) (criticalValue c p) c = 0 ∧
      PhysicalRenormalization c p ∧
      (∀ i j : ℕ, i < 3*p → j < 3*p → i ≠ j →
        Disjoint (((quadraticMap c)^[i]) '' physicalSource c p)
          (((quadraticMap c)^[j]) '' physicalSource c p)) ∧
      ExactPortrait (quadraticMap c) 0 (3*p+1) (3*p) ∧
      (Set.range (fun i => ((quadraticMap c)^[i]) 0)).ncard = 6*p+1 ∧
      (Set.range (fun i => ((quadraticMap c)^[i+1]) 0)).ncard = 6*p ∧
      (3/2 : ℝ) <
        ‖deriv ((quadraticMap c)^[3*p]) (-(criticalValue c (3*p) : ℂ))‖ := by
  obtain ⟨c,hc,hshoot⟩ := ActualTipItinerary.exists_actual_tip_with_itinerary p hp
  have hselected : SelectedParameter p c := Or.inr ⟨hp,hc⟩
  have hfirst := actual_parent_first_return_disjoint hp hc hshoot
  exact ⟨c,hc,hshoot,selected_physical_renormalization (by omega) hselected,
    constructed_full_open_cycle hp hc hshoot,
    constructed_critical_portrait hp hc hshoot,
    actual_critical_orbit_ncard (by omega) hselected hfirst,
    actual_postcritical_ncard (by omega) hselected hfirst,
    actual_physical_multiplier_gt hp hc⟩

end
end ActualPrimitiveReturn
