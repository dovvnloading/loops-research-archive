import SlitDiskMarking
import ActualParentSupremum

/-!
# The actual quadratic cuts lie inside their literal target disk

These inequalities instantiate the finite-disk extremal problem for every
constructed actual tip of period at least seventeen.
-/

namespace ActualParentDiskMarking

open Set MarkedSlitTransport ActualParentMarks ActualParentSupremum
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter
noncomputable section

theorem limitCuts_abs_le_one {k : ℝ} (hk : k ∈ parameterInterval) (i : Fin 4) :
    |limitCuts k i| ≤ 1 := by
  obtain ⟨h2l,h2u,h5l,h5u,h3l,h3u⟩ := limit_cut_boxes hk
  fin_cases i
  · change |criticalOrbit k 2| ≤ 1
    rw [abs_le]; constructor <;> linarith
  · change |criticalOrbit k 5| ≤ 1
    rw [abs_le]; constructor <;> linarith
  · change |criticalOrbit k 3| ≤ 1
    rw [abs_le]; constructor <;> linarith
  · norm_num [limitCuts]

theorem actualCuts_abs_le_two {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    (i : Fin 4) : |actualCuts c p i| ≤ 2 := by
  calc
    |actualCuts c p i| = |(actualCuts c p i-limitCuts k i)+limitCuts k i| := by ring_nf
    _ ≤ |actualCuts c p i-limitCuts k i|+|limitCuts k i| := abs_add_le _ _
    _ ≤ 2 := by
      have he := actualCuts_error_lt hp hc hk hroot i
      have hl := limitCuts_abs_le_one hk i
      linarith

theorem targetRadius_gt_four {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : 4 < targetRadius c p := by
  have hpow : (2 : ℝ)^17 ≤ 2^p := pow_le_pow_right₀ (by norm_num) hp
  have hr := targetRadius_lower hc
  norm_num at hpow
  linarith

theorem actualMarking_fits_disk {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    0 < targetRadius c p ∧
      -targetRadius c p < (actualMarking hp hc hk hroot).left ∧
      (actualMarking hp hc hk hroot).right < targetRadius c p := by
  have hr := targetRadius_gt_four hp hc
  have hl := (abs_le.mp (actualCuts_abs_le_two hp hc hk hroot 0)).1
  refine ⟨by linarith,?_,?_⟩
  · change -targetRadius c p < actualCuts c p 0
    linarith
  · change (1 : ℝ) < targetRadius c p
    linarith

/-- The actual finite-period critical-orbit cuts in the explicit
disk-to-slit-plane coordinate. -/
def actualTransformedMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : Marking :=
  SlitDiskMarking.transformedMarking (actualMarking_fits_disk hp hc hk hroot).1
    (actualMarking hp hc hk hroot) (actualMarking_fits_disk hp hc hk hroot).2.1
    (actualMarking_fits_disk hp hc hk hroot).2.2

end
end ActualParentDiskMarking
