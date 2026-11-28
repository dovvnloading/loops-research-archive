import SlitDiskRate
import ActualParentDiskMarking

/-!
# Exponential convergence of the complete physical parent optimum

The finite disk is identified with an exactly normalized full-plane
problem.  Its four actual critical-orbit cuts move by an explicit
reciprocal-radius amount; the actual target radius grows exponentially.
This removes the logarithmic escaping-family error from the previous
unrestricted-optimum comparison.
-/

namespace ActualParentExponentialRate

open Set Metric MarkedSlitTransport SlitWaveLimit SlitDiskRate
open ActualParentMarks ActualParentSupremum ActualParentRate ActualParentDiskMarking
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter LimitingCrestQuadraticReturn
open scoped ENNReal
noncomputable section

/-- The actual finite-period cuts after the proved affine disk normalization. -/
def actualNormalizedMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : Marking :=
  normalizedMarking (actualMarking_fits_disk hp hc hk hroot).1
    (actualMarking hp hc hk hroot) (actualMarking_fits_disk hp hc hk hroot).2.1
    (actualMarking_fits_disk hp hc hk hroot).2.2

theorem markCoords_actualNormalizedMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) (i : Fin 4) :
    markCoords (actualNormalizedMarking hp hc hk hroot) i =
      SlitDiskRate.normalizedCut (targetRadius c p) (actualCuts c p i) := by
  unfold actualNormalizedMarking
  rw [markCoords_normalizedMarking,markCoords_actualMarking]

theorem normalized_mark_error_le {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    cutError (markCoords (limitMarking k hk))
      (markCoords (actualNormalizedMarking hp hc hk hroot)) ≤
      markError c p k + 160/targetRadius c p := by
  have htri := cutError_triangle (markCoords (limitMarking k hk))
    (markCoords (actualMarking hp hc hk hroot))
    (markCoords (actualNormalizedMarking hp hc hk hroot))
  have hb : ∀ i, |markCoords (actualMarking hp hc hk hroot) i| ≤ 2 := by
    intro i
    rw [markCoords_actualMarking]
    exact actualCuts_abs_le_two hp hc hk hroot i
  have hnorm := normalizedMarking_error_le (actualMarking_fits_disk hp hc hk hroot).1
    (actualMarking hp hc hk hroot) (actualMarking_fits_disk hp hc hk hroot).2.1
    (actualMarking_fits_disk hp hc hk hroot).2.2 (targetRadius_gt_four hp hc).le hb
  have hfirst : cutError (markCoords (limitMarking k hk))
      (markCoords (actualMarking hp hc hk hroot)) = markError c p k := by
    rw [markCoords_limitMarking,markCoords_actualMarking]
    rfl
  rw [hfirst] at htri
  exact htri.trans (add_le_add le_rfl hnorm)

theorem radius_error_le {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    160/targetRadius c p ≤ 1920*(1/2:ℝ)^p := by
  calc
    160/targetRadius c p ≤ 160/((2:ℝ)^p/12) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (targetRadius_lower hc)
    _ = 1920*(1/2:ℝ)^p := by
      rw [one_div_pow]
      field_simp
      norm_num

theorem total_error_small {p : ℕ} (hp : 30 ≤ p) :
    4*3906*23646*scale p + 1920*(1/2:ℝ)^p ≤ 1/200 := by
  have hq : scale p ≤ (1/4:ℝ)^30 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  have hh : (1/2:ℝ)^p ≤ (1/2:ℝ)^30 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  have hnum : 4*3906*23646*(1/4:ℝ)^30 + 1920*(1/2:ℝ)^30 < 1/200 := by norm_num
  nlinarith

/-- The actual normalized four-cut displacement is exponentially small. -/
theorem actual_normalized_error_le {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    cutError (markCoords (limitMarking k hk))
      (markCoords (actualNormalizedMarking hp hc hk hroot)) ≤
      4*3906*23646*scale p + 1920*(1/2:ℝ)^p :=
  (normalized_mark_error_le hp hc hk hroot).trans
    (add_le_add (markError_le hp hc hk hroot) (radius_error_le hc))

theorem total_error_le_exponential {p : ℕ} (hp : 30 ≤ p) :
    4*3906*23646*scale p + 1920*(1/2:ℝ)^p ≤ 1921*(1/2:ℝ)^p := by
  have hh : (1/2:ℝ)^p ≤ (1/2:ℝ)^30 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  have hnum : 4*3906*23646*(1/2:ℝ)^30 < 1 := by norm_num
  have hc : 4*3906*23646*(1/2:ℝ)^p ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ) ≤ (1/2:ℝ)^p)
  have hs : scale p = (1/2:ℝ)^p*(1/2:ℝ)^p := by
    rw [←mul_pow]
    norm_num [scale]
  rw [hs]
  nlinarith

/-- The complete physical supremum is identified with its exact normalized plane problem. -/
theorem physical_parent_width_eq_normalized_plane {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalParentWidth hp hc hk hroot = width (actualNormalizedMarking hp hc hk hroot) univ := by
  rw [physicalParentWidth_eq_actual]
  exact width_disk_eq_normalized_plane (actualMarking_fits_disk hp hc hk hroot).1
    (actualMarking hp hc hk hroot) (actualMarking_fits_disk hp hc hk hroot).2.1
    (actualMarking_fits_disk hp hc hk hroot).2.2

/-- Explicit exponential error for every actual physical parent optimum.
The two terms distinguish actual critical-orbit motion from finite-disk geometry. -/
theorem physical_parent_exponential_error {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    |(physicalParentWidth (by omega : 17 ≤ p) hc hk hroot).toReal -
      (limitingParentWidth k hk).toReal| ≤
      1600*(4*3906*23646*scale p + 1920*(1/2:ℝ)^p)*(limitingParentWidth k hk).toReal := by
  have he := actual_normalized_error_le (by omega : 17 ≤ p) hc hk hroot
  have hsmall := he.trans (total_error_small hp)
  have hbase := plane_mark_real_error (limitMarking k hk)
    (actualNormalizedMarking (by omega : 17 ≤ p) hc hk hroot)
    (limitMarking_separated hk) hsmall
  rw [←physical_parent_width_eq_normalized_plane] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (by norm_num)) ENNReal.toReal_nonneg)

/-- A single explicit geometric rate replaces the previous reciprocal-period cutoff error. -/
theorem physical_parent_geometric_error {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    |(physicalParentWidth (by omega : 17 ≤ p) hc hk hroot).toReal -
      (limitingParentWidth k hk).toReal| ≤
      3073600*(1/2:ℝ)^p*(limitingParentWidth k hk).toReal := by
  have h := physical_parent_exponential_error hp hc hk hroot
  have ht := total_error_le_exponential hp
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 1600))
    (ENNReal.toReal_nonneg (a := limitingParentWidth k hk))
  calc
    _ ≤ 1600*(1921*(1/2:ℝ)^p)*(limitingParentWidth k hk).toReal := h.trans hm
    _ = _ := by ring

end
end ActualParentExponentialRate
