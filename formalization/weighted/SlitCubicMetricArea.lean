import SlitCubicAdmissible
import SlitCubicArea
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Area of the reflected cubic metric

All normalizations here refer to ordinary planar Lebesgue measure and the
archive's nonnegative modulus density.  Reflection across the axis doubles
the upper-half-plane energy; the axis is proved to have zero planar measure.
-/

namespace SlitCubicMetricArea

open Set Filter MeasureTheory Complex SlitCubicCalibration SlitCubicBoundary
  SlitPotentialReflection SlitCubicAdmissible SlitWaveModulus MarkedSlitTransport
open scoped Topology ENNReal
noncomputable section

theorem norm_differential_fold_sq (a b c : ℝ) (z : ℂ) :
    ‖differential a b c (fold z)‖^2 = SlitCubicArea.densitySq a b c z := by
  rw [differential_norm (fold_im_nonneg z)]
  simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt (norm_nonneg _),
    norm_fold_sub_real,SlitCubicArea.densitySq]

theorem density_eq_ofReal (M : Marking) (z : ℂ) :
    density M z = ENNReal.ofReal
      (‖differential M.left M.first M.second (fold z)‖ /
        (2 * period M.left M.first M.second)) := by
  have hB := period_pos M.left_lt_first M.first_lt_second
  unfold density SlitCubicAdmissible.slope
  rw [ENNReal.ofReal_div_of_pos (mul_pos (by norm_num) hB),
    ENNReal.ofReal_div_of_pos hB, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp only [ENNReal.ofReal_ofNat,div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (by norm_num : (2:ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (2:ℝ≥0∞) ≠ ∞))]
  ring

theorem density_sq_eq (M : Marking) (z : ℂ) :
    (density M z)^2 = ENNReal.ofReal
      ((1 / (4 * (period M.left M.first M.second)^2)) *
        SlitCubicArea.densitySq M.left M.first M.second z) := by
  have hB := period_pos M.left_lt_first M.first_lt_second
  rw [density_eq_ofReal, ← ENNReal.ofReal_pow (div_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) hB.le)) 2,
    div_pow,norm_differential_fold_sq]
  congr 1
  ring

/-- Exact conversion between the modulus area and the ordinary integral. -/
theorem area_eq_full_energy (M : Marking) :
    area (density M) = ENNReal.ofReal
      ((∫ z : ℂ, SlitCubicArea.densitySq M.left M.first M.second z) /
        (4 * (period M.left M.first M.second)^2)) := by
  have hi := (SlitCubicArea.integrable_densitySq M.left_lt_first M.first_lt_second).const_mul
    (1 / (4 * (period M.left M.first M.second)^2))
  unfold area
  simp_rw [density_sq_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (by
    intro z
    exact mul_nonneg (by positivity) (SlitCubicArea.densitySq_nonneg _ _ _ z))),
    integral_const_mul]
  congr 1
  ring

theorem area_lt_top (M : Marking) : area (density M) < ∞ := by
  rw [area_eq_full_energy]
  exact ENNReal.ofReal_lt_top

theorem real_axis_volume_zero : volume {z : ℂ | z.im = 0} = 0 := by
  have he : {z : ℂ | z.im = 0} =
      measurableEquivRealProd ⁻¹' (univ ×ˢ ({0}:Set ℝ)) := by
    ext z
    simp
  rw [he,volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet]
  change ((volume : Measure ℝ).prod volume) (univ ×ˢ ({0}:Set ℝ)) = 0
  simp

theorem densitySq_conj (a b c : ℝ) (z : ℂ) :
    SlitCubicArea.densitySq a b c ((starRingEnd ℂ) z) = SlitCubicArea.densitySq a b c z := by
  have he (t : ℝ) : ‖(starRingEnd ℂ) z - (t:ℂ)‖ = ‖z-(t:ℂ)‖ := by
    calc
      _ = ‖(starRingEnd ℂ) (z-(t:ℂ))‖ := by simp
      _ = _ := Complex.norm_conj _
  simp only [SlitCubicArea.densitySq,he]

theorem integral_densitySq_eq_twice_upper {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (∫ z : ℂ, SlitCubicArea.densitySq a b c z) =
      2 * ∫ z in upper, SlitCubicArea.densitySq a b c z := by
  have hi := SlitCubicArea.integrable_densitySq hab hbc
  have haxis : ∀ᵐ z : ℂ, z.im ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using real_axis_volume_zero
  have he : upperᶜ =ᵐ[volume] {z : ℂ | z.im < 0} := by
    filter_upwards [haxis] with z hz
    apply propext
    change (¬ 0 < z.im) ↔ z.im < 0
    exact not_lt.trans (le_iff_lt_or_eq.trans (or_iff_left hz))
  have href := conjLIE.measurePreserving.setIntegral_preimage_emb
    conjLIE.toHomeomorph.measurableEmbedding (SlitCubicArea.densitySq a b c) upper
  have hpre : conjLIE ⁻¹' upper = {z : ℂ | z.im < 0} := by
    ext z
    simp [upper]
  simp only [conjLIE_apply,densitySq_conj] at href
  rw [hpre] at href
  have hcomp : (∫ z in upperᶜ, SlitCubicArea.densitySq a b c z) =
      ∫ z in {z : ℂ | z.im < 0}, SlitCubicArea.densitySq a b c z := setIntegral_congr_set he
  rw [← integral_add_compl upper_open.measurableSet hi,hcomp,href]
  ring

theorem area_eq_upper_energy (M : Marking) :
    area (density M) = ENNReal.ofReal
      ((∫ z in upper, SlitCubicArea.densitySq M.left M.first M.second z) /
        (2 * (period M.left M.first M.second)^2)) := by
  rw [area_eq_full_energy,integral_densitySq_eq_twice_upper M.left_lt_first M.first_lt_second]
  congr 1
  ring

end
end SlitCubicMetricArea
