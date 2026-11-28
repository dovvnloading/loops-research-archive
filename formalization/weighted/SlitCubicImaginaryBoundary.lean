import SlitCubicBoundaryRange

/-!
# The second cubic period and the imaginary boundary range

Horizontal cancellation identifies the left-ray period with the finite
gap period.  The actual tail integral consequently lies between the two
horizontal sides of the candidate rectangle at every real boundary point.
-/

namespace SlitCubicImaginaryBoundary

open Set Filter MeasureTheory SlitCubicCalibration SlitCubicBoundaryRange
open scoped Topology

noncomputable section

private theorem real_differential_integrable {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) :
    Integrable (fun t : ℝ => differential a b c (t:ℂ)) := by
  exact hi.mono' (((differential_measurable a b c).comp
    Complex.measurable_ofReal).aestronglyMeasurable)
    (Eventually.of_forall fun t => (norm_differential_real a b c t).le)

/-- Cancellation of the full real boundary integral identifies its two
imaginary periods. -/
theorem left_ray_period_eq_height {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (∫ t in Iio a, realDensity a b c t) = height a b c := by
  have hi := realDensity_integrable hab hbc
  have hg := real_differential_integrable hi
  have hz : (∫ t : ℝ, differential a b c (t:ℂ)) = 0 := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      horizontal_integral_eq_zero hi (y := 0) le_rfl
  have him : (∫ t : ℝ, (differential a b c (t:ℂ)).im) = 0 := by
    have him' : (∫ t : ℝ, (differential a b c (t:ℂ)).im) =
        (∫ t : ℝ, differential a b c (t:ℂ)).im := Complex.imCLM.integral_comp_comm hg
    rw [him', hz]
    rfl
  simp_rw [differential_real_im hab hbc] at him
  rw [integral_sub (hi.indicator measurableSet_Iio) (hi.indicator measurableSet_Ioc),
    integral_indicator measurableSet_Iio, integral_indicator measurableSet_Ioc,
    integral_Ioc_eq_integral_Ioo] at him
  exact sub_eq_zero.mp him

/-- On the left ray the imaginary coordinate is the negative accumulated
left-ray density. -/
theorem tail_im_left {a b c x : ℝ} (hab : a < b) (hbc : b < c) (hxa : x ≤ a) :
    (tail a b c (x:ℂ)).im = -(∫ t in Iic x, realDensity a b c t) := by
  have hi := realDensity_integrable hab hbc
  have hg := (real_differential_integrable hi).integrableOn (s := Iic x)
  have he := tail_eq_neg_horizontal_Iic hi (z := (x:ℂ)) (by simp [closedUpper])
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_zero,
    zero_mul, add_zero] at he
  have him : (∫ t in Iic x, (differential a b c (t:ℂ)).im) =
      (∫ t in Iic x, differential a b c (t:ℂ)).im := Complex.imCLM.integral_comp_comm hg
  rw [he, Complex.neg_im, ← him]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t ht
  have hta : t ≤ a := ht.trans hxa
  change (differential a b c (t:ℂ)).im = realDensity a b c t
  rw [differential_real_left hta (hta.trans hab.le) (hta.trans (hab.trans hbc).le)]
  simp

/-- On the gap the imaginary coordinate is the negative remaining gap
period. -/
theorem tail_im_gap {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hbx : b ≤ x) (_hxc : x ≤ c) :
    (tail a b c (x:ℂ)).im = -(∫ t in Ioc x c, realDensity a b c t) := by
  have hi := realDensity_integrable hab hbc
  have ht := integrable_tailIntegrand hi (z := (x:ℂ)) (by simp [closedUpper])
  have he (t : ℝ) : (tailIntegrand a b c (x:ℂ) t).im =
      -(Ioc x c).indicator (realDensity a b c) t := by
    by_cases hxt : x < t
    · simp only [tailIntegrand, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_zero,
        zero_mul, add_zero, mem_Ioi, hxt, indicator_of_mem]
      rw [differential_real_im hab hbc]
      have hat : a < t := (hab.trans_le hbx).trans hxt
      have hbt : b < t := hbx.trans_lt hxt
      simp [Set.indicator, not_lt.mpr hat.le, hbt, hxt]
    · simp [tailIntegrand, hxt]
  change (∫ t, tailIntegrand a b c (x:ℂ) t).im = _
  have him : (∫ t, (tailIntegrand a b c (x:ℂ) t).im) =
      (∫ t, tailIntegrand a b c (x:ℂ) t).im := Complex.imCLM.integral_comp_comm ht
  rw [← him,
    integral_congr_ae (Eventually.of_forall he), integral_neg,
    integral_indicator measurableSet_Ioc]

/-- Every real boundary point lies between the two horizontal sides. -/
theorem tail_im_mem_Icc {a b c : ℝ} (hab : a < b) (hbc : b < c) (x : ℝ) :
    (tail a b c (x:ℂ)).im ∈ Icc (-height a b c) 0 := by
  have hC := (height_pos hab hbc).le
  have hi := realDensity_integrable hab hbc
  have hn (t : ℝ) : 0 ≤ realDensity a b c t :=
    SlitCubicIntegrability.kernel_nonneg a b c t
  by_cases hxa : x ≤ a
  · rw [tail_im_left hab hbc hxa]
    have hq0 : 0 ≤ ∫ t in Iic x, realDensity a b c t := integral_nonneg hn
    have hqC : (∫ t in Iic x, realDensity a b c t) ≤ height a b c := by
      have hq := setIntegral_mono_set (s := Iic x) (hi.integrableOn (s := Iic a))
        (Eventually.of_forall hn) (Eventually.of_forall fun t ht =>
          (show t ∈ Iic a from ht.trans hxa))
      rw [integral_Iic_eq_integral_Iio (x := a), left_ray_period_eq_height hab hbc] at hq
      exact hq
    constructor <;> linarith
  have hax : a < x := lt_of_not_ge hxa
  by_cases hxb : x ≤ b
  · rw [tail_im_first hab hbc hax.le hxb]
    exact ⟨le_rfl, neg_nonpos.mpr hC⟩
  have hbx : b < x := lt_of_not_ge hxb
  by_cases hxc : x ≤ c
  · rw [tail_im_gap hab hbc hbx.le hxc]
    have hq0 : 0 ≤ ∫ t in Ioc x c, realDensity a b c t := integral_nonneg hn
    have hqC : (∫ t in Ioc x c, realDensity a b c t) ≤ height a b c := by
      have hq := setIntegral_mono_set (s := Ioc x c) (hi.integrableOn (s := Ioc b c))
        (Eventually.of_forall hn) (Eventually.of_forall fun t ht =>
          (show t ∈ Ioc b c from ⟨hbx.le.trans_lt ht.1, ht.2⟩))
      rw [integral_Ioc_eq_integral_Ioo (x := b)] at hq
      exact hq
    constructor <;> linarith
  · rw [tail_im_right hab hbc (le_of_not_ge hxc)]
    exact ⟨neg_nonpos.mpr hC, le_rfl⟩

end
end SlitCubicImaginaryBoundary
