import SlitCubicBoundary

/-!
# Four boundary sides of the cubic integral

These statements locate the actual real-axis image.  They supply the
boundary information needed to identify the image of the holomorphic map.
-/

namespace SlitCubicBoundaryRange

open Set Filter MeasureTheory SlitCubicCalibration SlitCubicBoundary
open scoped Topology
noncomputable section

def height (a b c : ℝ) : ℝ := ∫ x in Ioo b c, realDensity a b c x

theorem height_pos {a b c : ℝ} (hab : a < b) (hbc : b < c) : 0 < height a b c := by
  have hs : Ioo b c ⊆ Function.support (realDensity a b c) := by
    intro x hx
    exact (SlitCubicIntegrability.kernel_pos (hab.trans hx.1).ne' hx.1.ne' hx.2.ne).ne'
  have hn (x : ℝ) : 0 ≤ realDensity a b c x := SlitCubicIntegrability.kernel_nonneg a b c x
  unfold height
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall hn)
    (realDensity_integrable hab hbc).integrableOn,
    inter_eq_self_of_subset_right hs,Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hbc)

theorem differential_real_im {a b c : ℝ} (hab : a < b) (hbc : b < c) (x : ℝ) :
    (differential a b c (x:ℂ)).im =
      (Iio a).indicator (realDensity a b c) x -
        (Ioc b c).indicator (realDensity a b c) x := by
  by_cases hxa : x < a
  · rw [differential_real_left hxa.le (hxa.trans hab).le ((hxa.trans hab).trans hbc).le]
    simp [hxa,not_lt.mpr (hxa.trans hab).le]
  · have hax : a ≤ x := le_of_not_gt hxa
    by_cases hxb : x ≤ b
    · rw [differential_real_first hax hxb (hxb.trans hbc.le)]
      simp [hxa,not_lt.mpr hxb]
    · have hbx : b < x := lt_of_not_ge hxb
      by_cases hxc : x ≤ c
      · rw [differential_real_gap (hab.trans hbx).le hbx.le hxc]
        simp [hxa,hbx,hxc]
      · have hcx : c < x := lt_of_not_ge hxc
        rw [differential_real_right ((hab.trans hbc).trans hcx).le
          (hbc.trans hcx).le hcx.le]
        simp [hxa,hxc]

theorem tail_im_first {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hax : a ≤ x) (hxb : x ≤ b) :
    (tail a b c (x:ℂ)).im = -height a b c := by
  have hi := realDensity_integrable hab hbc
  have ht := integrable_tailIntegrand hi (z := (x:ℂ)) (by simp [closedUpper])
  have he (t : ℝ) : (tailIntegrand a b c (x:ℂ) t).im =
      -(Ioc b c).indicator (realDensity a b c) t := by
    by_cases hxt : x < t
    · simp only [tailIntegrand,Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,
        zero_mul,add_zero,mem_Ioi,hxt,indicator_of_mem]
      rw [differential_real_im hab hbc]
      simp [not_lt.mpr (hax.trans hxt.le)]
    · have htb : t ≤ b := (le_of_not_gt hxt).trans hxb
      simp [tailIntegrand,hxt,not_lt.mpr htb]
  have him : (∫ t, (tailIntegrand a b c (x:ℂ) t).im) =
      (∫ t, tailIntegrand a b c (x:ℂ) t).im := Complex.imCLM.integral_comp_comm ht
  change (∫ t, tailIntegrand a b c (x:ℂ) t).im = _
  rw [← him,integral_congr_ae (Eventually.of_forall he),integral_neg,
    integral_indicator measurableSet_Ioc,integral_Ioc_eq_integral_Ioo]
  rfl

theorem tail_im_right {a b c x : ℝ} (hab : a < b) (hbc : b < c) (hcx : c ≤ x) :
    (tail a b c (x:ℂ)).im = 0 := by
  have hi := realDensity_integrable hab hbc
  have ht := integrable_tailIntegrand hi (z := (x:ℂ)) (by simp [closedUpper])
  have he (t : ℝ) : (tailIntegrand a b c (x:ℂ) t).im = 0 := by
    by_cases hxt : x < t
    · simp only [tailIntegrand,Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,
        zero_mul,add_zero,mem_Ioi,hxt,indicator_of_mem]
      rw [differential_real_right ((hab.trans hbc).le.trans (hcx.trans hxt.le))
        (hbc.le.trans (hcx.trans hxt.le)) (hcx.trans hxt.le)]
      rfl
    · simp [tailIntegrand,hxt]
  have him : (∫ t, (tailIntegrand a b c (x:ℂ) t).im) =
      (∫ t, tailIntegrand a b c (x:ℂ) t).im := Complex.imCLM.integral_comp_comm ht
  change (∫ t, tailIntegrand a b c (x:ℂ) t).im = _
  rw [← him,integral_congr_ae (Eventually.of_forall he),integral_zero]

theorem tail_re_first {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hax : a ≤ x) (hxb : x ≤ b) :
    (tail a b c (x:ℂ)).re = period a b c - ∫ t in Ioc x b, realDensity a b c t := by
  have hi := realDensity_integrable hab hbc
  have ht := integrable_tailIntegrand hi (z := (x:ℂ)) (by simp [closedUpper])
  have he (t : ℝ) : (tailIntegrand a b c (x:ℂ) t).re =
      (Ioi c).indicator (realDensity a b c) t -
        (Ioc x b).indicator (realDensity a b c) t := by
    by_cases hxt : x < t
    · simp only [tailIntegrand,Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,
        zero_mul,add_zero,mem_Ioi,hxt,indicator_of_mem]
      rw [differential_real_re hab hbc]
      simp only [indicator,mem_Ioc,hxt,hax.trans_lt hxt,true_and]
    · have htc : t ≤ c := (le_of_not_gt hxt).trans (hxb.trans hbc.le)
      simp [tailIntegrand,hxt,not_lt.mpr htc]
  have hre : (∫ t, (tailIntegrand a b c (x:ℂ) t).re) =
      (∫ t, tailIntegrand a b c (x:ℂ) t).re := Complex.reCLM.integral_comp_comm ht
  change (∫ t, tailIntegrand a b c (x:ℂ) t).re = _
  rw [← hre,integral_congr_ae (Eventually.of_forall he),
    integral_sub (hi.indicator measurableSet_Ioi) (hi.indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioi,integral_indicator measurableSet_Ioc]
  congr 1
  exact SlitCubicPeriods.ray_period_eq_finite_period hab hbc

theorem tail_re_right {a b c x : ℝ} (hab : a < b) (hbc : b < c) (hcx : c ≤ x) :
    (tail a b c (x:ℂ)).re = ∫ t in Ioi x, realDensity a b c t := by
  have hi := realDensity_integrable hab hbc
  have ht := integrable_tailIntegrand hi (z := (x:ℂ)) (by simp [closedUpper])
  have he (t : ℝ) : (tailIntegrand a b c (x:ℂ) t).re =
      (Ioi x).indicator (realDensity a b c) t := by
    by_cases hxt : x < t
    · simp only [tailIntegrand,Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,
        zero_mul,add_zero,mem_Ioi,hxt,indicator_of_mem]
      rw [differential_real_right ((hab.trans hbc).le.trans (hcx.trans hxt.le))
        (hbc.le.trans (hcx.trans hxt.le)) (hcx.trans hxt.le)]
      rfl
    · simp [tailIntegrand,hxt]
  have hre : (∫ t, (tailIntegrand a b c (x:ℂ) t).re) =
      (∫ t, tailIntegrand a b c (x:ℂ) t).re := Complex.reCLM.integral_comp_comm ht
  change (∫ t, tailIntegrand a b c (x:ℂ) t).re = _
  rw [← hre,integral_congr_ae (Eventually.of_forall he),integral_indicator measurableSet_Ioi]

theorem tail_re_mem_Icc {a b c : ℝ} (hab : a < b) (hbc : b < c) (x : ℝ) :
    (tail a b c (x:ℂ)).re ∈ Icc 0 (period a b c) := by
  have hB := (period_pos hab hbc).le
  have hi := realDensity_integrable hab hbc
  have hn (t : ℝ) : 0 ≤ realDensity a b c t := SlitCubicIntegrability.kernel_nonneg a b c t
  by_cases hxa : x ≤ a
  · rw [tail_re_left hab hbc hxa]
    exact ⟨le_rfl,hB⟩
  have hax : a < x := lt_of_not_ge hxa
  by_cases hxb : x ≤ b
  · rw [tail_re_first hab hbc hax.le hxb]
    have hq0 : 0 ≤ ∫ t in Ioc x b, realDensity a b c t := integral_nonneg hn
    have hqB : (∫ t in Ioc x b, realDensity a b c t) ≤ period a b c := by
      have hq := setIntegral_mono_set (s := Ioc x b) (hi.integrableOn (s := Ioc a b))
        (Eventually.of_forall hn) (Eventually.of_forall (fun t ht =>
          (show t ∈ Ioc a b from ⟨hax.le.trans_lt ht.1,ht.2⟩)))
      simpa only [period,integral_Ioc_eq_integral_Ioo] using hq
    constructor <;> linarith
  have hbx : b < x := lt_of_not_ge hxb
  by_cases hxc : x ≤ c
  · rw [tail_re_gap hab hbc hbx.le hxc]
    exact ⟨hB,le_rfl⟩
  have hcx : c < x := lt_of_not_ge hxc
  rw [tail_re_right hab hbc hcx.le]
  refine ⟨integral_nonneg hn,?_⟩
  have hq := setIntegral_mono_set (s := Ioi x) (hi.integrableOn (s := Ioi c))
    (Eventually.of_forall hn) (Eventually.of_forall (fun t ht =>
      (show t ∈ Ioi c from hcx.trans ht)))
  have hp : (∫ t in Ioi c, realDensity a b c t) = period a b c :=
    SlitCubicPeriods.ray_period_eq_finite_period hab hbc
  exact hq.trans_eq hp

end
end SlitCubicBoundaryRange
