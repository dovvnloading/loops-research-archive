import SlitCubicCalibration
import SlitCubicPeriods
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exact boundary values of the cubic tail potential

The constructed horizontal integral has real part zero on the left real
ray, and the positive finite period on the marked gap.  These are properties
of the actual integral, rather than assumptions about a conformal chart.
-/

namespace SlitCubicBoundary

open Set Filter MeasureTheory
open SlitCubicCalibration
open scoped Topology
noncomputable section

def period (a b c : ℝ) : ℝ := ∫ x in Ioo a b, realDensity a b c x

theorem period_pos {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    0 < period a b c := SlitCubicIntegrability.integral_Ioo_pos hab hbc

theorem differential_real_re {a b c : ℝ} (hab : a < b) (hbc : b < c) (x : ℝ) :
    (differential a b c (x:ℂ)).re =
      (Ioi c).indicator (realDensity a b c) x -
        (Ioc a b).indicator (realDensity a b c) x := by
  by_cases hxa : x ≤ a
  · rw [differential_real_left hxa (hxa.trans hab.le) (hxa.trans (hab.trans hbc).le)]
    simp [not_lt.mpr hxa, not_lt.mpr (hxa.trans (hab.trans hbc).le)]
  · have hax : a < x := lt_of_not_ge hxa
    by_cases hxb : x ≤ b
    · rw [differential_real_first hax.le hxb (hxb.trans hbc.le)]
      simp [hax, hxb, not_lt.mpr (hxb.trans hbc.le)]
    · have hbx : b < x := lt_of_not_ge hxb
      by_cases hxc : x ≤ c
      · rw [differential_real_gap (hab.trans hbx).le hbx.le hxc]
        simp [hxb, not_lt.mpr hxc]
      · have hcx : c < x := lt_of_not_ge hxc
        rw [differential_real_right ((hab.trans hbc).trans hcx).le
          (hbc.trans hcx).le hcx.le]
        simp [hxb, hcx]

private theorem tailIntegrand_real_re {a b c x t : ℝ} :
    (tailIntegrand a b c (x:ℂ) t).re =
      (Ioi x).indicator (fun s => (differential a b c (s:ℂ)).re) t := by
  by_cases h : x < t <;> simp [tailIntegrand, h]

theorem tail_re_left {a b c x : ℝ} (hab : a < b) (hbc : b < c) (hxa : x ≤ a) :
    (tail a b c (x:ℂ)).re = 0 := by
  have hi := realDensity_integrable hab hbc
  have ht := integrable_tailIntegrand hi (z := (x:ℂ)) (by simp [closedUpper])
  have he (t : ℝ) : (tailIntegrand a b c (x:ℂ) t).re =
      (Ioi c).indicator (realDensity a b c) t -
        (Ioc a b).indicator (realDensity a b c) t := by
    rw [tailIntegrand_real_re]
    by_cases hxt : x < t
    · simp only [mem_Ioi, hxt, indicator_of_mem]
      exact differential_real_re hab hbc t
    · have hta : t ≤ a := (le_of_not_gt hxt).trans hxa
      simp [hxt, not_lt.mpr hta, not_lt.mpr (hta.trans (hab.trans hbc).le)]
  change (∫ t, tailIntegrand a b c (x:ℂ) t).re = 0
  have hr : (∫ t, (tailIntegrand a b c (x:ℂ) t).re) =
      (∫ t, tailIntegrand a b c (x:ℂ) t).re := Complex.reCLM.integral_comp_comm ht
  rw [← hr, integral_congr_ae (Eventually.of_forall he),
    integral_sub (hi.indicator measurableSet_Ioi) (hi.indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioc]
  rw [integral_Ioc_eq_integral_Ioo]
  exact sub_eq_zero.mpr (SlitCubicPeriods.ray_period_eq_finite_period hab hbc)

theorem tail_re_gap {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hbx : b ≤ x) (hxc : x ≤ c) :
    (tail a b c (x:ℂ)).re = period a b c := by
  have hi := realDensity_integrable hab hbc
  have ht := integrable_tailIntegrand hi (z := (x:ℂ)) (by simp [closedUpper])
  have he (t : ℝ) : (tailIntegrand a b c (x:ℂ) t).re =
      (Ioi c).indicator (realDensity a b c) t := by
    rw [tailIntegrand_real_re]
    by_cases hxt : x < t
    · simp only [mem_Ioi, hxt, indicator_of_mem]
      rw [differential_real_re hab hbc]
      have hbt : b < t := hbx.trans_lt hxt
      simp [not_le.mpr hbt]
    · have htc : t ≤ c := (le_of_not_gt hxt).trans hxc
      simp [hxt, not_lt.mpr htc]
  change (∫ t, tailIntegrand a b c (x:ℂ) t).re = period a b c
  have hr : (∫ t, (tailIntegrand a b c (x:ℂ) t).re) =
      (∫ t, tailIntegrand a b c (x:ℂ) t).re := Complex.reCLM.integral_comp_comm ht
  rw [← hr, integral_congr_ae (Eventually.of_forall he),
    integral_indicator measurableSet_Ioi]
  exact SlitCubicPeriods.ray_period_eq_finite_period hab hbc

end
end SlitCubicBoundary
