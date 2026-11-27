import LimitingCrestLimit
import LimitingCrestModelGates

/-!
# A one-third lower bound for the full limiting-model coefficient

The proof uses a whole-interval affine minorant of the reciprocal radius.
There is no numerical quadrature and no asserted physical-width limit.
-/

namespace LimitingCrest

open Set MeasureTheory
noncomputable section

/-- The closed radial formula is the actual angular crossing throughout
the entire limiting parent interval. -/
theorem full_crossingCos_root {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) :
    crossing κ s (crossingCos κ s) = 0 := by
  have hs0 : s ≠ 0 := by linarith [hs.1]
  have hu := full_crossingCos_bounds hk hs
  have hu' : crossingCos κ s ∈ Icc (-1 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hcoord : -3 / 4 + s * crossingCos κ s = radialAbscissa κ s := by
    rw [crossingCos_radial_coordinate hs0]
    field_simp [hs0] <;> ring
  have he := radialPoint_eq_circlePoint hk hs hu' hcoord
  have hr := (radial_model_realization hk hs).2.2.1
  rw [he] at hr
  have hzero : (complexMap κ (circlePoint s (crossingCos κ s))).re = 0 := by
    simpa using congrArg Complex.re hr
  have hc : (complexMap κ (circlePoint s (crossingCos κ s))).re =
      crossing κ s (crossingCos κ s) := by
    simpa using congrArg Complex.re (circle_image κ s hu')
  linarith

private theorem sharp_left_crossing_sign {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (663 / 10000)) :
    crossing κ s (-1 / 200) < 0 := by
  have hs2 := pow_le_pow_left₀ (by linarith [hs.1] : (0 : ℝ) ≤ s) hs.2 2
  let b : ℝ := 9 / 16 + (3 / 2) * (1 / 16) * (1 / 200) +
    (663 / 10000) ^ 2 * (2 * (1 / 200) ^ 2 - 1)
  let q : ℝ := 9 / 16 - (3 / 2) * s * (-1 / 200) +
    s ^ 2 * (2 * (-1 / 200 : ℝ) ^ 2 - 1)
  have hb : 0 ≤ b := by norm_num [b]
  have hq : b ≤ q := by dsimp [b, q]; nlinarith [hs.1]
  have hm := mul_le_mul hk.1 hq hb (by linarith [hk.1] : (0 : ℝ) ≤ κ)
  have hc : (1 : ℝ) < (17903 / 10000) * b := by norm_num [b]
  change 1 - κ * q < 0
  linarith

/-- A sharper angular enclosure on the longer, fully certified inner
interval used for the coefficient estimate. -/
theorem sharp_crossingCos_lower {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (663 / 10000)) :
    (-1 / 200 : ℝ) < crossingCos κ s := by
  have hs' : s ∈ Icc (1 / 16 : ℝ) (1 / 8) := ⟨hs.1, by linarith [hs.2]⟩
  have hu := full_crossingCos_bounds hk hs'
  have hz := full_crossingCos_root hk hs'
  have hn := sharp_left_crossing_sign hk hs
  by_contra h
  have hle : crossingCos κ s ≤ (-1 / 200 : ℝ) := le_of_not_gt h
  have hm := (crossing_global_strictMono hk hs').monotoneOn
    (show crossingCos κ s ∈ Icc (-1 : ℝ) 1 from ⟨hu.1.le, hu.2.le⟩)
    (show (-1 / 200 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hle
  linarith

theorem sharp_crossing_angle_bound {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (663 / 10000)) :
    0 < Real.arccos (crossingCos κ s) ∧
      Real.arccos (crossingCos κ s) ≤ (251 / 500) * Real.pi := by
  have hs' : s ∈ Icc (1 / 16 : ℝ) (1 / 8) := ⟨hs.1, by linarith [hs.2]⟩
  have hu := full_crossingCos_bounds hk hs'
  have hl := sharp_crossingCos_lower hk hs
  have hp := Real.pi_gt_three
  have hsin : (1 / 200 : ℝ) ≤ Real.sin (3 / 500) := by
    have h := Real.sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 3 / 500)
    norm_num at h
    linarith
  have ha : Real.arcsin (1 / 200) ≤ (3 / 500 : ℝ) :=
    (Real.arcsin_le_iff_le_sin (by norm_num)
      ⟨by linarith, by linarith⟩).mpr hsin
  have hm := Real.arcsin_le_arcsin hl.le
  simp only [neg_div, Real.arcsin_neg] at hm
  refine ⟨Real.arccos_pos.mpr hu.2, ?_⟩
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

/-- A tangent line to 1/s gives an exact, integrable lower bound on the
whole interval. The integrated rational constant is 19/322. -/
theorem sharp_inner_integral_lower {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000)) :
    (19 / 322 : ℝ) / ((251 / 500) * Real.pi) ≤
      ∫ s in (1 / 16 : ℝ)..(663 / 10000 : ℝ),
        1 / (s * Real.arccos (crossingCos κ s)) := by
  let m : ℝ := 161 / 2500
  let A : ℝ := (251 / 500) * Real.pi
  have hm : 0 < m := by norm_num [m]
  have hA : 0 < A := by dsimp [A]; positivity
  have hm2 : 0 < m ^ 2 := pow_pos hm 2
  have hminor : Continuous (fun s : ℝ => (2 * m - s) / (m ^ 2 * A)) := by fun_prop
  have hmi : IntervalIntegrable (fun s : ℝ => (2 * m - s) / (m ^ 2 * A))
      volume (1 / 16) (663 / 10000) := hminor.intervalIntegrable _ _
  have hc : ContinuousOn (fun s => 1 / (s * Real.arccos (crossingCos κ s)))
      (Icc (1 / 16) (663 / 10000)) :=
    (full_integrand_continuousOn hk).mono (fun _ hs => ⟨hs.1, by linarith [hs.2]⟩)
  have hci : IntervalIntegrable (fun s => 1 / (s * Real.arccos (crossingCos κ s)))
      volume (1 / 16) (663 / 10000) :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hc
  have hbound : ∀ s ∈ Icc (1 / 16 : ℝ) (663 / 10000),
      (2 * m - s) / (m ^ 2 * A) ≤ 1 / (s * Real.arccos (crossingCos κ s)) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have ha := sharp_crossing_angle_bound hk hs
    have ht : (2 * m - s) / m ^ 2 ≤ 1 / s := by
      apply (div_le_div_iff₀ hm2 hs0).2
      nlinarith only [sq_nonneg (s - m)]
    calc
      (2 * m - s) / (m ^ 2 * A) = ((2 * m - s) / m ^ 2) / A := by rw [div_div]
      _ ≤ (1 / s) / A := div_le_div_of_nonneg_right ht hA.le
      _ = 1 / (s * A) := by rw [div_div]
      _ ≤ 1 / (s * Real.arccos (crossingCos κ s)) :=
        one_div_le_one_div_of_le (mul_pos hs0 ha.1)
          (mul_le_mul_of_nonneg_left ha.2 hs0.le)
  have hi := intervalIntegral.integral_mono_on
    (by norm_num : (1 / 16 : ℝ) ≤ 663 / 10000) hmi hci hbound
  have hlin : (∫ s in (1 / 16 : ℝ)..(663 / 10000 : ℝ),
      (2 * m - s) / (m ^ 2 * A)) = (19 / 322 : ℝ) / A := by
    rw [intervalIntegral.integral_div_const]
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 * m)
        volume (1 / 16) (663 / 10000))
      (continuous_id.intervalIntegrable (1 / 16 : ℝ) (663 / 10000))]
    norm_num [intervalIntegral.integral_const, intervalIntegral.integral_id, smul_eq_mul, m]
      <;> field_simp [hA.ne'] <;> ring
  rw [hlin] at hi
  exact hi

private theorem sharp_log_two_bound : Real.log 2 < (7 / 10 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 10) 4
  norm_num [Finset.sum_range_succ] at h
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr
  linarith

/-- A rigorous lower bound for the full model coefficient, including
the full unique terminal endpoint supplied by `unique_model_endpoint`. -/
theorem fullModelCoefficient_gt_third {κ r : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hr : r ∈ Icc (663 / 10000 : ℝ) (1 / 8)) :
    (1 / 3 : ℝ) < fullModelCoefficient κ r := by
  have hab : (1 / 16 : ℝ) ≤ r := by linarith [hr.1]
  have hc : ContinuousOn (fun s => 1 / (s * Real.arccos (crossingCos κ s)))
      (Icc (1 / 16) r) :=
    (full_integrand_continuousOn hk).mono (fun _ hs => ⟨hs.1, hs.2.trans hr.2⟩)
  have hi : IntervalIntegrable (fun s => 1 / (s * Real.arccos (crossingCos κ s)))
      volume (1 / 16) r := ContinuousOn.intervalIntegrable_of_Icc hab hc
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (1 / 16 : ℝ) r)]
      (fun s => 1 / (s * Real.arccos (crossingCos κ s))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Icc (1 / 16 : ℝ) (1 / 8) := ⟨hs.1.le, hs.2.trans hr.2⟩
    have ha : 0 < Real.arccos (crossingCos κ s) :=
      Real.arccos_pos.mpr (full_crossingCos_bounds hk hs').2
    have hs0 : 0 < s := by linarith [hs.1]
    positivity
  have hmon := intervalIntegral.integral_mono_interval
    (le_refl (1 / 16 : ℝ)) (by norm_num : (1 / 16 : ℝ) ≤ 663 / 10000) hr.1 hn hi
  have hlow := (sharp_inner_integral_lower hk).trans hmon
  have hp : 0 < Real.pi := Real.pi_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfac : 0 ≤ 2 * Real.pi / Real.log 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hlow hfac
  have he : (2 * Real.pi / Real.log 2) *
      ((19 / 322 : ℝ) / ((251 / 500) * Real.pi)) =
      (9500 / 40411 : ℝ) / Real.log 2 := by
    field_simp [hp.ne', hl.ne'] <;> ring
  rw [he] at hm
  have hstrict : (1 / 3 : ℝ) < (9500 / 40411 : ℝ) / Real.log 2 := by
    apply (lt_div_iff₀ hl).2
    have hlog := sharp_log_two_bound
    linarith
  exact hstrict.trans_le hm

/-- The distinguished parameter and terminal endpoint are both
constructed, and their full candidate integral exceeds one third. -/
theorem exists_full_model_coefficient_gt_third :
    ∃ κ r : ℝ, κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000) ∧
      LoopsLimitingCrestParameter.relation κ = 0 ∧
      r ∈ Ioo (663 / 10000 : ℝ) (133 / 2000) ∧
      crestTerminal κ r = -1 ∧ (1 / 3 : ℝ) < fullModelCoefficient κ r := by
  obtain ⟨κ, hk, _⟩ := LoopsLimitingCrestParameter.exists_unique_limiting_parameter
  obtain ⟨r, hr, he, _, _⟩ := unique_model_endpoint hk.1
  have hr' : r ∈ Icc (663 / 10000 : ℝ) (1 / 8) := ⟨hr.1.le, by linarith [hr.2]⟩
  exact ⟨κ, r, hk.1, hk.2, hr, he, fullModelCoefficient_gt_third hk.1 hr'⟩

end
end LimitingCrest
