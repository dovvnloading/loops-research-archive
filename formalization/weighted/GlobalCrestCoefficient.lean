import GlobalCrestCrossing
import CrestIntegralLimit

/-!
# A quantitative radial coefficient at every large return period

The complete actual collar contains a fixed inner radial interval.
Its actual crossing angles, rather than a limit formula, give a uniform
integrable minorant. The source normalization then gives a strict one-third
bound already at every return index at least seventeen.

This quantity is the archive's selected radial integral. No identification
with an unrestricted marked Wave optimum is asserted.
-/

namespace GlobalCrestCoefficient

open Set MeasureTheory
open NearTwoTip GlobalCrestCrossing CrestIntegralLimit
noncomputable section

/-- Restricting the globally chosen branch recovers the narrow angle band
throughout the endpoint window, independently of the return index. -/
theorem actual_angle_small {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ radiusInterval) :
    realAngle F s ∈ Ioo (-1/100 : ℝ) (1/100) := by
  have hs' : s ∈ Icc (1/16 : ℝ) (133/2000) := hs
  have hsG : s ∈ Radius := ⟨hs'.1,by linarith [hs'.2]⟩
  unfold realAngle
  rw [radiusProjection_eq hsG]
  exact (F.restrict hp hc).angle_mem ⟨s,hs'⟩

private theorem angle_cap {u : ℝ} (hu : u ∈ Icc (-1/100 : ℝ) (1/100)) :
    0 < Real.arccos u ∧ Real.arccos u ≤ (63/125)*Real.pi := by
  have hp := Real.pi_gt_three
  have hsin : (1/100 : ℝ) ≤ Real.sin (3/250) := by
    have h := Real.sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 3/250)
    norm_num at h
    linarith
  have ha : Real.arcsin (1/100) ≤ (3/250 : ℝ) :=
    (Real.arcsin_le_iff_le_sin (by norm_num)
      ⟨by linarith,by linarith⟩).mpr hsin
  have hm := Real.arcsin_le_arcsin hu.1
  simp only [neg_div,Real.arcsin_neg] at hm
  refine ⟨Real.arccos_pos.mpr (by linarith [hu.2]),?_⟩
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

/-- The actual selected integrand is continuous on the complete endpoint
window, with a positive denominator at every radius. -/
theorem actual_integrand_continuousOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    ContinuousOn (radialIntegrand (realAngle F)) radiusInterval := by
  apply radialIntegrand_continuousOn (realAngle_continuous F).continuousOn
  intro s hs
  have h := actual_angle_small hp hc F hs
  exact ⟨h.1.le,h.2.le⟩

/-- An exact affine minorant integrates to a period-independent positive
lower bound for the actual, whole inner-interval radial integral. -/
theorem actual_inner_integral_lower {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    (19/322 : ℝ)/((63/125)*Real.pi) ≤
      ∫ s in (1/16 : ℝ)..(663/10000 : ℝ), radialIntegrand (realAngle F) s := by
  let m : ℝ := 161/2500
  let A : ℝ := (63/125)*Real.pi
  have hm : 0 < m := by norm_num [m]
  have hA : 0 < A := by dsimp [A]; positivity
  have hm2 : 0 < m^2 := pow_pos hm 2
  have hminor : Continuous (fun s : ℝ => (2*m-s)/(m^2*A)) := by fun_prop
  have hmi : IntervalIntegrable (fun s : ℝ => (2*m-s)/(m^2*A))
      volume (1/16) (663/10000) := hminor.intervalIntegrable _ _
  have hcont : ContinuousOn (radialIntegrand (realAngle F))
      (Icc (1/16) (663/10000)) :=
    (actual_integrand_continuousOn hp hc F).mono
      (fun _ hs => ⟨hs.1,by linarith [hs.2]⟩)
  have hci : IntervalIntegrable (radialIntegrand (realAngle F))
      volume (1/16) (663/10000) :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hcont
  have hbound : ∀ s ∈ Icc (1/16 : ℝ) (663/10000),
      (2*m-s)/(m^2*A) ≤ radialIntegrand (realAngle F) s := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hang := actual_angle_small hp hc F
      (show s ∈ radiusInterval from ⟨hs.1,by linarith [hs.2]⟩)
    have ha := angle_cap ⟨hang.1.le,hang.2.le⟩
    have ht : (2*m-s)/m^2 ≤ 1/s := by
      apply (div_le_div_iff₀ hm2 hs0).2
      nlinarith only [sq_nonneg (s-m)]
    calc
      (2*m-s)/(m^2*A) = ((2*m-s)/m^2)/A := by rw [div_div]
      _ ≤ (1/s)/A := div_le_div_of_nonneg_right ht hA.le
      _ = 1/(s*A) := by rw [div_div]
      _ ≤ radialIntegrand (realAngle F) s :=
        one_div_le_one_div_of_le (mul_pos hs0 ha.1)
          (mul_le_mul_of_nonneg_left ha.2 hs0.le)
  have hi := intervalIntegral.integral_mono_on
    (by norm_num : (1/16 : ℝ) ≤ 663/10000) hmi hci hbound
  have hlin : (∫ s in (1/16 : ℝ)..(663/10000 : ℝ),
      (2*m-s)/(m^2*A)) = (19/322 : ℝ)/A := by
    rw [intervalIntegral.integral_div]
    rw [intervalIntegral.integral_sub (g := fun s : ℝ => s)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2*m)
        volume (1/16) (663/10000))
      (continuous_id.intervalIntegrable (1/16 : ℝ) (663/10000))]
    norm_num [intervalIntegral.integral_const,integral_id,smul_eq_mul,m]
      <;> field_simp [hA.ne'] <;> ring
  rw [hlin] at hi
  exact hi

private theorem log_two_lt : Real.log 2 < (7/10 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7/10) 4
  norm_num [Finset.sum_range_succ] at h
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr
  linarith

/-- The original finite-period parent normalization is positive and
strictly below the common logarithmic upper bound. -/
theorem parent_log_bounds {p : ℕ} (hp : 17 ≤ p) :
    0 < Real.log (2-2/(p : ℝ)) ∧ Real.log (2-2/(p : ℝ)) < 7/10 := by
  have hpR : (17 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hdiv : 2/(p : ℝ) < 1 := (div_lt_one hp0).2 (by linarith)
  have hb : 1 < 2-2/(p : ℝ) := by linarith
  have hb2 : 2-2/(p : ℝ) < 2 := by
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) hp0]
  refine ⟨Real.log_pos hb,?_⟩
  exact (Real.log_lt_log (by linarith : (0 : ℝ) < 2-2/(p : ℝ)) hb2).trans log_two_lt

/-- Every actual complete collar at every return index at least seventeen
has selected radial coefficient strictly above one third. No asymptotic
threshold or limiting-coefficient premise is used. -/
theorem actual_radialCoefficient_gt_third {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hr : r ∈ Icc (663/10000 : ℝ) (133/2000)) :
    (1/3 : ℝ) < radialCoefficient p (realAngle F) r := by
  have hab : (1/16 : ℝ) ≤ r := by linarith [hr.1]
  have hcont : ContinuousOn (radialIntegrand (realAngle F)) (Icc (1/16) r) :=
    (actual_integrand_continuousOn hp hc F).mono
      (fun _ hs => ⟨hs.1,hs.2.trans hr.2⟩)
  have hi : IntervalIntegrable (radialIntegrand (realAngle F)) volume (1/16) r :=
    ContinuousOn.intervalIntegrable_of_Icc hab hcont
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (1/16 : ℝ) r)]
      radialIntegrand (realAngle F) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ radiusInterval := ⟨hs.1.le,hs.2.trans hr.2⟩
    have hang := actual_angle_small hp hc F hs'
    have ha : 0 < Real.arccos (realAngle F s) :=
      Real.arccos_pos.mpr (by linarith [hang.2])
    have hs0 : 0 < s := by linarith [hs.1]
    dsimp [radialIntegrand]
    positivity
  have hmon := intervalIntegral.integral_mono_interval
    (le_refl (1/16 : ℝ)) (by norm_num : (1/16 : ℝ) ≤ 663/10000) hr.1 hn hi
  have hlow := (actual_inner_integral_lower hp hc F).trans hmon
  have hpi : 0 < Real.pi := Real.pi_pos
  have hl := (parent_log_bounds hp).1
  have hfac : 0 ≤ 2*Real.pi/Real.log (2-2/(p : ℝ)) := by positivity
  have hm := mul_le_mul_of_nonneg_left hlow hfac
  have he : (2*Real.pi/Real.log (2-2/(p : ℝ))) *
      ((19/322 : ℝ)/((63/125)*Real.pi)) =
        (2375/10143 : ℝ)/Real.log (2-2/(p : ℝ)) := by
    field_simp [hpi.ne',hl.ne'] <;> ring
  rw [he] at hm
  have hstrict : (1/3 : ℝ) < (2375/10143 : ℝ)/Real.log (2-2/(p : ℝ)) := by
    apply (lt_div_iff₀ hl).2
    have hlog := (parent_log_bounds hp).2
    linarith
  exact hstrict.trans_le hm

end
end GlobalCrestCoefficient
