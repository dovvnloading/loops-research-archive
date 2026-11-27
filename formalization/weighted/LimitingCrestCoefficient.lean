import Mathlib
import LimitingCrestGeometry

/-!
# A positive integral coefficient on the limiting quadratic collar

This coefficient is the explicit integral proposed in the crest asymptotics
note, restricted to a strictly interior radial interval. The theorem concerns
this analytic expression and the certified quadratic model. Its interpretation
as the limit of physical marked Wave widths requires a separate convergence
and marking theorem.
-/

namespace LimitingCrest

open Set MeasureTheory

noncomputable section

/-- The small algebraic solution of the circle/imaginary-axis equation. -/
def crossingCos (κ s : ℝ) : ℝ :=
  (3/2 - Real.sqrt (8/κ + 8*s^2 - 9/4)) / (4*s)

/-- The closed formula agrees with the unique small crossing for every
radius in the certified closed collar. -/
theorem crossingCos_spec {κ s : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hs : s ∈ Icc (63/1000) (33/500)) :
    crossingCos κ s ∈ Ioo (-1/100) (1/100) ∧
      crossing κ s (crossingCos κ s) = 0 := by
  obtain ⟨u, hu, _⟩ := crossing_root_unique hk hs
  have hk0 : κ ≠ 0 := by linarith [hk.1]
  have hs0 : s ≠ 0 := by linarith [hs.1]
  have hsu : s*u ≤ (33/500 : ℝ)*(1/100) := by
    calc
      s*u ≤ s*(1/100) :=
        mul_le_mul_of_nonneg_left hu.1.2.le (by linarith [hs.1])
      _ ≤ (33/500 : ℝ)*(1/100) :=
        mul_le_mul_of_nonneg_right hs.2 (by norm_num)
  have hpos : 0 ≤ (3/2 : ℝ)-4*s*u := by nlinarith
  have heq : 8/κ+8*s^2-9/4 = (3/2-4*s*u)^2 := by
    have hf := hu.2
    dsimp [crossing] at hf
    field_simp [hk0]
    nlinarith [hf]
  have hformula : crossingCos κ s = u := by
    unfold crossingCos
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg hpos]
    field_simp [hs0]
    ring
  rwa [hformula]

theorem crossingCos_continuousOn (κ : ℝ) :
    ContinuousOn (crossingCos κ) (Icc (63/1000) (33/500)) := by
  unfold crossingCos
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro s hs
    have : 0 < s := by linarith [hs.1]
    positivity

/-- An elementary exact angle bound; the constant deliberately has room
for perturbation of the selected angular root. -/
theorem small_crossing_angle_bound {u : ℝ}
    (hu : u ∈ Icc (-1/100) (1/100)) :
    0 < Real.arccos u ∧ Real.arccos u ≤ (51/100)*Real.pi := by
  have hp := Real.pi_gt_three
  have hsin : (1/100 : ℝ) ≤ Real.sin (1/50) := by
    have h := Real.sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1/50)
    norm_num at h
    linarith
  have ha : Real.arcsin (1/100) ≤ (1/50 : ℝ) :=
    (Real.arcsin_le_iff_le_sin (by norm_num)
      ⟨by linarith, by linarith⟩).mpr hsin
  have hm := Real.arcsin_le_arcsin hu.1
  simp only [neg_div, Real.arcsin_neg] at hm
  refine ⟨Real.arccos_pos.mpr (by linarith [hu.2]), ?_⟩
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

private theorem log_two_lt_seven_tenths : Real.log 2 < (7/10 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7/10) 4
  norm_num [Finset.sum_range_succ] at h
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr
  linarith

/-- The proposed normalized integral on the explicitly certified
subcollar. It is not an unrestricted canonical Wave supremum. -/
def selectedCoefficient (κ : ℝ) : ℝ :=
  (2*Real.pi/Real.log 2) *
    ∫ s in (63/1000 : ℝ)..(33/500 : ℝ),
      1/(s*Real.arccos (crossingCos κ s))

theorem selected_integrand_continuousOn {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) :
    ContinuousOn (fun s => 1/(s*Real.arccos (crossingCos κ s)))
      (Icc (63/1000) (33/500)) := by
  apply ContinuousOn.div continuousOn_const
  · exact continuousOn_id.mul (crossingCos_continuousOn κ).arccos
  · intro s hs
    have hroot := crossingCos_spec hk hs
    have ha := (small_crossing_angle_bound
      ⟨hroot.1.1.le, hroot.1.2.le⟩).1
    exact ne_of_gt (mul_pos (by linarith [hs.1]) ha)

/-- A whole-interval lower bound, with no quadrature, sampled radii,
assumed optimizer, or numerical value of pi or log two. -/
theorem selectedCoefficient_gt_quarter {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) :
    (1/4 : ℝ) < selectedCoefficient κ := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl7 := log_two_lt_seven_tenths
  let M : ℝ := (33/500)*(51/100)*Real.pi
  have hM : 0 < M := by dsimp [M]; positivity
  have hi := (selected_integrand_continuousOn hk).intervalIntegrable_of_Icc
    (by norm_num : (63/1000 : ℝ) ≤ 33/500)
  have hbound : ∀ s ∈ Icc (63/1000 : ℝ) (33/500),
      1/M ≤ 1/(s*Real.arccos (crossingCos κ s)) := by
    intro s hs
    have hroot := crossingCos_spec hk hs
    have ha := small_crossing_angle_bound ⟨hroot.1.1.le, hroot.1.2.le⟩
    have hspos : 0 < s := by linarith [hs.1]
    apply one_div_le_one_div_of_le (mul_pos hspos ha.1)
    calc
      s*Real.arccos (crossingCos κ s) ≤
          (33/500)*((51/100)*Real.pi) :=
        mul_le_mul hs.2 ha.2 ha.1.le (by norm_num)
      _ = M := by dsimp [M]; ring
  have hint := intervalIntegral.integral_mono_on
    (by norm_num : (63/1000 : ℝ) ≤ 33/500)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1/M)
      volume (63/1000) (33/500)) hi hbound
  have hint' : (3/1000 : ℝ)/M ≤
      ∫ s in (63/1000 : ℝ)..(33/500 : ℝ),
        1/(s*Real.arccos (crossingCos κ s)) := by
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hint
  have hcoef : (0 : ℝ) < 2*Real.pi/Real.log 2 := by positivity
  have hcompare := mul_le_mul_of_nonneg_left hint' hcoef.le
  have halgebra : (2*Real.pi/Real.log 2)*((3/1000)/M) =
      (100/561 : ℝ)/Real.log 2 := by
    dsimp [M]
    field_simp [ne_of_gt hp, ne_of_gt hl]
    <;> ring
  rw [halgebra] at hcompare
  have hquarter : (1/4 : ℝ) < (100/561 : ℝ)/Real.log 2 := by
    apply (lt_div_iff₀ hl).mpr
    linarith
  exact hquarter.trans_le hcompare

end
end LimitingCrest
