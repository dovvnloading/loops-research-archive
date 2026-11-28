import ParentWaveEllipticSides
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Regular elliptic integrals of the actual rectangle sides -/

namespace ParentWaveEllipticIntegrals

open Set MeasureTheory ParentWaveElliptic ParentWaveEllipticSides
noncomputable section

def horizontalIntegral (B C : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..Real.pi/2, 2 / Real.sqrt (C-B*(Real.sin θ)^2)

def verticalIntegral (B C : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..Real.pi/2, 2 / Real.sqrt (B+(C-B)*(Real.sin θ)^2)

theorem horizontal_integrand_continuous (B C : ℝ) (hB : 0 < B) (hBC : B < C) :
    Continuous (fun θ : ℝ => 2 / Real.sqrt (C-B*(Real.sin θ)^2)) := by
  apply continuous_const.div
    ((continuous_const.sub (continuous_const.mul (Real.continuous_sin.pow 2))).sqrt)
  intro θ
  have hs : (Real.sin θ)^2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg (Real.cos θ)]
  apply (Real.sqrt_pos.mpr ?_).ne'
  change 0 < C-B*(Real.sin θ)^2
  nlinarith [mul_le_mul_of_nonneg_left hs hB.le]

theorem vertical_integrand_continuous (B C : ℝ) (hB : 0 < B) (hBC : B < C) :
    Continuous (fun θ : ℝ => 2 / Real.sqrt (B+(C-B)*(Real.sin θ)^2)) := by
  apply continuous_const.div
    ((continuous_const.add (continuous_const.mul (Real.continuous_sin.pow 2))).sqrt)
  intro θ
  apply (Real.sqrt_pos.mpr ?_).ne'
  change 0 < B+(C-B)*(Real.sin θ)^2
  nlinarith [mul_nonneg (sub_pos.mpr hBC).le (sq_nonneg (Real.sin θ))]

theorem horizontal_side_eq_integral (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} (hG : ∀ t ∈ quadrant,HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    (E 0).re - (E (Real.sqrt B:ℂ)).re = horizontalIntegral B C := by
  let φ : ℝ → ℝ := fun θ => Real.sqrt B * Real.sin θ
  let f : ℝ → ℝ := fun θ => (E (φ θ:ℂ)).re
  have hφ : Continuous φ := by dsimp [φ]; fun_prop
  have hf : ContinuousOn f (Icc 0 (Real.pi/2)) := by
    apply Complex.continuous_re.comp_continuousOn
    apply hE.comp (Complex.continuous_ofReal.comp hφ).continuousOn
    intro θ hθ
    rw [closure_quadrant]
    exact ⟨mul_nonneg (Real.sqrt_nonneg B)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1,by linarith [hθ.2,Real.pi_pos]⟩),by simp⟩
  have hd : ∀ θ ∈ Ioo 0 (Real.pi/2), HasDerivAt f
      (-(2 / Real.sqrt (C-B*(Real.sin θ)^2))) θ := by
    intro θ hθ
    have hs := Real.sin_pos_of_mem_Ioo (show θ ∈ Ioo 0 Real.pi from ⟨hθ.1,by linarith [hθ.2,Real.pi_pos]⟩)
    have hc := Real.cos_pos_of_mem_Ioo (show θ ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩)
    have hb := Real.sqrt_pos.mpr hB
    have hp : φ θ ^ 2 = B*(Real.sin θ)^2 := by
      dsimp [φ]
      rw [mul_pow,Real.sq_sqrt hB.le]
    have hs1 : (Real.sin θ)^2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq θ,sq_pos_of_pos hc]
    have hpB : φ θ ^ 2 < B := by rw [hp]; nlinarith [mul_lt_mul_of_pos_left hs1 hB]
    have hpC := hpB.trans hBC
    have hp0 : 0 < φ θ := mul_pos hb hs
    have htrace := real_trace_hasDerivAt B C hG hE hGE hp0 hpB.ne hpC.ne
    rw [differential_real_first B C (φ θ) hpB hpC] at htrace
    have hr : HasDerivAt (fun s : ℝ => (E (s:ℂ)).re)
        (-(2/(Real.sqrt (B-(φ θ)^2)*Real.sqrt (C-(φ θ)^2)))) (φ θ) := by
      simpa only [Function.comp_def,Complex.reCLM_apply,Complex.neg_re,Complex.ofReal_re]
        using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt (φ θ) htrace
    have hsqrt : Real.sqrt (B-(φ θ)^2) = Real.sqrt B * Real.cos θ := by
      have he : B-(φ θ)^2 = B*(Real.cos θ)^2 := by
        rw [hp]
        linear_combination -B * (Real.sin_sq_add_cos_sq θ)
      rw [he,Real.sqrt_mul hB.le,Real.sqrt_sq hc.le]
    convert! hr.comp θ ((Real.hasDerivAt_sin θ).const_mul (Real.sqrt B)) using 1
    rw [hsqrt,hp]
    field_simp [hb.ne',hc.ne']
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by positivity : (0:ℝ) ≤ Real.pi/2) hf hd
    ((horizontal_integrand_continuous B C hB hBC).neg.intervalIntegrable _ _)
  simp only [f,φ,Real.sin_pi_div_two,Real.sin_zero,mul_one,mul_zero,
    Complex.ofReal_zero,intervalIntegral.integral_neg] at hi
  dsimp [horizontalIntegral]
  linarith

theorem vertical_side_eq_integral (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {G E : ℂ → ℂ} (hG : ∀ t ∈ quadrant,HasDerivAt G (differential B C t) t)
    (hE : ContinuousOn E (closure quadrant)) (hGE : EqOn G E quadrant) :
    (E (Real.sqrt B:ℂ)).im - (E (Real.sqrt C:ℂ)).im = verticalIntegral B C := by
  let φ : ℝ → ℝ := fun θ => Real.sqrt (B+(C-B)*(Real.sin θ)^2)
  let f : ℝ → ℝ := fun θ => (E (φ θ:ℂ)).im
  have hφ : Continuous φ := by dsimp [φ]; fun_prop
  have harg (θ : ℝ) : 0 < B+(C-B)*(Real.sin θ)^2 := by
    nlinarith [mul_nonneg (sub_pos.mpr hBC).le (sq_nonneg (Real.sin θ))]
  have hsq (θ : ℝ) : φ θ ^ 2 = B+(C-B)*(Real.sin θ)^2 :=
    Real.sq_sqrt (harg θ).le
  have hf : ContinuousOn f (Icc 0 (Real.pi/2)) := by
    apply Complex.continuous_im.comp_continuousOn
    apply hE.comp (Complex.continuous_ofReal.comp hφ).continuousOn
    intro θ _
    rw [closure_quadrant]
    exact ⟨Real.sqrt_nonneg _,by simp⟩
  have hd : ∀ θ ∈ Ioo 0 (Real.pi/2), HasDerivAt f
      (-(2 / Real.sqrt (B+(C-B)*(Real.sin θ)^2))) θ := by
    intro θ hθ
    have hs := Real.sin_pos_of_mem_Ioo (show θ ∈ Ioo 0 Real.pi from
      ⟨hθ.1,by linarith [hθ.2,Real.pi_pos]⟩)
    have hc := Real.cos_pos_of_mem_Ioo (show θ ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩)
    have hD := sub_pos.mpr hBC
    have hrD := Real.sqrt_pos.mpr hD
    have hp0 : 0 < φ θ := Real.sqrt_pos.mpr (harg θ)
    have hpB : B < φ θ ^ 2 := by rw [hsq]; nlinarith [mul_pos hD (sq_pos_of_pos hs)]
    have hs1 : (Real.sin θ)^2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq θ,sq_pos_of_pos hc]
    have hpC : φ θ ^ 2 < C := by rw [hsq]; nlinarith [mul_lt_mul_of_pos_left hs1 hD]
    have htrace := real_trace_hasDerivAt B C hG hE hGE hp0 hpB.ne' hpC.ne
    rw [differential_real_middle B C (φ θ) hpB hpC] at htrace
    have hr : HasDerivAt (fun s : ℝ => (E (s:ℂ)).im)
        (-(2/(Real.sqrt ((φ θ)^2-B)*Real.sqrt (C-(φ θ)^2)))) (φ θ) := by
      simpa only [Function.comp_def,Complex.imCLM_apply,Complex.mul_im,
        Complex.neg_im,Complex.neg_re,Complex.ofReal_im,Complex.ofReal_re,
        Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
        using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt (φ θ) htrace
    have hleft : Real.sqrt ((φ θ)^2-B) = Real.sqrt (C-B)*Real.sin θ := by
      rw [hsq,add_sub_cancel_left,Real.sqrt_mul hD.le,Real.sqrt_sq hs.le]
    have hright : Real.sqrt (C-(φ θ)^2) = Real.sqrt (C-B)*Real.cos θ := by
      have he : C-(φ θ)^2 = (C-B)*(Real.cos θ)^2 := by
        rw [hsq]
        linear_combination -(C-B) * (Real.sin_sq_add_cos_sq θ)
      rw [he,Real.sqrt_mul hD.le,Real.sqrt_sq hc.le]
    have hφd : HasDerivAt φ
        ((C-B)*Real.sin θ*Real.cos θ / φ θ) θ := by
      convert! (((Real.hasDerivAt_sin θ).pow 2).const_mul (C-B)).const_add B
        |>.sqrt (harg θ).ne' using 1
      dsimp [φ]
      ring
    convert! hr.comp θ hφd using 1
    rw [hleft,hright]
    change -(2 / φ θ) = _
    rw [show C-B = (Real.sqrt (C-B))^2 from (Real.sq_sqrt hD.le).symm]
    rw [Real.sqrt_sq hrD.le]
    field_simp [hrD.ne',hs.ne',hc.ne',hp0.ne']
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by positivity : (0:ℝ) ≤ Real.pi/2) hf hd
    ((vertical_integrand_continuous B C hB hBC).neg.intervalIntegrable _ _)
  simp only [f,φ,Real.sin_pi_div_two,Real.sin_zero,one_pow,zero_pow (by decide : (2:ℕ) ≠ 0),
    mul_one,mul_zero,add_zero,add_sub_cancel,intervalIntegral.integral_neg] at hi
  dsimp [verticalIntegral]
  linarith

end
end ParentWaveEllipticIntegrals

