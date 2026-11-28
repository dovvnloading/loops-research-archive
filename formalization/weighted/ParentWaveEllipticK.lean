import ParentWaveEllipticIntegrals

/-!
# Complete elliptic integral form of the canonical period ratio

`K m` uses the parameter convention: the integrand is
`1 / sqrt(1-m*sin(theta)^2)`.  The two actual chart sides have parameters
`B/C` and `1-B/C`, respectively, with the same scale factor.
-/

namespace ParentWaveEllipticK

open Set MeasureTheory ParentWaveEllipticIntegrals

noncomputable section

/-- The complete elliptic integral of the first kind, with parameter `m`. -/
def K (m : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..Real.pi/2, (Real.sqrt (1-m*(Real.sin θ)^2))⁻¹

theorem horizontalIntegral_eq_K (B C : ℝ) (hC : 0 < C) :
    horizontalIntegral B C = (2/Real.sqrt C) * K (B/C) := by
  have he (θ : ℝ) : C-B*(Real.sin θ)^2 = C*(1-(B/C)*(Real.sin θ)^2) := by
    field_simp
  have hint (θ : ℝ) : 2 / Real.sqrt (C-B*(Real.sin θ)^2) =
      (2/Real.sqrt C) * (Real.sqrt (1-(B/C)*(Real.sin θ)^2))⁻¹ := by
    rw [he,Real.sqrt_mul hC.le]
    ring
  simp only [horizontalIntegral,hint,K,intervalIntegral.integral_const_mul]

theorem verticalIntegral_eq_horizontal (B C : ℝ) :
    verticalIntegral B C = horizontalIntegral (C-B) C := by
  have he (θ : ℝ) : B+(C-B)*(Real.sin (Real.pi/2-θ))^2 =
      C-(C-B)*(Real.sin θ)^2 := by
    rw [Real.sin_pi_div_two_sub]
    linear_combination (C-B) * (Real.sin_sq_add_cos_sq θ)
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => 2 / Real.sqrt (B+(C-B)*(Real.sin θ)^2)) (Real.pi/2)
      (a := (0:ℝ)) (b := Real.pi/2)
  simpa only [sub_self,sub_zero,he,horizontalIntegral,verticalIntegral] using h.symm

theorem verticalIntegral_eq_K (B C : ℝ) (hC : 0 < C) :
    verticalIntegral B C = (2/Real.sqrt C) * K (1-B/C) := by
  rw [verticalIntegral_eq_horizontal,horizontalIntegral_eq_K (C-B) C hC]
  congr 2
  field_simp

/-- The factor from rescaling the physical slit cancels in the literal
chart-period ratio used by the canonical parent width. -/
theorem ratio_eq_K (B C : ℝ) (hC : 0 < C) :
    verticalIntegral B C / (2*horizontalIntegral B C) =
      K (1-B/C) / (2*K (B/C)) := by
  rw [horizontalIntegral_eq_K B C hC,verticalIntegral_eq_K B C hC]
  have hn : 2/Real.sqrt C ≠ 0 := div_ne_zero (by norm_num) (Real.sqrt_pos.mpr hC).ne'
  rw [show 2*(2/Real.sqrt C*K (B/C)) = (2/Real.sqrt C)*(2*K (B/C)) by ring]
  exact mul_div_mul_left _ _ hn

end
end ParentWaveEllipticK

