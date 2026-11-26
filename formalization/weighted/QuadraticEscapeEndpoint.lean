import QuadraticEscapeHolder
import QuadraticEscapeSharpness

/-!
# Characterization of the exceptional square-root endpoint

Among the actual bounded-critical-orbit parameters, minus two is exactly
the parameter at which no local power upper bound has exponent above one
half. This is an escape-potential theorem, not a parameter-fiber theorem.
-/

namespace QuadraticEscape

/-- A local power upper bound for the existing critical-value potential. -/
def HasBoundaryPowerBound (c : ℂ) (α : ℝ) : Prop :=
  ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ d : ℂ,
    ‖d - c‖ < r → parameterEscape d ≤ C * ‖d - c‖ ^ α

/-- Exactly one bounded-critical-orbit parameter prevents improvement of
the square-root exponent in a local power upper bound. -/
theorem parameter_escape_improves_half_iff (c : ℂ) (hc : parameterEscape c = 0) :
    (∃ α : ℝ, 1 / 2 < α ∧ HasBoundaryPowerBound c α) ↔ c ≠ -2 := by
  constructor
  · rintro ⟨α, hα, C, r, hC, hr, hb⟩ hceq
    subst c
    obtain ⟨d, _, hd, hbad⟩ := parameter_escape_no_holder_above_half α C r hα hr
    have hgood := hb d (by simpa only [sub_neg_eq_add] using hd)
    simp only [sub_neg_eq_add] at hgood
    exact (not_lt_of_ge hgood) hbad
  · intro hne
    let α : ℝ := Real.log 2 / Real.log (4 - ‖c + 2‖ ^ 2 / 576)
    refine ⟨α, parameter_escape_exponent_gt_half c hc hne,
      4 * Real.log 4 * (2 : ℝ) ^ α, 1 / 2, ?_, by norm_num, ?_⟩
    · exact mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
        (Real.rpow_pos_of_pos (by norm_num) α)
    · intro d hd
      have h := parameter_escape_holder c d hc hd.le
      change parameterEscape d ≤ 4 * Real.log 4 * (2 * ‖d - c‖) ^ α at h
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)] at h
      simpa only [mul_assoc] using h

/-- Matching square-root bounds on an entire actual real exterior interval. -/
theorem negative_real_escape_two_sided (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    (Real.log 2) ^ 2 / 64 * ε ≤ (parameterEscape ((-2 - ε : ℝ) : ℂ)) ^ 2 ∧
    (parameterEscape ((-2 - ε : ℝ) : ℂ)) ^ 2 ≤ 32 * (Real.log 4) ^ 2 * ε := by
  refine ⟨negative_real_escape_sq_lower ε hε (by linarith), ?_⟩
  have hd : ‖((-2 - ε : ℝ) : ℂ) - (-2)‖ = ε := by
    have he : ((-2 - ε : ℝ) : ℂ) - (-2) = -(ε : ℂ) := by
      push_cast
      ring
    rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have h := parameter_escape_half_holder_sq (-2) ((-2 - ε : ℝ) : ℂ)
    chebyshev_parameter_escape_zero (by simpa only [hd] using hεhalf)
  simpa only [hd] using h

end QuadraticEscape
