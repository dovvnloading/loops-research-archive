import QuadraticExtremalMultiplier
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit boundary exponents for the actual quadratic escape potential

The finite nonlinear shadowing estimate is converted at its exact growth
base to a real-power modulus. Its exponent improves strictly on one half
at every bounded-critical-orbit parameter other than the Chebyshev endpoint.
-/

namespace QuadraticEscape

noncomputable section

/-- The exponent associated with any admissible orbit-growth base is positive. -/
theorem growth_exponent_pos {A : ℝ} (hA : 3 ≤ A) :
    0 < Real.log 2 / Real.log A := by
  exact div_pos (Real.log_pos (by norm_num))
    (Real.log_pos (by linarith))

/-- A growth base strictly below four gives an exponent strictly above one half. -/
theorem growth_exponent_gt_half {A : ℝ} (hA : 3 ≤ A) (hA4 : A < 4) :
    (1 / 2 : ℝ) < Real.log 2 / Real.log A := by
  have hlog : 0 < Real.log A := Real.log_pos (by linarith)
  have hlt : Real.log A < Real.log 4 :=
    Real.log_lt_log (by linarith) hA4
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at hlt
  apply (lt_div_iff₀ hlog).mpr
  linarith

/-- The certified exponents stay in the range of ordinary Hölder moduli. -/
theorem growth_exponent_le_one {A : ℝ} (hA : 3 ≤ A) :
    Real.log 2 / Real.log A ≤ 1 := by
  apply (div_le_iff₀ (Real.log_pos (by linarith : 1 < A))).mpr
  simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (by linarith : (2 : ℝ) ≤ A)

private theorem growth_pow_ge_nat {A : ℝ} (hA : 3 ≤ A) (n : ℕ) :
    (n : ℝ) + 1 ≤ A ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm := mul_le_mul_of_nonneg_left
      (show (2 : ℝ) ≤ A by linarith) (pow_nonneg (by linarith : 0 ≤ A) n)
    nlinarith only [ih, hn, hm]

private theorem growth_scale_crossing {A ε : ℝ} (hA : 3 ≤ A)
    (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ n : ℕ, A ^ n * ε ≤ 1 ∧ 1 < A ^ (n + 1) * ε := by
  have hex : ∃ k : ℕ, 1 < A ^ k * ε := by
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    refine ⟨k, (div_lt_iff₀ he).mp ?_⟩
    linarith only [hk, growth_pow_ge_nat hA k]
  have hmin := Nat.find_spec hex
  cases h : Nat.find hex with
  | zero =>
    rw [h, pow_zero, one_mul] at hmin
    exact (not_lt_of_ge he1 hmin).elim
  | succ n =>
    refine ⟨n, ?_, ?_⟩
    · by_contra hh
      have hh' := Nat.find_min' hex (lt_of_not_ge hh)
      omega
    · simpa only [h] using hmin

private theorem growth_base_rpow {A : ℝ} (hA : 3 ≤ A) :
    A ^ (Real.log 2 / Real.log A) = (2 : ℝ) := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < A)]
  have hl : Real.log A ≠ 0 := (Real.log_pos (by linarith : 1 < A)).ne'
  rw [mul_div_cancel₀ _ hl, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem growth_nat_rpow {A : ℝ} (hA : 3 ≤ A) (n : ℕ) :
    (A ^ n) ^ (Real.log 2 / Real.log A) = (2 : ℝ) ^ n := by
  rw [← Real.rpow_natCast_mul (by linarith : 0 ≤ A), mul_comm,
    Real.rpow_mul_natCast (by linarith : 0 ≤ A), growth_base_rpow hA]

private theorem weight_two_pow (n : ℕ) : weight n * (2 : ℝ) ^ n = 1 := by
  unfold weight
  rw [← mul_pow]
  norm_num

/-- Convert the exact nonlinear growth scale to an explicit power law for
the actual critical-value potential. Both the parameter and its critical
value move, which accounts for the factor two inside the real power. -/
theorem parameter_escape_holder_of_growth (c d : ℂ)
    (hc : parameterEscape c = 0) {A : ℝ} (hA : 3 ≤ A) (hA4 : A ≤ 4)
    (hbase : ∀ j : ℕ, 2 * ‖orbit c j c‖ ≤ A) (hd : ‖d - c‖ ≤ 1 / 2) :
    parameterEscape d ≤
      4 * Real.log 4 * (2 * ‖d - c‖) ^ (Real.log 2 / Real.log A) := by
  by_cases hdc : d = c
  · subst d
    simp [hc, Real.zero_rpow (growth_exponent_pos hA).ne']
  · have he : 0 < 2 * ‖d - c‖ := by
      have := norm_pos_iff.mpr (sub_ne_zero.mpr hdc)
      positivity
    obtain ⟨n, hlo, hhi⟩ := growth_scale_crossing hA he (by linarith)
    have hg := parameter_escape_at_growth_scale c d hc hA hA4 hbase n hlo
    have hr := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) hhi
      (growth_exponent_pos hA)
    rw [Real.one_rpow,
      Real.mul_rpow (pow_nonneg (by linarith : 0 ≤ A) _) he.le,
      growth_nat_rpow hA (n + 1)] at hr
    have hm := mul_lt_mul_of_pos_left hr (weight_pos n)
    have hw : weight n < 2 * (2 * ‖d - c‖) ^ (Real.log 2 / Real.log A) := by
      calc
        weight n = weight n * 1 := (mul_one _).symm
        _ < weight n * ((2 : ℝ) ^ (n + 1) *
            (2 * ‖d - c‖) ^ (Real.log 2 / Real.log A)) := hm
        _ = (weight n * (2 : ℝ) ^ n) *
            (2 * (2 * ‖d - c‖) ^ (Real.log 2 / Real.log A)) := by
          rw [pow_succ]
          ring
        _ = 2 * (2 * ‖d - c‖) ^ (Real.log 2 / Real.log A) := by
          rw [weight_two_pow, one_mul]
    calc
      parameterEscape d ≤ weight n * (2 * Real.log 4) := hg
      _ ≤ (2 * (2 * ‖d - c‖) ^ (Real.log 2 / Real.log A)) *
          (2 * Real.log 4) :=
        mul_le_mul_of_nonneg_right hw.le
          (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
      _ = 4 * Real.log 4 * (2 * ‖d - c‖) ^ (Real.log 2 / Real.log A) := by ring

/-- An explicit parameter-dependent boundary exponent at every actual
bounded-critical-orbit parameter. -/
theorem parameter_escape_holder (c d : ℂ) (hc : parameterEscape c = 0)
    (hd : ‖d - c‖ ≤ 1 / 2) :
    parameterEscape d ≤ 4 * Real.log 4 *
      (2 * ‖d - c‖) ^ (Real.log 2 / Real.log (4 - ‖c + 2‖ ^ 2 / 576)) := by
  obtain ⟨hA, hA4, hbase⟩ := parameter_gap_base c hc
  exact parameter_escape_holder_of_growth c d hc hA hA4 hbase hd

/-- The explicit exponent improves on the universal one-half exponent
at every bounded-critical-orbit parameter other than minus two. -/
theorem parameter_escape_exponent_gt_half (c : ℂ)
    (hc : parameterEscape c = 0) (hne : c ≠ -2) :
    (1 / 2 : ℝ) < Real.log 2 / Real.log (4 - ‖c + 2‖ ^ 2 / 576) := by
  apply growth_exponent_gt_half (parameter_gap_base c hc).1
  have hn : 0 < ‖c + 2‖ := norm_pos_iff.mpr (by
    intro h
    apply hne
    linear_combination h)
  nlinarith [sq_pos_of_pos hn]

end
end QuadraticEscape
