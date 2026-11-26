import QuadraticEscape
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Actual quadratic bounded-orbit and derivative bounds.
No symbolic realization or unproved complex-dynamical input is assumed. -/
namespace QuadraticEscape

noncomputable section

theorem norm_step_lower (c z : ℂ) : ‖z‖ ^ 2 ≤ ‖z^2+c‖ + ‖c‖ := by
  calc
    ‖z‖ ^ 2 = ‖(z^2+c)-c‖ := by rw [add_sub_cancel_right, norm_pow]
    _ ≤ _ := norm_sub_le _ _

/-- Escape outside both the radius two and the parameter radius. -/
theorem escape_pos_of_large (c z : ℂ) (hz : 2 < ‖z‖)
    (hc : ‖c‖ ≤ ‖z‖) : 0 < escape c z := by
  by_contra h
  have hzero : escape c z = 0 :=
    le_antisymm (le_of_not_gt h) (escape_nonneg c z)
  have hgrowth (n : ℕ) :
      ‖z‖ + (n : ℝ) * (‖z‖-2) ≤ ‖orbit c n z‖ := by
    induction n with
    | zero => simp [orbit]
    | succ n ih =>
      have hnn : 0 ≤ (n : ℝ) * (‖z‖-2) := by positivity
      have hr : ‖z‖ ≤ ‖orbit c n z‖ := by linarith only [ih, hnn]
      have hr2 : 2 ≤ ‖orbit c n z‖ := (le_of_lt hz).trans hr
      have hprod : 0 ≤ (‖orbit c n z‖-2)*(‖orbit c n z‖-1) :=
        mul_nonneg (by linarith) (by linarith)
      have hs := norm_step_lower c (orbit c n z)
      simp only [orbit, Nat.cast_succ]
      nlinarith only [ih, hr, hc, hs, hprod]
  obtain ⟨n, hn⟩ := exists_nat_gt ((1+‖c‖)/(‖z‖-2))
  have hgt : 1+‖c‖ < (n : ℝ)*(‖z‖-2) :=
    (div_lt_iff₀ (sub_pos.mpr hz)).mp hn
  have hb := escape_zero_orbit_bound c z hzero n
  linarith only [hgrowth n, hgt, hb, norm_nonneg z]

/-- The true critical bounded-orbit parameter locus lies in the radius-two disk. -/
theorem parameter_norm_le_two (c : ℂ) (hc : parameterEscape c = 0) :
    ‖c‖ ≤ 2 := by
  by_contra h
  have hp := escape_pos_of_large c c (lt_of_not_ge h) le_rfl
  change escape c c = 0 at hc
  linarith

theorem bounded_point_norm_le_two (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) : ‖z‖ ≤ 2 := by
  by_contra h
  have hlt : 2 < ‖z‖ := lt_of_not_ge h
  have hp := escape_pos_of_large c z hlt (hc.trans hlt.le)
  linarith

theorem bounded_orbit_norm_le_two (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) (n : ℕ) : ‖orbit c n z‖ ≤ 2 := by
  apply bounded_point_norm_le_two c _ hc
  rw [escape_iterate, hz, mul_zero]

/-- The parameter-dependent squared radius improves the uniform disk bound. -/
theorem bounded_orbit_norm_sq (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) (n : ℕ) :
    ‖orbit c n z‖ ^ 2 ≤ 2 + ‖c‖ := by
  have h := norm_step_lower c (orbit c n z)
  have hb := bounded_orbit_norm_le_two c z hc hz (n+1)
  rw [orbit] at hb
  linarith only [h,hb]

/-- The derivative of the actual n-fold quadratic iterate, not an abstract product. -/
def multiplier (c z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => 2 * orbit c n z * multiplier c z n

theorem orbit_hasDerivAt (c z : ℂ) (n : ℕ) :
    HasDerivAt (orbit c n) (multiplier c z n) z := by
  induction n with
  | zero => simpa only [orbit, multiplier] using (hasDerivAt_id z)
  | succ n ih =>
    simpa only [orbit, multiplier, Nat.reduceSub, pow_one, Nat.cast_ofNat,
      Pi.pow_apply] using (ih.pow 2).add_const c

theorem multiplier_eq_deriv (c z : ℂ) (n : ℕ) :
    deriv (orbit c n) z = multiplier c z n :=
  (orbit_hasDerivAt c z n).deriv

theorem multiplier_norm_bound (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) (n : ℕ) :
    ‖multiplier c z n‖ ≤ (4 : ℝ)^n := by
  induction n with
  | zero => simp [multiplier]
  | succ n ih =>
    have hb := bounded_orbit_norm_le_two c z hc hz n
    have hf : 2 * ‖orbit c n z‖ ≤ 4 := by linarith
    rw [multiplier, norm_mul, norm_mul, Complex.norm_two, pow_succ]
    exact mul_le_mul hf ih (norm_nonneg _) (by norm_num) |>.trans_eq (mul_comm _ _)

theorem deriv_norm_bound (c z : ℂ) (hc : parameterEscape c = 0)
    (hz : escape c z = 0) (n : ℕ) : ‖deriv (orbit c n) z‖ ≤ (4:ℝ)^n := by
  rw [multiplier_eq_deriv]
  exact multiplier_norm_bound c z (parameter_norm_le_two c hc) hz n

end
end QuadraticEscape
