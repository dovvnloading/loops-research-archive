import QuadraticGreenPower

/-! A complex disk test of the regularized Jacobian partition at the actual
parabolic parameter one quarter. The cusp scaling is prior mathematical
context; this module supplies an all-horizon kernel-checked certificate. -/

namespace QuadraticEscape

open Set

noncomputable section

private theorem cusp_orbit_real (n : ℕ) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1/2 ∧
      orbit (1/4 : ℂ) n (1/4) = (x : ℂ) := by
  induction n with
  | zero =>
      refine ⟨1/4, by norm_num, by norm_num, ?_⟩
      norm_num [orbit]
  | succ n ih =>
      obtain ⟨x, hx0, hx1, hx⟩ := ih
      refine ⟨x^2+1/4, by positivity, ?_, ?_⟩
      · nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
      · simp only [orbit, hx]
        push_cast <;> ring

private theorem cusp_orbit_norm (n : ℕ) :
    ‖orbit (1/4 : ℂ) n (1/4)‖ ≤ 1/2 := by
  obtain ⟨x, hx0, hx1, hx⟩ := cusp_orbit_real n
  rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  exact hx1

private theorem cusp_response_bound (n : ℕ) :
    ∀ j ≤ n, regularizedResponse (1/4) (1/(2*((n:ℝ)+1))) j ≤
      2*((j:ℝ)+1) := by
  let ε : ℝ := 1/(2*((n:ℝ)+1))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hN : (n:ℝ)+1 ≠ 0 := by positivity
  have heq : (2*((n:ℝ)+1))*ε = 1 := by
    dsimp [ε]
    field_simp [hN] <;> ring
  intro j
  induction j with
  | zero =>
      intro _
      norm_num [regularizedResponse]
  | succ j ih =>
      intro hj
      have hi := ih (by omega)
      change regularizedResponse (1/4) ε j ≤ 2*((j:ℝ)+1) at hi
      have hJ : (j:ℝ)+1 ≤ (n:ℝ)+1 := by
        exact_mod_cast (Nat.succ_le_succ (Nat.le_of_succ_le hj))
      have hscale : 2*((j:ℝ)+1)*ε ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right hJ hε
        nlinarith only [h, heq]
      have ha : 2*‖orbit (1/4 : ℂ) j (1/4)‖ ≤ 1 := by
        linarith only [cusp_orbit_norm j]
      change (2*‖orbit (1/4 : ℂ) j (1/4)‖+ε) *
        regularizedResponse (1/4) ε j + 1 ≤ 2*((↑(j+1):ℝ)+1)
      calc
        _ ≤ (2*‖orbit (1/4 : ℂ) j (1/4)‖+ε) *
              (2*((j:ℝ)+1)) + 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hi (by positivity)) le_rfl
        _ ≤ (1+ε)*(2*((j:ℝ)+1))+1 :=
          add_le_add (mul_le_mul_of_nonneg_right
            (by linarith only [ha] : 2*‖orbit (1/4 : ℂ) j (1/4)‖+ε ≤ 1+ε)
            (by positivity)) le_rfl
        _ ≤ _ := by push_cast; nlinarith only [hscale]

/-- An all-horizon complex parameter disk has an exponentially small
actual Green value. The endpoint n=0 is included. -/
theorem cusp_green_disk (d : ℂ) (n : ℕ)
    (hd : ‖d-(1/4 : ℂ)‖ ≤ 1/(4*((n:ℝ)+1)^2)) :
    parameterEscape d ≤ weight n * Real.log (3/2) := by
  let N : ℝ := (n:ℝ)+1
  let ε : ℝ := 1/(2*N)
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [N]
    linarith only [hn]
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have heq : (2*N)*ε = 1 := by
    dsimp [ε]
    field_simp [hN.ne'] <;> ring
  have hεhalf : ε ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 2*N by linarith) hε
    nlinarith only [h, heq]
  have htest : ∀ j ≤ n,
      ‖d-(1/4 : ℂ)‖ * regularizedResponse (1/4) ε j ≤ ε := by
    intro j hj
    have hS := cusp_response_bound n j hj
    change regularizedResponse (1/4) ε j ≤ 2*((j:ℝ)+1) at hS
    have hJ : (j:ℝ)+1 ≤ N := by
      dsimp [N]
      exact_mod_cast Nat.succ_le_succ hj
    calc
      _ ≤ ‖d-(1/4 : ℂ)‖ * (2*((j:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hS (norm_nonneg _)
      _ ≤ ‖d-(1/4 : ℂ)‖ * (2*N) :=
        mul_le_mul_of_nonneg_left (by linarith only [hJ]) (norm_nonneg _)
      _ ≤ (1/(4*N^2))*(2*N) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ = ε := by
        dsimp [ε]
        field_simp [hN.ne'] <;> ring
  have hshadow := regularizedResponse_shadowing (1/4 : ℂ) d hε n htest
  have hdiff : ‖orbit d n d - orbit (1/4 : ℂ) n (1/4)‖ ≤ ε :=
    hshadow.trans (htest n le_rfl)
  have hlast : ‖orbit d n d‖ ≤ 1 := by
    calc
      _ = ‖(orbit d n d - orbit (1/4 : ℂ) n (1/4)) +
          orbit (1/4 : ℂ) n (1/4)‖ := by rw [sub_add_cancel]
      _ ≤ ‖orbit d n d - orbit (1/4 : ℂ) n (1/4)‖ +
          ‖orbit (1/4 : ℂ) n (1/4)‖ := norm_add_le _ _
      _ ≤ ε + 1/2 := add_le_add hdiff (cusp_orbit_norm n)
      _ ≤ 1 := by linarith only [hεhalf]
  have hquarter : ‖d-(1/4 : ℂ)‖ ≤ 1/4 := by
    have hscaled : ‖d-(1/4 : ℂ)‖*(4*N^2) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 4*N^2)).mp hd
    have hNsq : 1 ≤ N^2 := by nlinarith only [hN1, sq_nonneg (N-1)]
    have h := mul_le_mul_of_nonneg_left hNsq (norm_nonneg (d-(1/4 : ℂ)))
    nlinarith only [hscaled, h]
  have hdn : ‖d‖ ≤ 1/2 := by
    calc
      _ = ‖(d-(1/4 : ℂ))+(1/4 : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖d-(1/4 : ℂ)‖ + ‖(1/4 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1/4 + 1/4 := add_le_add hquarter (by norm_num)
      _ = 1/2 := by norm_num
  have happrox : approx d d n = 0 := by
    simp only [approx, logSize, size, max_eq_left hlast, Real.log_one, mul_zero]
  have herror := escape_error d d hdn n
  rw [happrox, zero_sub, abs_neg, abs_of_nonneg (escape_nonneg d d)] at herror
  simpa only [parameterEscape, show (1:ℝ)+1/2=3/2 by norm_num] using herror


/-- The actual parabolic critical-value orbit has zero escape. -/
theorem cusp_parameter_escape_zero : parameterEscape (1/4) = 0 := by
  exact (escape_zero_iff_bounded (1/4) (1/4)).mpr ⟨1/2, cusp_orbit_norm⟩

/-- Every exponential base above one dominates an appropriately
regularized partition at the actual cusp. -/
theorem cusp_response_geometric (A : ℝ) (hA : 1 < A) :
    ∃ ε K : ℝ, 0 < ε ∧ 1 ≤ K ∧
      ∀ n : ℕ, regularizedResponse (1/4) ε n ≤ K*A^n := by
  let ε : ℝ := (A-1)/2
  let K : ℝ := max 1 (1/ε)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hA0 : 0 ≤ A := by linarith
  have hKe : 1 ≤ K*ε := by
    calc
      1 = (1/ε)*ε := by field_simp [hε.ne']
      _ ≤ K*ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε.le
  have hAe : A = 1+2*ε := by dsimp [ε]; ring
  refine ⟨ε, K, hε, hK, ?_⟩
  intro n
  induction n with
  | zero => simpa [regularizedResponse] using hK
  | succ n ih =>
      have hpow : 1 ≤ A^n := one_le_pow₀ hA.le
      have hforce : 1 ≤ (K*ε)*A^n := by
        have hm := mul_le_mul_of_nonneg_left hpow (mul_nonneg hK0 hε.le)
        exact hKe.trans (by simpa only [mul_one] using hm)
      have ha : 2*‖orbit (1/4 : ℂ) n (1/4)‖+ε ≤ 1+ε := by
        linarith only [cusp_orbit_norm n]
      calc
        regularizedResponse (1/4) ε (n+1) =
            (2*‖orbit (1/4 : ℂ) n (1/4)‖+ε) *
              regularizedResponse (1/4) ε n + 1 := rfl
        _ ≤ (2*‖orbit (1/4 : ℂ) n (1/4)‖+ε) * (K*A^n) + 1 :=
          add_le_add (mul_le_mul_of_nonneg_left ih (by positivity)) le_rfl
        _ ≤ (1+ε)*(K*A^n)+1 :=
          add_le_add (mul_le_mul_of_nonneg_right ha (by positivity)) le_rfl
        _ ≤ (1+ε)*(K*A^n)+(K*ε)*A^n := add_le_add le_rfl hforce
        _ = K*A^(n+1) := by rw [pow_succ, hAe]; ring

theorem cusp_slowRegularizedGrowth : SlowRegularizedGrowth (1/4) := by
  intro A hA
  exact cusp_response_geometric A hA

/-- The actual cusp realizes every natural upper order of Green flatness. -/
theorem cusp_green_all_orders (k : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      ∀ d : ℂ, ‖d-(1/4 : ℂ)‖ ≤ r →
        parameterEscape d ≤ C * ‖d-(1/4 : ℂ)‖^(k+1) :=
  slowRegularizedGrowth_power_bound (1/4) cusp_parameter_escape_zero
    cusp_slowRegularizedGrowth k


private theorem real_cusp_growth (h : ℝ) (n : ℕ) :
    ∃ x : ℝ, (1/4+h)+(n:ℝ)*h ≤ x ∧
      orbit (((1/4+h : ℝ) : ℂ)) n (((1/4+h : ℝ) : ℂ)) = (x : ℂ) := by
  induction n with
  | zero =>
      refine ⟨1/4+h, by simp, ?_⟩
      simp [orbit]
  | succ n ih =>
      obtain ⟨x, hx, heq⟩ := ih
      refine ⟨x^2+(1/4+h), ?_, ?_⟩
      · rw [Nat.cast_succ]
        nlinarith only [hx, sq_nonneg (x-1/2)]
      · simp only [orbit, heq]
        push_cast <;> ring

/-- Every real parameter strictly to the right of the cusp escapes. -/
theorem real_above_cusp_escape_pos (h : ℝ) (hh : 0 < h) :
    0 < parameterEscape (((1/4+h : ℝ) : ℂ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1/h)
  have hnh : 1 < (n:ℝ)*h := (div_lt_iff₀ hh).mp hn
  obtain ⟨x, hx, heq⟩ := real_cusp_growth h n
  have hc0 : 0 ≤ (1/4+h : ℝ) := by linarith only [hh]
  have hx0 : 0 ≤ x := by linarith only [hx, hnh, hc0]
  change 0 < escape (((1/4+h : ℝ) : ℂ)) (((1/4+h : ℝ) : ℂ))
  apply (escape_pos_iff_crossing _ _).mpr
  refine ⟨n, ?_⟩
  simpa only [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx0, abs_of_nonneg hc0] using
      (show 1+(1/4+h : ℝ) < x by linarith only [hx, hnh])

/-- The slow-growth witness is not an interior parameter. -/
theorem cusp_not_interior_zero :
    (1/4 : ℂ) ∉ interior {d : ℂ | parameterEscape d = 0} := by
  intro hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hi)
  let h : ℝ := r/2
  have hh : 0 < h := by dsimp [h]; linarith only [hr]
  have hd : (((1/4+h : ℝ) : ℂ)) ∈ Metric.ball (1/4 : ℂ) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (((1/4+h : ℝ) : ℂ))-(1/4 : ℂ) = (h : ℂ) := by
      push_cast <;> ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    dsimp [h]
    linarith only [hr]
  have hz : parameterEscape (((1/4+h : ℝ) : ℂ)) = 0 := hball hd
  exact (real_above_cusp_escape_pos h hh).ne' hz

/-- The zero-growth, all-order-flat witness lies on the actual boundary. -/
theorem cusp_mem_frontier_zero :
    (1/4 : ℂ) ∈ frontier {d : ℂ | parameterEscape d = 0} := by
  change (1/4 : ℂ) ∈ closure {d : ℂ | parameterEscape d = 0} ∧
    (1/4 : ℂ) ∉ interior {d : ℂ | parameterEscape d = 0}
  exact ⟨subset_closure cusp_parameter_escape_zero, cusp_not_interior_zero⟩

/-- Arbitrarily slow regularized exponential growth cannot replace
bounded regularized response in the actual interior criterion. -/
theorem slow_growth_does_not_force_interior :
    ¬ ∀ c : ℂ, parameterEscape c = 0 → SlowRegularizedGrowth c →
      c ∈ interior {d : ℂ | parameterEscape d = 0} := by
  intro h
  exact cusp_not_interior_zero
    (h (1/4) cusp_parameter_escape_zero cusp_slowRegularizedGrowth)

end
end QuadraticEscape
