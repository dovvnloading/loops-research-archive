import QuadraticGreenPressure

/-! Conditional natural-power Green bounds from the growth of the actual
regularized renewal partition. No stationary pressure identification is used. -/

namespace QuadraticEscape

noncomputable section

/-- Growth of the actual regularized partition at a base whose mth power
is at most two gives an explicit mth-order parameter Green bound. -/
theorem regularizedResponse_natural_power (c d : ℂ) {ε K A : ℝ}
    (hc : parameterEscape c = 0) (hε : 0 < ε) (hK : 1 ≤ K) (hA : 1 < A)
    (hS : ∀ n : ℕ, regularizedResponse c ε n ≤ K * A^n)
    (m : ℕ) (hm : 0 < m) (hAm : A^m ≤ 2)
    (hsmall : ‖d-c‖ * K ≤ ε) :
    parameterEscape d ≤
      2 * (Real.log (2+ε) + Real.log (3+ε)) * (‖d-c‖*K/ε)^m := by
  by_cases hdc : d = c
  · subst d
    simp [hc, hm.ne']
  · let t : ℝ := ‖d-c‖*K/ε
    have hKpos : 0 < K := by linarith
    have hδpos : 0 < ‖d-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hdc)
    have ht : 0 < t := div_pos (mul_pos hδpos hKpos) hε
    have ht1 : t ≤ 1 := (div_le_iff₀ hε).mpr (by simpa using hsmall)
    have hinv : (1 : ℝ) ≤ 1/t :=
      (le_div_iff₀ ht).mpr (by simpa using ht1)
    obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near hinv hA
    have hlow : A^n*t ≤ 1 := (le_div_iff₀ ht).mp hlo
    have hhigh : 1 < A^(n+1)*t := (div_lt_iff₀ ht).mp hhi
    have htdef : t*ε = ‖d-c‖*K := by
      dsimp [t]
      exact div_mul_cancel₀ _ hε.ne'
    have hscale : ∀ j ≤ n, ‖d-c‖*regularizedResponse c ε j ≤ ε := by
      intro j hj
      have hp : A^j ≤ A^n := pow_le_pow_right₀ hA.le hj
      calc
        ‖d-c‖*regularizedResponse c ε j ≤ ‖d-c‖*(K*A^j) :=
          mul_le_mul_of_nonneg_left (hS j) (norm_nonneg _)
        _ = (A^j*t)*ε := by
          calc
            ‖d-c‖*(K*A^j) = A^j*(‖d-c‖*K) := by ring
            _ = A^j*(t*ε) := by rw [htdef]
            _ = (A^j*t)*ε := by ring
        _ ≤ (A^n*t)*ε := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp ht.le) hε.le
        _ ≤ 1*ε := mul_le_mul_of_nonneg_right hlow hε.le
        _ = ε := one_mul _
    have hpowhigh : 1 < (A^(n+1)*t)^m := one_lt_pow₀ hhigh hm.ne'
    have hswap : (A^(n+1))^m = (A^m)^(n+1) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (n+1) m]
    rw [mul_pow, hswap] at hpowhigh
    have hA0 : 0 ≤ A := by linarith
    have hpow : (A^m)^(n+1) ≤ (2:ℝ)^(n+1) :=
      pow_le_pow_left₀ (pow_nonneg hA0 m) hAm (n+1)
    have hhigh2 : 1 < (2:ℝ)^(n+1)*t^m :=
      hpowhigh.trans_le (mul_le_mul_of_nonneg_right hpow (pow_nonneg ht.le m))
    have hw2 : weight n * (2:ℝ)^n = 1 := by
      unfold weight
      rw [← mul_pow]
      norm_num
    have hw : weight n < 2*t^m := by
      calc
        weight n = weight n * 1 := (mul_one _).symm
        _ < weight n * ((2:ℝ)^(n+1)*t^m) :=
          mul_lt_mul_of_pos_left hhigh2 (weight_pos n)
        _ = (weight n*(2:ℝ)^n)*(2*t^m) := by rw [pow_succ]; ring
        _ = 2*t^m := by rw [hw2, one_mul]
    have hL : 0 ≤ Real.log (2+ε) + Real.log (3+ε) :=
      add_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by linarith))
    calc
      parameterEscape d ≤ weight n * (Real.log (2+ε)+Real.log (3+ε)) :=
        regularizedResponse_green c d hc hε.le n hscale
      _ ≤ (2*t^m)*(Real.log (2+ε)+Real.log (3+ε)) :=
        mul_le_mul_of_nonneg_right hw.le hL
      _ = 2*(Real.log (2+ε)+Real.log (3+ε))*(‖d-c‖*K/ε)^m := by
        dsimp [t]
        ring


/-- Arbitrarily small positive exponential growth is allowed after choosing
a positive regularizer. The regularizer and prefactor can depend on the base. -/
def SlowRegularizedGrowth (c : ℂ) : Prop :=
  ∀ A : ℝ, 1 < A → ∃ ε K : ℝ,
    0 < ε ∧ 1 ≤ K ∧
      ∀ n : ℕ, regularizedResponse c ε n ≤ K * A^n

/-- Every natural order is a local upper order for the actual parameter
Green potential. This is pointwise flatness, with no smoothness assertion. -/
theorem slowRegularizedGrowth_power_bound (c : ℂ)
    (hc : parameterEscape c = 0) (hs : SlowRegularizedGrowth c) (k : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      ∀ d : ℂ, ‖d-c‖ ≤ r → parameterEscape d ≤ C * ‖d-c‖^(k+1) := by
  have hm : 0 < ((k+1 : ℕ) : ℝ) := by positivity
  let A : ℝ := Real.exp (Real.log 2 / ((k+1 : ℕ) : ℝ))
  have hA : 1 < A := Real.one_lt_exp_iff.mpr
    (div_pos (Real.log_pos (by norm_num : (1:ℝ) < 2)) hm)
  have hAm : A^(k+1) = 2 := by
    dsimp [A]
    rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hm.ne',
      Real.exp_log (by norm_num : (0:ℝ) < 2)]
  obtain ⟨ε, K, hε, hK, hS⟩ := hs A hA
  have hKpos : 0 < K := by linarith
  let L : ℝ := Real.log (2+ε) + Real.log (3+ε)
  have hL : 0 < L := by
    dsimp [L]
    exact add_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
  let C : ℝ := 2 * L * (K/ε)^(k+1)
  let r : ℝ := ε/K
  refine ⟨C, r, ?_, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos (mul_pos (by norm_num) hL)
      (pow_pos (div_pos hKpos hε) _)
  · exact div_pos hε hKpos
  · intro d hd
    have hsmall : ‖d-c‖ * K ≤ ε := (le_div_iff₀ hKpos).mp hd
    have hg := regularizedResponse_natural_power c d hc hε hK hA hS
      (k+1) (Nat.succ_pos k) hAm.le hsmall
    calc
      parameterEscape d ≤
          2 * (Real.log (2+ε)+Real.log (3+ε)) * (‖d-c‖*K/ε)^(k+1) := hg
      _ = C * ‖d-c‖^(k+1) := by
        rw [show ‖d-c‖*K/ε = ‖d-c‖*(K/ε) by ring, mul_pow]
        dsimp [C, L]
        ring


/-- Every critical-value iterate at the actual parameter minus two has norm two. -/
theorem chebyshev_criticalValue_norm (n : ℕ) :
    ‖orbit (-2) n (-2)‖ = 2 := by
  cases n with
  | zero => norm_num [orbit]
  | succ n =>
    rw [← orbit_shift,
      show (-2 : ℂ)^2 + (-2 : ℂ) = 2 by norm_num,
      chebyshev_fixed_orbit]
    norm_num

/-- Regularization cannot hide the actual Chebyshev expansion. -/
theorem chebyshev_regularizedResponse_lower {ε : ℝ}
    (hε : 0 ≤ ε) (n : ℕ) :
    (4 : ℝ)^n ≤ regularizedResponse (-2) ε n := by
  induction n with
  | zero => norm_num [regularizedResponse]
  | succ n ih =>
    rw [regularizedResponse, chebyshev_criticalValue_norm, pow_succ]
    have hnon := mul_nonneg hε (regularizedResponse_nonneg (-2) hε n)
    nlinarith only [ih, hnon]

/-- Slow regularized growth fails at the actual square-root endpoint. -/
theorem chebyshev_not_slowRegularizedGrowth : ¬ SlowRegularizedGrowth (-2) := by
  intro hs
  obtain ⟨ε, K, hε, hK, hS⟩ := hs 2 (by norm_num)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt K (by norm_num : (1:ℝ) < 2)
  have hb : (4:ℝ)^n ≤ K * (2:ℝ)^n :=
    (chebyshev_regularizedResponse_lower hε.le n).trans (hS n)
  have hfour : (4:ℝ)^n = (2:ℝ)^n * (2:ℝ)^n := by
    rw [← mul_pow]
    norm_num
  rw [hfour] at hb
  exact (not_lt_of_ge hb) (mul_lt_mul_of_pos_right hn (by positivity))

end
end QuadraticEscape
