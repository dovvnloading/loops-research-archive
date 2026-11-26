import QuadraticExtremalMultiplier
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Sharpness of the boundary escape exponent at the actual Chebyshev parameter.
The real parameters below -2 supply a quantitative lower bound for the same
critical-value potential used by `QuadraticEscape`. All estimates concern
genuine quadratic iterates and their established potential approximation error.
-/

namespace QuadraticEscape
open Filter Topology
noncomputable section

private def realCritical (ε : ℝ) : ℕ → ℝ
  | 0 => -2 - ε
  | n + 1 => realCritical ε n ^ 2 - 2 - ε

private theorem realCritical_cast (ε : ℝ) (n : ℕ) :
    orbit ((-2 - ε : ℝ) : ℂ) n ((-2 - ε : ℝ) : ℂ) =
      (realCritical ε n : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orbit, ih]
    simp only [realCritical, Complex.ofReal_sub, Complex.ofReal_pow,
      Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring

private theorem realCritical_growth (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    2 + 2 * (4 : ℝ)^n * ε + ε ≤ realCritical ε (n + 1) := by
  induction n with
  | zero => simp only [realCritical, pow_zero]; nlinarith [sq_nonneg ε]
  | succ n ih =>
    have hs : 0 ≤ (realCritical ε (n + 1) - 2)^2 := sq_nonneg _
    change 2 + 2 * (4 : ℝ)^(n + 1) * ε + ε ≤ realCritical ε (n + 1)^2 - 2 - ε
    rw [pow_succ]
    nlinarith only [ih, hs, hε]

/-- Concrete exterior parameters approaching the leftmost real Mandelbrot point. -/
def chebyshevApproach (n : ℕ) : ℂ := ((-2 - (1 / 4 : ℝ)^n : ℝ) : ℂ)

/-- The parameter distance is exactly the fourth-power scale. -/
theorem chebyshevApproach_distance (n : ℕ) :
    ‖chebyshevApproach n + 2‖ = (1 / 4 : ℝ)^n := by
  have he : chebyshevApproach n + 2 = -(((1 / 4 : ℝ)^n : ℝ) : ℂ) := by
    unfold chebyshevApproach
    push_cast
    ring
  rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

private theorem chebyshevApproach_norm (n : ℕ) : ‖chebyshevApproach n‖ ≤ 3 := by
  have hε : (1 / 4 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hε0 : 0 ≤ (1 / 4 : ℝ)^n := by positivity
  rw [chebyshevApproach, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : -2 - (1 / 4 : ℝ)^n ≤ 0)]
  linarith

private theorem chebyshevApproach_large_iterate (n : ℕ) :
    8 ≤ ‖orbit (chebyshevApproach n) (n + 2) (chebyshevApproach n)‖ := by
  let ε : ℝ := (1 / 4 : ℝ)^n
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hprod : (4 : ℝ)^n * ε = 1 := by
    dsimp [ε]
    rw [← mul_pow]
    norm_num
  have hg := realCritical_growth ε hε n
  have hg' : 4 + ε ≤ realCritical ε (n + 1) := by
    nlinarith only [hg, hprod]
  have hs : 16 ≤ realCritical ε (n + 1)^2 := by
    nlinarith only [hg', hε, sq_nonneg (realCritical ε (n + 1) - 4)]
  have hx : 8 ≤ realCritical ε (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 by omega, realCritical]
    linarith only [hs, hε1]
  change 8 ≤ ‖orbit ((-2 - ε : ℝ) : ℂ) (n + 2) ((-2 - ε : ℝ) : ℂ)‖
  rw [realCritical_cast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ realCritical ε (n + 2))]
  exact hx

private theorem escape_lower_of_eight (c z : ℂ) (hc : ‖c‖ ≤ 3) (hz : 8 ≤ ‖z‖) :
    Real.log 2 ≤ escape c z := by
  have hl : Real.log 8 ≤ logSize z := by
    apply Real.log_le_log (by norm_num)
    exact hz.trans (norm_le_size z)
  have he := (abs_le.mp (escape_error c z hc 0)).2
  simp only [approx, weight, orbit, pow_zero, one_mul] at he
  have hlogs : Real.log 8 = Real.log 2 + Real.log 4 := by
    rw [show (8 : ℝ) = 2 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num only [show (1 : ℝ) + 3 = 4 by norm_num] at he
  linarith only [he, hl, hlogs]

private theorem last_four_scale {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n : ℕ, (4 : ℝ)^n * ε ≤ 1 ∧ 1 < (4 : ℝ)^(n + 1) * ε := by
  have hg (n : ℕ) : (n : ℝ) + 1 ≤ (4 : ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      linarith only [ih, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hex : ∃ k : ℕ, 1 < (4 : ℝ)^k * ε := by
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    refine ⟨k, (div_lt_iff₀ hε).mp ?_⟩
    linarith only [hk, hg k]
  have hmin := Nat.find_spec hex
  cases h : Nat.find hex with
  | zero =>
    rw [h, pow_zero, one_mul] at hmin
    exact (not_lt_of_ge hε1 hmin).elim
  | succ n =>
    refine ⟨n, ?_, ?_⟩
    · by_contra hh
      have hh' := Nat.find_min' hex (lt_of_not_ge hh)
      omega
    · simpa only [h] using hmin

/-- A lower square-root estimate on the entire exterior real interval,
not merely a chosen subsequence. -/
theorem negative_real_escape_sq_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Real.log 2)^2 / 64 * ε ≤ (parameterEscape ((-2 - ε : ℝ) : ℂ))^2 := by
  obtain ⟨n, hlo, hhi⟩ := last_four_scale hε hε1
  have hg := realCritical_growth ε hε.le (n + 2)
  have hscale : 4 < (4 : ℝ)^(n + 2) * ε := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    nlinarith only [hhi]
  have hx : 8 ≤ realCritical ε (n + 3) := by
    have hi : n + 2 + 1 = n + 3 := by omega
    rw [hi] at hg
    nlinarith only [hg, hscale, hε]
  let c : ℂ := ((-2 - ε : ℝ) : ℂ)
  have hc : ‖c‖ ≤ 3 := by
    dsimp [c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hz : 8 ≤ ‖orbit c (n + 3) c‖ := by
    dsimp [c]
    rw [realCritical_cast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ realCritical ε (n + 3))]
    exact hx
  have he := escape_lower_of_eight c (orbit c (n + 3) c) hc hz
  rw [escape_iterate] at he
  have hp : (1 / 2 : ℝ)^n * (2 : ℝ)^(n + 3) = 8 := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (1 / 2 : ℝ)^n)
  rw [← mul_assoc, hp] at hm
  have hlower : (Real.log 2 / 8) * (1 / 2 : ℝ)^n ≤ parameterEscape c := by
    change (Real.log 2 / 8) * (1 / 2 : ℝ)^n ≤ escape c c
    linarith only [hm]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs := pow_le_pow_left₀
    (show 0 ≤ (Real.log 2 / 8) * (1 / 2 : ℝ)^n by positivity) hlower 2
  have hprod : ((1 / 2 : ℝ)^n)^2 * (4 : ℝ)^n = 1 := by
    rw [pow_two, ← mul_pow, ← mul_pow]
    norm_num
  have hw := mul_le_mul_of_nonneg_left hlo (sq_nonneg ((1 / 2 : ℝ)^n))
  rw [← mul_assoc, hprod, one_mul] at hw
  have hgain := mul_le_mul_of_nonneg_left hw (sq_nonneg (Real.log 2))
  change (Real.log 2)^2 / 64 * ε ≤ (parameterEscape c)^2
  nlinarith only [hs, hgain]

/-- A quantitative lower estimate for the genuine critical-value potential
along exterior parameters, with no uniformization or boundary regularity input. -/
theorem chebyshevApproach_escape_lower (n : ℕ) :
    (Real.log 2 / 4) * (1 / 2 : ℝ)^n ≤ parameterEscape (chebyshevApproach n) := by
  have he := escape_lower_of_eight (chebyshevApproach n)
    (orbit (chebyshevApproach n) (n + 2) (chebyshevApproach n))
    (chebyshevApproach_norm n) (chebyshevApproach_large_iterate n)
  rw [escape_iterate] at he
  have hp : (1 / 2 : ℝ)^n * (2 : ℝ)^(n + 2) = 4 := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (1 / 2 : ℝ)^n)
  change (Real.log 2 / 4) * (1 / 2 : ℝ)^n ≤ escape (chebyshevApproach n) (chebyshevApproach n)
  rw [← mul_assoc, hp] at hm
  linarith only [hm]

/-- The endpoint square-root upper bound has a matching lower bound on an
explicit sequence of actual parameters. -/
theorem chebyshevApproach_escape_sq_lower (n : ℕ) :
    (Real.log 2)^2 / 16 * ‖chebyshevApproach n + 2‖ ≤
      (parameterEscape (chebyshevApproach n))^2 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs := pow_le_pow_left₀
    (show 0 ≤ (Real.log 2 / 4) * (1 / 2 : ℝ)^n by positivity)
    (chebyshevApproach_escape_lower n) 2
  have hpow : ((1 / 2 : ℝ)^n)^2 = (1 / 4 : ℝ)^n := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [chebyshevApproach_distance]
  nlinarith only [hs, hpow]

private theorem chebyshevApproach_distance_tendsto :
    Tendsto (fun n => ‖chebyshevApproach n + 2‖) atTop (𝓝 0) := by
  simp_rw [chebyshevApproach_distance]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private theorem half_rpow_quarter : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
  norm_num

/-- No exponent greater than one half bounds the parameter potential in
any neighborhood of -2, regardless of the proposed multiplicative constant. -/
theorem parameter_escape_no_holder_above_half (α C r : ℝ)
    (hα : 1 / 2 < α) (hr : 0 < r) :
    ∃ d : ℂ, 0 < ‖d + 2‖ ∧ ‖d + 2‖ < r ∧
      C * ‖d + 2‖ ^ α < parameterEscape d := by
  let q : ℝ := 2 * (1 / 4 : ℝ)^α
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1) hα
    rw [half_rpow_quarter] at hh
    dsimp [q]
    linarith
  have ht : Tendsto (fun n : ℕ => C * q^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hK : 0 < Real.log 2 / 4 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have he : ∀ᶠ n in atTop, C * q^n < Real.log 2 / 4 := ht.eventually (gt_mem_nhds hK)
  have hd : ∀ᶠ n in atTop, ‖chebyshevApproach n + 2‖ < r :=
    chebyshevApproach_distance_tendsto.eventually (gt_mem_nhds hr)
  obtain ⟨n, hn, hnr⟩ := (he.and hd).exists
  refine ⟨chebyshevApproach n, ?_, hnr, ?_⟩
  · rw [chebyshevApproach_distance]
    positivity
  · have hp : ((1 / 4 : ℝ)^n)^α = ((1 / 4 : ℝ)^α)^n := by
      rw [← Real.rpow_natCast_mul (by norm_num),
        mul_comm (n : ℝ) α, Real.rpow_mul_natCast (by norm_num)]
    have htwo : (2 : ℝ)^n * (1 / 2 : ℝ)^n = 1 := by
      rw [← mul_pow]
      norm_num
    have hm := mul_lt_mul_of_pos_right hn (by positivity : 0 < (1 / 2 : ℝ)^n)
    have hcalc : C * q^n * (1 / 2 : ℝ)^n = C * ((1 / 4 : ℝ)^n)^α := by
      rw [hp]
      dsimp [q]
      rw [mul_pow]
      calc
        C * ((2 : ℝ)^n * ((1 / 4 : ℝ)^α)^n) * (1 / 2 : ℝ)^n =
            C * ((1 / 4 : ℝ)^α)^n * ((2 : ℝ)^n * (1 / 2 : ℝ)^n) := by ring
        _ = _ := by rw [htwo, mul_one]
    rw [hcalc] at hm
    rw [chebyshevApproach_distance]
    exact hm.trans_le (chebyshevApproach_escape_lower n)

end
end QuadraticEscape
