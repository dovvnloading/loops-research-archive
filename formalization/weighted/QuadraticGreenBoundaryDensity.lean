import QuadraticGreenDensity
import QuadraticGreenCusp
import Mathlib.Analysis.Real.Sqrt

/-! The actual Jacobian renewal partition controls normalized parameter
densities. Its slow-growth regime fixes the sharp geometric decay threshold,
even on the Mandelbrot boundary, with the parabolic cusp as a witness. -/

namespace QuadraticGreenDensity

open QuadraticEscape Filter Topology

noncomputable section

theorem parameterTangent_response_bound (c : ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (n : ℕ) :
    ‖parameterTangent c n‖ ≤ regularizedResponse c ε n := by
  induction n with
  | zero => simp [parameterTangent, regularizedResponse]
  | succ n ih =>
    have hcoeff : 2 * ‖criticalValue c n‖ ≤ 2 * ‖criticalValue c n‖ + ε := by
      linarith only [hε]
    have hmul := mul_le_mul hcoeff ih (norm_nonneg (parameterTangent c n))
      (by positivity : 0 ≤ 2 * ‖criticalValue c n‖ + ε)
    calc
      ‖parameterTangent c (n+1)‖ ≤
          ‖2 * criticalValue c n * parameterTangent c n‖ + ‖(1:ℂ)‖ :=
        norm_add_le _ _
      _ = (2 * ‖criticalValue c n‖) * ‖parameterTangent c n‖ + 1 := by
        rw [norm_mul, norm_mul, Complex.norm_two, norm_one]
      _ ≤ (2 * ‖criticalValue c n‖ + ε) * regularizedResponse c ε n + 1 :=
        add_le_add hmul le_rfl
      _ = regularizedResponse c ε (n+1) := rfl

private theorem sphericalDensity_le_numerator (c : ℂ) (n : ℕ) :
    sphericalDensity c n ≤ weight n * ‖parameterTangent c n‖^2 := by
  unfold sphericalDensity
  apply div_le_self
  · exact mul_nonneg (weight_pos n).le (sq_nonneg _)
  · have hb : (1:ℝ) ≤ 1 + ‖criticalValue c n‖^2 := by
      nlinarith only [sq_nonneg ‖criticalValue c n‖]
    exact one_le_pow₀ hb

theorem sphericalDensity_response_bound (c : ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (n : ℕ) :
    sphericalDensity c n ≤ weight n * (regularizedResponse c ε n)^2 := by
  exact (sphericalDensity_le_numerator c n).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (parameterTangent_response_bound c hε n) 2)
      (weight_pos n).le)

theorem sphericalDensity_geometric_bound (c : ℂ) {ε K A : ℝ}
    (hε : 0 ≤ ε) (n : ℕ)
    (hS : regularizedResponse c ε n ≤ K*A^n) :
    sphericalDensity c n ≤ K^2 * (A^2/2)^n := by
  have hpow : (A^n)^2 = (A^2)^n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  calc
    sphericalDensity c n ≤ weight n * (regularizedResponse c ε n)^2 :=
      sphericalDensity_response_bound c hε n
    _ ≤ weight n * (K*A^n)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (regularizedResponse_nonneg c hε n) hS 2)
      (weight_pos n).le
    _ = K^2 * (weight n * (A^n)^2) := by ring
    _ = K^2 * ((1/2:ℝ) * A^2)^n := by
      unfold weight
      rw [hpow, ← mul_pow]
    _ = K^2 * (A^2/2)^n := by rw [show (1/2:ℝ)*A^2 = A^2/2 by ring]

theorem sphericalDensity_pair_geometric_bound (c : ℂ) {ε K A : ℝ}
    (hε : 0 ≤ ε) (hS : ∀ n : ℕ, regularizedResponse c ε n ≤ K*A^n) (n : ℕ) :
    sphericalDensity c n + sphericalDensity c (n+1) ≤
      K^2 * (1+A^2/2) * (A^2/2)^n := by
  calc
    _ ≤ K^2 * (A^2/2)^n + K^2 * (A^2/2)^(n+1) :=
      add_le_add (sphericalDensity_geometric_bound c hε n (hS n))
        (sphericalDensity_geometric_bound c hε (n+1) (hS (n+1)))
    _ = _ := by rw [pow_succ]; ring

/-- At every actual slow-growth parameter, every geometric base above
one half eventually dominates the paired densities with any positive coefficient. -/
theorem slowRegularizedGrowth_density_rate (c : ℂ)
    (hs : SlowRegularizedGrowth c) (r C : ℝ)
    (hr : (1/2:ℝ) < r) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      sphericalDensity c n + sphericalDensity c (n+1) < C*r^n := by
  have hr0 : 0 < r := by linarith only [hr]
  let A : ℝ := Real.sqrt (r+1/2)
  have hA : 1 < A := by
    change (1:ℝ) < Real.sqrt (r+1/2)
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1)
      (by linarith only [hr] : (1:ℝ) < r+1/2)
    simpa only [Real.sqrt_one] using h
  have hAsq : A^2 = r+1/2 := Real.sq_sqrt (by linarith only [hr])
  obtain ⟨ε, K, hε, hK, hS⟩ := hs A hA
  let b : ℝ := A^2/2
  let q : ℝ := b/r
  let D : ℝ := K^2*(1+b)
  have hb0 : 0 ≤ b := by change 0 ≤ A^2/2; positivity
  have hbr : b < r := by
    change A^2/2 < r
    rw [hAsq]
    linarith only [hr]
  have hq0 : 0 ≤ q := div_nonneg hb0 hr0.le
  have hq1 : q < 1 := (div_lt_iff₀ hr0).mpr (by simpa only [one_mul] using hbr)
  have ht : Tendsto (fun n : ℕ => D*q^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := D)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  filter_upwards [ht.eventually (gt_mem_nhds hC)] with n hn
  have hcancel : q^n*r^n = b^n := by
    change (b/r)^n*r^n = b^n
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hr0.ne')]
  have hpair : sphericalDensity c n + sphericalDensity c (n+1) ≤ D*b^n :=
    sphericalDensity_pair_geometric_bound c hε.le hS n
  calc
    sphericalDensity c n + sphericalDensity c (n+1) ≤ D*b^n := hpair
    _ = (D*q^n)*r^n := by
      calc
        D*b^n = D*(q^n*r^n) := congrArg (fun t : ℝ => D*t) hcancel.symm
        _ = (D*q^n)*r^n := (mul_assoc D (q^n) (r^n)).symm
    _ < C*r^n := mul_lt_mul_of_pos_right hn (pow_pos hr0 n)

/-- The degree exponent one half cannot be improved uniformly even on
the actual boundary: the parabolic cusp is an explicit witness. -/
theorem no_uniform_boundary_geometric_density_floor (r C : ℝ)
    (hr : (1/2:ℝ) < r) (hC : 0 < C) :
    ¬ ∀ n : ℕ, ∀ c : ℂ,
      c ∈ frontier {d : ℂ | parameterEscape d = 0} →
        C*r^n ≤ sphericalDensity c n + sphericalDensity c (n+1) := by
  intro h
  obtain ⟨n, hn⟩ :=
    (slowRegularizedGrowth_density_rate (1/4) cusp_slowRegularizedGrowth r C hr hC).exists
  exact (not_lt_of_ge (h n (1/4) cusp_mem_frontier_zero)) hn

end

end QuadraticGreenDensity
