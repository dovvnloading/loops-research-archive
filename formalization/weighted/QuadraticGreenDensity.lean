import QuadraticExtremalMultiplier

/-! Two successive actual critical-value observations retain parameter
information, even when a single observation has a critical point. The
squared spherical derivative is defined directly; no Laplacian identification
is asserted in this module. -/

namespace QuadraticGreenDensity

open QuadraticEscape Filter Topology

noncomputable section

def criticalValue (c : ℂ) (n : ℕ) : ℂ := orbit c n c

def parameterTangent (c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => 2 * criticalValue c n * parameterTangent c n + 1

theorem criticalValue_hasDerivAt (c : ℂ) (n : ℕ) :
    HasDerivAt (fun d : ℂ => criticalValue d n) (parameterTangent c n) c := by
  induction n with
  | zero =>
    simpa only [criticalValue, orbit, parameterTangent] using hasDerivAt_id c
  | succ n ih =>
    have h := (ih.pow 2).add (hasDerivAt_id c)
    simpa only [criticalValue, orbit, parameterTangent, Nat.cast_ofNat,
      Nat.reduceSub, pow_one] using h

theorem criticalValue_deriv (c : ℂ) (n : ℕ) :
    deriv (fun d : ℂ => criticalValue d n) c = parameterTangent c n :=
  (criticalValue_hasDerivAt c n).deriv

def sphericalDensity (c : ℂ) (n : ℕ) : ℝ :=
  weight n * ‖parameterTangent c n‖ ^ 2 / (1 + ‖criticalValue c n‖ ^ 2) ^ 2

theorem sphericalDensity_eq_deriv (c : ℂ) (n : ℕ) :
    sphericalDensity c n =
      weight n * ‖deriv (fun d : ℂ => criticalValue d n) c‖ ^ 2 /
        (1 + ‖criticalValue c n‖ ^ 2) ^ 2 := by
  simp only [sphericalDensity, criticalValue_deriv]

theorem sphericalDensity_nonneg (c : ℂ) (n : ℕ) :
    0 ≤ sphericalDensity c n := by
  exact div_nonneg (mul_nonneg (weight_pos n).le (sq_nonneg _)) (sq_nonneg _)

theorem criticalValue_pair_recovers_parameter (c : ℂ) (n : ℕ) :
    criticalValue c (n + 1) - criticalValue c n ^ 2 = c := by
  simp only [criticalValue, orbit]
  ring

theorem criticalValue_pair_injective (n : ℕ) :
    Function.Injective (fun c : ℂ => (criticalValue c n, criticalValue c (n + 1))) := by
  intro c d h
  have h₀ : criticalValue c n = criticalValue d n := congrArg Prod.fst h
  have h₁ : criticalValue c (n + 1) = criticalValue d (n + 1) := congrArg Prod.snd h
  calc
    c = criticalValue c (n + 1) - criticalValue c n ^ 2 :=
      (criticalValue_pair_recovers_parameter c n).symm
    _ = criticalValue d (n + 1) - criticalValue d n ^ 2 := by rw [h₀, h₁]
    _ = d := criticalValue_pair_recovers_parameter d n

theorem parameterTangent_no_consecutive_zeros (c : ℂ) (n : ℕ) :
    ¬ (parameterTangent c n = 0 ∧ parameterTangent c (n + 1) = 0) := by
  rintro ⟨h₀, h₁⟩
  rw [parameterTangent, h₀] at h₁
  norm_num at h₁

private theorem norm_affine_lower (q v : ℂ) (hq : ‖q‖ ≤ 2) :
    1 ≤ 18 * ‖v‖ ^ 2 + 9 * ‖2 * q * v + 1‖ ^ 2 := by
  have hid : (1 : ℂ) = (2 * q * v + 1) - 2 * q * v := by ring
  have ht := norm_sub_le (2 * q * v + 1) (2 * q * v)
  rw [← hid, norm_one, norm_mul, norm_mul, Complex.norm_two] at ht
  have hv := norm_nonneg v
  have hmul := mul_le_mul_of_nonneg_right hq hv
  have hle : 1 ≤ ‖2 * q * v + 1‖ + 4 * ‖v‖ := by linarith only [ht, hmul]
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hle 2
  nlinarith only [hs, sq_nonneg (‖v‖ - 2 * ‖2 * q * v + 1‖)]

private theorem denominator_le (c : ℂ) (hc : parameterEscape c = 0) (n : ℕ) :
    (1 + ‖criticalValue c n‖ ^ 2) ^ 2 ≤ 25 := by
  have hb : ‖criticalValue c n‖ ≤ 2 :=
    bounded_orbit_norm_le_two c c (parameter_norm_le_two c hc) hc n
  have hs := pow_le_pow_left₀ (norm_nonneg (criticalValue c n)) hb 2
  have hbase : 1 + ‖criticalValue c n‖ ^ 2 ≤ 5 := by nlinarith only [hs]
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖criticalValue c n‖ ^ 2) hbase 2
  norm_num at h
  exact h

private theorem tangent_density_bound (c : ℂ) (hc : parameterEscape c = 0) (n : ℕ) :
    weight n * ‖parameterTangent c n‖ ^ 2 ≤ 25 * sphericalDensity c n := by
  have hp : 0 < (1 + ‖criticalValue c n‖ ^ 2) ^ 2 := by positivity
  have he : sphericalDensity c n * (1 + ‖criticalValue c n‖ ^ 2) ^ 2 =
      weight n * ‖parameterTangent c n‖ ^ 2 := by
    unfold sphericalDensity
    exact div_mul_cancel₀ _ hp.ne'
  have h := mul_le_mul_of_nonneg_left (denominator_le c hc n)
    (sphericalDensity_nonneg c n)
  nlinarith only [h, he]

/-- Two successive observations give a uniform, degree-normalized positive
floor throughout the actual bounded critical-orbit locus. -/
theorem sphericalDensity_pair_lower (c : ℂ) (hc : parameterEscape c = 0) (n : ℕ) :
    weight n / 450 ≤ sphericalDensity c n + sphericalDensity c (n + 1) := by
  have hb : ‖criticalValue c n‖ ≤ 2 :=
    bounded_orbit_norm_le_two c c (parameter_norm_le_two c hc) hc n
  have ha := norm_affine_lower (criticalValue c n) (parameterTangent c n) hb
  change 1 ≤ 18 * ‖parameterTangent c n‖ ^ 2 +
    9 * ‖parameterTangent c (n + 1)‖ ^ 2 at ha
  have hm := mul_le_mul_of_nonneg_left ha (weight_pos n).le
  have h₀ := tangent_density_bound c hc n
  have h₁ := tangent_density_bound c hc (n + 1)
  rw [weight_succ] at h₁
  nlinarith only [hm, h₀, h₁]

theorem criticalValue_zero (n : ℕ) : criticalValue 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change criticalValue 0 n ^ 2 + 0 = 0
    simp [ih]

theorem parameterTangent_zero (n : ℕ) : parameterTangent 0 n = 1 := by
  cases n with
  | zero => rfl
  | succ n => simp [parameterTangent, criticalValue_zero]

theorem zero_parameterEscape : parameterEscape 0 = 0 := by
  apply (escape_zero_iff_bounded 0 0).mpr
  refine ⟨0, fun n => ?_⟩
  have h : orbit 0 n 0 = 0 := criticalValue_zero n
  simpa only [h, norm_zero] using (le_refl (0 : ℝ))

theorem sphericalDensity_zero (n : ℕ) : sphericalDensity 0 n = weight n := by
  simp [sphericalDensity, criticalValue_zero, parameterTangent_zero]

theorem sphericalDensity_pair_zero (n : ℕ) :
    sphericalDensity 0 n + sphericalDensity 0 (n + 1) = (3 / 2 : ℝ) * weight n := by
  rw [sphericalDensity_zero, sphericalDensity_zero, weight_succ]
  ring

theorem sphericalDensity_pair_tendsto_zero :
    Tendsto (fun n => sphericalDensity 0 n + sphericalDensity 0 (n + 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun n => (3 / 2 : ℝ) * weight n) atTop (𝓝 ((3 / 2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul weight_tendsto
  simpa only [sphericalDensity_pair_zero, mul_zero] using h

/-- Degree normalization has no positive level-independent floor,
even restricted to genuine zero-potential parameters. -/
theorem no_uniform_positive_density_floor :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ n c, parameterEscape c = 0 →
      ε ≤ sphericalDensity c n + sphericalDensity c (n + 1) := by
  rintro ⟨ε, hε, hbound⟩
  have h : ε ≤ 0 := ge_of_tendsto sphericalDensity_pair_tendsto_zero
    (Eventually.of_forall (fun n => hbound n 0 zero_parameterEscape))
  exact (not_le_of_gt hε) h

/-- The exponential rate of the floor is optimal: no larger geometric base
can give a positive lower bound uniform in parameter and observation time. -/
theorem no_slower_geometric_density_floor (r C : ℝ)
    (hr : (1 / 2 : ℝ) < r) (hC : 0 < C) :
    ∃ n : ℕ, sphericalDensity 0 n + sphericalDensity 0 (n + 1) < C * r ^ n := by
  have hr0 : 0 < r := by linarith
  have hq0 : 0 ≤ (1 / 2 : ℝ) / r := by positivity
  have hq1 : (1 / 2 : ℝ) / r < 1 := by
    apply (div_lt_iff₀ hr0).mpr
    simpa only [one_mul] using hr
  have ht : Tendsto (fun n : ℕ => (3 / 2 : ℝ) * ((1 / 2 : ℝ) / r) ^ n)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := (3 / 2 : ℝ))).mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hC)).exists
  have hcancel : ((1 / 2 : ℝ) / r) ^ n * r ^ n = weight n := by
    unfold weight
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hr0.ne')]
  refine ⟨n, ?_⟩
  calc
    sphericalDensity 0 n + sphericalDensity 0 (n + 1) = (3 / 2 : ℝ) * weight n :=
      sphericalDensity_pair_zero n
    _ = ((3 / 2 : ℝ) * ((1 / 2 : ℝ) / r) ^ n) * r ^ n := by
      rw [mul_assoc, hcancel]
    _ < C * r ^ n := mul_lt_mul_of_pos_right hn (pow_pos hr0 n)

end
end QuadraticGreenDensity
