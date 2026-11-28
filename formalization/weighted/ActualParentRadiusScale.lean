import ActualParentRate

/-!
# The actual normalized target radius has the sharp exponential scale

The critical-orbit product bounds the genuine quadratic coefficient from
above.  Together with the positive normalized coefficient of an actual
tip, this bounds the physical return scale from below.  Consequently the
normalized outer radius is comparable to `2^p` in both directions, and
the already proved mark perturbation is negligible relative to its inverse.
-/

namespace ActualParentRadiusScale

open Set Filter
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualParentMarks ActualParentRate LoopsLimitingCrestParameter
open scoped Topology

noncomputable section

private theorem coefficient_abs_le_pow_four (c : ℝ) (n : ℕ)
    (hcrit : ∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2) :
    |quadraticCoefficient c n| ≤ (4 : ℝ)^n := by
  induction n with
  | zero => norm_num [quadraticCoefficient]
  | succ n ih =>
    have ha := ih (fun j hj => hcrit j (by omega))
    have hd := hcrit (n+1) (by omega)
    calc
      |quadraticCoefficient c (n+1)| =
          (2 * |criticalValue c (n+1)|) * |quadraticCoefficient c n| := by
            norm_num [quadraticCoefficient, abs_mul]
      _ ≤ 4*(4 : ℝ)^n :=
        mul_le_mul (by linarith) ha (abs_nonneg _) (by norm_num)
      _ = (4 : ℝ)^(n+1) := by rw [pow_succ]; ring

private theorem four_pow_mul_scale (p : ℕ) :
    (4 : ℝ)^p * scale p = 1 := by
  simp only [scale, ← mul_pow]
  norm_num

private theorem two_pow_mul_scale (p : ℕ) :
    (2 : ℝ)^p * scale p = (1/2 : ℝ)^p := by
  simp only [scale, ← mul_pow]
  norm_num

/-- The actual positive return is uniformly bounded below at its true
`4⁻ᵖ` scale; this uses no itinerary or parameter-selection premise. -/
theorem criticalValue_lower {p : ℕ} (hp : 1 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : 7 * scale p ≤ criticalValue c p := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have hcoef := coefficient_abs_le_pow_four c n (by
    intro j hj
    exact hc.2.2.2.2.2.2 j hj)
  have hk : (7/4 : ℝ) ≤ kappa (n+1) c := by
    have hl := hc.2.2.2.1.1
    change 17903/10000 ≤ kappa (n+1) c at hl
    linarith
  have hbound : kappa (n+1) c ≤ (4 : ℝ)^n * criticalValue c (n+1) := by
    unfold kappa
    simp only [Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_right
      ((neg_le_abs _).trans hcoef) hc.2.1.le
  apply (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0 : ℝ) < 4) n)).mp
  calc
    (4 : ℝ)^n * (7 * scale (n+1)) = (7/4) * ((4 : ℝ)^n * scale n) := by
      unfold scale
      rw [pow_succ]
      ring
    _ = 7/4 := by rw [four_pow_mul_scale]; ring
    _ ≤ kappa (n+1) c := hk
    _ ≤ (4 : ℝ)^n * criticalValue c (n+1) := hbound

/-- The radius upper bound complements `ActualParentMarks.targetRadius_lower`. -/
theorem targetRadius_upper {p : ℕ} (hp : 1 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : targetRadius c p ≤ (2 : ℝ)^p / 7 := by
  unfold targetRadius
  apply (div_le_iff₀ hc.2.1).mpr
  calc
    (1/2 : ℝ)^p = ((2 : ℝ)^p / 7) * (7 * scale p) := by
      rw [← two_pow_mul_scale p]
      ring
    _ ≤ ((2 : ℝ)^p / 7) * criticalValue c p :=
      mul_le_mul_of_nonneg_left (criticalValue_lower hp hc) (by positivity)

theorem targetRadius_pos {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    0 < targetRadius c p := by
  exact div_pos (by positivity) hc.2.1

theorem inv_targetRadius (c : ℝ) (p : ℕ) :
    (targetRadius c p)⁻¹ = criticalValue c p * (2 : ℝ)^p := by
  simp [targetRadius, div_eq_mul_inv, mul_inv_rev]

/-- Reciprocal radii are comparable to `2⁻ᵖ` with explicit universal constants. -/
theorem inv_targetRadius_bounds {p : ℕ} (hp : 1 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    7 * (1/2 : ℝ)^p ≤ (targetRadius c p)⁻¹ ∧
      (targetRadius c p)⁻¹ ≤ 12 * (1/2 : ℝ)^p := by
  rw [inv_targetRadius]
  constructor
  · calc
      7 * (1/2 : ℝ)^p = (7 * scale p) * (2 : ℝ)^p := by
        rw [← two_pow_mul_scale p]
        ring
      _ ≤ criticalValue c p * (2 : ℝ)^p :=
        mul_le_mul_of_nonneg_right (criticalValue_lower hp hc) (by positivity)
  · calc
      criticalValue c p * (2 : ℝ)^p ≤ (12 * scale p) * (2 : ℝ)^p :=
        mul_le_mul_of_nonneg_right hc.2.2.1 (by positivity)
      _ = 12 * (1/2 : ℝ)^p := by
        rw [← two_pow_mul_scale p]
        ring

theorem targetRadius_mul_scale_le {p : ℕ} (hp : 1 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    targetRadius c p * scale p ≤ (1/7 : ℝ) * (1/2 : ℝ)^p := by
  calc
    targetRadius c p * scale p ≤ ((2 : ℝ)^p / 7) * scale p :=
      mul_le_mul_of_nonneg_right (targetRadius_upper hp hc) (scale_pos p).le
    _ = (1/7 : ℝ) * (1/2 : ℝ)^p := by
      rw [← two_pow_mul_scale p]
      ring

/-- Mark errors of order `4⁻ᵖ` are negligible after multiplication by
the actual outer radius, for every sequence of actual tips. -/
theorem tendsto_targetRadius_mul_scale (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => targetRadius (c n) (n+17) * scale (n+17)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (1/2 : ℝ)^(n+17)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 17)
  apply squeeze_zero
    (fun n => mul_nonneg (targetRadius_pos (hc n)).le (scale_pos _).le)
    (fun n => targetRadius_mul_scale_le (by omega) (hc n))
  simpa only [mul_zero] using hpow.const_mul (1/7 : ℝ)

/-- The complete four-mark displacement is lower order than the finite-domain
`1/R` effect. -/
theorem tendsto_targetRadius_mul_markError {k : ℝ}
    (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => targetRadius (c n) (n+17) * markError (c n) (n+17) k)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      targetRadius (c n) (n+17) * markError (c n) (n+17) k ≤
        (4*3906*23646 : ℝ) * (targetRadius (c n) (n+17) * scale (n+17)) := by
    calc
      _ ≤ targetRadius (c n) (n+17) * ((4*3906*23646 : ℝ) * scale (n+17)) :=
        mul_le_mul_of_nonneg_left (markError_le (by omega) (hc n) hk hroot)
          (targetRadius_pos (hc n)).le
      _ = _ := by ring
  apply squeeze_zero
    (fun n => mul_nonneg (targetRadius_pos (hc n)).le (markError_nonneg _ _ _)) hbound
  simpa only [mul_zero] using
    (tendsto_targetRadius_mul_scale c hc).const_mul (4*3906*23646 : ℝ)

end
end ActualParentRadiusScale
