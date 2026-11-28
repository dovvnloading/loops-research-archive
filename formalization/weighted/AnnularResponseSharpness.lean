import AnnularVariationalResponse

/-!
# Attained sharpness of the annular comparison factor

The common exit-trace rescaling is optimal already for one genuine Fourier
channel. The two terminal loads have coefficients `a` and `a⁻¹`, so that
their multiplicative comparison factor is `a²`, not `a`. Their minimized
responses have coefficients `radiusStep r a` and its reciprocal. All infima
below are the same variational infima used by the full-trace theorem, and
their minimizers are exhibited explicitly.
-/

namespace AnnularResponseSharpness

open AnnularModeContraction AnnularVariationalResponse
open scoped ENNReal

noncomputable section

/-- A terminal quadratic load on one real Fourier channel. -/
def scalarLoad (z : ℝ) : Load Unit where
  energy := fun v => ENNReal.ofReal (z * (v ()) ^ 2)
  zero := by simp
  homogeneous := by
    intro s v
    change ENNReal.ofReal (z * (s * v ()) ^ 2) =
      ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (z * (v ()) ^ 2)
    rw [← ENNReal.ofReal_mul (sq_nonneg s)]
    congr 1
    ring

/-- Exit amplitude which actually attains the terminal minimum. -/
def scalarExit (r z u : ℝ) : ℝ := 2 * r * u / radiusDenominator r z

theorem scalar_denominator_pos {r z : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hz : 0 ≤ z) : 0 < radiusDenominator r z := by
  have h := mul_nonneg hz (one_sub_sq_pos hr hr1).le
  have hr2 := sq_nonneg r
  dsimp [radiusDenominator]
  nlinarith

/-- The exact remainder after subtracting the scalar terminal response. -/
theorem scalar_completion {r z : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hz : 0 ≤ z) (u v : ℝ) :
    mode r u v + z * v ^ 2 - radiusStep r z * u ^ 2 =
      (radiusDenominator r z / (1 - r ^ 2)) * (v - scalarExit r z u) ^ 2 := by
  have hd : radiusDenominator r z ≠ 0 := (scalar_denominator_pos hr hr1 hz).ne'
  have hr_ne : 1 - r ^ 2 ≠ 0 := (one_sub_sq_pos hr hr1).ne'
  unfold mode radiusStep scalarExit
  field_simp [hd, hr_ne]
  unfold radiusNumerator radiusDenominator
  ring

theorem scalar_minimum_lower {r z : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hz : 0 ≤ z) (u v : ℝ) :
    radiusStep r z * u ^ 2 ≤ mode r u v + z * v ^ 2 := by
  have h := mul_nonneg
    (div_nonneg (scalar_denominator_pos hr hr1 hz).le (one_sub_sq_pos hr hr1).le)
    (sq_nonneg (v - scalarExit r z u))
  rw [← scalar_completion hr hr1 hz u v] at h
  linarith

theorem scalar_minimum_attained {r z : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hz : 0 ≤ z) (u : ℝ) :
    mode r u (scalarExit r z u) + z * (scalarExit r z u) ^ 2 =
      radiusStep r z * u ^ 2 := by
  have h := scalar_completion hr hr1 hz u (scalarExit r z u)
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at h
  linarith

theorem collar_unit (r : ℝ) (u v : Trace Unit) :
    collar (fun _ : Unit => r) u v = ENNReal.ofReal (mode r (u ()) (v ())) := by
  simp [collar]

/-- The actual extended-real variational response has the claimed value;
the proof supplies a competitor and controls every other competitor. -/
theorem response_scalar_eq {r z : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hz : 0 ≤ z) (u : Trace Unit) :
    response (fun _ : Unit => r) (scalarLoad z) u =
      ENNReal.ofReal (radiusStep r z * (u ()) ^ 2) := by
  apply le_antisymm
  · unfold response
    apply iInf_le_of_le (fun _ : Unit => scalarExit r z (u ()))
    rw [collar_unit]
    change ENNReal.ofReal (mode r (u ()) (scalarExit r z (u ()))) +
      ENNReal.ofReal (z * (scalarExit r z (u ())) ^ 2) ≤
        ENNReal.ofReal (radiusStep r z * (u ()) ^ 2)
    rw [← ENNReal.ofReal_add (mode_nonneg hr hr1 _ _)
      (mul_nonneg hz (sq_nonneg _)), scalar_minimum_attained hr hr1 hz]
  · unfold response
    apply le_iInf
    intro v
    rw [collar_unit]
    change ENNReal.ofReal (radiusStep r z * (u ()) ^ 2) ≤
      ENNReal.ofReal (mode r (u ()) (v ())) + ENNReal.ofReal (z * (v ()) ^ 2)
    rw [← ENNReal.ofReal_add (mode_nonneg hr hr1 _ _)
      (mul_nonneg hz (sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (scalar_minimum_lower hr hr1 hz (u ()) (v ()))

theorem radiusStep_inverse {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) : radiusStep r a⁻¹ = (radiusStep r a)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have ha_ne : a ≠ 0 := ha0.ne'
  have hd : (a + 1) - r ^ 2 * (a - 1) ≠ 0 :=
    (radiusDenominator_pos hr hr1 ha).ne'
  have hn : (a + 1) + r ^ 2 * (a - 1) ≠ 0 := (radiusNumerator_pos ha).ne'
  have hdi : (a⁻¹ + 1) - r ^ 2 * (a⁻¹ - 1) ≠ 0 :=
    (scalar_denominator_pos hr hr1 (inv_nonneg.mpr ha0.le)).ne'
  unfold radiusStep radiusNumerator radiusDenominator
  field_simp [ha_ne, hd, hn, hdi]
  ring

/-- The proposed terminal pair obeys exactly the theorem's squared-radius
comparison convention. -/
theorem scalar_loads_comparable {a : ℝ} (ha : 1 ≤ a) :
    Comparable a (scalarLoad a) (scalarLoad a⁻¹) := by
  have ha0 : a ≠ 0 := by linarith
  have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (a ^ 2) := by
    have h : (1 : ℝ) ≤ a ^ 2 := by nlinarith
    simpa using ENNReal.ofReal_le_ofReal h
  have heq (v : Trace Unit) :
      scalarLoad a v = ENNReal.ofReal (a ^ 2) * scalarLoad a⁻¹ v := by
    change ENNReal.ofReal (a * (v ()) ^ 2) =
      ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (a⁻¹ * (v ()) ^ 2)
    rw [← ENNReal.ofReal_mul (sq_nonneg a)]
    congr 1
    field_simp
  constructor
  · intro v
    calc
      scalarLoad a⁻¹ v = 1 * scalarLoad a⁻¹ v := (one_mul _).symm
      _ ≤ ENNReal.ofReal (a ^ 2) * scalarLoad a⁻¹ v := mul_le_mul_right' hc _
      _ = scalarLoad a v := (heq v).symm
      _ = 1 * scalarLoad a v := (one_mul _).symm
      _ ≤ ENNReal.ofReal (a ^ 2) * scalarLoad a v := mul_le_mul_right' hc _
  · intro v
    exact (heq v).le

/-- Reciprocal input coefficients give reciprocal attained output coefficients. -/
theorem sharp_pair_values {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) :
    response (fun _ : Unit => r) (scalarLoad a) (fun _ => 1) =
        ENNReal.ofReal (radiusStep r a) ∧
      response (fun _ : Unit => r) (scalarLoad a⁻¹) (fun _ => 1) =
        ENNReal.ofReal ((radiusStep r a)⁻¹) := by
  constructor
  · simpa using response_scalar_eq hr hr1 (by linarith : 0 ≤ a) (fun _ => 1)
  · have h := response_scalar_eq hr hr1
      (inv_nonneg.mpr (by linarith : 0 ≤ a)) (fun _ : Unit => 1)
    simpa [radiusStep_inverse hr hr1 ha] using h

/-- Any universally valid output factor is at least the factor already
attained by this single channel. Thus the sharpness is variational, not an
unattained spectral estimate. -/
theorem output_factor_is_optimal {r a K : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) (hK : 0 ≤ K)
    (h : response (fun _ : Unit => r) (scalarLoad a) (fun _ => 1) ≤
      ENNReal.ofReal K * response (fun _ : Unit => r) (scalarLoad a⁻¹) (fun _ => 1)) :
    (radiusStep r a) ^ 2 ≤ K := by
  have hv := sharp_pair_values hr hr1 ha
  rw [hv.1, hv.2, ← ENNReal.ofReal_mul hK] at h
  have hb : 0 < radiusStep r a := radiusStep_pos hr hr1 ha
  have hnonneg : 0 ≤ K * (radiusStep r a)⁻¹ :=
    mul_nonneg hK (inv_nonneg.mpr hb.le)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hb.le, ENNReal.toReal_ofReal hnonneg] at ht
  calc
    (radiusStep r a) ^ 2 = radiusStep r a * radiusStep r a := by ring
    _ ≤ (K * (radiusStep r a)⁻¹) * radiusStep r a :=
      mul_le_mul_of_nonneg_right ht hb.le
    _ = K := by field_simp

end
end AnnularResponseSharpness
