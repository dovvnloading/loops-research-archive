import QuadraticFlightJet

/-!
# The unique affine critical normalization

The source and target use the same nonzero affine scale. Requiring the
quadratic coefficient to be one then fixes that scale uniquely; it cannot
be made arbitrarily small to suppress the flight coefficients.
-/

namespace QuadraticCanonicalScale

open QuadraticFlightJet Polynomial

noncomputable section

theorem transport_homogeneous (c x σ : ℂ) (n : ℕ) :
    transport c x σ n = σ*transport c x 1 n := by
  induction n with
  | zero => simp [transport]
  | succ n ih =>
    simp only [transport, ih]
    ring

/-- The inverse genuine critical quadratic coefficient at this return time. -/
def canonicalScale (c : ℂ) (N : ℕ) : ℂ := (transport c c 1 N)⁻¹

theorem canonicalScale_ne_zero (c : ℂ) (N : ℕ)
    (hx : ∀ j < N, orbit c c j ≠ 0) : canonicalScale c N ≠ 0 := by
  unfold canonicalScale
  exact inv_ne_zero (transport_ne_zero c c 1 N one_ne_zero hx)

/-- The input and output scale agree in the canonical normalization. -/
theorem canonical_transport (c : ℂ) (N : ℕ)
    (hx : ∀ j < N, orbit c c j ≠ 0) :
    transport c c ((canonicalScale c N)^2) N = canonicalScale c N := by
  have hB := transport_ne_zero c c 1 N one_ne_zero hx
  rw [transport_homogeneous]
  unfold canonicalScale
  rw [pow_two, mul_assoc, inv_mul_cancel₀ hB, mul_one]

/-- Equality of the nonzero source and target scales determines the scale. -/
theorem canonicalScale_unique (c s : ℂ) (N : ℕ) (hs : s ≠ 0)
    (hmatch : transport c c (s^2) N = s) : s = canonicalScale c N := by
  rw [transport_homogeneous] at hmatch
  have hmul : s*transport c c 1 N = 1 := by
    apply mul_left_cancel₀ hs
    simpa only [pow_two, mul_assoc, mul_one] using hmatch
  have hB : transport c c 1 N ≠ 0 := by
    intro hzero
    simp only [hzero, mul_zero] at hmul
    exact zero_ne_one hmul
  unfold canonicalScale
  calc
    s = s*(transport c c 1 N*(transport c c 1 N)⁻¹) := by
      rw [mul_inv_cancel₀ hB, mul_one]
    _ = (s*transport c c 1 N)*(transport c c 1 N)⁻¹ := by ring
    _ = (transport c c 1 N)⁻¹ := by rw [hmul, one_mul]

/-- Literal centered return using the same linear scale in source and target. -/
def canonicalCriticalReturn (c : ℂ) (N : ℕ) : ℂ[X] :=
  C ((canonicalScale c N)⁻¹) *
    ((iteratePoly c (N+1)).comp (C (canonicalScale c N)*X) -
      C (orbit c 0 (N+1)))

theorem canonicalCriticalReturn_eval (c z : ℂ) (N : ℕ) :
    (canonicalCriticalReturn c N).eval z =
      ((fun w : ℂ => w^2+c)^[N+1] (canonicalScale c N*z) -
        (fun w : ℂ => w^2+c)^[N+1] 0) / canonicalScale c N := by
  simp [canonicalCriticalReturn, iteratePoly_eval, orbit_eq_iterate,
    div_eq_mul_inv] <;> ring

/-- The even flight representation holds for the uniquely normalized
critical return, not for a freely chosen vanishing zoom. -/
theorem canonicalCriticalReturn_eq_flight (c : ℂ) (N : ℕ)
    (hx : ∀ j < N, orbit c c j ≠ 0) :
    canonicalCriticalReturn c N =
      (normalizedActualFlight c c ((canonicalScale c N)^2) N).comp (X^2) := by
  have hs := canonicalScale_ne_zero c N hx
  unfold canonicalCriticalReturn
  rw [critical_return_identity c (canonicalScale c N) N hs hx,
    canonical_transport c N hx]
  simp only [add_sub_cancel_left]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul]

/-- An exact entire-polynomial expansion of the canonical critical return. -/
theorem canonicalCriticalReturn_expansion (c : ℂ) (N : ℕ)
    (hx : ∀ j < N, orbit c c j ≠ 0) :
    ∃ R : ℂ[X], canonicalCriticalReturn c N =
      X^2 + C ((flightJet (charge c c ((canonicalScale c N)^2)) N).a)*X^4 +
      C ((flightJet (charge c c ((canonicalScale c N)^2)) N).b)*X^6 +
      C ((flightJet (charge c c ((canonicalScale c N)^2)) N).d)*X^8 + X^10*R := by
  obtain ⟨R, hR⟩ := normalizedActualFlight_hasJet c c ((canonicalScale c N)^2) N
    (pow_ne_zero 2 (canonicalScale_ne_zero c N hx)) hx
  refine ⟨R.comp (X^2), ?_⟩
  rw [canonicalCriticalReturn_eq_flight c N hx, hR]
  simp only [jetPoly, add_comp, mul_comp, pow_comp, C_comp, X_comp]
  ring

theorem canonicalCriticalReturn_coeff_two (c : ℂ) (N : ℕ)
    (hx : ∀ j < N, orbit c c j ≠ 0) :
    (canonicalCriticalReturn c N).coeff 2 = 1 := by
  obtain ⟨R, hR⟩ := canonicalCriticalReturn_expansion c N hx
  rw [hR]
  simp [coeff_X_pow, coeff_X_pow_mul']

theorem canonicalCriticalReturn_coeff_four (c : ℂ) (N : ℕ)
    (hx : ∀ j < N, orbit c c j ≠ 0) :
    (canonicalCriticalReturn c N).coeff 4 =
      (flightJet (charge c c ((canonicalScale c N)^2)) N).a := by
  obtain ⟨R, hR⟩ := canonicalCriticalReturn_expansion c N hx
  rw [hR]
  simp [coeff_X_pow, coeff_X_pow_mul']

theorem canonicalCriticalReturn_coeff_six (c : ℂ) (N : ℕ)
    (hx : ∀ j < N, orbit c c j ≠ 0) :
    (canonicalCriticalReturn c N).coeff 6 =
      (flightJet (charge c c ((canonicalScale c N)^2)) N).b := by
  obtain ⟨R, hR⟩ := canonicalCriticalReturn_expansion c N hx
  rw [hR]
  simp [coeff_X_pow, coeff_X_pow_mul']

theorem canonicalCriticalReturn_coeff_eight (c : ℂ) (N : ℕ)
    (hx : ∀ j < N, orbit c c j ≠ 0) :
    (canonicalCriticalReturn c N).coeff 8 =
      (flightJet (charge c c ((canonicalScale c N)^2)) N).d := by
  obtain ⟨R, hR⟩ := canonicalCriticalReturn_expansion c N hx
  rw [hR]
  simp [coeff_X_pow, coeff_X_pow_mul']

end
end QuadraticCanonicalScale
