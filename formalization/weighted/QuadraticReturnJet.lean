import QuadraticCriticalTransversality

/-!
# The actual quadratic return jet at the critical point

The index `n` in the coefficients denotes the physical iterate `n + 1`.
The polynomial identity below identifies the coefficients with those of
the genuine quadratic iterate, with an exact polynomial remainder of
order at least six. At a center, scaling by the nonzero quadratic
coefficient makes the quartic coefficient `quarticCoeff / quadCoeff ^ 3`.
-/

namespace LoopsQuadraticTransversality

open Polynomial

noncomputable section

/-- Quadratic coefficient of the physical return of length `n + 1`. -/
def quadCoeff (c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => 2 * orbit c (n + 1) * quadCoeff c n

/-- Quartic coefficient of the physical return of length `n + 1`. -/
def quarticCoeff (c : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => quadCoeff c n ^ 2 + 2 * orbit c (n + 1) * quarticCoeff c n

/-- Polynomial in the initial dynamical point for the physical iterate
of length `n + 1`. -/
def criticalReturnPoly (c : ℂ) : ℕ → ℂ[X]
  | 0 => X ^ 2 + C c
  | n + 1 => criticalReturnPoly c n ^ 2 + C c

/-- The exact remainder after removing the constant, quadratic, and
quartic terms and dividing by the sixth power of the initial point. -/
def jetRemainderPoly (c : ℂ) : ℕ → ℂ[X]
  | 0 => 0
  | n + 1 =>
      C (2 * orbit c (n + 1)) * jetRemainderPoly c n +
      C (2 * quadCoeff c n * quarticCoeff c n) +
      C (quarticCoeff c n ^ 2) * X ^ 2 +
      C (2 * quadCoeff c n) * X ^ 2 * jetRemainderPoly c n +
      C (2 * quarticCoeff c n) * X ^ 4 * jetRemainderPoly c n +
      X ^ 6 * jetRemainderPoly c n ^ 2

theorem criticalReturnPoly_eval (c z : ℂ) (n : ℕ) :
    (criticalReturnPoly c n).eval z = returnOrbit c z (n + 1) := by
  induction n with
  | zero => simp [criticalReturnPoly, returnOrbit]
  | succ n ih =>
    simpa only [criticalReturnPoly, eval_add, eval_pow, eval_C, returnOrbit]
      using congrArg (fun w : ℂ => w ^ 2 + c) ih

/-- This is an identity of actual iterate polynomials, not a formal
recursion merely called a jet. -/
theorem criticalReturnPoly_jet (c : ℂ) (n : ℕ) :
    criticalReturnPoly c n =
      C (orbit c (n + 1)) + C (quadCoeff c n) * X ^ 2 +
      C (quarticCoeff c n) * X ^ 4 + X ^ 6 * jetRemainderPoly c n := by
  induction n with
  | zero =>
    simp [criticalReturnPoly, orbit, quadCoeff, quarticCoeff, jetRemainderPoly]
    <;> ring
  | succ n ih =>
    simp only [criticalReturnPoly, quadCoeff, quarticCoeff, jetRemainderPoly,
      orbit, ih, map_add, map_mul, map_pow, map_ofNat]
    ring

theorem criticalReturnPoly_coeff_zero (c : ℂ) (n : ℕ) :
    (criticalReturnPoly c n).coeff 0 = orbit c (n + 1) := by
  rw [criticalReturnPoly_jet]
  simp [coeff_X_pow_mul']

theorem criticalReturnPoly_coeff_two (c : ℂ) (n : ℕ) :
    (criticalReturnPoly c n).coeff 2 = quadCoeff c n := by
  rw [criticalReturnPoly_jet]
  simp [coeff_X_pow_mul']

theorem criticalReturnPoly_coeff_four (c : ℂ) (n : ℕ) :
    (criticalReturnPoly c n).coeff 4 = quarticCoeff c n := by
  rw [criticalReturnPoly_jet]
  simp [coeff_X_pow_mul']

/-- Exact global expansion of the genuine return map, with polynomial
remainder; no limiting argument or asymptotic identification is needed. -/
theorem returnOrbit_jet_expansion (c z : ℂ) (n : ℕ) :
    returnOrbit c z (n + 1) = orbit c (n + 1) +
      quadCoeff c n * z ^ 2 + quarticCoeff c n * z ^ 4 +
      z ^ 6 * (jetRemainderPoly c n).eval z := by
  rw [← criticalReturnPoly_eval c z n, criticalReturnPoly_jet]
  simp

theorem quadratic_iterate_jet_expansion (c z : ℂ) (n : ℕ) :
    ((fun w : ℂ => w ^ 2 + c)^[n + 1]) z = orbit c (n + 1) +
      quadCoeff c n * z ^ 2 + quarticCoeff c n * z ^ 4 +
      z ^ 6 * (jetRemainderPoly c n).eval z := by
  simpa only [returnOrbit_eq_iterate] using returnOrbit_jet_expansion c z n

theorem quadCoeff_integral {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    IsIntegral ℤ (quadCoeff c n) := by
  induction n with
  | zero => exact isIntegral_one
  | succ n ih =>
    have htwo : IsIntegral ℤ (2 : ℂ) := isIntegral_natCast 2
    exact (htwo.mul (orbit_integral hc (n + 1))).mul ih

theorem quarticCoeff_integral {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    IsIntegral ℤ (quarticCoeff c n) := by
  induction n with
  | zero => exact isIntegral_zero
  | succ n ih =>
    have htwo : IsIntegral ℤ (2 : ℂ) := isIntegral_natCast 2
    have hquad := quadCoeff_integral hc n
    simpa only [quarticCoeff, pow_two] using
      (hquad.mul hquad).add ((htwo.mul (orbit_integral hc (n + 1))).mul ih)

theorem jetRemainder_eval_integral {c z : ℂ} (hc : IsIntegral ℤ c)
    (hz : IsIntegral ℤ z) (n : ℕ) :
    IsIntegral ℤ ((jetRemainderPoly c n).eval z) := by
  induction n with
  | zero => simpa [jetRemainderPoly] using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  | succ n ih =>
    have htwo : IsIntegral ℤ (2 : ℂ) := isIntegral_natCast 2
    have hp := orbit_integral hc (n + 1)
    have ha := quadCoeff_integral hc n
    have hb := quarticCoeff_integral hc n
    have hfirst := ((htwo.mul hp).mul ih).add ((htwo.mul ha).mul hb)
    have hsecond := hfirst.add ((hb.pow 2).mul (hz.pow 2))
    have hthird := hsecond.add (((htwo.mul ha).mul (hz.pow 2)).mul ih)
    have hfourth := hthird.add (((htwo.mul hb).mul (hz.pow 4)).mul ih)
    simpa only [jetRemainderPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]
      using hfourth.add ((hz.pow 6).mul (ih.pow 2))

/-- No intermediate critical return implies a nonzero quadratic term. -/
theorem quadCoeff_ne_zero (c : ℂ) : ∀ n : ℕ,
    (∀ j < n, orbit c (j + 1) ≠ 0) → quadCoeff c n ≠ 0 := by
  intro n
  induction n with
  | zero => intro _; simp [quadCoeff]
  | succ n ih =>
    intro hcritical
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (hcritical n (by omega)))
      (ih (fun j hj => hcritical j (by omega)))

/-- The canonical linear critical normalization of the actual return. -/
def criticalNormalizedReturn (c : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  quadCoeff c n * returnOrbit c (w / quadCoeff c n) (n + 1)

/-- Its quartic coefficient, in the normalization fixing the quadratic
coefficient to one. -/
def criticalQuarticInvariant (c : ℂ) (n : ℕ) : ℂ :=
  quarticCoeff c n / quadCoeff c n ^ 3

/-- The actual normalized return, as a polynomial in the normalized
dynamical coordinate. -/
def criticalNormalizedPoly (c : ℂ) (n : ℕ) : ℂ[X] :=
  C (quadCoeff c n) *
    (criticalReturnPoly c n).comp (C ((quadCoeff c n)⁻¹) * X)

def normalizedJetRemainderPoly (c : ℂ) (n : ℕ) : ℂ[X] :=
  C ((quadCoeff c n ^ 5)⁻¹) *
    (jetRemainderPoly c n).comp (C ((quadCoeff c n)⁻¹) * X)

theorem criticalNormalizedPoly_eval (c : ℂ) (n : ℕ) (w : ℂ) :
    (criticalNormalizedPoly c n).eval w = criticalNormalizedReturn c n w := by
  simp only [criticalNormalizedPoly, eval_mul, eval_C, eval_comp, eval_X,
    criticalReturnPoly_eval, criticalNormalizedReturn, div_eq_mul_inv, mul_comm]

theorem normalizedJetRemainderPoly_eval (c : ℂ) (n : ℕ) (w : ℂ) :
    (normalizedJetRemainderPoly c n).eval w =
      (jetRemainderPoly c n).eval (w / quadCoeff c n) / quadCoeff c n ^ 5 := by
  simp only [normalizedJetRemainderPoly, eval_mul, eval_C, eval_comp, eval_X,
    div_eq_mul_inv, mul_comm]

/-- Exact transformation of the genuine return jet under the linear
critical coordinate `z ↦ s * z`. This includes the constant term away
from centers. -/
theorem linear_conjugate_return_jet (c : ℂ) (n : ℕ) {s : ℂ}
    (hs : s ≠ 0) (w : ℂ) :
    s * returnOrbit c (w / s) (n + 1) =
      s * orbit c (n + 1) + (quadCoeff c n / s) * w ^ 2 +
      (quarticCoeff c n / s ^ 3) * w ^ 4 +
      w ^ 6 * ((jetRemainderPoly c n).eval (w / s) / s ^ 5) := by
  rw [returnOrbit_jet_expansion]
  field_simp [hs]
  <;> ring

/-- The quartic ratio is unchanged by a nonzero linear critical
coordinate change. No invariance under nonlinear charts is asserted. -/
theorem linear_conjugate_quartic_invariant (c : ℂ) (n : ℕ) {s : ℂ}
    (ha : quadCoeff c n ≠ 0) (hs : s ≠ 0) :
    (quarticCoeff c n / s ^ 3) / (quadCoeff c n / s) ^ 3 =
      criticalQuarticInvariant c n := by
  unfold criticalQuarticInvariant
  field_simp [ha, hs]
  <;> ring

theorem center_normalized_return_jet {c : ℂ} (n : ℕ)
    (hcenter : orbit c (n + 1) = 0) (ha : quadCoeff c n ≠ 0) (w : ℂ) :
    criticalNormalizedReturn c n w =
      w ^ 2 + criticalQuarticInvariant c n * w ^ 4 +
      w ^ 6 * ((jetRemainderPoly c n).eval (w / quadCoeff c n) /
        quadCoeff c n ^ 5) := by
  unfold criticalNormalizedReturn criticalQuarticInvariant
  rw [returnOrbit_jet_expansion, hcenter]
  field_simp [ha]
  <;> ring

/-- Polynomial identity for the actual normalized central return. -/
theorem center_normalized_poly_jet {c : ℂ} (n : ℕ)
    (hcenter : orbit c (n + 1) = 0) (ha : quadCoeff c n ≠ 0) :
    criticalNormalizedPoly c n =
      X ^ 2 + C (criticalQuarticInvariant c n) * X ^ 4 +
      X ^ 6 * normalizedJetRemainderPoly c n := by
  apply Polynomial.funext
  intro w
  rw [criticalNormalizedPoly_eval, center_normalized_return_jet n hcenter ha]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C,
    normalizedJetRemainderPoly_eval]

theorem center_normalized_poly_coeff_zero {c : ℂ} (n : ℕ)
    (hcenter : orbit c (n + 1) = 0) (ha : quadCoeff c n ≠ 0) :
    (criticalNormalizedPoly c n).coeff 0 = 0 := by
  rw [center_normalized_poly_jet n hcenter ha]
  simp [coeff_X_pow_mul']

theorem center_normalized_poly_coeff_one {c : ℂ} (n : ℕ)
    (hcenter : orbit c (n + 1) = 0) (ha : quadCoeff c n ≠ 0) :
    (criticalNormalizedPoly c n).coeff 1 = 0 := by
  rw [center_normalized_poly_jet n hcenter ha]
  simp [coeff_X_pow_mul']

theorem center_normalized_poly_coeff_two {c : ℂ} (n : ℕ)
    (hcenter : orbit c (n + 1) = 0) (ha : quadCoeff c n ≠ 0) :
    (criticalNormalizedPoly c n).coeff 2 = 1 := by
  rw [center_normalized_poly_jet n hcenter ha]
  simp [coeff_X_pow_mul']

theorem center_normalized_poly_coeff_three {c : ℂ} (n : ℕ)
    (hcenter : orbit c (n + 1) = 0) (ha : quadCoeff c n ≠ 0) :
    (criticalNormalizedPoly c n).coeff 3 = 0 := by
  rw [center_normalized_poly_jet n hcenter ha]
  simp [coeff_X_pow_mul']

theorem center_normalized_poly_coeff_four {c : ℂ} (n : ℕ)
    (hcenter : orbit c (n + 1) = 0) (ha : quadCoeff c n ≠ 0) :
    (criticalNormalizedPoly c n).coeff 4 = criticalQuarticInvariant c n := by
  rw [center_normalized_poly_jet n hcenter ha]
  simp [coeff_X_pow_mul']

/-- The normalized remainder is itself a polynomial in the normalized
coordinate, so the displayed quartic term is an actual analytic jet. -/
theorem center_normalized_polynomial_remainder {c : ℂ} (n : ℕ)
    (hcenter : orbit c (n + 1) = 0) (ha : quadCoeff c n ≠ 0) :
    ∃ R : ℂ[X], ∀ w : ℂ,
      criticalNormalizedReturn c n w =
        w ^ 2 + criticalQuarticInvariant c n * w ^ 4 + w ^ 6 * R.eval w := by
  refine ⟨normalizedJetRemainderPoly c n, ?_⟩
  intro w
  rw [center_normalized_return_jet n hcenter ha, normalizedJetRemainderPoly_eval]

end

end LoopsQuadraticTransversality
