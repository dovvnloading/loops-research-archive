import QuadraticCriticalTransversality

/-! Arithmetic restrictions on genuine spatial multipliers of the quadratic
family, using the actual return orbit and integrality over the integers. -/

namespace LoopsQuadraticTransversality

noncomputable section

theorem returnOrbit_integral {c z : ℂ} (hc : IsIntegral ℤ c)
    (hz : IsIntegral ℤ z) (n : ℕ) : IsIntegral ℤ (returnOrbit c z n) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    simpa only [returnOrbit, pow_two] using (ih.mul ih).add hc

/-- Product of the first n actual orbit points. -/
def orbitProduct (c z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => returnOrbit c z n * orbitProduct c z n

theorem orbitProduct_integral {c z : ℂ} (hc : IsIntegral ℤ c)
    (hz : IsIntegral ℤ z) (n : ℕ) : IsIntegral ℤ (orbitProduct c z n) := by
  induction n with
  | zero => exact isIntegral_one
  | succ n ih => exact (returnOrbit_integral hc hz n).mul ih

/-- Exact factorization of the actual spatial derivative. -/
theorem returnMultiplier_factor (c z : ℂ) (n : ℕ) :
    returnMultiplier c z n = (2:ℂ)^n * orbitProduct c z n := by
  induction n with
  | zero => simp [returnMultiplier, orbitProduct]
  | succ n ih =>
    simp only [returnMultiplier, orbitProduct, pow_succ, ih]
    ring

theorem returnMultiplier_normSq_factor (c z : ℂ) (n : ℕ) :
    ‖returnMultiplier c z n‖^2 = (4:ℝ)^n * ‖orbitProduct c z n‖^2 := by
  have htwo : ‖(2:ℂ)‖ = 2 := by norm_num
  have hpow : ((2:ℝ)^n)^2 = (4:ℝ)^n := by
    rw [pow_two, ← mul_pow] <;> norm_num
  rw [returnMultiplier_factor, norm_mul, norm_pow, htwo, mul_pow, hpow]

/-- A rational squared modulus of a complex algebraic integer is an integer. -/
theorem rational_normSq_integral {u : ℂ} (hu : IsIntegral ℤ u)
    {q : ℚ} (hq : ‖u‖^2 = (q:ℝ)) :
    ∃ k : ℤ, q = (k:ℚ) := by
  have hconj : IsIntegral ℤ ((starRingEnd ℂ) u) :=
    map_isIntegral_int (starRingEnd ℂ) hu
  have hI : IsIntegral ℤ ((‖u‖^2 : ℝ):ℂ) := by
    rw [← Complex.mul_conj']
    exact hu.mul hconj
  let f : ℚ →ₐ[ℤ] ℂ := IsScalarTower.toAlgHom ℤ ℚ ℂ
  have hf : f q = ((q:ℝ):ℂ) := by simp [f]
  have hqI : IsIntegral ℤ q := by
    apply (isIntegral_algHom_iff f f.injective).mp
    rw [hf, ← hq]
    exact hI
  obtain ⟨k,hk⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqI
  exact ⟨k, by simpa using hk.symm⟩

/-- Rational squared modulus is an exact nonnegative integer multiple of 4^n,
with no periodicity or dynamical expansion hypothesis. -/
theorem returnMultiplier_rational_normSq {c z : ℂ} (hc : IsIntegral ℤ c)
    (hz : IsIntegral ℤ z) (n : ℕ) {q : ℚ}
    (hq : ‖returnMultiplier c z n‖^2 = (q:ℝ)) :
    ∃ k : ℤ, 0 ≤ k ∧ q = (4:ℚ)^n * (k:ℚ) := by
  have hs := returnMultiplier_normSq_factor c z n
  have hq' : ‖orbitProduct c z n‖^2 = ((q / (4:ℚ)^n : ℚ):ℝ) := by
    push_cast
    apply (eq_div_iff (by positivity : (4:ℝ)^n ≠ 0)).2
    calc
      ‖orbitProduct c z n‖^2 * (4:ℝ)^n =
          (4:ℝ)^n * ‖orbitProduct c z n‖^2 := mul_comm _ _
      _ = ‖returnMultiplier c z n‖^2 := hs.symm
      _ = (q:ℝ) := hq
  obtain ⟨k,hk⟩ := rational_normSq_integral (orbitProduct_integral hc hz n) hq'
  have he : ‖orbitProduct c z n‖^2 = (k:ℝ) := by
    rw [hq', hk]
    push_cast
  have hkn : (0:ℝ) ≤ (k:ℝ) := by
    rw [← he]
    positivity
  refine ⟨k, by exact_mod_cast hkn, ?_⟩
  have hh := (div_eq_iff (by positivity : (4:ℚ)^n ≠ 0)).mp hk
  simpa [mul_comm] using hh

theorem returnMultiplier_rational_normSq_gap {c z : ℂ} (hc : IsIntegral ℤ c)
    (hz : IsIntegral ℤ z) (n : ℕ) {q : ℚ}
    (hq : ‖returnMultiplier c z n‖^2 = (q:ℝ))
    (hne : returnMultiplier c z n ≠ 0) : (4:ℚ)^n ≤ q := by
  obtain ⟨k,hk,h⟩ := returnMultiplier_rational_normSq hc hz n hq
  have hk0 : k ≠ 0 := by
    intro hkz
    have hq0 : q = 0 := by simpa [hkz] using h
    have hnpos : 0 < ‖returnMultiplier c z n‖ := norm_pos_iff.mpr hne
    have hsq : ‖returnMultiplier c z n‖^2 = 0 := by simpa [hq0] using hq
    nlinarith
  have hk1 : (1:ℚ) ≤ (k:ℚ) := by
    exact_mod_cast (show (1:ℤ) ≤ k by omega)
  rw [h]
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hk1 (show 0 ≤ (4:ℚ)^n by positivity))

/-- Neutrality is arithmetically impossible at positive iteration length. -/
theorem returnMultiplier_not_neutral {c z : ℂ} (hc : IsIntegral ℤ c)
    (hz : IsIntegral ℤ z) (n : ℕ) (hn : 0 < n) :
    ‖returnMultiplier c z n‖ ≠ 1 := by
  intro he
  have hne : returnMultiplier c z n ≠ 0 := by
    intro hz'
    simp [hz'] at he
  have hq : ‖returnMultiplier c z n‖^2 = ((1:ℚ):ℝ) := by
    rw [he]
    norm_num
  have hgap := returnMultiplier_rational_normSq_gap hc hz n hq hne
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ] at hgap
  have hj : (1:ℚ) ≤ (4:ℚ)^j := one_le_pow₀ (by norm_num)
  linarith

/-- The actual spatial derivative on the postcritical orbit of every
collision parameter cannot be neutral, even at a nonreturn time. -/
theorem collision_return_deriv_not_neutral (c : ℂ) (a b m n : ℕ)
    (hab : a < b) (hcoll : orbit c a = orbit c b) (hn : 0 < n) :
    ‖deriv (fun w : ℂ => returnOrbit c w n) (orbit c m)‖ ≠ 1 := by
  have hc := integral_of_collision c a b hab hcoll
  rw [(returnMultiplier_hasDerivAt c (orbit c m) n).deriv]
  exact returnMultiplier_not_neutral hc (orbit_integral hc m) n hn

theorem collision_return_deriv_rational_gap (c : ℂ) (a b m n : ℕ)
    (hab : a < b) (hcoll : orbit c a = orbit c b) {q : ℚ}
    (hq : ‖deriv (fun w : ℂ => returnOrbit c w n) (orbit c m)‖^2 = (q:ℝ))
    (hne : deriv (fun w : ℂ => returnOrbit c w n) (orbit c m) ≠ 0) :
    (4:ℚ)^n ≤ q := by
  have hc := integral_of_collision c a b hab hcoll
  rw [(returnMultiplier_hasDerivAt c (orbit c m) n).deriv] at hq hne
  exact returnMultiplier_rational_normSq_gap hc (orbit_integral hc m) n hq hne

end LoopsQuadraticTransversality
