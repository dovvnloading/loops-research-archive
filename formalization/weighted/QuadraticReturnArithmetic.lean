import QuadraticCriticalUnits
import QuadraticReturnJet

/-!
# Exact arithmetic cost of normalizing a quadratic critical return

At an exact critical center of physical period `n + 2`, the quartic
coefficient of the return with quadratic coefficient one has exact
power-of-two denominator `2 * n + 3`.  The statement concerns the
actual complex family and algebraic integrality over the integers.
-/

namespace LoopsQuadraticReturnArithmetic

open LoopsQuadraticTransversality LoopsQuadraticCriticalUnits

noncomputable section

/-- An integral element with an explicit inverse modulo two. -/
def OddIntegral (x : ℂ) : Prop :=
  IsIntegral ℤ x ∧ ∃ y z : ℂ,
    IsIntegral ℤ y ∧ IsIntegral ℤ z ∧ x * y = 1 + 2 * z

theorem oddIntegral_one : OddIntegral 1 := by
  exact ⟨isIntegral_one, 1, 0, isIntegral_one, isIntegral_zero, by ring⟩

theorem oddIntegral_of_unit {x : ℂ} (hx : IsIntegral ℤ x)
    (hi : IsIntegral ℤ x⁻¹) (hne : x ≠ 0) : OddIntegral x := by
  exact ⟨hx, x⁻¹, 0, hi, isIntegral_zero, by simp [hne]⟩

theorem OddIntegral.mul {x y : ℂ} (hx : OddIntegral x) (hy : OddIntegral y) :
    OddIntegral (x * y) := by
  obtain ⟨hxI, a, b, haI, hbI, hab⟩ := hx
  obtain ⟨hyI, d, e, hdI, heI, hde⟩ := hy
  refine ⟨hxI.mul hyI, a*d, b+e+2*b*e, haI.mul hdI,
    (hbI.add heI).add (((isIntegral_natCast 2).mul hbI).mul heI), ?_⟩
  calc
    (x*y)*(a*d) = (x*a)*(y*d) := by ring
    _ = (1+2*b)*(1+2*e) := by rw [hab, hde]
    _ = 1+2*(b+e+2*b*e) := by ring

theorem OddIntegral.add_two_mul {x t : ℂ} (hx : OddIntegral x)
    (ht : IsIntegral ℤ t) : OddIntegral (x + 2*t) := by
  obtain ⟨hxI, a, b, haI, hbI, hab⟩ := hx
  refine ⟨hxI.add ((isIntegral_natCast 2).mul ht), a, b+t*a,
    haI, hbI.add (ht.mul haI), ?_⟩
  linear_combination hab

theorem OddIntegral.not_half_integral {x : ℂ} (hx : OddIntegral x) :
    ¬ IsIntegral ℤ (x/2) := by
  obtain ⟨_, a, b, haI, hbI, hab⟩ := hx
  intro hh
  apply integral_not_half ((hh.mul haI).sub hbI)
  linear_combination hab

/-- Product of the noninitial critical values before the shifted return. -/
def criticalProduct (c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => orbit c (n+1) * criticalProduct c n

/-- Integral numerator after removing the forced powers of two from the
quartic coefficient. Index `n` corresponds to physical return `n + 2`. -/
def quarticNumerator (c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => (2:ℂ)^(n+1) * criticalProduct c (n+1)^2 +
      orbit c (n+2) * quarticNumerator c n

theorem criticalProduct_integral {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    IsIntegral ℤ (criticalProduct c n) := by
  induction n with
  | zero => exact isIntegral_one
  | succ n ih => exact (orbit_integral hc (n+1)).mul ih

theorem quadCoeff_factor (c : ℂ) (n : ℕ) :
    quadCoeff c n = (2:ℂ)^n * criticalProduct c n := by
  induction n with
  | zero => simp [quadCoeff, criticalProduct]
  | succ n ih =>
    simp only [quadCoeff, criticalProduct, pow_succ, ih]
    ring

theorem quarticCoeff_factor (c : ℂ) (n : ℕ) :
    quarticCoeff c (n+1) = (2:ℂ)^n * quarticNumerator c n := by
  induction n with
  | zero => simp [quarticCoeff, quadCoeff, quarticNumerator]
  | succ n ih =>
    change quadCoeff c (n+1)^2 + 2*orbit c (n+2)*quarticCoeff c (n+1) =
      (2:ℂ)^(n+1) * ((2:ℂ)^(n+1)*criticalProduct c (n+1)^2 +
        orbit c (n+2)*quarticNumerator c n)
    rw [ih, quadCoeff_factor]
    simp only [pow_succ]
    ring

theorem criticalProduct_unit (c : ℂ) (N : ℕ) (hN : 0 < N)
    (hcenter : orbit c N = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < N → orbit c j ≠ 0)
    (n : ℕ) (hn : n < N) :
    IsIntegral ℤ (criticalProduct c n) ∧
      IsIntegral ℤ (criticalProduct c n)⁻¹ ∧ criticalProduct c n ≠ 0 := by
  have hc : IsIntegral ℤ c :=
    integral_of_collision c 0 N hN (by simpa only [orbit] using hcenter.symm)
  induction n with
  | zero =>
    exact ⟨isIntegral_one, by simpa [criticalProduct] using
      (isIntegral_one : IsIntegral ℤ (1:ℂ)), by simp [criticalProduct]⟩
  | succ n ih =>
    have hj : orbit c (n+1) ≠ 0 := hmin (n+1) (by omega) hn
    obtain ⟨ha, hi, hz⟩ := ih (by omega)
    refine ⟨(orbit_integral hc (n+1)).mul ha, ?_, mul_ne_zero hj hz⟩
    simpa only [criticalProduct, mul_inv_rev] using
      hi.mul (center_orbit_inv_integral c N hN hcenter (n+1) hj)

theorem quarticNumerator_odd (c : ℂ) (N : ℕ) (hN : 0 < N)
    (hcenter : orbit c N = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < N → orbit c j ≠ 0)
    (n : ℕ) (hn : n+1 < N) : OddIntegral (quarticNumerator c n) := by
  have hc : IsIntegral ℤ c :=
    integral_of_collision c 0 N hN (by simpa only [orbit] using hcenter.symm)
  induction n with
  | zero => exact oddIntegral_one
  | succ n ih =>
    have hj : orbit c (n+2) ≠ 0 := hmin (n+2) (by omega) hn
    have hP := oddIntegral_of_unit (orbit_integral hc (n+2))
      (center_orbit_inv_integral c N hN hcenter (n+2) hj) hj
    have hW := hP.mul (ih (by omega))
    have hV := criticalProduct_integral hc (n+1)
    have ht : IsIntegral ℤ ((2:ℂ)^n * criticalProduct c (n+1)^2) :=
      ((isIntegral_natCast 2).pow n).mul (hV.pow 2)
    have hh := hW.add_two_mul ht
    convert hh using 1 <;> simp only [quarticNumerator, pow_succ] <;> ring

/-- The quartic coefficient of the linearly normalized physical return
of length `n + 2`. Its exact polynomial expansion is proved below. -/
def normalizedQuartic (c : ℂ) (n : ℕ) : ℂ :=
  quarticCoeff c (n+1) / quadCoeff c (n+1)^3

theorem normalizedQuartic_scaled (c : ℂ) (n : ℕ)
    (hV : criticalProduct c (n+1) ≠ 0) :
    (2:ℂ)^(2*n+3) * normalizedQuartic c n =
      quarticNumerator c n * (criticalProduct c (n+1)⁻¹)^3 := by
  rw [normalizedQuartic, quadCoeff_factor, quarticCoeff_factor]
  have h2 : (2:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpow : (2:ℂ)^(2*n+3) = ((2:ℂ)^n)^2 * 8 := by
    rw [show 2*n+3 = n+n+3 by omega, pow_add, pow_add]
    ring
  rw [hpow, pow_succ]
  field_simp [hV, h2]
  <;> ring

/-- Exact modulo-two certificate, independent of any chosen embedding or
nonarchimedean valuation. All hypotheses refer to the actual critical orbit. -/
theorem normalizedQuartic_odd_numerator (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0) :
    OddIntegral ((2:ℂ)^(2*n+3) * normalizedQuartic c n) := by
  obtain ⟨hVI, hIi, hV⟩ := criticalProduct_unit c (n+2) (by omega)
    hcenter hmin (n+1) (by omega)
  rw [normalizedQuartic_scaled c n hV]
  have hInv : OddIntegral (criticalProduct c (n+1)⁻¹) :=
    oddIntegral_of_unit hIi (by simpa using hVI) (inv_ne_zero hV)
  have hCube : OddIntegral ((criticalProduct c (n+1)⁻¹)^3) := by
    convert (hInv.mul hInv).mul hInv using 1 <;> ring
  exact (quarticNumerator_odd c (n+2) (by omega) hcenter hmin n (by omega)).mul hCube

theorem odd_numerator_denominator_exact (x : ℂ) (e : ℕ)
    (hx : OddIntegral ((2:ℂ)^e * x)) (k : ℕ) :
    IsIntegral ℤ ((2:ℂ)^k * x) ↔ e ≤ k := by
  constructor
  · intro hk
    by_contra hle
    have hlt : k < e := Nat.lt_of_not_ge hle
    have he : k + (e-k-1) + 1 = e := by omega
    have hp : IsIntegral ℤ ((2:ℂ)^(e-k-1) * ((2:ℂ)^k*x)) :=
      ((isIntegral_natCast 2).pow (e-k-1)).mul hk
    have hpow : (2:ℂ)^e = (2:ℂ)^k * (2:ℂ)^(e-k-1) * 2 := by
      calc
        (2:ℂ)^e = (2:ℂ)^(k+(e-k-1)+1) := congrArg (fun j : ℕ => (2:ℂ)^j) he.symm
        _ = (2:ℂ)^k * (2:ℂ)^(e-k-1) * 2 := by rw [pow_succ, pow_add]
    apply hx.not_half_integral
    convert hp using 1
    rw [hpow]
    ring
  · intro hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hp := ((isIntegral_natCast 2).pow d).mul hx.1
    convert hp using 1 <;> rw [pow_add] <;> ring

/-- Main obstruction: the least power of two making the normalized
quartic coefficient integral is exactly `2N-1`, where `N=n+2`. -/
theorem normalizedQuartic_integral_iff (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0) (k : ℕ) :
    IsIntegral ℤ ((2:ℂ)^k * normalizedQuartic c n) ↔ 2*n+3 ≤ k :=
  odd_numerator_denominator_exact (normalizedQuartic c n) (2*n+3)
    (normalizedQuartic_odd_numerator c n hcenter hmin) k

/-- In particular the canonical quartic coefficient is never integral
at any exact critical center of period at least two. -/
theorem normalizedQuartic_not_integral (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0) :
    ¬ IsIntegral ℤ (normalizedQuartic c n) := by
  have hh := normalizedQuartic_integral_iff c n hcenter hmin 0
  simp only [pow_zero, one_mul] at hh
  intro h
  have := hh.mp h
  omega

/-- The arithmetic obstruction is attached to the genuine polynomial
iterate in its canonical linear critical coordinate, with a polynomial
remainder proving that this is its actual quartic coefficient. -/
theorem actual_center_return_jet_denominator (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0) :
    ∃ R : Polynomial ℂ,
      (∀ w : ℂ, quadCoeff c (n+1) *
        ((fun z : ℂ => z^2+c)^[n+2]) (w / quadCoeff c (n+1)) =
          w^2 + normalizedQuartic c n * w^4 + w^6 * R.eval w) ∧
      (∀ k : ℕ, IsIntegral ℤ ((2:ℂ)^k * normalizedQuartic c n) ↔
        2*n+3 ≤ k) := by
  have ha : quadCoeff c (n+1) ≠ 0 :=
    quadCoeff_ne_zero c (n+1) (fun j hj => hmin (j+1) (by omega) (by omega))
  obtain ⟨R, hR⟩ := center_normalized_polynomial_remainder (n+1) hcenter ha
  refine ⟨R, ?_, normalizedQuartic_integral_iff c n hcenter hmin⟩
  intro w
  simpa only [criticalNormalizedReturn, criticalQuarticInvariant,
    normalizedQuartic, returnOrbit_eq_iterate] using hR w

/-- Period two is a concrete nonvacuous check of the exact denominator. -/
theorem basilica_normalizedQuartic : normalizedQuartic (-1) 0 = -(1:ℂ)/8 := by
  norm_num [normalizedQuartic, quarticCoeff, quadCoeff, orbit]

/-- An integral change of the quartic coefficient cannot conceal its
exact arithmetic denominator. -/
theorem normalizedQuartic_add_integral_iff (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0)
    (t : ℂ) (ht : IsIntegral ℤ t) (k : ℕ) :
    IsIntegral ℤ ((2:ℂ)^k * (normalizedQuartic c n + t)) ↔ 2*n+3 ≤ k := by
  have ht' : IsIntegral ℤ ((2:ℂ)^k * t) := ((isIntegral_natCast 2).pow k).mul ht
  rw [← normalizedQuartic_integral_iff c n hcenter hmin k]
  constructor
  · intro h
    convert h.sub ht' using 1 <;> ring
  · intro h
    convert h.add ht' using 1 <;> ring

/-- The half-quartic coefficient forced by the Böttcher equation has
one further exact factor of two in its denominator. -/
theorem half_normalizedQuartic_integral_iff (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0) (k : ℕ) :
    IsIntegral ℤ ((2:ℂ)^k * (normalizedQuartic c n / 2)) ↔ 2*n+4 ≤ k := by
  have hh : OddIntegral ((2:ℂ)^(2*n+4) * (normalizedQuartic c n / 2)) := by
    convert normalizedQuartic_odd_numerator c n hcenter hmin using 1
    rw [show 2*n+4 = (2*n+3)+1 by omega, pow_succ]
    ring
  exact odd_numerator_denominator_exact _ _ hh k

/-- The return period is determined by the arithmetic of the normalized
quartic coefficient, even after a field automorphism of the complex numbers. -/
theorem normalizedQuartic_galois_period_rigidity (c d : ℂ) (n m : ℕ)
    (hc : orbit c (n+2) = 0)
    (hcm : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0)
    (hd : orbit d (m+2) = 0)
    (hdm : ∀ j : ℕ, 0 < j → j < m+2 → orbit d j ≠ 0)
    (σ : ℂ ≃+* ℂ) (hσ : σ (normalizedQuartic c n) = normalizedQuartic d m) :
    n = m := by
  have hIc := (normalizedQuartic_integral_iff c n hc hcm (2*n+3)).2 le_rfl
  have hId := (normalizedQuartic_integral_iff d m hd hdm (2*m+3)).2 le_rfl
  have hmap := map_isIntegral_int σ.toRingHom hIc
  change IsIntegral ℤ (σ ((2:ℂ)^(2*n+3) * normalizedQuartic c n)) at hmap
  have hmap' : IsIntegral ℤ ((2:ℂ)^(2*n+3) * normalizedQuartic d m) := by
    simpa only [map_mul, map_pow, map_ofNat, hσ] using hmap
  have hback := map_isIntegral_int σ.symm.toRingHom hId
  change IsIntegral ℤ (σ.symm ((2:ℂ)^(2*m+3) * normalizedQuartic d m)) at hback
  have hback' : IsIntegral ℤ ((2:ℂ)^(2*m+3) * normalizedQuartic c n) := by
    simpa [← hσ] using hback
  have hnm := (normalizedQuartic_integral_iff d m hd hdm (2*n+3)).1 hmap'
  have hmn := (normalizedQuartic_integral_iff c n hc hcm (2*m+3)).1 hback'
  omega

/-- No unbounded-period family of genuine centers admits one denominator
bound for all of its canonically normalized quartic coefficients. -/
theorem no_uniform_normalizedQuartic_denominator (c : ℕ → ℂ) (n : ℕ → ℕ)
    (hcenter : ∀ i, orbit (c i) (n i+2) = 0)
    (hmin : ∀ i j : ℕ, 0 < j → j < n i+2 → orbit (c i) j ≠ 0)
    (hunbounded : ∀ K : ℕ, ∃ i : ℕ, K < n i) :
    ¬ ∃ k : ℕ, ∀ i : ℕ, IsIntegral ℤ ((2:ℂ)^k * normalizedQuartic (c i) (n i)) := by
  rintro ⟨k, hk⟩
  obtain ⟨i, hi⟩ := hunbounded k
  have hh := (normalizedQuartic_integral_iff (c i) (n i) (hcenter i) (hmin i) k).1 (hk i)
  omega

end

end LoopsQuadraticReturnArithmetic
