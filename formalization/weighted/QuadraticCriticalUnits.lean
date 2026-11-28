import QuadraticCriticalTransversality

/-!
# Integral inverses on a periodic quadratic critical orbit

The quotient below factors the genuine spatial return at the critical
point.  When zero and a nonzero integral point are both periodic for the
same return, it gives an explicit integral inverse of that point.  The
application is to the nonzero entries of an exact critical cycle.
-/

namespace LoopsQuadraticCriticalUnits

open LoopsQuadraticTransversality

noncomputable section

/-- The quotient after removing the initial quadratic critical factor.
The index `n` corresponds to the spatial return of length `n + 1`. -/
def criticalReturnQuotient (c z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
      (returnOrbit c z (n + 1) + orbit c (n + 1)) *
        criticalReturnQuotient c z n

/-- Exact factorization of the actual iterate, with no division. -/
theorem criticalReturnQuotient_factor (c z : ℂ) (n : ℕ) :
    returnOrbit c z (n + 1) - orbit c (n + 1) =
      z ^ 2 * criticalReturnQuotient c z n := by
  induction n with
  | zero => simp [returnOrbit, orbit, criticalReturnQuotient]
  | succ n ih =>
    change (returnOrbit c z (n + 1) ^ 2 + c) -
        (orbit c (n + 1) ^ 2 + c) =
      z ^ 2 * ((returnOrbit c z (n + 1) + orbit c (n + 1)) *
        criticalReturnQuotient c z n)
    calc
      (returnOrbit c z (n + 1) ^ 2 + c) -
          (orbit c (n + 1) ^ 2 + c) =
          (returnOrbit c z (n + 1) - orbit c (n + 1)) *
            (returnOrbit c z (n + 1) + orbit c (n + 1)) := by ring
      _ = z ^ 2 *
          ((returnOrbit c z (n + 1) + orbit c (n + 1)) *
            criticalReturnQuotient c z n) := by rw [ih]; ring

private theorem integral_returnOrbit {c z : ℂ}
    (hc : IsIntegral ℤ c) (hz : IsIntegral ℤ z) (n : ℕ) :
    IsIntegral ℤ (returnOrbit c z n) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    simpa only [returnOrbit, pow_two] using (ih.mul ih).add hc

/-- The explicit quotient is integral at integral inputs. -/
theorem criticalReturnQuotient_integral {c z : ℂ}
    (hc : IsIntegral ℤ c) (hz : IsIntegral ℤ z) (n : ℕ) :
    IsIntegral ℤ (criticalReturnQuotient c z n) := by
  induction n with
  | zero => exact isIntegral_one
  | succ n ih =>
    exact ((integral_returnOrbit hc hz (n + 1)).add
      (orbit_integral hc (n + 1))).mul ih

/-- If the critical point and a nonzero integral point return at the same
positive time, the quotient is an explicit integral multiplicative inverse. -/
theorem center_periodic_integral_inverse {c z : ℂ}
    (hc : IsIntegral ℤ c) (hz : IsIntegral ℤ z)
    (N : ℕ) (hN : 0 < N) (hcenter : orbit c N = 0)
    (hperiodic : returnOrbit c z N = z) (hne : z ≠ 0) :
    ∃ u : ℂ, IsIntegral ℤ u ∧ z * u = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  refine ⟨criticalReturnQuotient c z n,
    criticalReturnQuotient_integral hc hz n, ?_⟩
  have hfactor := criticalReturnQuotient_factor c z n
  rw [hcenter, hperiodic, sub_zero] at hfactor
  have hzero : z * (z * criticalReturnQuotient c z n - 1) = 0 := by
    linear_combination -hfactor
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hne)

/-- A critical return makes every later critical-orbit entry periodic. -/
theorem center_orbit_periodic (c : ℂ) (N : ℕ)
    (hcenter : orbit c N = 0) (j : ℕ) :
    returnOrbit c (orbit c j) N = orbit c j := by
  have hshift : ∀ k : ℕ, orbit c (N + k) = orbit c k := by
    intro k
    induction k with
    | zero => simpa only [Nat.add_zero, orbit] using hcenter
    | succ k ih =>
      change orbit c (N + k) ^ 2 + c = orbit c k ^ 2 + c
      rw [ih]
  rw [returnOrbit_orbit, Nat.add_comm j N]
  exact hshift j

/-- Every nonzero point on a periodic critical orbit has an explicit
integral inverse. Exact period is unnecessary once nonvanishing is supplied. -/
theorem center_orbit_integral_inverse (c : ℂ) (N : ℕ)
    (hN : 0 < N) (hcenter : orbit c N = 0) (j : ℕ)
    (hne : orbit c j ≠ 0) :
    ∃ u : ℂ, IsIntegral ℤ u ∧ orbit c j * u = 1 := by
  have hc : IsIntegral ℤ c :=
    integral_of_collision c 0 N hN (by simpa only [orbit] using hcenter.symm)
  exact center_periodic_integral_inverse hc (orbit_integral hc j) N hN
    hcenter (center_orbit_periodic c N hcenter j) hne

/-- Integral-unit witness in the argument order used by critical return
coefficient computations. -/
theorem orbit_unit_of_center (c : ℂ) (N j : ℕ) (hN : 0 < N)
    (hcenter : orbit c N = 0) (hne : orbit c j ≠ 0) :
    ∃ u : ℂ, IsIntegral ℤ u ∧ orbit c j * u = 1 :=
  center_orbit_integral_inverse c N hN hcenter j hne

/-- The field inverse is integral, in a form convenient for normalized
coefficients of the genuine critical return. -/
theorem center_orbit_inv_integral (c : ℂ) (N : ℕ)
    (hN : 0 < N) (hcenter : orbit c N = 0) (j : ℕ)
    (hne : orbit c j ≠ 0) :
    IsIntegral ℤ (orbit c j)⁻¹ := by
  obtain ⟨u, hu, hmul⟩ :=
    center_orbit_integral_inverse c N hN hcenter j hne
  have hinv : (orbit c j)⁻¹ = u := by
    apply mul_left_cancel₀ hne
    rw [mul_inv_cancel₀ hne]
    exact hmul.symm
  rw [hinv]
  exact hu

/-- At an exact center, every critical-orbit entry before the first return
is an algebraic unit. This statement concerns the actual quadratic family. -/
theorem exact_center_orbit_unit (c : ℂ) (N : ℕ)
    (hN : 0 < N) (hcenter : orbit c N = 0)
    (hmin : ∀ k : ℕ, 0 < k → k < N → orbit c k ≠ 0)
    (j : ℕ) (hj : 0 < j) (hjN : j < N) :
    IsIntegral ℤ (orbit c j) ∧ IsIntegral ℤ (orbit c j)⁻¹ := by
  have hc : IsIntegral ℤ c :=
    integral_of_collision c 0 N hN (by simpa only [orbit] using hcenter.symm)
  exact ⟨orbit_integral hc j,
    center_orbit_inv_integral c N hN hcenter j (hmin j hj hjN)⟩

end

end LoopsQuadraticCriticalUnits
