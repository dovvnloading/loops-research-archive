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
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
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
    push_cast <;> rfl
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


/-! The spatial collision polynomial removes the integral-starting-point
hypothesis for every preperiodic point of an integral parameter. -/

open Polynomial

/-- Polynomial for the actual spatial iterate, over any coefficient ring. -/
def spatialPoly {R : Type*} [CommRing R] (c : R) : ℕ → R[X]
  | 0 => X
  | n+1 => spatialPoly c n ^ 2 + C c

theorem spatialPoly_monic_degree {R : Type*} [CommRing R] [Nontrivial R]
    (c : R) (n : ℕ) :
    (spatialPoly c n).Monic ∧ (spatialPoly c n).natDegree = 2^n := by
  induction n with
  | zero => simp [spatialPoly]
  | succ n ih =>
    have hp := ih.1.pow 2
    have hd : (spatialPoly c n ^ 2).natDegree = 2^(n+1) := by
      rw [ih.1.natDegree_pow, ih.2, pow_succ]
      ring
    have hlt : (C c : R[X]).natDegree < (spatialPoly c n ^ 2).natDegree := by
      rw [natDegree_C, hd]
      positivity
    change (spatialPoly c n ^ 2 + C c).Monic ∧
      (spatialPoly c n ^ 2 + C c).natDegree = 2^(n+1)
    exact ⟨hp.add_of_left (degree_lt_degree hlt),
      (natDegree_add_eq_left_of_natDegree_lt hlt).trans hd⟩

theorem spatialPoly_eval₂ (c : integralClosure ℤ ℂ) (z : ℂ) (n : ℕ) :
    eval₂ (integralClosure ℤ ℂ).val.toRingHom z (spatialPoly c n) =
      returnOrbit (c:ℂ) z n := by
  induction n with
  | zero => simp [spatialPoly, returnOrbit]
  | succ n ih =>
    simp [spatialPoly, returnOrbit, eval₂_pow]
    exact congrArg (fun w : ℂ => w ^ 2) ih

/-- Every eventual spatial collision at an algebraic-integer parameter starts
at an algebraic integer. In particular no periodic orbit has to be assumed
postcritical. This uses the actual monic iterate-difference polynomial. -/
theorem integral_of_spatial_collision {c z : ℂ} (hc : IsIntegral ℤ c)
    (a b : ℕ) (hab : a < b)
    (hcoll : returnOrbit c z a = returnOrbit c z b) : IsIntegral ℤ z := by
  letI := (integralClosure ℤ ℂ).algebra
  let cc : integralClosure ℤ ℂ := ⟨c,hc⟩
  have hdeg : StrictMono (fun n => (spatialPoly cc n).natDegree) := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [(spatialPoly_monic_degree cc n).2,
      (spatialPoly_monic_degree cc (n+1)).2, pow_succ]
    have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
    omega
  have hm := (spatialPoly_monic_degree cc b).1.sub_of_left
    (degree_lt_degree (hdeg hab))
  apply isIntegral_trans (A := integralClosure ℤ ℂ) z
  refine ⟨spatialPoly cc b - spatialPoly cc a, hm, ?_⟩
  change eval₂ (integralClosure ℤ ℂ).val.toRingHom z
    (spatialPoly cc b - spatialPoly cc a) = 0
  rw [eval₂_sub, spatialPoly_eval₂, spatialPoly_eval₂]
  change returnOrbit c z b - returnOrbit c z a = 0
  exact sub_eq_zero.mpr hcoll.symm

/-- Every actual preperiodic point at an integral parameter has no neutral
positive-length iterate derivative, including all genuine periodic points. -/
theorem preperiodic_deriv_not_neutral {c z : ℂ} (hc : IsIntegral ℤ c)
    (a b n : ℕ) (hab : a < b)
    (hcoll : returnOrbit c z a = returnOrbit c z b) (hn : 0 < n) :
    ‖deriv ((fun w : ℂ => w^2+c)^[n]) z‖ ≠ 1 := by
  have hz := integral_of_spatial_collision hc a b hab hcoll
  have hd := (returnMultiplier_hasDerivAt c z n).deriv
  simp only [returnOrbit_eq_iterate] at hd
  rw [hd]
  exact returnMultiplier_not_neutral hc hz n hn

/-- At every algebraic-integer parameter, all positive-period cycles are
nonneutral; not just the periodic cycle reached by the critical point. -/
theorem periodic_deriv_not_neutral {c z : ℂ} (hc : IsIntegral ℤ c)
    (p : ℕ) (hp : 0 < p)
    (hper : (fun w : ℂ => w^2+c)^[p] z = z) :
    ‖deriv ((fun w : ℂ => w^2+c)^[p]) z‖ ≠ 1 := by
  have hcoll : returnOrbit c z 0 = returnOrbit c z p := by
    change z = returnOrbit c z p
    rw [returnOrbit_eq_iterate]
    exact hper.symm
  exact preperiodic_deriv_not_neutral hc 0 p p hp hcoll hp

/-- Arithmetic exclusion of neutral cycles anywhere in the actual dynamical
plane of every quadratic critical-collision parameter. -/
theorem collision_parameter_all_cycles_nonneutral (c : ℂ) (a b : ℕ)
    (hab : a < b) (hcoll : orbit c a = orbit c b)
    (z : ℂ) (p : ℕ) (hp : 0 < p)
    (hper : (fun w : ℂ => w^2+c)^[p] z = z) :
    ‖deriv ((fun w : ℂ => w^2+c)^[p]) z‖ ≠ 1 :=
  periodic_deriv_not_neutral (integral_of_collision c a b hab hcoll) p hp hper

/-- Full quantization of the squared norm of the derivative at every actual
preperiodic point of an integral parameter. -/
theorem preperiodic_deriv_rational_normSq {c z : ℂ} (hc : IsIntegral ℤ c)
    (a b n : ℕ) (hab : a < b)
    (hcoll : returnOrbit c z a = returnOrbit c z b) {q : ℚ}
    (hq : ‖deriv ((fun w : ℂ => w^2+c)^[n]) z‖^2 = (q:ℝ)) :
    ∃ k : ℤ, 0 ≤ k ∧ q = (4:ℚ)^n * (k:ℚ) := by
  have hz := integral_of_spatial_collision hc a b hab hcoll
  have hd := (returnMultiplier_hasDerivAt c z n).deriv
  simp only [returnOrbit_eq_iterate] at hd
  rw [hd] at hq
  exact returnMultiplier_rational_normSq hc hz n hq

/-- The arithmetic gap is sharp for the actual fixed point 1 of z ↦ z². -/
theorem zero_parameter_fixed_one_sharp (n : ℕ) :
    ‖deriv ((fun w : ℂ => w^2+(0:ℂ))^[n]) (1:ℂ)‖^2 = (4:ℝ)^n := by
  have horb : ∀ k : ℕ, returnOrbit 0 1 k = 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [returnOrbit, ih]
  have hprod : orbitProduct 0 1 n = 1 := by
    induction n with
    | zero => rfl
    | succ k ih => simp [orbitProduct, horb, ih]
  have hd := (returnMultiplier_hasDerivAt 0 1 n).deriv
  simp only [returnOrbit_eq_iterate] at hd
  rw [hd, returnMultiplier_normSq_factor, hprod]
  simp

end

end LoopsQuadraticTransversality
