import Mathlib

/-!
# Critical-relation transversality for the actual quadratic family

The algebraic parity proof is independent of local linearization or
parameter uniformization. No global marked-width gate is asserted.
-/

namespace LoopsQuadraticTransversality

open Polynomial
noncomputable section

def orbit (c : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => orbit c n ^ 2 + c

def slope (c : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => 2 * orbit c n * slope c n + 1

/-- The recursively computed tangent is the actual complex parameter derivative. -/
theorem orbit_hasDerivAt (n : ℕ) (c : ℂ) :
    HasDerivAt (fun w : ℂ => orbit w n) (slope c n) c := by
  induction n with
  | zero => simpa [orbit, slope] using (hasDerivAt_const c (0 : ℂ))
  | succ n ih =>
    convert (ih.pow 2).add (hasDerivAt_id c) using 1 <;>
      simp [orbit, slope, pow_one] <;> ring

/-- Integer polynomial representing the entire critical orbit. -/
def orbitPoly : ℕ → ℤ[X]
  | 0 => 0
  | n + 1 => orbitPoly n ^ 2 + X

theorem orbitPoly_aeval (c : ℂ) (n : ℕ) :
    aeval c (orbitPoly n) = orbit c n := by
  induction n with
  | zero => simp [orbitPoly, orbit]
  | succ n ih => simp [orbitPoly, orbit, ih]

theorem orbitPoly_monic_degree (n : ℕ) :
    (orbitPoly (n+1)).Monic ∧ (orbitPoly (n+1)).natDegree = 2^n := by
  induction n with
  | zero => simp [orbitPoly]
  | succ n ih =>
    have hp := ih.1.pow 2
    have hd : (orbitPoly (n+1)^2).natDegree = 2^(n+1) := by
      rw [ih.1.natDegree_pow, ih.2, pow_succ]
      ring
    have hlt : (X : ℤ[X]).natDegree < (orbitPoly (n+1)^2).natDegree := by
      rw [natDegree_X, hd, pow_succ]
      have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
      omega
    change (orbitPoly (n+1)^2 + X).Monic ∧
      (orbitPoly (n+1)^2 + X).natDegree = 2^(n+1)
    exact ⟨hp.add_of_left (degree_lt_degree hlt),
      (natDegree_add_eq_left_of_natDegree_lt hlt).trans hd⟩

theorem orbitPoly_degree_strictMono :
    StrictMono (fun n => (orbitPoly n).natDegree) := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp [orbitPoly]
  | succ n =>
    change (orbitPoly (n+1)).natDegree < (orbitPoly (n+1+1)).natDegree
    rw [(orbitPoly_monic_degree n).2, (orbitPoly_monic_degree (n+1)).2, pow_succ]
    have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
    omega

/-- Every actual collision parameter, including every center, is an algebraic integer. -/
theorem integral_of_collision (c : ℂ) (a b : ℕ) (hab : a < b)
    (h : orbit c a = orbit c b) : IsIntegral ℤ c := by
  have hm : (orbitPoly b).Monic := by
    cases b with
    | zero => omega
    | succ b => exact (orbitPoly_monic_degree b).1
  refine ⟨orbitPoly b - orbitPoly a,
    hm.sub_of_left (degree_lt_degree (orbitPoly_degree_strictMono hab)), ?_⟩
  rw [← aeval_def]
  simp [orbitPoly_aeval, h]

theorem orbit_integral {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    IsIntegral ℤ (orbit c n) := by
  induction n with
  | zero => exact isIntegral_zero
  | succ n ih =>
    simpa only [orbit, pow_two] using (ih.mul ih).add hc

theorem slope_integral {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    IsIntegral ℤ (slope c n) := by
  induction n with
  | zero => exact isIntegral_zero
  | succ n ih =>
    simpa only [slope] using
      (((isIntegral_natCast (B := ℂ) 2).mul (orbit_integral hc n)).mul ih).add
        (isIntegral_one : IsIntegral ℤ (1 : ℂ))

/-- Two cannot have an inverse among the complex algebraic integers. -/
theorem integral_not_half {x : ℂ} (hx : IsIntegral ℤ x) :
    (2 : ℂ) * x ≠ 1 := by
  intro h
  have hx' : x = (1:ℂ)/2 := by linear_combination (1/2:ℂ) * h
  let f : ℚ →ₐ[ℤ] ℂ := IsScalarTower.toAlgHom ℤ ℚ ℂ
  have hmap : f (1/2 : ℚ) = (1:ℂ)/2 := by
    simp [f]
  have hq : IsIntegral ℤ (1/2 : ℚ) := by
    apply (isIntegral_algHom_iff f f.injective).mp
    rw [hmap, ← hx']
    exact hx
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  have hz' : (z : ℚ) = 1/2 := by simpa using hz
  have hz'' : (2:ℚ) * (z:ℚ) = 1 := by linarith
  have hzInt : (2:ℤ) * z = 1 := by exact_mod_cast hz''
  omega

/-- The weighted tangent is congruent to the orbit modulo two, even at time zero. -/
theorem orbit_slope_parity {c : ℂ} (hc : IsIntegral ℤ c) (n : ℕ) :
    ∃ t : ℂ, IsIntegral ℤ t ∧
      orbit c n * slope c n = orbit c n + 2*t := by
  cases n with
  | zero => exact ⟨0, isIntegral_zero, by simp [orbit, slope]⟩
  | succ n =>
    refine ⟨orbit c (n+1) * orbit c n * slope c n,
      ((orbit_integral hc (n+1)).mul (orbit_integral hc n)).mul
        (slope_integral hc n), ?_⟩
    simp only [slope]
    ring

/-- The signed predecessor relation has nonzero derivative at every algebraic-integer
parameter satisfying it. Both indices are positive, not fixed numerical periods. -/
theorem signed_relation_transverse {c : ℂ} (hc : IsIntegral ℤ c) (a b : ℕ)
    (hsign : orbit c (a+1) + orbit c (b+1) = 0) :
    slope c (a+1) + slope c (b+1) ≠ 0 := by
  intro hzero
  obtain ⟨u, huI, hu⟩ := orbit_slope_parity hc a
  obtain ⟨v, hvI, hv⟩ := orbit_slope_parity hc b
  simp only [slope] at hzero
  have hs : orbit c a + orbit c b = -1 - 2*(u+v) := by
    linear_combination (1/2:ℂ) * hzero - hu - hv
  have hsq : (orbit c a + orbit c b)^2 =
      2*(orbit c a * orbit c b - c) := by
    simp only [orbit] at hsign
    linear_combination hsign
  let t := u+v
  let w := orbit c a * orbit c b - c - 2*t - 2*t*t
  have ht : IsIntegral ℤ t := huI.add hvI
  have h2 : IsIntegral ℤ (2:ℂ) := isIntegral_natCast 2
  have hw : IsIntegral ℤ w :=
    ((((orbit_integral hc a).mul (orbit_integral hc b)).sub hc).sub
      (h2.mul ht)).sub ((h2.mul ht).mul ht)
  apply integral_not_half hw
  dsimp [w, t]
  rw [hs] at hsq
  linear_combination -hsq

/-- Actual centers are simple roots of the critical-return polynomial,
at every positive return time (not only the exact period). -/
theorem center_transverse (c : ℂ) (n : ℕ) (h : orbit c (n+1) = 0) :
    slope c (n+1) ≠ 0 := by
  have hc := integral_of_collision c 0 (n+1) (by omega) (by simpa [orbit] using h.symm)
  intro hd
  have hi := ((orbit_integral hc n).mul (slope_integral hc n)).neg
  apply integral_not_half hi
  simp only [slope] at hd
  linear_combination -hd

/-- A collision with unequal predecessors is transverse in the actual
complex parameter. No repelling multiplier or linearization is assumed. -/
theorem first_collision_transverse (c : ℂ) (a b : ℕ) (hab : a < b)
    (hcoll : orbit c (a+2) = orbit c (b+2))
    (hprev : orbit c (a+1) ≠ orbit c (b+1)) :
    slope c (b+2) - slope c (a+2) ≠ 0 := by
  have hc := integral_of_collision c (a+2) (b+2) (by omega) hcoll
  have hprod : (orbit c (a+1)-orbit c (b+1)) *
      (orbit c (a+1)+orbit c (b+1)) = 0 := by
    change orbit c (a+1)^2+c = orbit c (b+1)^2+c at hcoll
    linear_combination hcoll
  have hsign := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hprev)
  have hb : orbit c (b+1) ≠ 0 := by
    intro hz
    rw [hz, add_zero] at hsign
    exact hprev (hsign.trans hz.symm)
  intro hd
  have hfactor : 2*orbit c (b+1)*(slope c (a+1)+slope c (b+1)) = 0 := by
    change (2*orbit c (b+1)*slope c (b+1)+1) -
      (2*orbit c (a+1)*slope c (a+1)+1) = 0 at hd
    linear_combination hd + 2*slope c (a+1)*hsign
  exact signed_relation_transverse hc a b hsign
    ((mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero (by norm_num) hb))

/-- Transversality expressed using mathlib's genuine complex derivative. -/
theorem first_collision_deriv_ne_zero (c : ℂ) (a b : ℕ) (hab : a < b)
    (hcoll : orbit c (a+2) = orbit c (b+2))
    (hprev : orbit c (a+1) ≠ orbit c (b+1)) :
    deriv (fun w : ℂ => orbit w (b+2) - orbit w (a+2)) c ≠ 0 := by
  rw [((orbit_hasDerivAt (b+2) c).sub (orbit_hasDerivAt (a+2) c)).deriv]
  exact first_collision_transverse c a b hab hcoll hprev

end
end LoopsQuadraticTransversality
