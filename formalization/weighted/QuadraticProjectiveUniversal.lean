import QuadraticProjectiveResidue
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots

/-!
# Universal polynomial dependence of the critical return residue

The inner polynomial variable records the quartic correction and the outer
variable records the multiplier.  Lifting a pointwise divisibility statement
to this polynomial ring produces one quotient that works for all corrections.
In particular, evaluating the correction at a varying parameter does not
require a discontinuous choice of pointwise quotients.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Polynomial

/-- The normalized critical tail with its quartic correction left as an
indeterminate in the coefficient ring. -/
def aU : ℕ → (ℂ[X])[X]
  | 0 => C (C (-1 / 2 : ℂ))
  | n + 1 => aU n + X ^ n * (aU n) ^ 2 *
      (1 + C (X : ℂ[X]) * X ^ 2 * (1 + X ^ n * aU n) ^ 2)

/-- Universal normalized increment. -/
def incU (n : ℕ) : (ℂ[X])[X] :=
  (aU n) ^ 2 * (1 + C (X : ℂ[X]) * X ^ 2 * (1 + X ^ n * aU n) ^ 2)

/-- Universal divided tail. -/
def HU (m : ℕ) : ℕ → (ℂ[X])[X]
  | 0 => 0
  | k + 1 => HU m k + X ^ k * incU (m + k)

@[simp] theorem map_aU (e : ℂ) (n : ℕ) :
    (aU n).map (evalRingHom e) = a e n := by
  induction n with
  | zero => simp [aU, a]
  | succ n ih => simp [aU, a, ih]

@[simp] theorem map_incU (e : ℂ) (n : ℕ) :
    (incU n).map (evalRingHom e) = inc e n := by
  simp [incU, inc]

@[simp] theorem map_HU (e : ℂ) (m k : ℕ) :
    (HU m k).map (evalRingHom e) = H e m k := by
  induction k with
  | zero => simp [HU, H]
  | succ k ih => simp [HU, H, ih]

/-- Vanishing of finitely many multiplier coefficients at every complex
correction forces those coefficients to vanish as polynomials. -/
theorem X_pow_dvd_of_forall_specialize (P : (ℂ[X])[X]) (n : ℕ)
    (h : ∀ e : ℂ, (X : ℂ[X]) ^ n ∣ P.map (evalRingHom e)) :
    (X : (ℂ[X])[X]) ^ n ∣ P := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro d hd
  apply Polynomial.funext
  intro e
  have he := Polynomial.X_pow_dvd_iff.mp (h e) d hd
  simpa using he

/-- Universal denominator of the regular projective part. -/
def denU (k : ℕ) : (ℂ[X])[X] :=
  (1 + 2 * X ^ k * aU k) * (aU (2 * k) - X ^ k * aU (3 * k))

/-- Universal numerator of the regular projective part. -/
def remU (k : ℕ) : (ℂ[X])[X] :=
  HU k k + 2 * aU k * aU (2 * k) - 2 * X ^ k * aU k * aU (3 * k) -
    (X ^ k) ^ 2 * HU (2 * k) k - 2 * (X ^ k) ^ 2 * aU k * aU (3 * k) +
    2 * (X ^ k) ^ 3 * aU (2 * k) * aU (3 * k)

/-- The correction jet, polynomial in both the error and multiplier. -/
def correctionU : (ℂ[X])[X] :=
  C (C (3 / 4 : ℂ)) + C (C (1 / 16 : ℂ)) * X +
    C (C (1 / 16 : ℂ) * X) * X ^ 2

/-- The universal corrected numerator, before removing its cubic factor. -/
def residueU (k : ℕ) : (ℂ[X])[X] := remU k + correctionU * denU k

@[simp] theorem map_denU (e : ℂ) (k : ℕ) :
    (denU k).map (evalRingHom e) = denPoly e k := by
  simp [denU, denPoly]

@[simp] theorem map_remU (e : ℂ) (k : ℕ) :
    (remU k).map (evalRingHom e) = remPoly e k := by
  simp [remU, remPoly]

@[simp] theorem map_correctionU (e : ℂ) :
    correctionU.map (evalRingHom e) = correctionPoly e := by
  have he : (1 / 16 : ℂ) * e = e / 16 := by ring
  simp only [correctionU, correctionPoly, jetPoly, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, coe_evalRingHom,
    eval_C, eval_mul, eval_X, he]

@[simp] theorem map_residueU (e : ℂ) (k : ℕ) :
    (residueU k).map (evalRingHom e) =
      remPoly e k + correctionPoly e * denPoly e k := by
  simp [residueU]

/-- A cubic factor for every constant correction lifts to a single polynomial
factor in both variables. -/
theorem universal_residue_dvd_of_pointwise (k : ℕ)
    (h : ∀ e : ℂ, (X : ℂ[X]) ^ 3 ∣
      remPoly e k + correctionPoly e * denPoly e k) :
    (X : (ℂ[X])[X]) ^ 3 ∣ residueU k := by
  apply X_pow_dvd_of_forall_specialize
  intro e
  simpa using h e

/-- The evaluated universal quotient can be used at a varying correction
without choosing a new polynomial at each parameter. -/
theorem exists_universal_residue_factor_of_pointwise (k : ℕ)
    (h : ∀ e : ℂ, (X : ℂ[X]) ^ 3 ∣
      remPoly e k + correctionPoly e * denPoly e k) :
    ∃ Q : (ℂ[X])[X], residueU k = X ^ 3 * Q ∧
      ∀ e q : ℂ,
        (remPoly e k).eval q + (correctionPoly e).eval q * (denPoly e k).eval q =
          q ^ 3 * Q.eval₂ (evalRingHom e) q := by
  obtain ⟨Q, hQ⟩ := universal_residue_dvd_of_pointwise k h
  refine ⟨Q, hQ, ?_⟩
  intro e q
  have he := congrArg (fun P : (ℂ[X])[X] => (P.map (evalRingHom e)).eval q) hQ
  simpa only [map_residueU, Polynomial.map_mul, Polynomial.map_pow,
    map_X, eval_add, eval_mul, eval_pow, eval_X, eval_map] using he

/-- The residue has one polynomial quotient in both variables for every
return clock at least three. -/
theorem exists_universal_residue_factor (k : ℕ) (hk : 3 ≤ k) :
    ∃ Q : (ℂ[X])[X], residueU k = X ^ 3 * Q ∧
      ∀ e q : ℂ,
        (remPoly e k).eval q + (correctionPoly e).eval q * (denPoly e k).eval q =
          q ^ 3 * Q.eval₂ (evalRingHom e) q :=
  exists_universal_residue_factor_of_pointwise k (fun e => residue_cubic_dvd e k hk)

/-- One polynomial in the two dynamical variables gives the exact cubic
remainder for every correction and every nondegenerate multiplier. -/
theorem normalizedClock_universal_cubic_remainder (k : ℕ) (hk : 3 ≤ k) :
    ∃ Q : (ℂ[X])[X], ∀ e q : ℂ,
      q ≠ 0 → (denPoly e k).eval q ≠ 0 →
      normalizedClock e q k + (q ^ k)⁻¹ + 3 / 4 + q / 16 + e * q ^ 2 / 16 =
        q ^ 3 * Q.eval₂ (evalRingHom e) q / (denPoly e k).eval q := by
  obtain ⟨Q, _, hQ⟩ := exists_universal_residue_factor k hk
  refine ⟨Q, fun e q hq hD => ?_⟩
  rw [normalizedClock_regular_part e q k hq hD]
  apply (eq_div_iff hD).2
  have h := hQ e q
  simp only [correctionPoly, jetPoly, eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
  field_simp at *
  linear_combination h

end LoopsQuadraticProjective
