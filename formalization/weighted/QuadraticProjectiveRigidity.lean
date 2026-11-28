import QuadraticProjectiveActual
import QuadraticProjectiveResidue
import QuadraticProjectiveUniversal

/-!
# Critical-orbit projective jets in the actual quadratic family

The statements use genuine critical iterates, with the actual fixed-point
or two-cycle multiplier.  Polynomial remainders and denominator units make
the finite Laurent coefficients exact, rather than numerical evidence.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Polynomial

/-- Ordered four-point projective observable of the actual critical orbit. -/
def criticalClock (c : ℂ) (n : ℕ) : ℂ :=
  crossRatio 0 (criticalOrbit c n) (criticalOrbit c (2*n))
    (criticalOrbit c (3*n))

/-- Scaling all marked points preserves this ordered cross-ratio. -/
theorem crossRatio_zero_scale (L x y z : ℂ) (hL : L ≠ 0) :
    crossRatio 0 (L*x) (L*y) (L*z) = crossRatio 0 x y z := by
  simp only [crossRatio, sub_zero, ← mul_sub]
  rw [show L*z*(L*(x-y)) = L^2*(z*(x-y)) by ring,
    show L*x*(L*(z-y)) = L^2*(x*(z-y)) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hL)

theorem criticalOrbit_main_mark (q : ℂ) (n : ℕ) :
    criticalOrbit (mainParameter q) n = (q/2)*normalizedMark 0 q n := by
  rw [criticalOrbit_main]
  dsimp [normalizedMark]
  ring

/-- Exact identification of the projective configuration in the main chart. -/
theorem criticalClock_main_normalized (q : ℂ) (k : ℕ) (hq : q ≠ 0) :
    criticalClock (mainParameter q) k = normalizedClock 0 q k := by
  simp only [criticalClock, criticalOrbit_main_mark, normalizedClock]
  exact crossRatio_zero_scale (q/2) _ _ _ (div_ne_zero hq (by norm_num))

theorem criticalOrbit_periodTwo_mark (t : ℂ) (n : ℕ) (ht : t+1 ≠ 0) :
    criticalOrbit (periodTwoParameter t) (2*n) =
      t*normalizedMark (periodTwoError t) (periodTwoMultiplier t) n := by
  rw [criticalOrbit_periodTwo t n ht]
  rfl

/-- Exact identification of the projective configuration in the period-two chart. -/
theorem criticalClock_periodTwo_normalized (t : ℂ) (k : ℕ)
    (ht : t ≠ 0) (ht1 : t+1 ≠ 0) :
    criticalClock (periodTwoParameter t) (2*k) =
      normalizedClock (periodTwoError t) (periodTwoMultiplier t) k := by
  have hi : 3*(2*k) = 2*(3*k) := by omega
  simp only [criticalClock, hi, criticalOrbit_periodTwo_mark t _ ht1, normalizedClock]
  exact crossRatio_zero_scale t _ _ _ ht

theorem periodTwoMultiplier_ne_zero (t : ℂ) (ht : t ≠ 0) (ht1 : t+1 ≠ 0) :
    periodTwoMultiplier t ≠ 0 := by
  have h : 1+t ≠ 0 := by simpa only [add_comm] using ht1
  exact mul_ne_zero (mul_ne_zero (by norm_num) ht) h

/-- Actual-family finite residue, with no identification or rigidity assumption. -/
theorem criticalClock_main_regular_part (q : ℂ) (k : ℕ)
    (hq : q ≠ 0) (hD : (denPoly 0 k).eval q ≠ 0) :
    criticalClock (mainParameter q) k + (q^k)⁻¹ =
      (remPoly 0 k).eval q / (denPoly 0 k).eval q := by
  rw [criticalClock_main_normalized q k hq]
  exact normalizedClock_regular_part 0 q k hq hD

/-- Actual period-two finite residue in its genuine return multiplier. -/
theorem criticalClock_periodTwo_regular_part (t : ℂ) (k : ℕ)
    (ht : t ≠ 0) (ht1 : t+1 ≠ 0)
    (hD : (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) ≠ 0) :
    criticalClock (periodTwoParameter t) (2*k) + ((periodTwoMultiplier t)^k)⁻¹ =
      (remPoly (periodTwoError t) k).eval (periodTwoMultiplier t) /
        (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) := by
  rw [criticalClock_periodTwo_normalized t k ht ht1]
  exact normalizedClock_regular_part _ _ k (periodTwoMultiplier_ne_zero t ht ht1) hD

/-- All clocks at least three have the same exact main-chart Laurent jet.
The quadratic finite coefficient is zero, and the remainder is one polynomial
divided by a polynomial with constant term -1/4. -/
theorem criticalClock_main_cubic_remainder (k : ℕ) (hk : 3 ≤ k) :
    ∃ U : ℂ[X], (denPoly 0 k).eval 0 = -1/4 ∧
      ∀ q : ℂ, q ≠ 0 → (denPoly 0 k).eval q ≠ 0 →
        criticalClock (mainParameter q) k + (q^k)⁻¹ + 3/4 + q/16 =
          q^3*U.eval q/(denPoly 0 k).eval q := by
  obtain ⟨U, hU⟩ := normalizedClock_cubic_remainder 0 k hk
  refine ⟨U, denPoly_eval_zero 0 k (by omega), ?_⟩
  intro q hq hD
  rw [criticalClock_main_normalized q k hq]
  simpa using hU q hq hD

/-- The curvature term in the exact period-two normalization. -/
theorem periodTwo_curvature_term (t : ℂ) :
    periodTwoError t * (periodTwoMultiplier t)^2/16 =
      -(periodTwoMultiplier t)^2 / (128*(1+t)^3) := by
  simp only [periodTwoError, div_mul_eq_mul_div, div_div]
  congr 1 <;> ring

/-- A single bivariate polynomial remainder controls the actual period-two
chart. Its quartic error may vary with the parameter; it is not frozen. -/
theorem criticalClock_periodTwo_cubic_remainder (k : ℕ) (hk : 3 ≤ k) :
    ∃ Q : (ℂ[X])[X],
      (denPoly (periodTwoError 0) k).eval (periodTwoMultiplier 0) = -1/4 ∧
      ∀ t : ℂ, t ≠ 0 → t+1 ≠ 0 →
        (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) ≠ 0 →
        criticalClock (periodTwoParameter t) (2*k) + ((periodTwoMultiplier t)^k)⁻¹ +
          3/4 + periodTwoMultiplier t/16 -
            (periodTwoMultiplier t)^2/(128*(1+t)^3) =
          (periodTwoMultiplier t)^3 *
            Q.eval₂ (evalRingHom (periodTwoError t)) (periodTwoMultiplier t) /
              (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) := by
  obtain ⟨Q, hQ⟩ := normalizedClock_universal_cubic_remainder k hk
  refine ⟨Q, ?_, ?_⟩
  · simpa [periodTwoMultiplier] using denPoly_eval_zero (periodTwoError 0) k (by omega)
  · intro t ht ht1 hD
    rw [criticalClock_periodTwo_normalized t k ht ht1]
    have h := hQ (periodTwoError t) (periodTwoMultiplier t)
      (periodTwoMultiplier_ne_zero t ht ht1) hD
    rw [periodTwo_curvature_term] at h
    simpa only [sub_eq_add_neg, neg_div] using h

/-- Changing from the varying quartic coefficient to its center value
changes only the cubic remainder in the genuine multiplier. -/
theorem periodTwo_curvature_center_correction (t : ℂ) (ht1 : t+1 ≠ 0) :
    (periodTwoMultiplier t)^2/(128*(1+t)^3) - (periodTwoMultiplier t)^2/128 =
      (periodTwoMultiplier t)^3 * (3+3*t+t^2)/(512*(1+t)^4) := by
  have h : 1+t ≠ 0 := by simpa only [add_comm] using ht1
  dsimp [periodTwoMultiplier]
  field_simp
  ring

/-- The actual period-two critical-orbit Laurent jet has quadratic finite
coefficient 1/128, at every return clock at least three. All remainders
are explicit rational evaluations of one polynomial in two variables. -/
theorem criticalClock_periodTwo_center_jet (k : ℕ) (hk : 3 ≤ k) :
    ∃ Q : (ℂ[X])[X],
      (denPoly (periodTwoError 0) k).eval (periodTwoMultiplier 0) = -1/4 ∧
      ∀ t : ℂ, t ≠ 0 → t+1 ≠ 0 →
        (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) ≠ 0 →
        criticalClock (periodTwoParameter t) (2*k) + ((periodTwoMultiplier t)^k)⁻¹ +
          3/4 + periodTwoMultiplier t/16 - (periodTwoMultiplier t)^2/128 =
          (periodTwoMultiplier t)^3 *
            (Q.eval₂ (evalRingHom (periodTwoError t)) (periodTwoMultiplier t) /
              (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) +
              (3+3*t+t^2)/(512*(1+t)^4)) := by
  obtain ⟨Q, h0, hQ⟩ := criticalClock_periodTwo_cubic_remainder k hk
  refine ⟨Q, h0, ?_⟩
  intro t ht ht1 hD
  have h := hQ t ht ht1 hD
  have hc := periodTwo_curvature_center_correction t ht1
  linear_combination h + hc

/-- The two actual center return polynomials have different normalized
quartic curvature. These are the values recovered by the finite jet. -/
theorem actual_center_return_curvatures :
    (∀ z : ℂ, quadraticMap 0 z = z^2) ∧
    (∀ z : ℂ, quadraticMap (-1) (quadraticMap (-1) z) = -2*z^2+z^4) ∧
    (1 : ℂ)/(-2)^3 = -1/8 ∧ (0 : ℂ) ≠ -1/8 := by
  constructor
  · intro z
    simp [quadraticMap]
  constructor
  · intro z
    dsimp [quadraticMap]
    ring
  norm_num

end LoopsQuadraticProjective
