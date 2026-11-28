import QuadraticReturnCoordinateObstruction

/-!
# The optimal arithmetic cost of changing the critical coordinate

For the actual return at an exact quadratic center, any coordinate
tangent to the identity that makes the cubic and quartic target
coefficients integral has a cubic coordinate coefficient with exact
dyadic denominator exponent twice the physical return period.  The
coordinate itself is not assumed integral or algebraic.
-/

namespace LoopsQuadraticReturnArithmetic

open Polynomial LoopsQuadraticTransversality QuadraticJetConjugacy

noncomputable section

/-- Integral cubic and quartic target coefficients force the exact
arithmetic cost in the coordinate itself.  The conjugacy hypothesis is
the actual polynomial composition equation through degree four, with
arbitrary polynomial tails and no integrality assumption on the coordinate. -/
theorem actual_integral_target_coordinate_denominator (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0)
    (H G : ℂ[X]) (hH0 : H.coeff 0 = 0) (hH1 : H.coeff 1 = 1)
    (hG0 : G.coeff 0 = 0) (hG1 : G.coeff 1 = 0) (hG2 : G.coeff 2 = 1)
    (hG3 : IsIntegral ℤ (G.coeff 3)) (hG4 : IsIntegral ℤ (G.coeff 4))
    (hcomp : (X : ℂ[X])^5 ∣ H.comp (criticalNormalizedPoly c (n+1)) - G.comp H) :
    IsIntegral ℤ (2 * H.coeff 2) ∧
      ∀ k : ℕ, IsIntegral ℤ ((2:ℂ)^k * H.coeff 3) ↔ 2*n+4 ≤ k := by
  have ha : quadCoeff c (n+1) ≠ 0 :=
    quadCoeff_ne_zero c (n+1) (fun j hj => hmin (j+1) (by omega) (by omega))
  obtain ⟨h3, h4⟩ := conjugacy_coeff_law (criticalNormalizedPoly c (n+1)) H G
    (center_normalized_poly_coeff_zero (n+1) hcenter ha)
    (center_normalized_poly_coeff_one (n+1) hcenter ha)
    (center_normalized_poly_coeff_two (n+1) hcenter ha)
    (center_normalized_poly_coeff_three (n+1) hcenter ha)
    hH0 hH1 hG0 hG1 hG2 hcomp
  rw [center_normalized_poly_coeff_four (n+1) hcenter ha] at h4
  change G.coeff 4 = normalizedQuartic c n +
    5 * (H.coeff 2)^2 + H.coeff 2 - 2 * H.coeff 3 at h4
  have htwoa : (2:ℂ) * H.coeff 2 = -G.coeff 3 := by
    linear_combination h3
  have haI : IsIntegral ℤ ((2:ℂ) * H.coeff 2) := by
    rw [htwoa]
    exact hG3.neg
  refine ⟨haI, ?_⟩
  let r : ℂ := 5 * (H.coeff 2)^2 + H.coeff 2 - G.coeff 4
  have htwob : (2:ℂ) * H.coeff 3 = normalizedQuartic c n + r := by
    dsimp [r]
    linear_combination h4
  have hr4eq : (4:ℂ) * r =
      5 * ((2:ℂ) * H.coeff 2)^2 +
        2 * ((2:ℂ) * H.coeff 2) - 4 * G.coeff 4 := by
    dsimp [r]
    ring
  have hr4 : IsIntegral ℤ ((4:ℂ) * r) := by
    rw [hr4eq]
    exact (((isIntegral_natCast 5).mul (haI.pow 2)).add
      ((isIntegral_natCast 2).mul haI)).sub
        ((isIntegral_natCast 4).mul hG4)
  have ht : IsIntegral ℤ ((2:ℂ)^(2*n) * (4*r)) :=
    ((isIntegral_natCast 2).pow (2*n)).mul hr4
  have hscale : (2:ℂ)^(2*n+4) * H.coeff 3 =
      (2:ℂ)^(2*n+3) * normalizedQuartic c n +
        2 * ((2:ℂ)^(2*n) * (4*r)) := by
    calc
      (2:ℂ)^(2*n+4) * H.coeff 3 =
          (2:ℂ)^(2*n+3) * (2 * H.coeff 3) := by
            rw [show 2*n+4 = (2*n+3)+1 by omega, pow_succ]
            ring
      _ = (2:ℂ)^(2*n+3) * (normalizedQuartic c n + r) := by rw [htwob]
      _ = (2:ℂ)^(2*n+3) * normalizedQuartic c n +
          2 * ((2:ℂ)^(2*n) * (4*r)) := by
            simp only [pow_add]
            ring
  have hodd : OddIntegral ((2:ℂ)^(2*n+4) * H.coeff 3) := by
    rw [hscale]
    exact (normalizedQuartic_odd_numerator c n hcenter hmin).add_two_mul ht
  intro k
  exact odd_numerator_denominator_exact (H.coeff 3) (2*n+4) hodd k

/-- The forced cubic coordinate exponent is attained: the target can be
the integral monomial `X ^ 2`, and a polynomial coordinate jet satisfies
the genuine composition equation modulo `X ^ 5`. -/
theorem actual_integral_target_coordinate_cost_attained (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0) :
    ∃ H : ℂ[X], H.coeff 0 = 0 ∧ H.coeff 1 = 1 ∧ H.coeff 2 = 0 ∧
      ((X : ℂ[X])^5 ∣ H.comp (criticalNormalizedPoly c (n+1)) - (X^2).comp H) ∧
      ∀ k : ℕ, IsIntegral ℤ ((2:ℂ)^k * H.coeff 3) ↔ 2*n+4 ≤ k := by
  obtain ⟨H, h0, h1, h2, hcomp, hdenom⟩ :=
    actual_bottcher_jet_exists_with_exact_denominator c n hcenter hmin
  exact ⟨H, h0, h1, h2, by simpa using hcomp, hdenom⟩

end

end LoopsQuadraticReturnArithmetic
