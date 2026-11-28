import QuadraticReturnArithmetic
import QuadraticJetConjugacy

/-!
# Integral-coordinate obstruction for actual quadratic center returns

The exact denominator of the actual normalized quartic coefficient
survives every integral coordinate change through order four.  The
conjugacy hypothesis is divisibility of the genuine polynomial
composition defect by `X ^ 5`; coefficient relations are proved from it.
-/

namespace LoopsQuadraticReturnArithmetic

open Polynomial LoopsQuadraticTransversality QuadraticJetConjugacy

noncomputable section

/-- Any integral coordinate tangent to the identity preserves the exact
quartic denominator of the genuine normalized critical return. Arbitrary
higher coefficients and arbitrary polynomial degree are allowed. -/
theorem integral_coordinate_preserves_denominator (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0)
    (H G : ℂ[X]) (hH0 : H.coeff 0 = 0) (hH1 : H.coeff 1 = 1)
    (hH2 : IsIntegral ℤ (H.coeff 2)) (hH3 : IsIntegral ℤ (H.coeff 3))
    (hG0 : G.coeff 0 = 0) (hG1 : G.coeff 1 = 0) (hG2 : G.coeff 2 = 1)
    (hcomp : (X : ℂ[X])^5 ∣ H.comp (criticalNormalizedPoly c (n+1)) - G.comp H) :
    G.coeff 3 = -2 * H.coeff 2 ∧
      ∀ k : ℕ, IsIntegral ℤ ((2:ℂ)^k * G.coeff 4) ↔ 2*n+3 ≤ k := by
  have ha : quadCoeff c (n+1) ≠ 0 :=
    quadCoeff_ne_zero c (n+1) (fun j hj => hmin (j+1) (by omega) (by omega))
  obtain ⟨h3, h4⟩ := conjugacy_coeff_law (criticalNormalizedPoly c (n+1)) H G
    (center_normalized_poly_coeff_zero (n+1) hcenter ha)
    (center_normalized_poly_coeff_one (n+1) hcenter ha)
    (center_normalized_poly_coeff_two (n+1) hcenter ha)
    (center_normalized_poly_coeff_three (n+1) hcenter ha)
    hH0 hH1 hG0 hG1 hG2 hcomp
  rw [center_normalized_poly_coeff_four (n+1) hcenter ha] at h4
  let t : ℂ := 5*(H.coeff 2)^2 + H.coeff 2 - 2*H.coeff 3
  have ht : IsIntegral ℤ t :=
    (((isIntegral_natCast 5).mul (hH2.pow 2)).add hH2).sub
      ((isIntegral_natCast 2).mul hH3)
  have h4' : G.coeff 4 = normalizedQuartic c n + t := by
    rw [h4]
    dsimp [normalizedQuartic, criticalQuarticInvariant, t]
    ring
  refine ⟨h3, ?_⟩
  intro k
  rw [h4']
  exact normalizedQuartic_add_integral_iff c n hcenter hmin t ht k

/-- No coordinate with integral quadratic and cubic coefficients can
conjugate the genuine normalized return to a germ with integral quartic
coefficient, even if conjugacy is required only through degree four. -/
theorem no_integral_normalized_return_coordinate (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0)
    (H G : ℂ[X]) (hH0 : H.coeff 0 = 0) (hH1 : H.coeff 1 = 1)
    (hH2 : IsIntegral ℤ (H.coeff 2)) (hH3 : IsIntegral ℤ (H.coeff 3))
    (hG0 : G.coeff 0 = 0) (hG1 : G.coeff 1 = 0) (hG2 : G.coeff 2 = 1)
    (hG4 : IsIntegral ℤ (G.coeff 4)) :
    ¬ (X : ℂ[X])^5 ∣ H.comp (criticalNormalizedPoly c (n+1)) - G.comp H := by
  intro hcomp
  have hh := (integral_coordinate_preserves_denominator c n hcenter hmin H G
    hH0 hH1 hH2 hH3 hG0 hG1 hG2 hcomp).2 0
  have hb : 2*n+3 ≤ 0 := hh.mp (by simpa using hG4)
  omega

/-- Every Böttcher coordinate jet for the actual normalized center return
has cubic coefficient with exact denominator exponent `2N`, N=n+2. -/
theorem actual_bottcher_cubic_denominator (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0)
    (H : ℂ[X]) (hH0 : H.coeff 0 = 0) (hH1 : H.coeff 1 = 1)
    (hcomp : (X : ℂ[X])^5 ∣ H.comp (criticalNormalizedPoly c (n+1)) - H^2) :
    H.coeff 2 = 0 ∧
      ∀ k : ℕ, IsIntegral ℤ ((2:ℂ)^k * H.coeff 3) ↔ 2*n+4 ≤ k := by
  have ha : quadCoeff c (n+1) ≠ 0 :=
    quadCoeff_ne_zero c (n+1) (fun j hj => hmin (j+1) (by omega) (by omega))
  obtain ⟨h2, h3⟩ := bottcher_coeff_law (criticalNormalizedPoly c (n+1)) H
    (center_normalized_poly_coeff_zero (n+1) hcenter ha)
    (center_normalized_poly_coeff_one (n+1) hcenter ha)
    (center_normalized_poly_coeff_two (n+1) hcenter ha)
    (center_normalized_poly_coeff_three (n+1) hcenter ha) hH0 hH1 hcomp
  rw [center_normalized_poly_coeff_four (n+1) hcenter ha] at h3
  refine ⟨h2, ?_⟩
  intro k
  rw [h3]
  exact half_normalizedQuartic_integral_iff c n hcenter hmin k

/-- Nonvacuity: every exact center has a Böttcher jet satisfying the
actual composition equation through degree four, and its exact cubic
denominator is forced by the physical return period. -/
theorem actual_bottcher_jet_exists_with_exact_denominator (c : ℂ) (n : ℕ)
    (hcenter : orbit c (n+2) = 0)
    (hmin : ∀ j : ℕ, 0 < j → j < n+2 → orbit c j ≠ 0) :
    ∃ H : ℂ[X], H.coeff 0 = 0 ∧ H.coeff 1 = 1 ∧ H.coeff 2 = 0 ∧
      ((X : ℂ[X])^5 ∣ H.comp (criticalNormalizedPoly c (n+1)) - H^2) ∧
      ∀ k : ℕ, IsIntegral ℤ ((2:ℂ)^k * H.coeff 3) ↔ 2*n+4 ≤ k := by
  have ha : quadCoeff c (n+1) ≠ 0 :=
    quadCoeff_ne_zero c (n+1) (fun j hj => hmin (j+1) (by omega) (by omega))
  obtain ⟨H, h0, h1, h2, _, hcomp⟩ := bottcher_jet_exists (criticalNormalizedPoly c (n+1))
    (center_normalized_poly_coeff_zero (n+1) hcenter ha)
    (center_normalized_poly_coeff_one (n+1) hcenter ha)
    (center_normalized_poly_coeff_two (n+1) hcenter ha)
    (center_normalized_poly_coeff_three (n+1) hcenter ha)
  exact ⟨H, h0, h1, h2, hcomp,
    (actual_bottcher_cubic_denominator c n hcenter hmin H h0 h1 hcomp).2⟩

end

end LoopsQuadraticReturnArithmetic
