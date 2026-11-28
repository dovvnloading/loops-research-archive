import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Integral-coordinate obstruction for a normalized quadratic return

The hypotheses below concern genuine polynomial composition modulo `X ^ 5`.
The coefficient equations are conclusions, not a definition of conjugacy.
Arbitrary higher coefficients of all three polynomials are retained.
-/

namespace QuadraticJetConjugacy

open Polynomial

noncomputable section

variable {K : Type*} [CommRing K]

/-- A coordinate tangent to the identity, retaining an arbitrary tail. -/
def coordinateJet (a b : K) (tail : K[X]) : K[X] :=
  X + C a * X ^ 2 + C b * X ^ 3 + X ^ 4 * tail

/-- A normalized critical germ, retaining an arbitrary tail. -/
def criticalJet (gamma delta : K) (tail : K[X]) : K[X] :=
  X ^ 2 + C gamma * X ^ 3 + C delta * X ^ 4 + X ^ 5 * tail

private theorem coordinateJet_exists (H : K[X])
    (h0 : H.coeff 0 = 0) (h1 : H.coeff 1 = 1) :
    ∃ tail : K[X], coordinateJet (H.coeff 2) (H.coeff 3) tail = H := by
  have hdvd : (X : K[X]) ^ 4 ∣
      H - (X + C (H.coeff 2) * X ^ 2 + C (H.coeff 3) * X ^ 3) := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    interval_cases d <;> simp [h0, h1, coeff_X]
  obtain ⟨tail, htail⟩ := hdvd
  refine ⟨tail, ?_⟩
  unfold coordinateJet
  linear_combination -htail

private theorem criticalJet_exists (F : K[X])
    (h0 : F.coeff 0 = 0) (h1 : F.coeff 1 = 0)
    (h2 : F.coeff 2 = 1) :
    ∃ tail : K[X], criticalJet (F.coeff 3) (F.coeff 4) tail = F := by
  have hdvd : (X : K[X]) ^ 5 ∣
      F - (X ^ 2 + C (F.coeff 3) * X ^ 3 + C (F.coeff 4) * X ^ 4) := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    interval_cases d <;> simp [h0, h1, h2]
  obtain ⟨tail, htail⟩ := hdvd
  refine ⟨tail, ?_⟩
  unfold criticalJet
  linear_combination -htail

private def coordinateUnit (a b : K) (tail : K[X]) : K[X] :=
  1 + C a * X + C b * X ^ 2 + X ^ 3 * tail

private def criticalUnit (beta : K) (tail : K[X]) : K[X] :=
  1 + C beta * X ^ 2 + X ^ 3 * tail

private theorem coordinateJet_factor (a b : K) (tail : K[X]) :
    coordinateJet a b tail = X * coordinateUnit a b tail := by
  unfold coordinateJet coordinateUnit
  ring

private theorem criticalJet_zero_factor (beta : K) (tail : K[X]) :
    criticalJet 0 beta tail = X ^ 2 * criticalUnit beta tail := by
  simp only [criticalJet, criticalUnit, map_zero, zero_mul, add_zero]
  ring

private theorem coordinateJet_comp (a b : K) (tail p : K[X]) :
    (coordinateJet a b tail).comp p =
      p + C a * p ^ 2 + C b * p ^ 3 + p ^ 4 * tail.comp p := by
  simp [coordinateJet]

private theorem criticalJet_comp (gamma delta : K) (tail p : K[X]) :
    (criticalJet gamma delta tail).comp p =
      p ^ 2 + C gamma * p ^ 3 + C delta * p ^ 4 + p ^ 5 * tail.comp p := by
  simp [criticalJet]

/-- Factor off the powers of X before extracting coefficients. In particular
the arbitrary composed tails occur only after an explicit factor X^5. -/
private theorem defect_factor (a b beta gamma delta : K) (u v w : K[X]) :
    (coordinateJet a b u).comp (criticalJet 0 beta v) -
        (criticalJet gamma delta w).comp (coordinateJet a b u) =
      X ^ 2 * (criticalUnit beta v - (coordinateUnit a b u) ^ 2) +
      X ^ 3 * (-C gamma * (coordinateUnit a b u) ^ 3) +
      X ^ 4 * (C a * (criticalUnit beta v) ^ 2 -
        C delta * (coordinateUnit a b u) ^ 4) +
      X ^ 5 * (C b * X * (criticalUnit beta v) ^ 3 +
        X ^ 3 * (criticalUnit beta v) ^ 4 * u.comp (criticalJet 0 beta v) -
        (coordinateUnit a b u) ^ 5 * w.comp (coordinateJet a b u)) := by
  rw [coordinateJet_comp, criticalJet_comp]
  simp only [coordinateJet_factor, criticalJet_zero_factor]
  ring

private theorem coeff_mul_two (p q : K[X]) :
    (p * q).coeff 2 =
      p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.antidiagonal_eq_map]
  simp [Finset.sum_range_succ]
  <;> ring

private theorem defect_coeff_three (a b beta gamma delta : K)
    (u v w : K[X]) :
    ((coordinateJet a b u).comp (criticalJet 0 beta v) -
      (criticalJet gamma delta w).comp (coordinateJet a b u)).coeff 3 =
        -(2 * a + gamma) := by
  rw [defect_factor]
  simp only [coeff_add, coeff_X_pow_mul']
  norm_num
  simp [coordinateUnit, criticalUnit, coeff_X, coeff_one, coeff_X_pow_mul',
    pow_succ, mul_coeff_one]
  <;> ring

private theorem defect_coeff_four (a b beta gamma delta : K)
    (u v w : K[X]) :
    ((coordinateJet a b u).comp (criticalJet 0 beta v) -
      (criticalJet gamma delta w).comp (coordinateJet a b u)).coeff 4 =
        beta + a - (a ^ 2 + 2 * b + 3 * a * gamma + delta) := by
  rw [defect_factor]
  simp only [coeff_add, coeff_X_pow_mul']
  norm_num
  simp [coordinateUnit, criticalUnit, coeff_X, coeff_one, coeff_X_pow_mul',
    pow_succ, mul_coeff_one, coeff_mul_two]
  <;> ring

/-- Cubic and quartic conjugacy laws, with arbitrary polynomial remainders.
The modulus-five relation is a necessary condition for an actual formal
coordinate conjugacy, and follows from any exact polynomial conjugacy. -/
theorem conjugacy_jet_law (a b beta gamma delta : K) (u v w : K[X])
    (h : (X : K[X]) ^ 5 ∣
      (coordinateJet a b u).comp (criticalJet 0 beta v) -
        (criticalJet gamma delta w).comp (coordinateJet a b u)) :
    gamma = -2 * a ∧ delta = beta + 5 * a ^ 2 + a - 2 * b := by
  have h3 := X_pow_dvd_iff.mp h 3 (by decide)
  have h4 := X_pow_dvd_iff.mp h 4 (by decide)
  rw [defect_coeff_three] at h3
  rw [defect_coeff_four] at h4
  have hgamma : gamma = -2 * a := by linear_combination -h3
  refine ⟨hgamma, ?_⟩
  rw [hgamma] at h4
  linear_combination -h4

/-- The coefficient law for arbitrary actual polynomials. In particular `F`
can be the complete normalized iterate of `z ↦ z²+c`; its degree is unrestricted.
No truncation of the dynamical polynomial is assumed. -/
theorem conjugacy_coeff_law (F H G : K[X])
    (hF0 : F.coeff 0 = 0) (hF1 : F.coeff 1 = 0)
    (hF2 : F.coeff 2 = 1) (hF3 : F.coeff 3 = 0)
    (hH0 : H.coeff 0 = 0) (hH1 : H.coeff 1 = 1)
    (hG0 : G.coeff 0 = 0) (hG1 : G.coeff 1 = 0)
    (hG2 : G.coeff 2 = 1)
    (h : (X : K[X]) ^ 5 ∣ H.comp F - G.comp H) :
    G.coeff 3 = -2 * H.coeff 2 ∧
      G.coeff 4 = F.coeff 4 + 5 * (H.coeff 2) ^ 2 + H.coeff 2 - 2 * H.coeff 3 := by
  obtain ⟨u, hu⟩ := coordinateJet_exists H hH0 hH1
  obtain ⟨v, hv⟩ := criticalJet_exists F hF0 hF1 hF2
  obtain ⟨w, hw⟩ := criticalJet_exists G hG0 hG1 hG2
  rw [hF3] at hv
  apply conjugacy_jet_law (H.coeff 2) (H.coeff 3) (F.coeff 4)
    (G.coeff 3) (G.coeff 4) u v w
  simpa only [hu, hv, hw] using h

/-- Any Böttcher conjugacy through degree four has vanishing quadratic
coordinate coefficient and cubic coefficient exactly half the return's quartic
coefficient. This is about the composition equation, not prescribed coefficients. -/
theorem bottcher_coeff_law {K : Type*} [Field K] [CharZero K] (F H : K[X])
    (hF0 : F.coeff 0 = 0) (hF1 : F.coeff 1 = 0)
    (hF2 : F.coeff 2 = 1) (hF3 : F.coeff 3 = 0)
    (hH0 : H.coeff 0 = 0) (hH1 : H.coeff 1 = 1)
    (h : (X : K[X]) ^ 5 ∣ H.comp F - H ^ 2) :
    H.coeff 2 = 0 ∧ H.coeff 3 = F.coeff 4 / 2 := by
  have hcomp : (X : K[X]) ^ 5 ∣ H.comp F - (X ^ 2).comp H := by
    simpa using h
  obtain ⟨h3, h4⟩ := conjugacy_coeff_law F H (X ^ 2)
    hF0 hF1 hF2 hF3 hH0 hH1 (by simp) (by simp) (by simp) hcomp
  have ha : H.coeff 2 = 0 := by
    have he : (2 : K) * H.coeff 2 = 0 := by
      simpa using congrArg Neg.neg h3.symm
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  refine ⟨ha, ?_⟩
  norm_num [ha] at h4
  apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).mpr
  linear_combination h4

private theorem explicit_bottcher_jet {K : Type*} [Field K] [CharZero K]
    (beta : K) (tail : K[X]) :
    (X : K[X]) ^ 5 ∣
      (coordinateJet 0 (beta / 2) 0).comp (criticalJet 0 beta tail) -
        (coordinateJet 0 (beta / 2) 0) ^ 2 := by
  have h : (X : K[X]) ^ 5 ∣
      (coordinateJet 0 (beta / 2) 0).comp (criticalJet 0 beta tail) -
        (criticalJet 0 0 0).comp (coordinateJet 0 (beta / 2) 0) := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    interval_cases d
    · rw [defect_factor]
      norm_num [coeff_X_pow_mul']
    · rw [defect_factor]
      norm_num [coeff_X_pow_mul']
    · rw [defect_factor]
      simp only [coeff_add, coeff_X_pow_mul']
      norm_num [coordinateUnit, criticalUnit, coeff_X, coeff_one, pow_succ]
    · rw [defect_coeff_three]
      ring
    · rw [defect_coeff_four]
      ring
  simpa [criticalJet] using h

/-- The Böttcher equation through degree four is nonvacuous: for every actual
normalized even critical polynomial, the cubic coordinate displayed here solves
the genuine composition equation modulo `X ^ 5`. -/
theorem bottcher_jet_exists {K : Type*} [Field K] [CharZero K] (F : K[X])
    (hF0 : F.coeff 0 = 0) (hF1 : F.coeff 1 = 0)
    (hF2 : F.coeff 2 = 1) (hF3 : F.coeff 3 = 0) :
    ∃ H : K[X], H.coeff 0 = 0 ∧ H.coeff 1 = 1 ∧
      H.coeff 2 = 0 ∧ H.coeff 3 = F.coeff 4 / 2 ∧
        (X : K[X]) ^ 5 ∣ H.comp F - H ^ 2 := by
  obtain ⟨tail, htail⟩ := criticalJet_exists F hF0 hF1 hF2
  rw [hF3] at htail
  refine ⟨coordinateJet 0 (F.coeff 4 / 2) 0, ?_, ?_, ?_, ?_, ?_⟩
  · simp [coordinateJet, coeff_X]
  · simp [coordinateJet, coeff_X]
  · simp [coordinateJet, coeff_X]
  · simp [coordinateJet, coeff_X]
  · simpa only [htail] using explicit_bottcher_jet (F.coeff 4) tail

end

end QuadraticJetConjugacy
