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
    interval_cases d <;> simp [h0, h1, coeff_C_mul_X_pow]
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
    interval_cases d <;> simp [h0, h1, h2, coeff_C_mul_X_pow]
  obtain ⟨tail, htail⟩ := hdvd
  refine ⟨tail, ?_⟩
  unfold criticalJet
  linear_combination -htail

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem defect_coeff_three (a b beta gamma delta : K)
    (u v w : K[X]) :
    ((coordinateJet a b u).comp (criticalJet 0 beta v) -
      (criticalJet gamma delta w).comp (coordinateJet a b u)).coeff 3 =
        -(2 * a + gamma) := by
  simp [coordinateJet, criticalJet, coeff_mul,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ, pow_succ]
  <;> ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem defect_coeff_four (a b beta gamma delta : K)
    (u v w : K[X]) :
    ((coordinateJet a b u).comp (criticalJet 0 beta v) -
      (criticalJet gamma delta w).comp (coordinateJet a b u)).coeff 4 =
        beta + a - (a ^ 2 + 2 * b + 3 * a * gamma + delta) := by
  simp [coordinateJet, criticalJet, coeff_mul,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ, pow_succ]
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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem explicit_bottcher_jet {K : Type*} [Field K] [CharZero K]
    (beta : K) (tail : K[X]) :
    (X : K[X]) ^ 5 ∣
      (coordinateJet 0 (beta / 2) 0).comp (criticalJet 0 beta tail) -
        (coordinateJet 0 (beta / 2) 0) ^ 2 := by
  apply X_pow_dvd_iff.mpr
  intro d hd
  interval_cases d <;>
    simp [coordinateJet, criticalJet, coeff_mul,
      Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ, pow_succ] <;> ring

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
  · simp [coordinateJet]
  · simp [coordinateJet]
  · simp [coordinateJet]
  · simp [coordinateJet]
  · simpa only [htail] using explicit_bottcher_jet (F.coeff 4) tail

end

end QuadraticJetConjugacy
