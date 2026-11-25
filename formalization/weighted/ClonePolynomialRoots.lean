import FullClonePolynomial

/-!
# Simple roots and the exact product for the clone polynomial

This file proves the previously written scalar simplicity and Vieta steps
for every delay. The polynomial is the one derived from actual adjacency
eigenvectors in `FullClonePolynomial`.

The matrix characteristic-polynomial identification is a separate bridge;
the theorems here do not assume or claim that identification.

AI assistance: OpenAI GPT-6 Astra Pro, proof construction and API audit.
-/

namespace LoopsSpectral

noncomputable section

open Polynomial

/-- The scalar polynomial already forced by every actual clone eigenpair. -/
def clonePolynomial (n : ℕ) : ℂ[X] :=
  X ^ (2 * n + 5) - (X + 1)

theorem clonePolynomial_monic (n : ℕ) : (clonePolynomial n).Monic := by
  apply Polynomial.monic_X_pow_sub
  have hdeg : (X + 1 : ℂ[X]).degree = 1 := by
    simpa using Polynomial.degree_X_add_C (1 : ℂ)
  rw [hdeg]
  exact_mod_cast (show 1 < 2 * n + 5 by omega)

theorem clonePolynomial_natDegree (n : ℕ) :
    (clonePolynomial n).natDegree = 2 * n + 5 := by
  unfold clonePolynomial
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · have hdeg : (X + 1 : ℂ[X]).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_add_C (1 : ℂ)
    rw [hdeg]
    simp only [Polynomial.natDegree_X_pow]
    omega

/-- No root of `z^d-z-1`, for any integer degree d≥2, is also a root
of its derivative. This scalar statement is independent of any matrix. -/
theorem unit_trinomial_derivative_ne_zero (d : ℕ) (hd : 2 ≤ d)
    (z : ℂ) (hz : z ^ d = z + 1) :
    (d : ℂ) * z ^ (d - 1) - 1 ≠ 0 := by
  intro hzero
  have hder : (d : ℂ) * z ^ (d - 1) = 1 := sub_eq_zero.mp hzero
  have hpow : z ^ d = z ^ (d - 1) * z := by
    have he : d - 1 + 1 = d := by omega
    simpa only [he] using (pow_succ z (d - 1))
  have hmul : (d : ℂ) * (z + 1) = z := by
    calc
      (d : ℂ) * (z + 1) = (d : ℂ) * z ^ d := by rw [hz]
      _ = ((d : ℂ) * z ^ (d - 1)) * z := by rw [hpow]; ring
      _ = z := by rw [hder, one_mul]
  have hlinear : ((d : ℂ) - 1) * z = -(d : ℂ) := by
    linear_combination hmul
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnonneg : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have hcastnorm : ‖(d : ℂ) - 1‖ = (d : ℝ) - 1 := by
    have hc : (d : ℂ) - 1 = (((d : ℝ) - 1 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hnorm : ((d : ℝ) - 1) * ‖z‖ = (d : ℝ) := by
    have h := congrArg (fun w : ℂ => ‖w‖) hlinear
    simpa only [norm_mul, norm_neg, Complex.norm_natCast, hcastnorm] using h
  have hnorm_gt : 1 < ‖z‖ := by
    by_contra hnot
    have hle : ‖z‖ ≤ 1 := le_of_not_gt hnot
    have hm := mul_le_mul_of_nonneg_left hle hnonneg
    linarith
  have hpowers : ∀ k : ℕ, 1 ≤ ‖z‖ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        calc
          1 = 1 * 1 := by ring
          _ ≤ ‖z‖ ^ k * ‖z‖ :=
            mul_le_mul ih hnorm_gt.le (by norm_num) (pow_nonneg (norm_nonneg z) k)
  have hdernorm : (d : ℝ) * ‖z‖ ^ (d - 1) = 1 := by
    have h := congrArg (fun w : ℂ => ‖w‖) hder
    simpa only [norm_mul, Complex.norm_natCast, norm_pow, norm_one] using h
  have hm := mul_le_mul_of_nonneg_left (hpowers (d - 1))
    (Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))
  linarith

/-- The clone polynomial is separable over the complex numbers for all n. -/
theorem clonePolynomial_separable (n : ℕ) : (clonePolynomial n).Separable := by
  rw [Polynomial.separable_def,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ]
  intro z
  by_cases hz : Polynomial.aeval z (clonePolynomial n) = 0
  · right
    have hroot : z ^ (2 * n + 5) = z + 1 := by
      have h : z ^ (2 * n + 5) - (z + 1) = 0 := by
        simpa [clonePolynomial] using hz
      exact sub_eq_zero.mp h
    simpa [clonePolynomial, Polynomial.derivative_sub,
      Polynomial.derivative_add, Polynomial.derivative_X_pow] using
      unit_trinomial_derivative_ne_zero (2 * n + 5) (by omega) z hroot
  · exact Or.inl hz

theorem clonePolynomial_squarefree (n : ℕ) : Squarefree (clonePolynomial n) :=
  (clonePolynomial_separable n).squarefree

theorem clonePolynomial_roots_nodup (n : ℕ) : (clonePolynomial n).roots.Nodup :=
  Polynomial.nodup_roots (clonePolynomial_separable n)

/-- There are exactly d distinct complex scalar roots. -/
theorem clonePolynomial_card_roots (n : ℕ) :
    (clonePolynomial n).roots.card = 2 * n + 5 := by
  rw [IsAlgClosed.card_roots_eq_natDegree, clonePolynomial_natDegree]

private theorem norm_multiset_product (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map (fun z : ℂ => ‖z‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih => simp [norm_mul, ih]

/-- Exact Vieta product in modulus, with multiplicities supplied by
mathlib's polynomial roots. No numerical root approximation is used. -/
theorem clonePolynomial_norm_product (n : ℕ) :
    ((clonePolynomial n).roots.map (fun z : ℂ => ‖z‖)).prod = 1 := by
  have h := (IsAlgClosed.splits (clonePolynomial n)).eval_eq_prod_roots_of_monic
    (clonePolynomial_monic n) 0
  have hn := congrArg (fun z : ℂ => ‖z‖) h
  rw [norm_multiset_product] at hn
  simpa [clonePolynomial, show 2 * n + 5 ≠ 0 by omega,
    Multiset.map_map, Function.comp_def] using hn.symm

#print axioms unit_trinomial_derivative_ne_zero
#print axioms clonePolynomial_separable
#print axioms clonePolynomial_squarefree
#print axioms clonePolynomial_roots_nodup
#print axioms clonePolynomial_card_roots
#print axioms clonePolynomial_norm_product

end

end LoopsSpectral
