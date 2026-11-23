import FullClonePolynomial

/-!
# The actual clone adjacency as a stochastic renewal clock

The Parry (positive-eigenvector) normalization is constructed from the
existing row-source matrix. Its rows are nonnegative and sum to one.
At the sole branch, the long/short choices have probabilities
1/(1+t) and t/(1+t). Complex eigenvectors transport by division by
the same positive vector, with eigenvalues divided by t.

The converse polynomial-to-matrix step is also proved: every root of
z^(2n+5)=z+1 has an explicit nonzero eigenvector of the actual adjacency.
This is needed before asymptotic polynomial roots can be called modes
of this graph's Markov chain.

The analytic cubic-gap limit is a separate written proof in
research/independent_audits/clone_renewal_clock_20261123.md.
No identification with a native KL operator or a quadratic invariant
measure is assumed or claimed here. Parry's normalization is classical.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph

noncomputable section

/-- Positive-eigenvector normalization, with the row-source convention. -/
def perronTransition {ι : Type*} (A : Matrix ι ι ℝ)
    (t : ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => A i j * v j / (t * v i)

theorem perronTransition_nonneg {ι : Type*}
    (A : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (ht : 0 < t) (hv : ∀ i, 0 < v i)
    (i j : ι) : 0 ≤ perronTransition A t v i j := by
  exact div_nonneg (mul_nonneg (hA i j) (le_of_lt (hv j)))
    (le_of_lt (mul_pos ht (hv i)))

theorem perronTransition_row_sum {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ)
    (ht : 0 < t) (hv : ∀ i, 0 < v i)
    (hAv : ∀ i, (∑ j, A i j * v j) = t * v i) (i : ι) :
    (∑ j, perronTransition A t v i j) = 1 := by
  simp only [perronTransition, ← Finset.sum_div, hAv i]
  exact div_self (ne_of_gt (mul_pos ht (hv i)))

/-- The diagonal change of coordinates preserves every complex mode,
with the explicitly normalized eigenvalue. -/
theorem perronTransition_complex_eigen {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ)
    (ht : 0 < t) (hv : ∀ i, 0 < v i)
    (μ : ℂ) (z : ι → ℂ)
    (hAz : ∀ i, (∑ j, (A i j : ℂ) * z j) = μ * z i) (i : ι) :
    (∑ j, (perronTransition A t v i j : ℂ) * (z j / (v j : ℂ))) =
      (μ / (t : ℂ)) * (z i / (v i : ℂ)) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hv0 (j : ι) : (v j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hv j))
  calc
    (∑ j, (perronTransition A t v i j : ℂ) * (z j / (v j : ℂ))) =
        ∑ j, ((A i j : ℂ) * z j) / ((t : ℂ) * (v i : ℂ)) := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [perronTransition, Complex.ofReal_div, Complex.ofReal_mul]
          field_simp
    _ = (∑ j, (A i j : ℂ) * z j) / ((t : ℂ) * (v i : ℂ)) := by
          rw [Finset.sum_div]
    _ = (μ / (t : ℂ)) * (z i / (v i : ℂ)) := by
          rw [hAz i]
          ring

/-- The normalized transition matrix of the existing full clone graph. -/
def cloneTransition (n : ℕ) (t : ℝ) : Matrix (Vertex n) (Vertex n) ℝ :=
  perronTransition (fullAdjacencyMatrix n) t (fullCloneVector n t)

theorem cloneTransition_stochastic (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1) :
    (∀ i j, 0 ≤ cloneTransition n t i j) ∧
      (∀ i, (∑ j, cloneTransition n t i j) = 1) := by
  constructor
  · exact perronTransition_nonneg _ _ _ (fullAdjacencyMatrix_nonneg n)
      (by linarith) (fullCloneVector_pos n t ht)
  · exact perronTransition_row_sum _ _ _ (by linarith)
      (fullCloneVector_pos n t ht) (fullAdjacencyMatrix_eigen n t ht hroot)

/-- The one vertex skipped by the shortcut. -/
def skippedVertex (n : ℕ) : Vertex n :=
  ⟨n + 1, by dsimp [size]; omega⟩

theorem cloneTransition_long_choice (n : ℕ) (t : ℝ) (ht : 1 < t) :
    cloneTransition n t (tip n) (skippedVertex n) = 1 / (t + 1) := by
  have ht0 : t ≠ 0 := by linarith
  have hden : t + 1 ≠ 0 := by linarith
  have hedge : Edge n (tip n) (skippedVertex n) := by
    left
    rfl
  have hA := (fullAdjacencyMatrix_one_iff_edge n _ _).mpr hedge
  unfold cloneTransition perronTransition
  rw [hA]
  simp only [fullCloneVector, tip, skippedVertex, le_refl, ite_true]
  rw [if_neg (by omega : ¬ n + 1 ≤ n), pow_succ]
  field_simp

theorem cloneTransition_short_choice (n : ℕ) (t : ℝ) (ht : 1 < t) :
    cloneTransition n t (tip n) (afterTip n) = t / (t + 1) := by
  have ht0 : t ≠ 0 := by linarith
  have hden : t + 1 ≠ 0 := by linarith
  have hedge : Edge n (tip n) (afterTip n) := by
    right
    right
    constructor <;> rfl
  have hA := (fullAdjacencyMatrix_one_iff_edge n _ _).mpr hedge
  unfold cloneTransition perronTransition
  rw [hA]
  simp only [fullCloneVector, tip, afterTip, le_refl, ite_true]
  rw [if_neg (by omega : ¬ n + 2 ≤ n), pow_succ, pow_succ]
  field_simp

/-- A complex root has the same explicit coordinates as the real
Perron vector. This definition does not assume the root is positive. -/
def complexCloneVector (n : ℕ) (μ : ℂ) (u : Vertex n) : ℂ :=
  if u.val ≤ n then μ ^ u.val else μ ^ u.val / (μ + 1)

/-- The converse missing from a merely necessary polynomial equation:
every polynomial root gives an eigenvector of the actual edge matrix. -/
theorem complexCloneVector_eigen (n : ℕ) (μ : ℂ)
    (hroot : μ ^ (2 * n + 5) = μ + 1) (u : Vertex n) :
    (∑ w, (fullAdjacencyMatrix n u w : ℂ) * complexCloneVector n μ w) =
      μ * complexCloneVector n μ u := by
  have hμ : μ ≠ 0 := by
    intro hz
    simp [hz] at hroot
  have hden : μ + 1 ≠ 0 := by
    intro hz
    exact (pow_ne_zero _ hμ) (hroot.trans hz)
  rw [complex_full_matrix_action]
  change (if h : u.val + 1 < size n then
      complexCloneVector n μ (nextVertex n u h) +
        (if u.val = n then complexCloneVector n μ (afterTip n) else 0)
      else complexCloneVector n μ (hub n)) = μ * complexCloneVector n μ u
  by_cases hnext : u.val + 1 < size n
  · rw [dif_pos hnext]
    by_cases htip : u.val = n
    · have hcur : u.val ≤ n := by omega
      have hnextlarge : ¬ u.val + 1 ≤ n := by omega
      have hsklarge : ¬ n + 2 ≤ n := by omega
      simp only [htip, ite_true, complexCloneVector, nextVertex, afterTip,
        hcur, hnextlarge, hsklarge, ite_false]
      simp only [htip]
      rw [pow_succ, pow_succ]
      field_simp
      <;> ring
    · rw [if_neg htip, add_zero]
      by_cases hlow : u.val < n
      · have hcur : u.val ≤ n := by omega
        have hnextlow : u.val + 1 ≤ n := by omega
        simp only [complexCloneVector, nextVertex, hcur, hnextlow, ite_true, pow_succ]
        ring
      · have hcur : ¬ u.val ≤ n := by omega
        have hnex : ¬ u.val + 1 ≤ n := by omega
        simp only [complexCloneVector, nextVertex, hcur, hnex, ite_false, pow_succ]
        ring
  · rw [dif_neg hnext]
    have hlast : u.val = 2 * n + 4 := by
      have hv := u.isLt
      dsimp [size] at *
      omega
    have hcur : ¬ u.val ≤ n := by omega
    simp only [complexCloneVector, hub, Nat.zero_le, ite_true, pow_zero, hcur, ite_false]
    rw [hlast]
    have hpow : μ * μ ^ (2 * n + 4) = μ ^ (2 * n + 5) := by
      rw [pow_succ]
      ring
    rw [← mul_div_assoc, hpow, hroot]
    exact (div_self hden).symm

theorem clone_polynomial_root_is_eigenvalue (n : ℕ) (μ : ℂ)
    (hroot : μ ^ (2 * n + 5) = μ + 1) :
    ∃ z : Vertex n → ℂ, (∃ i, z i ≠ 0) ∧
      ∀ u, (∑ w, (fullAdjacencyMatrix n u w : ℂ) * z w) = μ * z u := by
  refine ⟨complexCloneVector n μ, ⟨hub n, ?_⟩, complexCloneVector_eigen n μ hroot⟩
  simp [complexCloneVector, hub]

/-- Each normalized polynomial root is a genuine matrix eigenmode.
This algebra alone does not require the real root equation. The next
theorem supplies that equation before asserting stochastic semantics. -/
theorem clone_normalized_root_is_eigenvalue (n : ℕ) (t : ℝ)
    (ht : 1 < t) (μ : ℂ) (hroot : μ ^ (2 * n + 5) = μ + 1) :
    ∃ z : Vertex n → ℂ, (∃ i, z i ≠ 0) ∧
      ∀ u, (∑ w, (cloneTransition n t u w : ℂ) * z w) = (μ / (t : ℂ)) * z u := by
  obtain ⟨z, ⟨i, hi⟩, hz⟩ := clone_polynomial_root_is_eigenvalue n μ hroot
  refine ⟨fun j => z j / (fullCloneVector n t j : ℂ), ⟨i, ?_⟩, ?_⟩
  · apply div_ne_zero hi
    exact_mod_cast (ne_of_gt (fullCloneVector_pos n t ht i))
  · exact perronTransition_complex_eigen _ _ _ (by linarith)
      (fullCloneVector_pos n t ht) μ z hz

/-- A complete stochastic certificate on the SAME t and matrix: the
real root equation supplies the probability rows, and the complex root
equation supplies a nonzero normalized eigenmode. -/
theorem clone_stochastic_root_mode (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hreal : t ^ (2 * n + 5) = t + 1)
    (μ : ℂ) (hcomplex : μ ^ (2 * n + 5) = μ + 1) :
    (∀ i j, 0 ≤ cloneTransition n t i j) ∧
    (∀ i, (∑ j, cloneTransition n t i j) = 1) ∧
    ∃ z : Vertex n → ℂ, (∃ i, z i ≠ 0) ∧
      ∀ u, (∑ w, (cloneTransition n t u w : ℂ) * z w) = (μ / (t : ℂ)) * z u := by
  obtain ⟨hnonneg, hsum⟩ := cloneTransition_stochastic n t ht hreal
  exact ⟨hnonneg, hsum, clone_normalized_root_is_eigenvalue n t ht μ hcomplex⟩

/-- Mean of the two consecutive renewal lengths d and d-1. The
identification of those lengths uses the graph's first-return paths. -/
theorem consecutive_return_mean (t d : ℝ) (ht : t + 1 ≠ 0) :
    (1 / (t + 1)) * d + (t / (t + 1)) * (d - 1) = d - t / (t + 1) := by
  field_simp
  <;> ring

/-- Algebraic weighted centered-second-moment identity. For the
stochastic branch probabilities above this is their variance, independent
of d. The analytic consequence for the growing clock is proved separately. -/
theorem consecutive_return_variance (t d : ℝ) (ht : t + 1 ≠ 0) :
    (1 / (t + 1)) * (d - (d - t / (t + 1))) ^ 2 +
      (t / (t + 1)) * ((d - 1) - (d - t / (t + 1))) ^ 2 =
        t / (t + 1) ^ 2 := by
  field_simp
  <;> ring

#print axioms cloneTransition_stochastic
#print axioms cloneTransition_long_choice
#print axioms cloneTransition_short_choice
#print axioms clone_polynomial_root_is_eigenvalue
#print axioms clone_normalized_root_is_eigenvalue
#print axioms clone_stochastic_root_mode
#print axioms consecutive_return_variance

end

end LoopsSpectral
