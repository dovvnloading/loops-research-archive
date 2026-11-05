import FullCloneMatrix

/-!
# Positive eigenvectors dominate the modulus of all complex eigenvalues

A finite nonnegative matrix with a strictly positive real eigenvector
at a real eigenvalue t has no complex eigenvalue of modulus greater
than t. This is an elementary finite-dimensional Perron bound: choose
a vertex maximizing the weighted quotient ‖z_i‖/x_i, use the triangle
inequality in that row, then cancel the positive maximal coordinate.

This theorem is reusable beyond the particular cloned graph, and the
specialization below applies it to every cloned five-vertex matrix.
It is strictly stronger than merely exhibiting a positive eigenpair.
-/

namespace LoopsSpectral

noncomputable section

/-- General finite-dimensional Perron modulus bound from an exact
    positive eigenvector of a nonnegative matrix. -/
theorem complex_eigenvalue_norm_le_of_positive_vector
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) (t : ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hx : ∀ i, 0 < x i)
    (hAx : ∀ i, (∑ j, A i j * x j) = t * x i)
    (μ : ℂ) (z : ι → ℂ)
    (hz : ∃ i, z i ≠ 0)
    (hAz : ∀ i, (∑ j, ((A i j : ℝ) : ℂ) * z j) = μ * z i) :
    ‖μ‖ ≤ t := by
  classical
  let ratio : ι → ℝ := fun i => ‖z i‖ / x i
  obtain ⟨i, _, himax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι)
      ratio Finset.univ_nonempty
  have hratio_mul (j : ι) : ratio j * x j = ‖z j‖ := by
    dsimp [ratio]
    field_simp [ne_of_gt (hx j)]
  have hbound (j : ι) : ‖z j‖ ≤ ratio i * x j := by
    calc
      ‖z j‖ = ratio j * x j := (hratio_mul j).symm
      _ ≤ ratio i * x j :=
        mul_le_mul_of_nonneg_right (himax j (Finset.mem_univ j))
          (le_of_lt (hx j))
  have hratio_pos : 0 < ratio i := by
    obtain ⟨j, hj⟩ := hz
    have hjpos : 0 < ‖z j‖ := norm_pos_iff.mpr hj
    have hjratio : 0 < ratio j :=
      div_pos hjpos (hx j)
    exact lt_of_lt_of_le hjratio (himax j (Finset.mem_univ j))
  have hnormpos : 0 < ‖z i‖ := by
    rw [← hratio_mul i]
    exact mul_pos hratio_pos (hx i)
  have hnorm_entry (j : ι) :
      ‖((A i j : ℝ) : ℂ) * z j‖ = A i j * ‖z j‖ := by
    rw [norm_mul, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (hA i j)]
  have hsum_bound :
      (∑ j, A i j * ‖z j‖) ≤
        (∑ j, A i j * (ratio i * x j)) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hbound j) (hA i j)
  have hsum_value :
      (∑ j, A i j * (ratio i * x j)) =
        ratio i * (t * x i) := by
    calc
      (∑ j, A i j * (ratio i * x j)) =
          ∑ j, ratio i * (A i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ratio i * (∑ j, A i j * x j) := by
        rw [Finset.mul_sum]
      _ = ratio i * (t * x i) := by rw [hAx i]
  have hmul :
      ‖μ‖ * ‖z i‖ ≤ t * ‖z i‖ := by
    calc
      ‖μ‖ * ‖z i‖ = ‖μ * z i‖ := (norm_mul μ (z i)).symm
      _ = ‖∑ j, ((A i j : ℝ) : ℂ) * z j‖ := by
        rw [hAz i]
      _ ≤ ∑ j, ‖((A i j : ℝ) : ℂ) * z j‖ :=
        norm_sum_le _ _
      _ = ∑ j, A i j * ‖z j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        exact hnorm_entry j
      _ ≤ ∑ j, A i j * (ratio i * x j) := hsum_bound
      _ = ratio i * (t * x i) := hsum_value
      _ = t * ‖z i‖ := by rw [← hratio_mul i]; ring
  exact (mul_le_mul_right hnormpos).mp hmul

/-- Every complex eigenvalue of the *full* cloned graph has
modulus bounded by the positive real clone root. -/
theorem full_clone_eigenvalue_modulus_le (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1)
    (μ : ℂ) (z : Vertex n → ℂ)
    (hz : ∃ i, z i ≠ 0)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) = μ * z u) :
    ‖μ‖ ≤ t := by
  exact complex_eigenvalue_norm_le_of_positive_vector
    (fullAdjacencyMatrix n) (fullCloneVector n t) t
    (fullAdjacencyMatrix_nonneg n)
    (fullCloneVector_pos n t ht)
    (fun u => fullAdjacencyMatrix_eigen n t ht hroot u)
    μ z hz hAz

end

end LoopsSpectral
