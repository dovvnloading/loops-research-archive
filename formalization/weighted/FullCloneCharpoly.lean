import ClonePolynomialRoots

/-!
# Exact characteristic polynomial of the actual cloned graph

Every scalar root now supplies an explicit nonzero eigenvector of the
actual row-source adjacency matrix. Separability gives distinct roots;
the degree and monicity of the matrix characteristic polynomial then
force equality with `X^(2*n+5)-X-1`.

This identifies the actual graph matrix, without taking a determinant
formula or algebraic multiplicity as a premise.

AI assistance: OpenAI GPT-6 Astra Pro, proof construction and API audit.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph
open Polynomial

noncomputable section

/-- Complexification of the actual row-source 0/1 adjacency matrix. -/
def complexFullAdjacencyMatrix (n : ℕ) : Matrix (Vertex n) (Vertex n) ℂ :=
  fun u w => (fullAdjacencyMatrix n u w : ℂ)

/-- A vector normalized to 1 immediately after the shortcut tip.
This formula works for every complex root, without dividing by it. -/
def cloneComplexRootVector (n : ℕ) (μ : ℂ) (u : Vertex n) : ℂ :=
  if u.val ≤ n then μ ^ (u.val + n + 4) else μ ^ (u.val - (n + 1))

theorem cloneComplexRootVector_nonzero (n : ℕ) (μ : ℂ) :
    cloneComplexRootVector n μ ≠ 0 := by
  intro hz
  have h := congrFun hz (⟨n + 1, by dsimp [size]; omega⟩ : Vertex n)
  have hnot : ¬n + 1 ≤ n := by omega
  simp [cloneComplexRootVector, hnot] at h

/-- Every scalar root gives all rows of an actual adjacency eigenpair. -/
theorem cloneComplexRootVector_eigen (n : ℕ) (μ : ℂ)
    (hroot : μ ^ (2 * n + 5) = μ + 1) (u : Vertex n) :
    (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * cloneComplexRootVector n μ w) =
        μ * cloneComplexRootVector n μ u := by
  rw [complex_full_matrix_action]
  change (if h : u.val + 1 < size n then
    cloneComplexRootVector n μ (nextVertex n u h) +
      (if u.val = n then cloneComplexRootVector n μ (afterTip n) else 0)
    else cloneComplexRootVector n μ (hub n)) =
      μ * cloneComplexRootVector n μ u
  by_cases hnext : u.val + 1 < size n
  · rw [dif_pos hnext]
    by_cases htip : u.val = n
    · rw [if_pos htip]
      have hu : u.val ≤ n := by omega
      have hv : ¬(nextVertex n u hnext).val ≤ n := by
        dsimp [nextVertex]
        omega
      have ha : ¬(afterTip n).val ≤ n := by
        dsimp [afterTip]
        omega
      have hnextExp : (nextVertex n u hnext).val - (n + 1) = 0 := by
        dsimp [nextVertex]
        omega
      have hafterExp : (afterTip n).val - (n + 1) = 1 := by
        dsimp [afterTip]
        omega
      have htipExp : u.val + n + 4 = 2 * n + 4 := by omega
      simp only [cloneComplexRootVector, if_pos hu, if_neg hv, if_neg ha]
      rw [hnextExp, hafterExp, htipExp, pow_zero, pow_one]
      calc
        1 + μ = μ + 1 := by ring
        _ = μ ^ (2 * n + 5) := hroot.symm
        _ = μ * μ ^ (2 * n + 4) := by
          rw [show 2 * n + 5 = (2 * n + 4) + 1 by omega, pow_succ]
          ring
    · rw [if_neg htip, add_zero]
      by_cases hu : u.val ≤ n
      · have hv : (nextVertex n u hnext).val ≤ n := by
          dsimp [nextVertex]
          omega
        have he : (nextVertex n u hnext).val + n + 4 =
            (u.val + n + 4) + 1 := by
          dsimp [nextVertex]
          omega
        simp only [cloneComplexRootVector, if_pos hu, if_pos hv]
        rw [he, pow_succ]
        ring
      · have hv : ¬(nextVertex n u hnext).val ≤ n := by
          dsimp [nextVertex]
          omega
        have he : (nextVertex n u hnext).val - (n + 1) =
            (u.val - (n + 1)) + 1 := by
          dsimp [nextVertex]
          omega
        simp only [cloneComplexRootVector, if_neg hu, if_neg hv]
        rw [he, pow_succ]
        ring
  · rw [dif_neg hnext]
    have hulast : u.val = 2 * n + 4 := by
      have hu := u.isLt
      dsimp [size] at hu hnext
      omega
    have hu : ¬u.val ≤ n := by omega
    have he : u.val - (n + 1) = n + 3 := by omega
    have hhub : cloneComplexRootVector n μ (hub n) = μ ^ (n + 4) := by
      simp [cloneComplexRootVector, hub]
    rw [hhub, cloneComplexRootVector, if_neg hu, he]
    rw [show n + 4 = (n + 3) + 1 by omega, pow_succ]
    ring

/-- The scalar polynomial-root condition implies a genuine eigenvalue
of the actual matrix, expressed in mathlib's endomorphism API. -/
theorem clone_root_has_actual_eigenvalue (n : ℕ) (μ : ℂ)
    (hroot : μ ^ (2 * n + 5) = μ + 1) :
    (complexFullAdjacencyMatrix n).mulVecLin.HasEigenvalue μ := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := cloneComplexRootVector n μ)
  refine ⟨?_, cloneComplexRootVector_nonzero n μ⟩
  apply Module.End.mem_eigenspace_iff.mpr
  funext u
  change (∑ w : Vertex n,
    ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * cloneComplexRootVector n μ w) =
      μ * cloneComplexRootVector n μ u
  exact cloneComplexRootVector_eigen n μ hroot u

theorem clone_root_is_actual_charpoly_root (n : ℕ) (μ : ℂ)
    (hroot : μ ^ (2 * n + 5) = μ + 1) :
    (complexFullAdjacencyMatrix n).charpoly.IsRoot μ := by
  have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly
    (complexFullAdjacencyMatrix n).mulVecLin μ).mp
      (clone_root_has_actual_eigenvalue n μ hroot)
  simpa only [Matrix.charpoly_mulVecLin] using he

/-- The missing all-delay characteristic-polynomial identity for the
actual graph's full adjacency matrix, including algebraic multiplicity. -/
theorem full_clone_complex_charpoly (n : ℕ) :
    (complexFullAdjacencyMatrix n).charpoly = cloneCharPolynomial n := by
  have hcop : IsCoprime (cloneCharPolynomial n) (cloneCharPolynomial n).derivative :=
    cloneCharPolynomial_separable n
  have hdvd : cloneCharPolynomial n ∣ (complexFullAdjacencyMatrix n).charpoly := by
    apply hcop.dvd_of_dvd_mul_left
    apply (Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul
      (cloneCharPolynomial_monic n).ne_zero).mp
    intro μ hμ
    have hroot : μ ^ (2 * n + 5) = μ + 1 := by
      have h : μ ^ (2 * n + 5) - (μ + 1) = 0 := by
        simpa [Polynomial.IsRoot, cloneCharPolynomial] using hμ
      exact sub_eq_zero.mp h
    exact clone_root_is_actual_charpoly_root n μ hroot
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (cloneCharPolynomial_monic n) (Matrix.charpoly_monic _) hdvd
  simp [Matrix.charpoly_natDegree_eq_dim, cloneCharPolynomial_natDegree, Vertex, size]

/-- The determinant identity itself, evaluated at every complex parameter. -/
theorem full_clone_complex_characteristic_det (n : ℕ) (μ : ℂ) :
    (Matrix.scalar (Vertex n) μ - complexFullAdjacencyMatrix n).det =
      μ ^ (2 * n + 5) - μ - 1 := by
  rw [← Matrix.eval_charpoly, full_clone_complex_charpoly]
  simp only [cloneCharPolynomial, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  ring

/-- Every actual characteristic root has algebraic multiplicity one. -/
theorem full_clone_complex_charpoly_separable (n : ℕ) :
    (complexFullAdjacencyMatrix n).charpoly.Separable := by
  rw [full_clone_complex_charpoly]
  exact cloneCharPolynomial_separable n

/-- The actual adjacency characteristic polynomial has d distinct roots. -/
theorem full_clone_complex_charpoly_roots (n : ℕ) :
    (complexFullAdjacencyMatrix n).charpoly.roots.Nodup ∧
      (complexFullAdjacencyMatrix n).charpoly.roots.card = 2 * n + 5 := by
  rw [full_clone_complex_charpoly]
  exact ⟨cloneCharPolynomial_roots_nodup n, cloneCharPolynomial_card_roots n⟩

/-- Vieta's modulus product now refers to the actual adjacency spectrum. -/
theorem full_clone_complex_charpoly_norm_product (n : ℕ) :
    ((complexFullAdjacencyMatrix n).charpoly.roots.map
      (fun μ : ℂ => ‖μ‖)).prod = 1 := by
  rw [full_clone_complex_charpoly]
  exact cloneCharPolynomial_norm_product n

/-- The actual adjacency endomorphism is semisimple, by its squarefree
characteristic polynomial and Cayley--Hamilton. -/
theorem full_clone_complex_semisimple (n : ℕ) :
    (complexFullAdjacencyMatrix n).mulVecLin.IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (complexFullAdjacencyMatrix n).mulVecLin.charpoly)
  · simpa only [Matrix.charpoly_mulVecLin] using
      (full_clone_complex_charpoly_separable n).squarefree
  · exact LinearMap.aeval_self_charpoly _

/-- Diagonalizability stated as spanning by complex eigenspaces. -/
theorem full_clone_complex_eigenspaces_span (n : ℕ) :
    (⨆ μ : ℂ, (complexFullAdjacencyMatrix n).mulVecLin.eigenspace μ) = ⊤ :=
  (full_clone_complex_semisimple n).iSup_eigenspace_eq_top

#print axioms cloneComplexRootVector_eigen
#print axioms clone_root_has_actual_eigenvalue
#print axioms full_clone_complex_charpoly
#print axioms full_clone_complex_characteristic_det
#print axioms full_clone_complex_charpoly_separable
#print axioms full_clone_complex_charpoly_roots
#print axioms full_clone_complex_charpoly_norm_product
#print axioms full_clone_complex_semisimple
#print axioms full_clone_complex_eigenspaces_span

end

end LoopsSpectral
