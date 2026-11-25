import ClonePolynomialRoots
import FullCloneRenewal

/-!
# Exact characteristic polynomial of the actual cloned graph

The existing `FullCloneRenewal` converse supplies a nonzero eigenvector
of the actual row-source adjacency matrix for every scalar root.
The new separability proof gives distinct roots;
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

/-- The scalar polynomial-root condition implies a genuine eigenvalue
of the actual matrix, expressed in mathlib's endomorphism API. -/
theorem clone_root_has_actual_eigenvalue (n : ℕ) (μ : ℂ)
    (hroot : μ ^ (2 * n + 5) = μ + 1) :
    Module.End.HasEigenvalue (complexFullAdjacencyMatrix n).mulVecLin μ := by
  obtain ⟨z, hz, hAz⟩ := clone_polynomial_root_is_eigenvalue n μ hroot
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := z)
  refine ⟨?_, ?_⟩
  · apply Module.End.mem_eigenspace_iff.mpr
    funext u
    change (∑ w : Vertex n, (fullAdjacencyMatrix n u w : ℂ) * z w) = μ * z u
    exact hAz u
  · intro hzero
    obtain ⟨u, hu⟩ := hz
    exact hu (congrFun hzero u)

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
    Module.End.IsSemisimple (complexFullAdjacencyMatrix n).mulVecLin := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (complexFullAdjacencyMatrix n).mulVecLin.charpoly)
  · simpa only [Matrix.charpoly_mulVecLin] using
      (full_clone_complex_charpoly_separable n).squarefree
  · exact LinearMap.aeval_self_charpoly _

/-- Diagonalizability stated as spanning by complex eigenspaces. -/
theorem full_clone_complex_eigenspaces_span (n : ℕ) :
    (⨆ μ : ℂ, Module.End.eigenspace (complexFullAdjacencyMatrix n).mulVecLin μ) = ⊤ :=
  Module.End.IsSemisimple.iSup_eigenspace_eq_top (full_clone_complex_semisimple n)

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
