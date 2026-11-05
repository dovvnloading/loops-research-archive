import SpectralDominance

/-!
# Dominant real eigenvalue of every full cloned adjacency matrix

The positive root t of t^(2n+5)=t+1 is an eigenvalue of the
whole (2n+5)-vertex matrix, via the explicitly positive vector
in FullCloneMatrix.lean. SpectralDominance.lean also proves that
every complex eigenvalue has modulus at most t.

The conjunction below is a source-checkable Perron spectral
characterization: t occurs in the complex spectrum and attains the
maximum modulus of its eigenvalues.

The theorem does not yet identify a specific mathlib API named
spectralRadius, nor prove simplicity or a strict spectral gap.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph

noncomputable section

/-- The exact positive root is a genuine complex eigenvalue of the
full matrix obtained by casting the checked real eigenvector. -/
theorem full_clone_real_root_is_complex_eigenvalue (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1) :
    ∃ z : Vertex n → ℂ,
      (∃ i, z i ≠ 0) ∧
      ∀ u, (∑ w : Vertex n,
        ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
          (t : ℂ) * z u := by
  refine ⟨fun i => (fullCloneVector n t i : ℂ), ?_, ?_⟩
  · refine ⟨hub n, ?_⟩
    have hp : (fullCloneVector n t (hub n) : ℝ) ≠ 0 :=
      ne_of_gt (fullCloneVector_pos n t ht (hub n))
    change (fullCloneVector n t (hub n) : ℂ) ≠ 0
    exact_mod_cast hp
  · intro u
    have hreal := fullAdjacencyMatrix_eigen n t ht hroot u
    change (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) *
        (fullCloneVector n t w : ℂ)) =
          (t : ℂ) * (fullCloneVector n t u : ℂ)
    exact_mod_cast hreal

/-- Every clone length has a positive real eigenvalue which actually
attains the largest possible modulus among all *complex* eigenvalues
of the full graph adjacency matrix. -/
theorem full_clone_root_is_dominant_complex_eigenvalue (n : ℕ)
    (t : ℝ) (ht : 1 < t)
    (hroot : t ^ (2 * n + 5) = t + 1) :
    (∃ z : Vertex n → ℂ,
      (∃ i, z i ≠ 0) ∧
      ∀ u, (∑ w : Vertex n,
        ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
          (t : ℂ) * z u) ∧
    (∀ μ : ℂ, ∀ z : Vertex n → ℂ,
      (∃ i, z i ≠ 0) →
      (∀ u, (∑ w : Vertex n,
        ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
          μ * z u) → ‖μ‖ ≤ t) := by
  constructor
  · exact full_clone_real_root_is_complex_eigenvalue n t ht hroot
  · intro μ z hz hAz
    exact full_clone_eigenvalue_modulus_le n t ht hroot μ z hz hAz

/-- The dominant complex eigenvalue can be selected canonically as
the unique root of the finite-clone characteristic polynomial in (1,2).
This is a Prop-valued existence statement for every n≥0. -/
theorem exists_dominant_full_clone_root (n : ℕ) :
    ∃ t : ℝ, 1 < t ∧ t < 2 ∧
      (∃ z : Vertex n → ℂ,
        (∃ i, z i ≠ 0) ∧
        ∀ u, (∑ w : Vertex n,
          ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
            (t : ℂ) * z u) ∧
      (∀ μ : ℂ, ∀ z : Vertex n → ℂ,
        (∃ i, z i ≠ 0) →
        (∀ u, (∑ w : Vertex n,
          ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
            μ * z u) → ‖μ‖ ≤ t) := by
  obtain ⟨t, ht, ht2, hpoly⟩ := finite_clone_root_exists n
  refine ⟨t, ht, ht2, ?_⟩
  exact full_clone_root_is_dominant_complex_eigenvalue n t ht hpoly

end

end LoopsSpectral
