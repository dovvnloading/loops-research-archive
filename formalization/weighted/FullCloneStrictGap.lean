import FullClonePolynomial

/-!
# Strict complex spectral gap without Perron--Frobenius machinery

The clone's actual eigenvalue equation is μ^(2n+5)=μ+1.
Its positive root t>1 is already known to dominate complex eigenvalue
moduli. If ‖μ‖=t, then ‖μ+1‖=t+1. Comparing squared complex norms
forces Re μ=t and Im μ=0. Thus μ=t.

This removes the leading-modulus equality case for EVERY n and
every complex eigenvector of the actual adjacency matrix. It does NOT
claim a uniform numerical gap as n→∞ or algebraic multiplicity one.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph

noncomputable section

/-- A scalar rigidity theorem for the distinguished positive root
of z^(2n+5)-z-1. No spectral or matrix hypothesis is needed here. -/
theorem clone_polynomial_norm_rigidity (n : ℕ)
    (t : ℝ) (ht : 1 < t)
    (hroot : t ^ (2 * n + 5) = t + 1)
    (μ : ℂ)
    (hμ : μ ^ (2 * n + 5) = μ + 1)
    (hnorm : ‖μ‖ = t) :
    μ = (t : ℂ) := by
  have hplus : ‖μ + 1‖ = t + 1 := by
    calc
      ‖μ + 1‖ = ‖μ ^ (2 * n + 5)‖ := by rw [hμ]
      _ = ‖μ‖ ^ (2 * n + 5) := norm_pow μ _
      _ = t ^ (2 * n + 5) := by rw [hnorm]
      _ = t + 1 := hroot
  have hsq : μ.re ^ 2 + μ.im ^ 2 = t ^ 2 := by
    have h := Complex.sq_norm μ
    rw [hnorm, Complex.normSq_apply] at h
    nlinarith
  have hplusSq : (μ.re + 1) ^ 2 + μ.im ^ 2 = (t + 1) ^ 2 := by
    have h := Complex.sq_norm (μ + 1)
    rw [hplus, Complex.normSq_apply] at h
    simp only [Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, add_zero] at h
    nlinarith
  have hre : μ.re = t := by nlinarith
  have him : μ.im = 0 := by
    have hz : μ.im ^ 2 = 0 := by nlinarith
    nlinarith [sq_nonneg μ.im]
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- Every OTHER complex eigenvalue of the full cloned adjacency
matrix has modulus strictly below the positive real root. -/
theorem full_clone_strict_complex_spectral_gap
    (n : ℕ) (t : ℝ) (ht : 1 < t)
    (hroot : t ^ (2 * n + 5) = t + 1)
    (μ : ℂ) (z : Vertex n → ℂ)
    (hz : ∃ u, z u ≠ 0)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        μ * z u)
    (hne : μ ≠ (t : ℂ)) :
    ‖μ‖ < t := by
  have hle : ‖μ‖ ≤ t :=
    full_clone_eigenvalue_modulus_le n t ht hroot μ z hz hAz
  have hpoly : μ ^ (2 * n + 5) = μ + 1 :=
    full_clone_complex_eigenvalue_polynomial n μ z hz hAz
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact False.elim (hne
      (clone_polynomial_norm_rigidity n t ht hroot μ hpoly heq))

/-- Each clone possesses a dominant complex eigenvalue in (1,2);
every different complex eigenvalue has strictly smaller modulus.
This is quantified over all delays, not a finite numerical test. -/
theorem exists_strictly_dominant_full_clone_root (n : ℕ) :
    ∃ t : ℝ, 1 < t ∧ t < 2 ∧
      (∃ z : Vertex n → ℂ,
        (∃ u, z u ≠ 0) ∧
        ∀ u, (∑ w : Vertex n,
          ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
            (t : ℂ) * z u) ∧
      (∀ μ : ℂ, ∀ z : Vertex n → ℂ,
        (∃ u, z u ≠ 0) →
        (∀ u, (∑ w : Vertex n,
          ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
            μ * z u) →
        μ ≠ (t : ℂ) → ‖μ‖ < t) := by
  obtain ⟨t, ht, ht2, hroot⟩ := finite_clone_root_exists n
  refine ⟨t, ht, ht2, ?_, ?_⟩
  · exact full_clone_real_root_is_complex_eigenvalue n t ht hroot
  · intro μ z hz hAz hne
    exact full_clone_strict_complex_spectral_gap
      n t ht hroot μ z hz hAz hne

#print axioms full_clone_complex_eigenvalue_polynomial
#print axioms clone_polynomial_norm_rigidity
#print axioms full_clone_strict_complex_spectral_gap
#print axioms exists_strictly_dominant_full_clone_root

end

end LoopsSpectral
