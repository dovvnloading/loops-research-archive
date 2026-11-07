import FullCloneStrictGap

/-!
# The full clone leading eigenline is unique

The source-graph row recurrence determines the whole complex vector
from its hub coordinate as soon as the spectral parameter has μ+1≠0.
At the actual positive root t>1 this is automatic.

This is GEOMETRIC simplicity: every t-eigenvector is a scalar multiple
of the checked strictly positive fullCloneVector. Algebraic simplicity
of the characteristic root is a separate statement.
-/

namespace LoopsSpectral

open LoopsFormal.CloneGraph

noncomputable section

/-- Any two complex eigenvectors for the same spectral parameter
obey a hub-cross-multiplication identity. No nonzero hypotheses on
the vectors are required. -/
theorem complex_clone_same_eigenvalue_cross
    (n : ℕ) (μ : ℂ) (z w : Vertex n → ℂ)
    (hden : μ + 1 ≠ 0)
    (hAz : ∀ u, (∑ v : Vertex n,
      ((fullAdjacencyMatrix n u v : ℝ) : ℂ) * z v) = μ * z u)
    (hAw : ∀ u, (∑ v : Vertex n,
      ((fullAdjacencyMatrix n u v : ℝ) : ℂ) * w v) = μ * w u)
    (u : Vertex n) :
    z u * w (hub n) = w u * z (hub n) := by
  by_cases hleft : u.val ≤ n
  · have hz := complex_eigen_prefix n μ z hAz u.val hleft
    have hw := complex_eigen_prefix n μ w hAw u.val hleft
    have heq :
        (⟨u.val, by dsimp [size]; omega⟩ : Vertex n) = u :=
      Fin.ext rfl
    rw [heq] at hz hw
    rw [hz, hw]
    ring
  · let mid : Vertex n := ⟨n + 1, by dsimp [size]; omega⟩
    have htz := complex_eigen_shortcut n μ z hAz
    have htw := complex_eigen_shortcut n μ w hAw
    change (μ + 1) * z mid = μ ^ (n + 1) * z (hub n) at htz
    change (μ + 1) * w mid = μ ^ (n + 1) * w (hub n) at htw
    have hmid :
        z mid * w (hub n) = w mid * z (hub n) := by
      have hp :
          (μ + 1) * (z mid * w (hub n) - w mid * z (hub n)) = 0 := by
        calc
          (μ + 1) * (z mid * w (hub n) - w mid * z (hub n)) =
              ((μ + 1) * z mid) * w (hub n) -
                ((μ + 1) * w mid) * z (hub n) := by ring
          _ = (μ ^ (n + 1) * z (hub n)) * w (hub n) -
                (μ ^ (n + 1) * w (hub n)) * z (hub n) := by rw [htz, htw]
          _ = 0 := by ring
      have hdiff : z mid * w (hub n) - w mid * z (hub n) = 0 :=
        (mul_eq_zero.mp hp).resolve_left hden
      exact sub_eq_zero.mp hdiff
    let j := u.val - (n + 1)
    have hj : j ≤ n + 3 := by
      dsimp [j]
      have hu := u.isLt
      dsimp [size] at hu
      omega
    have hz := complex_eigen_suffix n μ z hAz j hj
    have hw := complex_eigen_suffix n μ w hAw j hj
    have heq :
        (⟨n + 1 + j, by dsimp [size]; omega⟩ : Vertex n) = u := by
      apply Fin.ext
      dsimp [j]
      omega
    rw [heq] at hz hw
    change z u = μ ^ j * z mid at hz
    change w u = μ ^ j * w mid at hw
    rw [hz, hw]
    calc
      (μ ^ j * z mid) * w (hub n) =
          μ ^ j * (z mid * w (hub n)) := by ring
      _ = μ ^ j * (w mid * z (hub n)) := by rw [hmid]
      _ = (μ ^ j * w mid) * z (hub n) := by ring

/-- The positive root has a one-dimensional complex eigenspace:
EVERY eigenvector is a scalar multiple of the explicit real positive
fullCloneVector, with scalar equal to its hub coordinate. -/
theorem full_clone_root_eigenline_unique
    (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1)
    (z : Vertex n → ℂ)
    (hAz : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * z w) =
        (t : ℂ) * z u)
    (u : Vertex n) :
    z u = z (hub n) * (fullCloneVector n t u : ℂ) := by
  let v : Vertex n → ℂ := fun u => (fullCloneVector n t u : ℂ)
  have hv : ∀ u, (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) * v w) =
        (t : ℂ) * v u := by
    intro u
    have he := fullAdjacencyMatrix_eigen n t ht hroot u
    change (∑ w : Vertex n,
      ((fullAdjacencyMatrix n u w : ℝ) : ℂ) *
        (fullCloneVector n t w : ℂ)) =
          (t : ℂ) * (fullCloneVector n t u : ℂ)
    exact_mod_cast he
  have hdenReal : t + 1 ≠ 0 := by linarith
  have hden : (t : ℂ) + 1 ≠ 0 := by
    exact_mod_cast hdenReal
  have hc := complex_clone_same_eigenvalue_cross n (t : ℂ)
    z v hden hAz hv u
  have hvhub : v (hub n) = 1 := by
    simp [v, fullCloneVector, hub]
  rw [hvhub, mul_one] at hc
  change z u = v u * z (hub n) at hc
  simpa [v, mul_comm] using hc

/-- Any two leading eigenvectors that agree at the hub agree at
ALL vertices. This is a simple fully quantified uniqueness statement. -/
theorem full_clone_root_eigenvector_unique_of_hub
    (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hroot : t ^ (2 * n + 5) = t + 1)
    (z w : Vertex n → ℂ)
    (hAz : ∀ u, (∑ v : Vertex n,
      ((fullAdjacencyMatrix n u v : ℝ) : ℂ) * z v) =
        (t : ℂ) * z u)
    (hAw : ∀ u, (∑ v : Vertex n,
      ((fullAdjacencyMatrix n u v : ℝ) : ℂ) * w v) =
        (t : ℂ) * w u)
    (hhub : z (hub n) = w (hub n)) :
    z = w := by
  funext u
  calc
    z u = z (hub n) * (fullCloneVector n t u : ℂ) :=
      full_clone_root_eigenline_unique n t ht hroot z hAz u
    _ = w (hub n) * (fullCloneVector n t u : ℂ) := by rw [hhub]
    _ = w u := (full_clone_root_eigenline_unique n t ht hroot w hAw u).symm

#print axioms complex_clone_same_eigenvalue_cross
#print axioms full_clone_root_eigenline_unique
#print axioms full_clone_root_eigenvector_unique_of_hub

end

end LoopsSpectral
