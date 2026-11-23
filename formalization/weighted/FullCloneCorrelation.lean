import FullCloneRenewal
import FiniteMarkovCorrelation

/-!
# Observable correlations of the actual normalized clone matrix

The same real root and actual adjacency used by `FullCloneRenewal` supply
the stochastic matrix. Every non-Perron complex root supplies a nonzero
observable. Given an explicitly stationary, strictly positive probability
vector for this matrix, its mean, variance and all integer-time correlations
are certified below, including the changed eigenvalue under a fair holding
clock. The stationary-vector hypothesis is not replaced by a graph label.

For the explicit formula for the stationary masses and its identification
with an invariant measure of the constructed affine interval map, see the
written proof in clone_renewal_clock_20261123.md, sections 2 and 6--7.
The readout asymptotics and random-clock physical processes are proved in
clone_resonant_readout_20261123.md. Those analytic and measure-theoretic
arguments are not asserted to be Lean proofs by this finite algebra module.
-/

namespace LoopsSpectral

open Matrix LoopsFormal.CloneGraph LoopsMarkovCorrelation

noncomputable section

theorem clone_transition_stochastic_certificate (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hreal : t ^ (2 * n + 5) = t + 1) :
    Stochastic (cloneTransition n t) := by
  obtain ⟨hnonneg, hsum⟩ := cloneTransition_stochastic n t ht hreal
  exact ⟨hnonneg, hsum⟩

/-- At every horizon the actual clone transition matrix gives probability
endpoint laws, under the explicit stationary-distribution identification. -/
theorem clone_joint_probability (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hreal : t ^ (2 * n + 5) = t + 1)
    (π : Vertex n → ℝ) (hπ : Stationary (cloneTransition n t) π) (q : ℕ) :
    (∀ i j, 0 ≤ joint (cloneTransition n t) π q i j) ∧
      (∑ i, ∑ j, joint (cloneTransition n t) π q i j) = 1 ∧
      (∀ i, ∑ j, joint (cloneTransition n t) π q i j = π i) ∧
      (∀ j, ∑ i, joint (cloneTransition n t) π q i j = π j) := by
  exact joint_probability _ π (clone_transition_stochastic_certificate n t ht hreal) hπ q

/-- Non-Perron roots give nondegenerate centered observables with exact
deterministic-clock and fair-holding-clock correlations. Every supplied
probability hypothesis concerns the actual `cloneTransition n t`. -/
theorem clone_stationary_mode_correlation (n : ℕ) (t : ℝ)
    (ht : 1 < t) (hreal : t ^ (2 * n + 5) = t + 1)
    (π : Vertex n → ℝ) (hπ : Stationary (cloneTransition n t) π)
    (hπpos : ∀ i, 0 < π i)
    (μ : ℂ) (hcomplex : μ ^ (2 * n + 5) = μ + 1) (hne : μ ≠ (t : ℂ)) :
    Stochastic (cloneTransition n t) ∧
      Stochastic (lazyTransition (cloneTransition n t)) ∧
      Stationary (lazyTransition (cloneTransition n t)) π ∧
      ∃ g : Vertex n → ℂ, (∃ i, g i ≠ 0) ∧ mean π g = 0 ∧
        0 < secondMoment π g ∧
        (∀ q, correlation (cloneTransition n t) π g q =
          (μ / (t : ℂ)) ^ q * (secondMoment π g : ℂ)) ∧
        (∀ q, correlation (lazyTransition (cloneTransition n t)) π g q =
          ((1 + μ / (t : ℂ)) / 2) ^ q * (secondMoment π g : ℂ)) := by
  have hP := clone_transition_stochastic_certificate n t ht hreal
  obtain ⟨g, hg, hmode⟩ := clone_normalized_root_is_eigenvalue n t ht μ hcomplex
  have hmv : complexify (cloneTransition n t) *ᵥ g = (μ / (t : ℂ)) • g :=
    funext hmode
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one ht))
  have hunit : μ / (t : ℂ) ≠ 1 := by
    intro heq
    exact hne ((div_eq_one_iff_eq ht0).mp heq)
  exact ⟨hP, lazy_stochastic _ hP, lazy_stationary _ π hπ, g, hg,
    stationary_mode_correlation _ π hπ hπpos g hg _ hmv hunit⟩

#print axioms clone_joint_probability
#print axioms clone_stationary_mode_correlation

end

end LoopsSpectral
