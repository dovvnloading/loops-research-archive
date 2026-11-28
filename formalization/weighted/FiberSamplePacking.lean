import Mathlib

/-!
# Finite sample packing and unnormalized quadratic energy

Separated sites require distinct witnesses in a finite sample family.
Each witness away from an anchor then contributes separately to the
unnormalized second moment. Repetition in the original sample family is
allowed; no probability normalization can erase the counted witnesses.
-/

namespace Loops.FiberSampling

open scoped BigOperators

variable {X I J : Type*} [PseudoMetricSpace X]

/-- The unnormalized second moment of an indexed finite sample family. -/
noncomputable def energy [Fintype I] (s : I → X) (a : X) : ℝ :=
  ∑ i, dist (s i) a ^ 2

/-- Quadratic sample energy is nonnegative. -/
theorem energy_nonneg [Fintype I] (s : I → X) (a : X) :
    0 ≤ energy s a := by
  unfold energy
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (dist (s i) a))

/-- A radius-`r` witness cannot serve two sites separated by more than
`2*r`. This needs no finiteness and also holds in a pseudometric space. -/
theorem sample_witness_injective (p : J → X) (s : I → X) (r : ℝ)
    (hsep : ∀ j k, j ≠ k → 2 * r < dist (p j) (p k))
    (f : J → I) (hclose : ∀ j, dist (p j) (s (f j)) ≤ r) :
    Function.Injective f := by
  intro j k hjk
  by_contra hne
  have hj := hclose j
  have hk : dist (s (f j)) (p k) ≤ r := by
    rw [hjk, dist_comm]
    exact hclose k
  have ht := dist_triangle (p j) (s (f j)) (p k)
  have hs := hsep j k hne
  linarith

/-- Any sample cover of separated sites admits an injective witness
selection. The separation assumption proves injectivity after choice. -/
theorem exists_injective_samples (p : J → X) (s : I → X) (r : ℝ)
    (hsep : ∀ j k, j ≠ k → 2 * r < dist (p j) (p k))
    (hcover : ∀ j, ∃ i, dist (p j) (s i) ≤ r) :
    ∃ f : J → I, Function.Injective f ∧
      ∀ j, dist (p j) (s (f j)) ≤ r := by
  classical
  choose f hf using hcover
  exact ⟨f, sample_witness_injective p s r hsep f hf, hf⟩

/-- Distinct samples at distance at least `L` each contribute at least
`L^2`. The conclusion counts indexed witnesses, not distinct geometric
locations assumed without proof. -/
theorem packing_energy_lower_bound [Fintype I] [Fintype J]
    (s : I → X) (a : X) (f : J → I) (hf : Function.Injective f)
    (L : ℝ) (hL : 0 ≤ L) (hfar : ∀ j, L ≤ dist (s (f j)) a) :
    (Fintype.card J : ℝ) * L ^ 2 ≤ energy s a := by
  classical
  calc
    (Fintype.card J : ℝ) * L ^ 2 = ∑ _j : J, L ^ 2 := by simp
    _ ≤ ∑ j : J, dist (s (f j)) a ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ hL (hfar j) 2
    _ = ∑ i ∈ Finset.univ.image f, dist (s i) a ^ 2 := by
      exact (Finset.sum_image hf.injOn).symm
    _ ≤ energy s a := by
      unfold energy
      exact Finset.sum_le_univ_sum_of_nonneg
        (fun i => sq_nonneg (dist (s i) a))

end Loops.FiberSampling
