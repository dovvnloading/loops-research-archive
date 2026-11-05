import WeightedReturn

/-!
# Quantitative finite-clone power estimates

For every delay n >= 0, any real t>1 satisfying the exact clone
characteristic equation t^(2n+5)=t+1 obeys

  t^(2n+4) < 2 < t^(2n+6).

This is the integer-power form of the two-sided finite-clone root
estimate obtained from shortest and longest first-return lengths.
It does not require a numerical solver or an unproved Perron theorem.
-/

namespace LoopsSpectral

/-- An exact two-sided power bracket for a positive clone root. -/
theorem finite_clone_power_bounds (n : ℕ) (t : ℝ)
    (ht : 1 < t)
    (hpoly : t ^ (2 * n + 5) = t + 1) :
    t ^ (2 * n + 4) < 2 ∧ 2 < t ^ (2 * n + 6) := by
  have ht0 : 0 ≤ t := by linarith
  have h5 : t ^ (2 * n + 4) * t = t + 1 := by
    calc
      t ^ (2 * n + 4) * t =
          t ^ ((2 * n + 4) + 1) := (pow_succ t (2 * n + 4)).symm
      _ = t ^ (2 * n + 5) := by congr 1
      _ = t + 1 := hpoly
  have h6 : t ^ (2 * n + 6) = (t + 1) * t := by
    rw [show 2 * n + 6 = (2 * n + 5) + 1 by omega, pow_succ, hpoly]
  constructor
  · by_contra hh
    have hlarge : (2 : ℝ) ≤ t ^ (2 * n + 4) := le_of_not_gt hh
    have hm : 0 ≤ (t ^ (2 * n + 4) - 2) * t :=
      mul_nonneg (sub_nonneg.mpr hlarge) ht0
    nlinarith
  · have hmul : 0 < (t - 1) * (t + 2) := by
      apply mul_pos <;> linarith
    rw [h6]
    nlinarith

end LoopsSpectral
