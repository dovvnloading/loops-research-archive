import Mathlib
import QuadraticEscape

/-!
# Mixed susceptibility for the actual quadratic family

The coefficient in the difference of two critical orbits is the sum of
their orbit values. Its reciprocal products give a complex series whose
ordinary convergence, together with boundedness of both critical orbits,
forces its off-diagonal value to vanish. Uniform convergence on a connected
parameter set then turns a nonzero diagonal value into rigidity.
-/

namespace QuadraticMixedSusceptibility

open Set Filter
open scoped Topology

noncomputable section

/-- The actual bounded-critical-orbit parameter locus. -/
def mandelbrot : Set ℂ :=
  {c | ∃ B : ℝ, ∀ n : ℕ, ‖QuadraticEscape.orbit c n 0‖ ≤ B}

/-- The exact multiplier of a difference of quadratic critical orbits. -/
def factor (c d : ℂ) (n : ℕ) : ℂ :=
  QuadraticEscape.orbit c (n + 1) 0 + QuadraticEscape.orbit d (n + 1) 0

/-- Products begin at the critical value, with the empty product equal to one. -/
def product (c d : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => product c d n * factor c d n

/-- Ordinary complex partialSum sums; no absolute summation is imposed. -/
def partialSum (c d : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => partialSum c d n + (product c d (n + 1))⁻¹

def Nonvanishing (c d : ℂ) : Prop := ∀ n : ℕ, factor c d n ≠ 0

theorem product_ne_zero (c d : ℂ) (h : Nonvanishing c d) (n : ℕ) :
    product c d n ≠ 0 := by
  induction n with
  | zero => simp [product]
  | succ n ih => exact mul_ne_zero ih (h n)

theorem partialSum_eq_sum (c d : ℂ) (n : ℕ) :
    partialSum c d n = 1 + ∑ k ∈ Finset.range n, (product c d (k + 1))⁻¹ := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [partialSum, ih, Finset.sum_range_succ]
    ring

/-- Exact finite, nonlinear parameter-difference identity. -/
theorem orbit_difference_eq (c d : ℂ) (h : Nonvanishing c d) (n : ℕ) :
    QuadraticEscape.orbit c (n + 1) 0 - QuadraticEscape.orbit d (n + 1) 0 =
      (c - d) * product c d n * partialSum c d n := by
  induction n with
  | zero => simp [QuadraticEscape.orbit, product, partialSum]
  | succ n ih =>
    calc
      QuadraticEscape.orbit c (n + 1 + 1) 0 -
          QuadraticEscape.orbit d (n + 1 + 1) 0 =
          factor c d n * (QuadraticEscape.orbit c (n + 1) 0 -
            QuadraticEscape.orbit d (n + 1) 0) + (c - d) := by
              simp only [QuadraticEscape.orbit, factor]
              ring
      _ = (c - d) * product c d (n + 1) * partialSum c d n + (c - d) := by
        rw [ih, product]
        ring
      _ = (c - d) * product c d (n + 1) * partialSum c d (n + 1) := by
        rw [partialSum, mul_add]
        simp only [mul_assoc, mul_inv_cancel₀ (product_ne_zero c d h (n + 1)),
          mul_one]

theorem normalized_difference_eq (c d : ℂ) (h : Nonvanishing c d) (n : ℕ) :
    (c - d) * partialSum c d n =
      (QuadraticEscape.orbit c (n + 1) 0 - QuadraticEscape.orbit d (n + 1) 0) *
        (product c d n)⁻¹ := by
  rw [orbit_difference_eq c d h n]
  calc
    (c - d) * partialSum c d n =
        (c - d) * partialSum c d n *
          (product c d n * (product c d n)⁻¹) := by
            rw [mul_inv_cancel₀ (product_ne_zero c d h n), mul_one]
    _ = _ := by ring

end
end QuadraticMixedSusceptibility
