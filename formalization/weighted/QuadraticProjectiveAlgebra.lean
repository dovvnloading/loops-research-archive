import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Exact algebra for four marked points of an actual critical orbit.
The dynamical identifications and the finite residue are in the companion modules.
-/

namespace LoopsQuadraticProjective

noncomputable section

/-- The ordered projective observable used for critical return marks. -/
def crossRatio (x₀ x₁ x₂ x₃ : ℂ) : ℂ :=
  (x₃ - x₀) * (x₁ - x₂) / ((x₁ - x₀) * (x₃ - x₂))

/-- The nonsingular denominator after extracting the return multiplier power. -/
def clockDen (t A B C : ℂ) : ℂ := (1 + 2*t*A)*(B - t*C)

/-- The corresponding nonsingular numerator. -/
def clockNum (t A B C : ℂ) : ℂ := (1 + 2*t^3*C)*(A - t*B)

/-- The exact finite part obtained by two telescoped critical-orbit increments. -/
def clockRem (t A B C H J : ℂ) : ℂ :=
  H + 2*A*B - 2*t*A*C - t^2*J - 2*t^2*A*C + 2*t^3*B*C

theorem clock_difference_factor (t A B C H J : ℂ)
    (hB : B = A + t*H) (hC : C = B + t^2*J) :
    clockDen t A B C - clockNum t A B C = t * clockRem t A B C H J := by
  unfold clockDen clockNum clockRem
  linear_combination hB - t*hC

theorem crossRatio_scaled_clock (L t A B C : ℂ)
    (hL : L ≠ 0) (ht : t ≠ 0) (hD : clockDen t A B C ≠ 0) :
    crossRatio 0 (L*(1+2*t*A)) (L*(1+2*t^2*B)) (L*(1+2*t^3*C)) =
      -clockNum t A B C / (t * clockDen t A B C) := by
  have h₁ : 1+2*t*A ≠ 0 := (mul_ne_zero_iff.mp hD).1
  have h₂ : B-t*C ≠ 0 := (mul_ne_zero_iff.mp hD).2
  have hd : L*(1+2*t^3*C) - L*(1+2*t^2*B) =
      -(2*L*t^2*(B-t*C)) := by ring
  unfold crossRatio clockNum clockDen
  simp only [sub_zero]
  rw [hd]
  field_simp
  <;> ring

theorem crossRatio_scaled_regular_part (L t A B C H J : ℂ)
    (hL : L ≠ 0) (ht : t ≠ 0) (hD : clockDen t A B C ≠ 0)
    (hB : B = A + t*H) (hC : C = B + t^2*J) :
    crossRatio 0 (L*(1+2*t*A)) (L*(1+2*t^2*B)) (L*(1+2*t^3*C)) + t⁻¹ =
      clockRem t A B C H J / clockDen t A B C := by
  rw [crossRatio_scaled_clock L t A B C hL ht hD]
  have h := clock_difference_factor t A B C H J hB hC
  field_simp
  linear_combination h

end
end LoopsQuadraticProjective
