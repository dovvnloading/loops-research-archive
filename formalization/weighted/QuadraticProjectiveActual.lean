import QuadraticProjectiveTail
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FieldSimp

/-!
# Actual quadratic-family coordinates for projective orbit tails

The polynomial recurrence of `QuadraticProjectiveTail` is identified here
with genuine critical iterates of `z ↦ z^2 + c`, both in the fixed-point
multiplier coordinate and in the period-two return coordinate.  These are
exact identities, including the zero-multiplier parameters.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Polynomial

/-- The actual complex quadratic polynomial. -/
def quadraticMap (c z : ℂ) : ℂ := z ^ 2 + c

/-- The actual critical orbit, starting at its unique critical point. -/
def criticalOrbit (c : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => (criticalOrbit c n) ^ 2 + c

/-- The usual multiplier parameterization of the fixed-point component. -/
def mainParameter (u : ℂ) : ℂ := u / 2 - u ^ 2 / 4

/-- The period-two parameterization by a point of the two-cycle. -/
def periodTwoParameter (t : ℂ) : ℂ := -1 - t - t ^ 2

/-- Product of the two derivatives along the parameterized two-cycle. -/
def periodTwoMultiplier (t : ℂ) : ℂ := -4 * t * (1 + t)

/-- Exact quartic correction in the normalized second-return map. -/
def periodTwoError (t : ℂ) : ℂ := -1 / (8 * (1 + t) ^ 3)

/-- Evaluation of the polynomial tail, with its forced multiplier power. -/
def normalizedTail (e u : ℂ) (n : ℕ) : ℂ := u ^ n * (a e n).eval u

theorem criticalOrbit_eq_iterate (c : ℂ) (n : ℕ) :
    criticalOrbit c n = ((quadraticMap c)^[n]) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [criticalOrbit, Function.iterate_succ_apply', ← ih]
    rfl

theorem main_fixed_point (u : ℂ) :
    quadraticMap (mainParameter u) (u / 2) = u / 2 := by
  simp only [quadraticMap, mainParameter]
  ring

/-- The multiplier of the displayed fixed point is exactly its coordinate. -/
theorem main_multiplier (u : ℂ) : 2 * (u / 2) = u := by ring

theorem periodTwo_first_step (t : ℂ) :
    quadraticMap (periodTwoParameter t) t = -1 - t := by
  simp only [quadraticMap, periodTwoParameter]
  ring

theorem periodTwo_second_step (t : ℂ) :
    quadraticMap (periodTwoParameter t) (-1 - t) = t := by
  simp only [quadraticMap, periodTwoParameter]
  ring

/-- Away from the root, the displayed points form a genuine two-cycle. -/
theorem periodTwo_cycle_distinct (t : ℂ) (ht : t ≠ -1 / 2) : t ≠ -1 - t := by
  intro h
  apply ht
  linear_combination (1 / 2 : ℂ) * h

theorem periodTwo_multiplier_product (t : ℂ) :
    (2 * t) * (2 * (-1 - t)) = periodTwoMultiplier t := by
  simp only [periodTwoMultiplier]
  ring

@[simp] theorem normalizedTail_zero (e u : ℂ) : normalizedTail e u 0 = -1 / 2 := by
  simp [normalizedTail]

/-- The evaluated polynomial recurrence is the exact normalized quartic map. -/
theorem normalizedTail_succ (e u : ℂ) (n : ℕ) :
    normalizedTail e u (n + 1) =
      u * (normalizedTail e u n + (normalizedTail e u n) ^ 2) +
        e * u ^ 3 * (normalizedTail e u n + (normalizedTail e u n) ^ 2) ^ 2 := by
  simp only [normalizedTail, a_succ, inc, eval_add, eval_mul, eval_pow,
    eval_X, eval_one, eval_C, pow_succ]
  ring

/-- No model-identification hypothesis is used: this is the actual orbit. -/
theorem criticalOrbit_main (u : ℂ) (n : ℕ) :
    criticalOrbit (mainParameter u) n =
      u * (1 / 2 + u ^ n * (a 0 n).eval u) := by
  change criticalOrbit (mainParameter u) n = u * (1 / 2 + normalizedTail 0 u n)
  induction n with
  | zero => norm_num [criticalOrbit]
  | succ n ih =>
    rw [criticalOrbit, ih, normalizedTail_succ]
    simp only [mainParameter]
    ring

theorem periodTwo_error_multiplier_cube (t : ℂ) (ht : t + 1 ≠ 0) :
    periodTwoError t * (periodTwoMultiplier t) ^ 3 = 8 * t ^ 3 := by
  have ht' : 1 + t ≠ 0 := by simpa [add_comm] using ht
  simp only [periodTwoError, periodTwoMultiplier]
  field_simp
  ring

/-- The complete second iterate, without truncation, in the critical coordinate. -/
theorem periodTwo_normalized_return (t y : ℂ) (ht : t + 1 ≠ 0) :
    quadraticMap (periodTwoParameter t)
      (quadraticMap (periodTwoParameter t) (t * (1 + 2 * y))) =
        t * (1 + 2 * (periodTwoMultiplier t * (y + y ^ 2) +
          periodTwoError t * (periodTwoMultiplier t) ^ 3 * (y + y ^ 2) ^ 2)) := by
  rw [periodTwo_error_multiplier_cube t ht]
  simp only [quadraticMap, periodTwoParameter, periodTwoMultiplier]
  ring

/-- The same polynomial tail is identified with every actual even critical
iterate in the period-two coordinate, including the superattracting center. -/
theorem criticalOrbit_periodTwo (t : ℂ) (n : ℕ) (ht : t + 1 ≠ 0) :
    criticalOrbit (periodTwoParameter t) (2 * n) =
      t * (1 + 2 * (periodTwoMultiplier t) ^ n *
        (a (periodTwoError t) n).eval (periodTwoMultiplier t)) := by
  simp only [mul_assoc]
  change criticalOrbit (periodTwoParameter t) (2 * n) =
    t * (1 + 2 * normalizedTail (periodTwoError t) (periodTwoMultiplier t) n)
  induction n with
  | zero => norm_num [criticalOrbit]
  | succ n ih =>
    rw [Nat.mul_add, Nat.mul_one]
    change quadraticMap (periodTwoParameter t)
      (quadraticMap (periodTwoParameter t)
        (criticalOrbit (periodTwoParameter t) (2 * n))) = _
    rw [ih, normalizedTail_succ]
    exact periodTwo_normalized_return t _ ht

end LoopsQuadraticProjective
