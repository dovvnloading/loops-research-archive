import QuadraticProjectiveRigidity

/-!
# Finite-order separation of two actual quadratic return configurations

The main-component and period-two critical return quadruples are compared
at the same true multiplier.  Their poles and first two finite terms
cancel exactly.  The remaining quadratic factor has coefficient `1/128`.
No limiting dynamical space or model realization enters this identity.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Polynomial

/-- The rational unit left after removing the quadratic multiplier factor
from the difference of the two actual critical-orbit observables. -/
def separationUnit (k : ℕ) (U : ℂ[X]) (Q : (ℂ[X])[X]) (t : ℂ) : ℂ :=
  1 / 128 + periodTwoMultiplier t *
    (Q.eval₂ (evalRingHom (periodTwoError t)) (periodTwoMultiplier t) /
        (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) +
      (3 + 3 * t + t ^ 2) / (512 * (1 + t) ^ 4) -
      U.eval (periodTwoMultiplier t) / (denPoly 0 k).eval (periodTwoMultiplier t))

@[simp] theorem separationUnit_zero (k : ℕ) (U : ℂ[X]) (Q : (ℂ[X])[X]) :
    separationUnit k U Q 0 = 1 / 128 := by
  simp [separationUnit, periodTwoMultiplier]

/-- Exact algebraic separation at matched multipliers, for every clock at
least three, of two ordered configurations in the actual quadratic family. -/
theorem criticalClock_separation_factor (k : ℕ) (hk : 3 ≤ k) :
    ∃ U : ℂ[X], ∃ Q : (ℂ[X])[X],
      ∀ t : ℂ, t ≠ 0 → t + 1 ≠ 0 →
        (denPoly 0 k).eval (periodTwoMultiplier t) ≠ 0 →
        (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) ≠ 0 →
        criticalClock (periodTwoParameter t) (2 * k) -
          criticalClock (mainParameter (periodTwoMultiplier t)) k =
          (periodTwoMultiplier t) ^ 2 *
            (1 / 128 + periodTwoMultiplier t *
              (Q.eval₂ (evalRingHom (periodTwoError t)) (periodTwoMultiplier t) /
                  (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) +
                (3 + 3 * t + t ^ 2) / (512 * (1 + t) ^ 4) -
                U.eval (periodTwoMultiplier t) /
                  (denPoly 0 k).eval (periodTwoMultiplier t))) := by
  obtain ⟨U, _, hU⟩ := criticalClock_main_cubic_remainder k hk
  obtain ⟨Q, _, hQ⟩ := criticalClock_periodTwo_center_jet k hk
  refine ⟨U, Q, ?_⟩
  intro t ht ht₁ hD₁ hD₂
  have hmain := hU (periodTwoMultiplier t) (periodTwoMultiplier_ne_zero t ht ht₁) hD₁
  have htwo := hQ t ht ht₁ hD₂
  linear_combination htwo - hmain

/-- The same exact separation, with its rational unit named. -/
theorem criticalClock_separation_unit (k : ℕ) (hk : 3 ≤ k) :
    ∃ U : ℂ[X], ∃ Q : (ℂ[X])[X],
      ∀ t : ℂ, t ≠ 0 → t + 1 ≠ 0 →
        (denPoly 0 k).eval (periodTwoMultiplier t) ≠ 0 →
        (denPoly (periodTwoError t) k).eval (periodTwoMultiplier t) ≠ 0 →
        criticalClock (periodTwoParameter t) (2 * k) -
          criticalClock (mainParameter (periodTwoMultiplier t)) k =
          (periodTwoMultiplier t) ^ 2 * separationUnit k U Q t :=
  criticalClock_separation_factor k hk

end LoopsQuadraticProjective
