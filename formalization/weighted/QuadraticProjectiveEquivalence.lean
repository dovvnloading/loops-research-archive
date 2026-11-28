import QuadraticProjectiveAffine
import QuadraticProjectiveLimits

/-!
# Projective inequivalence of actual critical return configurations

At matched true multipliers, the ordered critical return quadruples in
the main and period-two quadratic charts cannot be carried to one another
by a fractional linear map sufficiently near their centers.  This is a
consequence of the finite algebraic separation coefficient, with the
return clock fixed.  No statement about Mandelbrot fibers is made.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Filter
open scoped Topology

/-- Fractional-linear invariance also respects the total-field convention
when one of the denominator differences of the observable vanishes. -/
theorem crossRatio_fractionalMap_total (A B C D x₀ x₁ x₂ x₃ : ℂ)
    (hdet : A * D - B * C ≠ 0)
    (h₀ : C * x₀ + D ≠ 0) (h₁ : C * x₁ + D ≠ 0)
    (h₂ : C * x₂ + D ≠ 0) (h₃ : C * x₃ + D ≠ 0) :
    crossRatio (fractionalMap A B C D x₀) (fractionalMap A B C D x₁)
      (fractionalMap A B C D x₂) (fractionalMap A B C D x₃) =
      crossRatio x₀ x₁ x₂ x₃ := by
  by_cases h₁₀ : x₁ = x₀
  · subst x₁
    simp [crossRatio]
  by_cases h₃₂ : x₃ = x₂
  · subst x₃
    simp [crossRatio]
  exact crossRatio_fractionalMap A B C D x₀ x₁ x₂ x₃ hdet h₀ h₁ h₂ h₃ h₁₀ h₃₂

/-- A nondegenerate fractional linear map sends all four ordered critical
return marks of the first parameter to those of the second.  Every image
is required to lie in the finite affine chart. -/
def NondegenerateProjectiveEquivalent (c : ℂ) (n : ℕ) (d : ℂ) (m : ℕ) : Prop :=
  ∃ A B C D : ℂ,
    A * D - B * C ≠ 0 ∧ D ≠ 0 ∧
    C * criticalOrbit c n + D ≠ 0 ∧
    C * criticalOrbit c (2 * n) + D ≠ 0 ∧
    C * criticalOrbit c (3 * n) + D ≠ 0 ∧
    fractionalMap A B C D 0 = 0 ∧
    fractionalMap A B C D (criticalOrbit c n) = criticalOrbit d m ∧
    fractionalMap A B C D (criticalOrbit c (2 * n)) = criticalOrbit d (2 * m) ∧
    fractionalMap A B C D (criticalOrbit c (3 * n)) = criticalOrbit d (3 * m)

/-- Any such ordered projective identification forces equality of the
actual critical-orbit observables. -/
theorem criticalClock_eq_of_projectiveEquivalent (c : ℂ) (n : ℕ) (d : ℂ) (m : ℕ)
    (h : NondegenerateProjectiveEquivalent c n d m) :
    criticalClock c n = criticalClock d m := by
  obtain ⟨A, B, C, D, hdet, hD, h₁, h₂, h₃, h₀, hm₁, hm₂, hm₃⟩ := h
  have hD₀ : C * 0 + D ≠ 0 := by simpa using hD
  have heq := crossRatio_fractionalMap_total A B C D 0 (criticalOrbit c n)
    (criticalOrbit c (2 * n)) (criticalOrbit c (3 * n)) hdet hD₀ h₁ h₂ h₃
  rw [h₀, hm₁, hm₂, hm₃] at heq
  exact heq.symm

/-- For each fixed return clock at least three, no nondegenerate projective
map identifies the two actual ordered critical return configurations near
their centers when their genuine multipliers agree. -/
theorem criticalClock_eventually_not_projectiveEquivalent (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ t : ℂ in 𝓝 0, t ≠ 0 →
      ¬ NondegenerateProjectiveEquivalent
        (mainParameter (periodTwoMultiplier t)) k (periodTwoParameter t) (2 * k) := by
  filter_upwards [criticalClock_eventually_separated k hk] with t ht
  intro ht₀ h
  exact ht ht₀ (criticalClock_eq_of_projectiveEquivalent _ _ _ _ h).symm

end LoopsQuadraticProjective
