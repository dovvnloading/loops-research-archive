import Mathlib

/-!
# Real-axis regularity does not imply a global homeomorphism

This supporting example concerns the actual quadratic pair at `c = 0`.
The map fixes algebraic complex numbers and conjugates the others.  It
intertwines `z ↦ z^2` and `z ↦ z^2 + 1`, and its restriction to the
real axis is the identity, but the map is not continuous on the plane.

This is a boundary example, not an additional local-connectivity criterion.
-/

namespace QuadraticTwinDiscontinuous

open Set

noncomputable section

/-- Switch between identity and conjugation according to algebraicity over
the rationals. -/
def algebraicSwitch (z : ℂ) : ℂ := by
  classical
  exact if IsAlgebraic ℚ z then z else star z

/-- Algebraic arguments are fixed. -/
theorem algebraicSwitch_of_algebraic {z : ℂ} (hz : IsAlgebraic ℚ z) :
    algebraicSwitch z = z := by
  classical
  simp [algebraicSwitch, hz]

/-- Nonalgebraic arguments are conjugated. -/
theorem algebraicSwitch_of_not_algebraic {z : ℂ} (hz : ¬ IsAlgebraic ℚ z) :
    algebraicSwitch z = star z := by
  classical
  simp [algebraicSwitch, hz]

/-- Both branches agree on the real axis. -/
theorem algebraicSwitch_real (x : ℝ) :
    algebraicSwitch (x : ℂ) = (x : ℂ) := by
  classical
  simp [algebraicSwitch]

/-- The exact regularity assumed by the parameter-rigidity theorem holds. -/
theorem continuous_real_restriction :
    Continuous (fun x : ℝ => algebraicSwitch (x : ℂ)) := by
  simpa only [algebraicSwitch_real] using Complex.continuous_ofReal

/-- Squaring preserves the algebraicity decision in both directions. -/
theorem algebraicSwitch_square (z : ℂ) :
    algebraicSwitch (z ^ 2) = algebraicSwitch z ^ 2 := by
  classical
  have hiff : IsAlgebraic ℚ (z ^ 2) ↔ IsAlgebraic ℚ z :=
    ⟨fun h => h.of_pow (by norm_num : 0 < (2 : ℕ)), fun h => h.pow 2⟩
  by_cases hz : IsAlgebraic ℚ z
  · simp [algebraicSwitch, hz, hiff.mpr hz]
  · have hn : ¬ IsAlgebraic ℚ (z ^ 2) := fun h => hz (hiff.mp h)
    simp [algebraicSwitch, hz, hn]

/-- Unit translation also preserves the algebraicity decision. -/
theorem algebraicSwitch_add_one (z : ℂ) :
    algebraicSwitch (z + 1) = algebraicSwitch z + 1 := by
  classical
  have hone : IsAlgebraic ℚ (1 : ℂ) := isAlgebraic_one
  have hiff : IsAlgebraic ℚ (z + 1) ↔ IsAlgebraic ℚ z := by
    constructor
    · intro h
      simpa only [add_sub_cancel_right] using h.sub hone
    · intro h
      exact h.add hone
  by_cases hz : IsAlgebraic ℚ z
  · simp [algebraicSwitch, hz, hiff.mpr hz]
  · have hn : ¬ IsAlgebraic ℚ (z + 1) := fun h => hz (hiff.mp h)
    simp [algebraicSwitch, hz, hn]

/-- Both actual quadratic generator equations hold at the parameter zero. -/
theorem algebraicSwitch_twin :
    (∀ z : ℂ, algebraicSwitch (z ^ 2 + 0) = algebraicSwitch z ^ 2 + 0) ∧
    (∀ z : ℂ, algebraicSwitch (z ^ 2 + 0 + 1) =
      algebraicSwitch z ^ 2 + 0 + 1) := by
  constructor
  · intro z
    simpa using algebraicSwitch_square z
  · intro z
    simpa only [add_zero] using
      (algebraicSwitch_add_one (z ^ 2)).trans
        (congrArg (fun w : ℂ => w + 1) (algebraicSwitch_square z))

private theorem imaginary_unit_algebraic : IsAlgebraic ℚ Complex.I := by
  have hone : IsAlgebraic ℚ (1 : ℂ) := isAlgebraic_one
  have hsq : IsAlgebraic ℚ (Complex.I ^ 2) := by
    simpa only [Complex.I_sq] using hone.neg
  exact hsq.of_pow (by norm_num : 0 < (2 : ℕ))

private theorem exists_non_algebraic_real :
    ∃ t : ℝ, ¬ IsAlgebraic ℚ t := by
  by_contra! h
  have heq : {t : ℝ | IsAlgebraic ℚ t} = Set.univ := by
    ext t
    simp [h t]
  have hc := Algebraic.countable ℚ ℝ
  rw [heq] at hc
  exact Set.not_countable_univ hc

/-- Global continuity fails despite the exact two generator identities
and identity restriction to the entire real axis. -/
theorem algebraicSwitch_not_continuous :
    ¬ Continuous algebraicSwitch := by
  intro hcont
  have hline :
      (fun x : ℝ => algebraicSwitch ((x : ℂ) + Complex.I)) =
      (fun x : ℝ => (x : ℂ) + Complex.I) := by
    apply Rat.denseRange_cast.equalizer
      (hcont.comp (Complex.continuous_ofReal.add continuous_const))
      (Complex.continuous_ofReal.add continuous_const)
    funext r
    have hr : IsAlgebraic ℚ (((r : ℝ) : ℂ) + Complex.I) := by
      simpa using (isAlgebraic_rat ℚ (A := ℂ) r).add imaginary_unit_algebraic
    exact algebraicSwitch_of_algebraic hr
  obtain ⟨t, ht⟩ := exists_non_algebraic_real
  have htc : ¬ IsAlgebraic ℚ (t : ℂ) := by
    intro h
    apply ht
    exact (isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
      (algebraMap ℝ ℂ).injective).mp h
  have htI : ¬ IsAlgebraic ℚ ((t : ℂ) + Complex.I) := by
    intro h
    apply htc
    simpa only [add_sub_cancel_right] using h.sub imaginary_unit_algebraic
  have hstar : star ((t : ℂ) + Complex.I) = (t : ℂ) + Complex.I := by
    simpa only [algebraicSwitch_of_not_algebraic htI] using congrFun hline t
  have hbad : (-1 : ℝ) = 1 := by
    simpa using congrArg Complex.im hstar
  norm_num at hbad

/-- A concrete map witnesses that real-axis continuity in the two
quadratic equations cannot be replaced by an implicit global continuity
assumption. -/
theorem exists_discontinuous_twin :
    ∃ h : ℂ → ℂ,
      Continuous (fun x : ℝ => h (x : ℂ)) ∧
      (∀ z : ℂ, h (z ^ 2 + 0) = h z ^ 2 + 0) ∧
      (∀ z : ℂ, h (z ^ 2 + 0 + 1) = h z ^ 2 + 0 + 1) ∧
      ¬ Continuous h := by
  exact ⟨algebraicSwitch, continuous_real_restriction,
    algebraicSwitch_twin.1, algebraicSwitch_twin.2,
    algebraicSwitch_not_continuous⟩

end

end QuadraticTwinDiscontinuous
