import ActualChildParameter
import ActualChildRate
import ActualChildPositive

/-!
# The child limit for the archive's uniquely selected signed chart

This endpoint assembles the proved chart identification, complete physical
source, exact orbit marks, positive geometric width, and effective limit.
The selected parameter is the root of the archive's literal chart, whose
equivalence with the quantitative actual-tip predicate is proved in
`ActualChildParameter`. No external ideal-boundary equivalence is asserted.
-/

namespace SelectedChildLimit

open Set Filter
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter
open ActualChildParameter ActualChildSupremum ActualChildPositive
open scoped Topology ENNReal

noncomputable section

def limitingParameter : ℝ := exists_unique_limiting_parameter.exists.choose

theorem limitingParameter_spec :
    limitingParameter ∈ parameterInterval ∧ relation limitingParameter = 0 :=
  exists_unique_limiting_parameter.exists.choose_spec

/-- The full concrete geometric child optimum on the uniquely selected
physical source, with its literal six endpoints. -/
def selectedChildWidth (p : ℕ) (hp : 17 ≤ p) : ℝ≥0∞ :=
  physicalChildWidth hp (canonicalParameter_actual p hp)
    limitingParameter_spec.1 limitingParameter_spec.2

def limitingWidth : ℝ≥0∞ :=
  limitingChildWidth limitingParameter limitingParameter_spec.1

/-- Every root admitted by the source's signed chart gives exactly this
same physical extremal problem. This uses the proved converse chart bridge. -/
theorem selectedChildWidth_eq_of_archived {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ArchivedSelectedTip p c) :
    selectedChildWidth p hp =
      physicalChildWidth hp ((archivedSelectedTip_iff_actualTip hp).mp hc)
        limitingParameter_spec.1 limitingParameter_spec.2 := by
  have he : c = canonicalParameter p hp :=
    (actualTip_iff_eq_canonicalParameter hp).mp
      ((archivedSelectedTip_iff_actualTip hp).mp hc)
  subst c
  rfl

theorem selectedChildWidth_lower (p : ℕ) (hp : 17 ≤ p) :
    ENNReal.ofReal (1/(3*Real.pi)) ≤ selectedChildWidth p hp :=
  physicalChildWidth_lower hp (canonicalParameter_actual p hp)
    limitingParameter_spec.1 limitingParameter_spec.2

theorem selectedChildWidth_ne_top (p : ℕ) (hp : 17 ≤ p) :
    selectedChildWidth p hp ≠ ⊤ :=
  physicalChildWidth_ne_top hp (canonicalParameter_actual p hp)
    limitingParameter_spec.1 limitingParameter_spec.2

theorem limitingWidth_pos : 0 < limitingWidth :=
  limitingChildWidth_pos limitingParameter_spec.1

theorem limitingWidth_ne_top : limitingWidth ≠ ⊤ :=
  limitingChildWidth_ne_top limitingParameter limitingParameter_spec.1

theorem selected_child_real_limit :
    Tendsto (fun n : ℕ => (selectedChildWidth (n+17) (by omega)).toReal)
      atTop (𝓝 limitingWidth.toReal) :=
  physical_child_optimum_real_converges
    limitingParameter_spec.1 limitingParameter_spec.2
    (fun n => canonicalParameter (n+17) (by omega))
    (fun n => canonicalParameter_actual (n+17) (by omega))

/-- A period-only error certificate for every parameter of the literal
archive chart, expressed using the unique physical selected width. -/
theorem selected_child_real_error (p : ℕ) (hp : 30 ≤ p) :
    |(selectedChildWidth p (by omega)).toReal - limitingWidth.toReal| ≤
      1600*(6*3906*23646*scale p)*limitingWidth.toReal +
        3*Real.pi/((p/2-8 : ℕ) : ℝ) :=
  ActualChildRate.physical_child_real_error hp
    (canonicalParameter_actual p (by omega))
    limitingParameter_spec.1 limitingParameter_spec.2

/-- Compact exhaustion concerns the source component belonging to the
archive's own selected parameter at each period. -/
theorem selected_source_exhaustion {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n : ℕ in atTop, K ⊆
      ActualChildSource.normalizedSource
        (canonicalParameter (n+17) (by omega)) (n+17) :=
  ActualChildSource.eventually_compact_subset
    (fun n => canonicalParameter (n+17) (by omega))
    (fun n => canonicalParameter_actual (n+17) (by omega)) hK

end
end SelectedChildLimit
