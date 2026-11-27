import CollarExtremalLength
import CollarCapacityLower
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Exact arclength of the horizontal crossing segments

The metric length is that of the complete rectifiable-curve definition,
not an assumed line-integral surrogate. Its natural parameter is computed
exactly before applying translation invariance of Lebesgue measure.
-/

namespace CollarStraightLength

open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
open CollarExtremalLength CollarCapacityLower

noncomputable section

private theorem straight_lipschitz (y a b : ℝ) :
    LipschitzWith ⟨|b-a|, abs_nonneg _⟩
      (fun t : ℝ => horizontal y (a+(b-a)*t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [horizontal, dist_eq_norm, add_sub_add_right_eq_sub,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have heq : a+(b-a)*s-(a+(b-a)*t) = (b-a)*(s-t) := by ring
  rw [heq, abs_mul]
  exact le_rfl

/-- The full straight segment, including either orientation and the
degenerate case. Positive orientation is required only by its length
formula below. -/
def straightCurve (y a b : ℝ) : RectifiableCurve where
  toFun t := horizontal y (a+(b-a)*t)
  continuous := (straight_lipschitz y a b).continuous.continuousOn
  finite := by
    have h := (straight_lipschitz y a b).locallyBoundedVariationOn (Icc 0 1)
      0 1 (by norm_num) (by norm_num)
    simpa using h

theorem straightCurve_apply (y a b t : ℝ) :
    straightCurve y a b t = horizontal y (a+(b-a)*t) := rfl

private theorem horizontal_isometry (y : ℝ) : Isometry (horizontal y) := by
  apply Isometry.of_dist_eq
  intro s t
  simp [horizontal, dist_eq_norm, ← Complex.ofReal_sub]

private theorem horizontal_variation (y : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    eVariationOn (horizontal y ∘ f) S = eVariationOn f S := by
  simp only [eVariationOn, Function.comp_apply, (horizontal_isometry y).edist_eq]

private theorem real_monotone_variation {f : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t) (hf : MonotoneOn f (Icc s t)) :
    eVariationOn f (Icc s t) = ENNReal.ofReal (f t-f s) := by
  apply le_antisymm
  · have h := hf.eVariationOn_le (a := s) (b := t) ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩
    rw [Set.inter_self] at h
    exact h
  · have h := eVariationOn.edist_le f (by exact ⟨hst, le_rfl⟩ : t ∈ Icc s t)
      (by exact ⟨le_rfl, hst⟩ : s ∈ Icc s t)
    simpa only [edist_dist, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hf ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst))] using h

theorem straight_variation {y a b t : ℝ} (hab : a < b) (ht : t ∈ Icc (0 : ℝ) 1) :
    variationOnFromTo (straightCurve y a b).toFun (Icc 0 1) 0 t = (b-a)*t := by
  rw [variationOnFromTo.eq_of_le _ _ ht.1, Icc_inter_Icc,
    max_self, min_eq_right ht.2]
  change (eVariationOn (horizontal y ∘ (fun s : ℝ => a+(b-a)*s)) (Icc 0 t)).toReal = _
  rw [horizontal_variation, real_monotone_variation ht.1]
  · simp only [mul_zero, add_zero, add_sub_cancel_left]
    exact ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr hab.le) ht.1)
  · intro x hx z hz hxz
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxz (sub_nonneg.mpr hab.le))

theorem straightCurve_length {y a b : ℝ} (hab : a < b) :
    curveLength (straightCurve y a b) = b-a := by
  have h := straight_variation (y := y) (a := a) (b := b) hab
    (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa [curveLength, variationOnFromTo.eq_of_le] using h

/-- Exact unit-speed parameter, including both endpoints. -/
theorem straightCurve_arcParameter {y a b s : ℝ} (hab : a < b)
    (hs : s ∈ Icc (0 : ℝ) (b-a)) :
    arcParameter (straightCurve y a b) s = horizontal y (a+s) := by
  have hba : 0 < b-a := sub_pos.mpr hab
  have ht : s/(b-a) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hs.1 hba.le
    · exact (div_le_one hba).mpr hs.2
  have hv := straight_variation (y := y) (a := a) (b := b) hab ht
  have heq : (b-a)*(s/(b-a)) = s := by field_simp
  rw [heq] at hv
  have h := edist_naturalParameterization_eq_zero
    (straightCurve y a b).finite.locallyBoundedVariationOn
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht
  rw [hv] at h
  change edist (arcParameter (straightCurve y a b) s)
    (horizontal y (a+(b-a)*(s/(b-a)))) = 0 at h
  rw [heq] at h
  exact edist_eq_zero.mp h

/-- Every measurable conformal density has exactly its horizontal
Lebesgue line integral on this actual rectifiable segment. -/
theorem metricLength_straightCurve {y a b : ℝ} (hab : a < b)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    metricLength ρ (straightCurve y a b) =
      ∫⁻ x in Icc a b, ρ (horizontal y x) := by
  rw [metricLength, straightCurve_length hab]
  calc
    (∫⁻ s in Icc 0 (b-a), ρ (arcParameter (straightCurve y a b) s)) =
        ∫⁻ s in Icc 0 (b-a), ρ (horizontal y (a+s)) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s hs
      exact congrArg ρ (straightCurve_arcParameter (y := y) hab hs)
    _ = _ := by
      have hpre : (fun s : ℝ => a+s) ⁻¹' Icc a b = Icc 0 (b-a) := by
        ext s
        simp only [mem_preimage, mem_Icc]
        constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      have h := (measurePreserving_add_left (volume : Measure ℝ) a).setLIntegral_comp_preimage
        (s := Icc a b) measurableSet_Icc
        (hρ.comp (horizontal_lipschitz y).continuous.measurable)
      rwa [hpre] at h

end
end CollarStraightLength
