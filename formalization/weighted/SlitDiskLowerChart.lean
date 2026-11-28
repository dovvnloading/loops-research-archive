import SlitDiskCayley
import SlitRectangleLowerEnergy

/-!
# The actual inverse rectangle chart in a finite disk

Composing the inverse cubic integral with the explicit inverse Cayley map
gives the required analytic chart.  Its source and target and its derivative
are proved for these actual functions.
-/

namespace SlitDiskLowerChart

open Set MeasureTheory SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
  SlitCubicRectangle SlitCubicSurjective
open scoped ENNReal

noncomputable section

/-- The composed inverse, with its ordinary complex chain-rule derivative. -/
def inverseConformal {R a b c : ℝ} (hR : 0 < R) (hab : a < b) (hbc : b < c) :
    CrestConformalModulus.ConformalChart where
  homeomorph := (SlitCubicLowerEnergy.inverseConformal hab hbc).homeomorph.trans
    (SlitDiskCayley.conformalChart hR).homeomorph.symm
  derivative := fun w =>
    SlitDiskCayley.inverseDerivative R ((rectangleChart hab hbc).symm w) *
      SlitCubicLowerEnergy.inverseVelocity hab hbc w
  hasDeriv := by
    intro w hw
    exact (SlitDiskCayley.inverse_hasDerivAt hR hw.2).comp w
      ((SlitCubicLowerEnergy.inverseConformal hab hbc).hasDeriv w hw.1)
  derivative_continuous := by
    apply ContinuousOn.mul
    · have hc : ContinuousOn (SlitDiskCayley.inverseDerivative R) SlitDiskCayley.slit :=
        fun z hz => (SlitDiskCayley.inverseDerivative_continuousAt hR hz).continuousWithinAt
      exact hc.comp
        ((SlitCubicLowerEnergy.inverseConformal hab hbc).homeomorph.continuousOn.mono
          inter_subset_left) (fun w hw => hw.2)
    · exact (SlitCubicLowerEnergy.inverseConformal hab hbc).derivative_continuous.mono
        inter_subset_left
  derivative_ne_zero := fun w hw => mul_ne_zero
    (SlitDiskCayley.inverseDerivative_ne_zero hR hw.2)
    ((SlitCubicLowerEnergy.inverseConformal hab hbc).derivative_ne_zero w hw.1)

@[simp] theorem inverseConformal_source {R a b c : ℝ} (hR : 0 < R)
    (hab : a < b) (hbc : b < c) :
    (inverseConformal hR hab hbc).homeomorph.source =
      openRectangle (period a b c) (height a b c) := by
  change openRectangle (period a b c) (height a b c) ∩
    (rectangleChart hab hbc).symm ⁻¹' SlitDiskCayley.slit = _
  apply inter_eq_left.mpr
  intro w hw
  have hz : (rectangleChart hab hbc).symm w ∈ upper := (rectangleChart hab hbc).map_target hw
  exact Or.inr (show 0 < ((rectangleChart hab hbc).symm w).im from hz).ne'

@[simp] theorem inverseConformal_target {R a b c : ℝ} (hR : 0 < R)
    (hab : a < b) (hbc : b < c) :
    (inverseConformal hR hab hbc).homeomorph.target = SlitDiskCayley.disk R ∩ upper := by
  ext z
  change (z ∈ SlitDiskCayley.disk R ∧ SlitDiskCayley.map R z ∈ upper) ↔
    z ∈ SlitDiskCayley.disk R ∧ z ∈ upper
  constructor
  · intro hz
    exact ⟨hz.1, (SlitDiskCayley.map_im_pos_iff hR hz.1).mp hz.2⟩
  · intro hz
    exact ⟨hz.1, (SlitDiskCayley.map_im_pos_iff hR hz.1).mpr hz.2⟩

theorem inverseConformal_target_subset_upper {R a b c : ℝ} (hR : 0 < R)
    (hab : a < b) (hbc : b < c) :
    (inverseConformal hR hab hbc).homeomorph.target ⊆ upper := by
  rw [inverseConformal_target]
  exact inter_subset_right

@[simp] theorem inverseConformal_apply {R a b c : ℝ} (hR : 0 < R)
    (hab : a < b) (hbc : b < c) (w : ℂ) :
    (inverseConformal hR hab hbc).homeomorph w =
      SlitDiskCayley.inverse R ((rectangleChart hab hbc).symm w) := rfl

@[simp] theorem inverseConformal_symm_apply {R a b c : ℝ} (hR : 0 < R)
    (hab : a < b) (hbc : b < c) (z : ℂ) :
    (inverseConformal hR hab hbc).homeomorph.symm z =
      tail a b c (SlitDiskCayley.map R z) := rfl

@[simp] theorem inverseConformal_derivative {R a b c : ℝ} (hR : 0 < R)
    (hab : a < b) (hbc : b < c) (w : ℂ) :
    (inverseConformal hR hab hbc).derivative w =
      SlitDiskCayley.inverseDerivative R ((rectangleChart hab hbc).symm w) *
        SlitCubicLowerEnergy.inverseVelocity hab hbc w := rfl

theorem area_lower_of_inverse_slices {R a b c : ℝ} (hR : 0 < R)
    (hab : a < b) (hbc : b < c) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    (hlen : ∀ y ∈ Ioo (-height a b c) 0,
      1 ≤ SlitRectangleLowerEnergy.sliceLength (inverseConformal hR hab hbc)
        (period a b c) ρ y) :
    ENNReal.ofReal (height a b c / (2*period a b c)) ≤ SlitWaveModulus.area ρ :=
  SlitRectangleLowerEnergy.area_lower_of_chart_slices (inverseConformal hR hab hbc)
    (height_pos hab hbc) (period_pos hab hbc) (inverseConformal_source hR hab hbc)
    (inverseConformal_target_subset_upper hR hab hbc) hρ hlen

end
end SlitDiskLowerChart
