import ActualPairableWaves
import SlitParametricLength
import SlitRectangleLowerEnergy
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Arbitrary-density lower bound for the actual pairable family

The physical inverse extends continuously to both real ports with a
continuous velocity.  Weighted Hausdorff length of each complete glued
leaf is therefore bounded by its two inverse-horizontal integrals.  The
actual conformal Jacobian and the reflected rectangle energy inequality
then apply to every measurable extended density, without a finiteness or
rectifiability assumption on that density.
-/

namespace ActualPairableLeafLength

open Set Filter Function MeasureTheory Measure MarkedSlitTransport
open NearTwoTip
open SlitCubicRectangle SlitCubicClosedChart SlitCubicLowerEnergy
open ActualPairableClosedChart
open scoped Topology ENNReal

noncomputable section

variable {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)

def segment (y x : ℝ) : ℂ := closedInverse hp hc (point x y)

def velocity (y x : ℝ) : ℂ := closedVelocity hp hc (point x y)

def closedSliceLength (ρ : ℂ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo 0 (width hp hc),
    (ρ (segment hp hc y x) + ρ ((starRingEnd ℂ) (segment hp hc y x))) *
      ENNReal.ofReal ‖velocity hp hc y x‖

private theorem point_mem_band {x y : ℝ} (hx : x ∈ Icc 0 (width hp hc))
    (hy : y ∈ Ioo (-height hp hc) 0) :
    point x y ∈ closedHorizontalBand (width hp hc) (height hp hc) := by
  simpa [point,closedHorizontalBand] using And.intro hx.1 (And.intro hx.2 hy)

private theorem point_mem_rectangle {x y : ℝ} (hx : x ∈ Ioo 0 (width hp hc))
    (hy : y ∈ Ioo (-height hp hc) 0) :
    point x y ∈ openRectangle (width hp hc) (height hp hc) := by
  simpa [point,openRectangle] using And.intro hx.1 (And.intro hx.2 hy)

theorem segment_continuousOn {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0) :
    ContinuousOn (segment hp hc y) (Icc 0 (width hp hc)) := by
  have hpoint : Continuous (fun x : ℝ => point x y) := by unfold point; fun_prop
  exact (closedInverse_continuousOn hp hc).comp hpoint.continuousOn
    (fun _ hx => point_mem_band hp hc hx hy)

theorem velocity_continuousOn {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0) :
    ContinuousOn (velocity hp hc y) (Icc 0 (width hp hc)) := by
  have hpoint : Continuous (fun x : ℝ => point x y) := by unfold point; fun_prop
  exact (closedVelocity_continuousOn hp hc).comp hpoint.continuousOn
    (fun _ hx => point_mem_band hp hc hx hy)

theorem segment_hasDerivAt {x y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0)
    (hx : x ∈ Ioo 0 (width hp hc)) :
    HasDerivAt (segment hp hc y) (velocity hp hc y x) x := by
  have hd := closedInverse_hasDerivAt hp hc (point_mem_rectangle hp hc hx hy)
  have hh := hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ)*Complex.I))
  have hr := hh.comp_ofReal
  change HasDerivAt (fun t : ℝ => closedInverse hp hc ((t : ℂ)+(y : ℂ)*Complex.I)) _ x
  simpa only [point,segment,velocity,mul_one,Function.comp_def,id_eq] using! hr

theorem segment_lineLength_le {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (segment hp hc y '' Icc 0 (width hp hc)) ≤
      ∫⁻ x in Icc 0 (width hp hc), ρ (segment hp hc y x) *
        ENNReal.ofReal ‖velocity hp hc y x‖ :=
  SlitParametricLength.lintegral_image_le_lintegral_speed (width_pos hp hc)
    (segment_continuousOn hp hc hy) (velocity_continuousOn hp hc hy)
    (fun _ hx => segment_hasDerivAt hp hc hy hx) hρ

theorem reflected_segment_lineLength_le {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ
      ((fun x => (starRingEnd ℂ) (segment hp hc y x)) '' Icc 0 (width hp hc)) ≤
      ∫⁻ x in Icc 0 (width hp hc), ρ ((starRingEnd ℂ) (segment hp hc y x)) *
        ENNReal.ofReal ‖velocity hp hc y x‖ := by
  have h := SlitParametricLength.lintegral_image_le_lintegral_speed (width_pos hp hc)
    (Complex.continuous_conj.comp_continuousOn (segment_continuousOn hp hc hy))
    (Complex.continuous_conj.comp_continuousOn (velocity_continuousOn hp hc hy))
    (fun t ht => (segment_hasDerivAt hp hc hy ht).star) hρ
  simpa only [Function.comp_def,starRingEnd_apply,norm_star,SlitWaveModulus.lineLength] using h

theorem segments_lineLength_le_closedSliceLength {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ
      ((segment hp hc y '' Icc 0 (width hp hc)) ∪
        ((fun x => (starRingEnd ℂ) (segment hp hc y x)) '' Icc 0 (width hp hc))) ≤
      closedSliceLength hp hc ρ y := by
  let f := segment hp hc y
  let v := velocity hp hc y
  have hm : AEMeasurable (fun x => ρ (f x) * ENNReal.ofReal ‖v x‖)
      (volume.restrict (Icc 0 (width hp hc))) :=
    (hρ.comp_aemeasurable ((segment_continuousOn hp hc hy).aemeasurable
      measurableSet_Icc)).mul ((ENNReal.continuous_ofReal.comp_continuousOn
      (velocity_continuousOn hp hc hy).norm).aemeasurable measurableSet_Icc)
  calc
    _ ≤ SlitWaveModulus.lineLength ρ (f '' Icc 0 (width hp hc)) +
        SlitWaveModulus.lineLength ρ ((fun x => (starRingEnd ℂ) (f x)) ''
          Icc 0 (width hp hc)) := lintegral_union_le _ _ _
    _ ≤ (∫⁻ x in Icc 0 (width hp hc), ρ (f x) * ENNReal.ofReal ‖v x‖) +
        ∫⁻ x in Icc 0 (width hp hc),
          ρ ((starRingEnd ℂ) (f x)) * ENNReal.ofReal ‖v x‖ :=
      add_le_add (segment_lineLength_le hp hc hy hρ) (reflected_segment_lineLength_le hp hc hy hρ)
    _ = ∫⁻ x in Icc 0 (width hp hc),
        (ρ (f x) + ρ ((starRingEnd ℂ) (f x))) * ENNReal.ofReal ‖v x‖ := by
      rw [← lintegral_add_left' hm]
      congr 1
      funext x
      exact (add_mul _ _ _).symm
    _ = closedSliceLength hp hc ρ y := setLIntegral_congr MeasureTheory.Ioo_ae_eq_Icc.symm

theorem closedSliceLength_eq_sliceLength {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0)
    (ρ : ℂ → ℝ≥0∞) : closedSliceLength hp hc ρ y =
      SlitRectangleLowerEnergy.sliceLength (inverseConformal hp hc) (width hp hc) ρ y := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hw := point_mem_rectangle hp hc hx hy
  simp only [segment,velocity,closedInverse_eq_inverseConformal hp hc hw,
    inverseConformal_derivative hp hc hw]

/-- Every complete physical leaf supplies its actual two-chart slice
condition, for every measurable extended density. -/
theorem curve_lineLength_le_sliceLength {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (trace (ActualPairableWaves.curve hp hc hy)) ≤
      SlitRectangleLowerEnergy.sliceLength (inverseConformal hp hc) (width hp hc) ρ y := by
  have hsub := ActualPairableWaves.trace_curve_subset_segments hp hc hy
  exact ((lintegral_mono_set hsub).trans
    (segments_lineLength_le_closedSliceLength hp hc hy hρ)).trans_eq
      (closedSliceLength_eq_sliceLength hp hc hy ρ)

theorem area_lower_of_admissible {ρ : ℂ → ℝ≥0∞}
    (hρ : SlitWaveModulus.Admissible (traces (ActualPairableWaves.family hp hc)) ρ) :
    ENNReal.ofReal (height hp hc / (2 * width hp hc)) ≤ SlitWaveModulus.area ρ := by
  apply SlitRectangleLowerEnergy.area_lower_of_chart_slices (inverseConformal hp hc)
    (height_pos hp hc) (width_pos hp hc) (inverseConformal_source hp hc)
    (inverseConformal_target_subset_upper hp hc) hρ.1
  intro y hy
  exact (hρ.2 _ ⟨ActualPairableWaves.curve hp hc hy,
    ActualPairableWaves.curve_mem_family hp hc hy,rfl⟩).trans
      (curve_lineLength_le_sliceLength hp hc hy hρ.1)

/-- A matching lower bound for the actual constructed pairable family.
The infimum ranges over all admissible measurable densities. -/
theorem family_modulus_lower :
    ENNReal.ofReal (height hp hc / (2 * width hp hc)) ≤
      SlitWaveModulus.modulus (traces (ActualPairableWaves.family hp hc)) := by
  apply le_iInf₂
  intro ρ hρ
  exact area_lower_of_admissible hp hc hρ

end
end ActualPairableLeafLength
