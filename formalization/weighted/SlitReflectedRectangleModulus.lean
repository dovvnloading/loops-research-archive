import SlitReflectedRectangles
import SlitParametricLength
import SlitRectangleLowerEnergy
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # All-density modulus lower bound for a reflected analytic rectangle -/

namespace SlitReflectedRectangleModulus

open Set Filter Function MeasureTheory Measure MarkedSlitTransport
open SlitCubicRectangle SlitCubicClosedChart SlitCubicLowerEnergy
open scoped Topology ENNReal
noncomputable section

structure Data (B A : ℝ) extends SlitReflectedRectangles.InverseData B A where
  chart : CrestConformalModulus.ConformalChart
  chart_source : chart.homeomorph.source = openRectangle B A
  chart_target : chart.homeomorph.target ⊆ SlitCubicCalibration.upper
  velocity : ℂ → ℂ
  velocity_continuous : ContinuousOn velocity (closedHorizontalBand B A)
  hasDeriv : ∀ z ∈ openRectangle B A, HasDerivAt toFun (velocity z) z
  interior_eq : ∀ z ∈ openRectangle B A, toFun z = chart.homeomorph z
  derivative_eq : ∀ z ∈ openRectangle B A, chart.derivative z = velocity z

variable {B A : ℝ} (D : Data B A)

def segment (y x : ℝ) : ℂ := D.toFun (point x y)
def velocity (y x : ℝ) : ℂ := D.velocity (point x y)
def closedSliceLength (ρ : ℂ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo 0 B, (ρ (segment D y x) + ρ ((starRingEnd ℂ) (segment D y x))) *
    ENNReal.ofReal ‖velocity D y x‖

private theorem point_mem_band {x y : ℝ} (hx : x ∈ Icc 0 B) (hy : y ∈ Ioo (-A) 0) :
    point x y ∈ closedHorizontalBand B A := by
  simpa [point,closedHorizontalBand] using And.intro hx.1 (And.intro hx.2 hy)

private theorem point_mem_rectangle {x y : ℝ} (hx : x ∈ Ioo 0 B) (hy : y ∈ Ioo (-A) 0) :
    point x y ∈ openRectangle B A := by
  simpa [point,openRectangle] using And.intro hx.1 (And.intro hx.2 hy)

theorem segment_continuousOn {y : ℝ} (hy : y ∈ Ioo (-A) 0) :
    ContinuousOn (segment D y) (Icc 0 B) := by
  have hp : Continuous (fun x : ℝ => point x y) := by unfold point; fun_prop
  exact D.continuous.comp hp.continuousOn (fun _ hx => point_mem_band hx hy)

theorem velocity_continuousOn {y : ℝ} (hy : y ∈ Ioo (-A) 0) :
    ContinuousOn (velocity D y) (Icc 0 B) := by
  have hp : Continuous (fun x : ℝ => point x y) := by unfold point; fun_prop
  exact D.velocity_continuous.comp hp.continuousOn (fun _ hx => point_mem_band hx hy)

theorem segment_hasDerivAt {x y : ℝ} (hy : y ∈ Ioo (-A) 0) (hx : x ∈ Ioo 0 B) :
    HasDerivAt (segment D y) (velocity D y x) x := by
  have hd := D.hasDeriv _ (point_mem_rectangle hx hy)
  have hh := hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ)*Complex.I))
  have hr := hh.comp_ofReal
  change HasDerivAt (fun t : ℝ => D.toFun ((t : ℂ)+(y : ℂ)*Complex.I)) _ x
  simpa only [point,segment,velocity,mul_one,Function.comp_def,id_eq] using! hr

theorem segment_lineLength_le {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (segment D y '' Icc 0 B) ≤
      ∫⁻ x in Icc 0 B, ρ (segment D y x)*ENNReal.ofReal ‖velocity D y x‖ :=
  SlitParametricLength.lintegral_image_le_lintegral_speed D.width_pos
    (segment_continuousOn D hy) (velocity_continuousOn D hy)
    (fun _ hx => segment_hasDerivAt D hy hx) hρ

theorem reflected_segment_lineLength_le {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ ((fun x => (starRingEnd ℂ) (segment D y x)) '' Icc 0 B) ≤
      ∫⁻ x in Icc 0 B, ρ ((starRingEnd ℂ) (segment D y x))*ENNReal.ofReal ‖velocity D y x‖ := by
  have h := SlitParametricLength.lintegral_image_le_lintegral_speed D.width_pos
    (Complex.continuous_conj.comp_continuousOn (segment_continuousOn D hy))
    (Complex.continuous_conj.comp_continuousOn (velocity_continuousOn D hy))
    (fun t ht => (segment_hasDerivAt D hy ht).star) hρ
  simpa only [Function.comp_def,starRingEnd_apply,norm_star,SlitWaveModulus.lineLength] using h

theorem segments_lineLength_le_closedSliceLength {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ
      ((segment D y '' Icc 0 B) ∪ ((fun x => (starRingEnd ℂ) (segment D y x)) '' Icc 0 B)) ≤
      closedSliceLength D ρ y := by
  let f := segment D y
  let v := velocity D y
  have hm : AEMeasurable (fun x => ρ (f x)*ENNReal.ofReal ‖v x‖) (volume.restrict (Icc 0 B)) :=
    (hρ.comp_aemeasurable ((segment_continuousOn D hy).aemeasurable measurableSet_Icc)).mul
      ((ENNReal.continuous_ofReal.comp_continuousOn (velocity_continuousOn D hy).norm).aemeasurable
        measurableSet_Icc)
  calc
    _ ≤ SlitWaveModulus.lineLength ρ (f '' Icc 0 B) +
        SlitWaveModulus.lineLength ρ ((fun x => (starRingEnd ℂ) (f x)) '' Icc 0 B) :=
      lintegral_union_le _ _ _
    _ ≤ (∫⁻ x in Icc 0 B, ρ (f x)*ENNReal.ofReal ‖v x‖) +
        ∫⁻ x in Icc 0 B, ρ ((starRingEnd ℂ) (f x))*ENNReal.ofReal ‖v x‖ :=
      add_le_add (segment_lineLength_le D hy hρ) (reflected_segment_lineLength_le D hy hρ)
    _ = ∫⁻ x in Icc 0 B, (ρ (f x)+ρ ((starRingEnd ℂ) (f x)))*ENNReal.ofReal ‖v x‖ := by
      rw [← lintegral_add_left' hm]
      congr 1
      funext x
      exact (add_mul _ _ _).symm
    _ = closedSliceLength D ρ y := setLIntegral_congr MeasureTheory.Ioo_ae_eq_Icc.symm

theorem closedSliceLength_eq_sliceLength {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    (ρ : ℂ → ℝ≥0∞) : closedSliceLength D ρ y =
      SlitRectangleLowerEnergy.sliceLength D.chart B ρ y := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hw := point_mem_rectangle hx hy
  simp only [segment,velocity,D.interior_eq _ hw,D.derivative_eq _ hw]

theorem curve_lineLength_le_sliceLength {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (trace (SlitReflectedRectangles.curve D.toInverseData hy)) ≤
      SlitRectangleLowerEnergy.sliceLength D.chart B ρ y := by
  have hsub := SlitReflectedRectangles.trace_curve_subset_segments D.toInverseData hy
  exact ((lintegral_mono_set hsub).trans
    (segments_lineLength_le_closedSliceLength D hy hρ)).trans_eq
      (closedSliceLength_eq_sliceLength D hy ρ)

theorem area_lower_of_admissible {ρ : ℂ → ℝ≥0∞}
    (hρ : SlitWaveModulus.Admissible (traces (SlitReflectedRectangles.family D.toInverseData)) ρ) :
    ENNReal.ofReal (A/(2*B)) ≤ SlitWaveModulus.area ρ := by
  apply SlitRectangleLowerEnergy.area_lower_of_chart_slices D.chart D.height_pos D.width_pos
    D.chart_source D.chart_target hρ.1
  intro y hy
  exact (hρ.2 _ ⟨SlitReflectedRectangles.curve D.toInverseData hy,⟨⟨y,hy⟩,rfl⟩,rfl⟩).trans
    (curve_lineLength_le_sliceLength D hy hρ.1)

theorem family_modulus_lower : ENNReal.ofReal (A/(2*B)) ≤
    SlitWaveModulus.modulus (traces (SlitReflectedRectangles.family D.toInverseData)) := by
  apply le_iInf₂
  intro ρ hρ
  exact area_lower_of_admissible D hρ

end
end SlitReflectedRectangleModulus
