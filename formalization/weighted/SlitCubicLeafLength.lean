import SlitCubicClosedChart
import SlitCubicLowerEnergy
import SlitCubicWaves
import SlitParametricLength
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Geometric length of the actual reflected inverse leaf

The continuous inverse extends along a full closed horizontal segment.
Its explicit continuous velocity controls weighted Hausdorff length,
including both edge endpoints. Reflection gives the second half of the
leaf, and the two parameter integrals are the actual inverse slice length.
-/

namespace SlitCubicLeafLength

open Set Filter Function MeasureTheory Measure
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open SlitCubicRectangle SlitCubicSurjective SlitCubicClosedChart SlitCubicLowerEnergy
open scoped Topology ENNReal
noncomputable section

def segment (a b c y : ℝ) (x : ℝ) : ℂ :=
  closedInverse a b c (point x y)

def velocity (a b c y : ℝ) (x : ℝ) : ℂ :=
  -(upperRoot a (segment a b c y x) * upperRoot b (segment a b c y x) *
    upperRoot c (segment a b c y x))

theorem point_mem_band {a b c x y : ℝ}
    (hx : x ∈ Icc 0 (period a b c)) (hy : y ∈ Ioo (-height a b c) 0) :
    point x y ∈ closedHorizontalBand (period a b c) (height a b c) := by
  simpa only [point, closedHorizontalBand, mem_setOf_eq, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add, mem_Ioo] using
      And.intro hx.1 (And.intro hx.2 hy)

theorem point_mem_rectangle {a b c x y : ℝ}
    (hx : x ∈ Ioo 0 (period a b c)) (hy : y ∈ Ioo (-height a b c) 0) :
    point x y ∈ openRectangle (period a b c) (height a b c) := by
  simpa only [point, openRectangle, mem_setOf_eq, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add, mem_Ioo] using
      And.intro hx.1 (And.intro hx.2 hy)

theorem segment_continuousOn {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    ContinuousOn (segment a b c y) (Icc 0 (period a b c)) := by
  have hp : Continuous (fun x : ℝ => point x y) := by unfold point; fun_prop
  exact (closedInverse_continuousOn hab hbc).comp hp.continuousOn
    (fun _ hx => point_mem_band hx hy)

theorem velocity_continuousOn {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    ContinuousOn (velocity a b c y) (Icc 0 (period a b c)) := by
  have hf := segment_continuousOn hab hbc hy
  exact (((upperRoot_continuous a).comp_continuousOn hf).mul
    ((upperRoot_continuous b).comp_continuousOn hf) |>.mul
    ((upperRoot_continuous c).comp_continuousOn hf)).neg

theorem segment_hasDerivAt {a b c x y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) (hx : x ∈ Ioo 0 (period a b c)) :
    HasDerivAt (segment a b c y) (velocity a b c y x) x := by
  have hd := closedInverse_hasDerivAt hab hbc (point_mem_rectangle hx hy)
  have hh := hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * Complex.I))
  have hr := hh.comp_ofReal
  change HasDerivAt (fun t : ℝ => closedInverse a b c ((t : ℂ) + (y : ℂ) * Complex.I)) _ x
  simpa only [point, segment, velocity, mul_one, Function.comp_def, id_eq] using hr

theorem segment_eq_rectangleChart_symm {a b c x y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) (hx : x ∈ Ioo 0 (period a b c)) :
    segment a b c y x = (rectangleChart hab hbc).symm (point x y) :=
  closedInverse_eq_rectangleChart_symm hab hbc (point_mem_rectangle hx hy)

theorem velocity_eq_inverseVelocity {a b c x y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) (hx : x ∈ Ioo 0 (period a b c)) :
    velocity a b c y x = inverseVelocity hab hbc (point x y) := by
  simp only [velocity, inverseVelocity, segment_eq_rectangleChart_symm hab hbc hy hx]

theorem segment_lineLength_le {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (segment a b c y '' Icc 0 (period a b c)) ≤
      ∫⁻ x in Icc 0 (period a b c), ρ (segment a b c y x) *
        ENNReal.ofReal ‖velocity a b c y x‖ :=
  SlitParametricLength.lintegral_image_le_lintegral_speed (period_pos hab hbc)
    (segment_continuousOn hab hbc hy) (velocity_continuousOn hab hbc hy)
    (fun _ hx => segment_hasDerivAt hab hbc hy hx) hρ

theorem reflected_segment_lineLength_le {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ
      ((fun x => (starRingEnd ℂ) (segment a b c y x)) '' Icc 0 (period a b c)) ≤
      ∫⁻ x in Icc 0 (period a b c), ρ ((starRingEnd ℂ) (segment a b c y x)) *
        ENNReal.ofReal ‖velocity a b c y x‖ := by
  have h := SlitParametricLength.lintegral_image_le_lintegral_speed (period_pos hab hbc)
    (Complex.continuous_conj.comp_continuousOn (segment_continuousOn hab hbc hy))
    (Complex.continuous_conj.comp_continuousOn (velocity_continuousOn hab hbc hy))
    (fun t ht => (segment_hasDerivAt hab hbc hy ht).star) hρ
  simpa only [Function.comp_def, starRingEnd_apply, norm_star, SlitWaveModulus.lineLength] using h

/-- The two full geometric inverse segments have total weighted length
at most the inverse rectangle slice integral. -/
theorem segments_lineLength_le_inverseSliceLength {a b c y : ℝ}
    (hab : a < b) (hbc : b < c) (hy : y ∈ Ioo (-height a b c) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ
      ((segment a b c y '' Icc 0 (period a b c)) ∪
        ((fun x => (starRingEnd ℂ) (segment a b c y x)) '' Icc 0 (period a b c))) ≤
      inverseSliceLength hab hbc ρ y := by
  have hm : AEMeasurable (fun x => ρ (segment a b c y x) *
      ENNReal.ofReal ‖velocity a b c y x‖) (volume.restrict (Icc 0 (period a b c))) :=
    (hρ.comp_aemeasurable ((segment_continuousOn hab hbc hy).aemeasurable measurableSet_Icc)).mul
      ((ENNReal.continuous_ofReal.comp_continuousOn
        (velocity_continuousOn hab hbc hy).norm).aemeasurable measurableSet_Icc)
  calc
    _ ≤ SlitWaveModulus.lineLength ρ (segment a b c y '' Icc 0 (period a b c)) +
        SlitWaveModulus.lineLength ρ
          ((fun x => (starRingEnd ℂ) (segment a b c y x)) '' Icc 0 (period a b c)) :=
      lintegral_union_le _ _ _
    _ ≤ (∫⁻ x in Icc 0 (period a b c), ρ (segment a b c y x) *
        ENNReal.ofReal ‖velocity a b c y x‖) +
        ∫⁻ x in Icc 0 (period a b c), ρ ((starRingEnd ℂ) (segment a b c y x)) *
          ENNReal.ofReal ‖velocity a b c y x‖ :=
      add_le_add (segment_lineLength_le hab hbc hy hρ) (reflected_segment_lineLength_le hab hbc hy hρ)
    _ = ∫⁻ x in Icc 0 (period a b c),
        (ρ (segment a b c y x) + ρ ((starRingEnd ℂ) (segment a b c y x))) *
          ENNReal.ofReal ‖velocity a b c y x‖ := by
      rw [← lintegral_add_left' hm]
      congr 1
      funext x
      exact (add_mul _ _ _).symm
    _ = ∫⁻ x in Ioo 0 (period a b c),
        (ρ (segment a b c y x) + ρ ((starRingEnd ℂ) (segment a b c y x))) *
          ENNReal.ofReal ‖velocity a b c y x‖ :=
      setLIntegral_congr MeasureTheory.Ioo_ae_eq_Icc.symm
    _ = inverseSliceLength hab hbc ρ y := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [segment_eq_rectangleChart_symm hab hbc hy hx,
        velocity_eq_inverseVelocity hab hbc hy hx]

/-- Geometric length of the actual complete parent leaf is controlled by
the inverse rectangle slice, for every measurable extended density. -/
theorem curve_lineLength_le_inverseSliceLength {a b c y : ℝ}
    (hab : a < b) (hbc : b < c) (hy : y ∈ Ioo (-height a b c) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (MarkedSlitTransport.trace (SlitCubicWaves.curve hab hbc hy)) ≤
      inverseSliceLength hab hbc ρ y := by
  have hsub := SlitCubicWaves.trace_curve_subset_segments hab hbc hy
  exact (lintegral_mono_set hsub).trans
    (segments_lineLength_le_inverseSliceLength hab hbc hy hρ)

end
end SlitCubicLeafLength
