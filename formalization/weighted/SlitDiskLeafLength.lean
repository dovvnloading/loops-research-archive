import SlitDiskWaves
import SlitCubicLeafLength
import SlitDiskLowerChart

/-!
# Weighted geometric length of the actual finite-disk leaves

The inverse Cayley derivative and cubic inverse derivative give a
continuous velocity on each closed horizontal segment. The Hausdorff
length estimate therefore applies at every height, including both real
edge endpoints of each physical leaf.
-/

namespace SlitDiskLeafLength

open Set Filter Function MeasureTheory Measure MarkedSlitTransport
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open SlitCubicRectangle SlitCubicSurjective SlitCubicClosedChart SlitCubicLowerEnergy
open SlitDiskMarking
open scoped Topology ENNReal
noncomputable section

def segment (R a b c y : ℝ) (x : ℝ) : ℂ :=
  SlitDiskCayley.inverse R (SlitCubicLeafLength.segment a b c y x)

def velocity (R a b c y : ℝ) (x : ℝ) : ℂ :=
  SlitDiskCayley.inverseDerivative R (SlitCubicLeafLength.segment a b c y x) *
    SlitCubicLeafLength.velocity a b c y x

def composedSliceLength (R a b c : ℝ) (ρ : ℂ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo 0 (period a b c),
    (ρ (segment R a b c y x) + ρ ((starRingEnd ℂ) (segment R a b c y x))) *
      ENNReal.ofReal ‖velocity R a b c y x‖

variable {R : ℝ} (hR : 0 < R) (M : Marking)
  (hleft : -R < M.left) (hright : M.right < R)
local notation "N" => transformedMarking hR M hleft hright

theorem segment_continuousOn {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) :
    ContinuousOn (segment R (N).left (N).first (N).second y)
      (Icc 0 (period (N).left (N).first (N).second)) := by
  have hp : Continuous (fun x : ℝ => point x y) := by unfold point; fun_prop
  exact (SlitDiskWaves.inverse_closedInverse_continuousOn hR M hleft hright).comp
    hp.continuousOn (fun _ hx => SlitCubicLeafLength.point_mem_band hx hy)

theorem velocity_continuousOn {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) :
    ContinuousOn (velocity R (N).left (N).first (N).second y)
      (Icc 0 (period (N).left (N).first (N).second)) := by
  have hG := SlitCubicLeafLength.segment_continuousOn (N).left_lt_first (N).first_lt_second hy
  have hJ : ContinuousOn (fun x => SlitDiskCayley.inverseDerivative R
      (SlitCubicLeafLength.segment (N).left (N).first (N).second y x))
      (Icc 0 (period (N).left (N).first (N).second)) := by
    intro x hx
    have hd : ContinuousAt (SlitDiskCayley.inverseDerivative R)
        (SlitCubicLeafLength.segment (N).left (N).first (N).second y x) :=
      SlitDiskCayley.inverseDerivative_continuousAt hR
      (SlitDiskWaves.closedInverse_mem_slit hR M hleft hright
        (SlitCubicLeafLength.point_mem_band hx hy))
    exact hd.comp_continuousWithinAt (hG x hx)
  exact hJ.mul (SlitCubicLeafLength.velocity_continuousOn (N).left_lt_first (N).first_lt_second hy)

theorem segment_hasDerivAt {x y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    (hx : x ∈ Ioo 0 (period (N).left (N).first (N).second)) :
    HasDerivAt (segment R (N).left (N).first (N).second y)
      (velocity R (N).left (N).first (N).second y x) x := by
  have hJ := (SlitDiskCayley.inverse_hasDerivAt hR
    (SlitDiskWaves.closedInverse_mem_slit hR M hleft hright
      (SlitCubicLeafLength.point_mem_band (Ioo_subset_Icc_self hx) hy))).complexToReal_fderiv
  have hG := SlitCubicLeafLength.segment_hasDerivAt (N).left_lt_first (N).first_lt_second hy hx
  simpa only [Function.comp_def, _root_.smul_apply, one_apply_eq_self,
    smul_eq_mul, segment, velocity, SlitCubicLeafLength.segment] using! hJ.comp_hasDerivAt x hG

theorem segment_lineLength_le {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ
      (segment R (N).left (N).first (N).second y '' Icc 0 (period (N).left (N).first (N).second)) ≤
      ∫⁻ x in Icc 0 (period (N).left (N).first (N).second),
        ρ (segment R (N).left (N).first (N).second y x) *
          ENNReal.ofReal ‖velocity R (N).left (N).first (N).second y x‖ :=
  SlitParametricLength.lintegral_image_le_lintegral_speed (period_pos (N).left_lt_first (N).first_lt_second)
    (segment_continuousOn hR M hleft hright hy) (velocity_continuousOn hR M hleft hright hy)
    (fun _ hx => segment_hasDerivAt hR M hleft hright hy hx) hρ

theorem reflected_segment_lineLength_le {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ
      ((fun x => (starRingEnd ℂ) (segment R (N).left (N).first (N).second y x)) ''
        Icc 0 (period (N).left (N).first (N).second)) ≤
      ∫⁻ x in Icc 0 (period (N).left (N).first (N).second),
        ρ ((starRingEnd ℂ) (segment R (N).left (N).first (N).second y x)) *
          ENNReal.ofReal ‖velocity R (N).left (N).first (N).second y x‖ := by
  have h := SlitParametricLength.lintegral_image_le_lintegral_speed
    (period_pos (N).left_lt_first (N).first_lt_second)
    (Complex.continuous_conj.comp_continuousOn (segment_continuousOn hR M hleft hright hy))
    (Complex.continuous_conj.comp_continuousOn (velocity_continuousOn hR M hleft hright hy))
    (fun t ht => (segment_hasDerivAt hR M hleft hright hy ht).star) hρ
  simpa only [Function.comp_def, starRingEnd_apply, norm_star, SlitWaveModulus.lineLength] using h

theorem segments_lineLength_le_composedSliceLength {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ
      ((segment R (N).left (N).first (N).second y '' Icc 0 (period (N).left (N).first (N).second)) ∪
        ((fun x => (starRingEnd ℂ) (segment R (N).left (N).first (N).second y x)) ''
          Icc 0 (period (N).left (N).first (N).second))) ≤
      composedSliceLength R (N).left (N).first (N).second ρ y := by
  let f := segment R (N).left (N).first (N).second y
  let v := velocity R (N).left (N).first (N).second y
  have hm : AEMeasurable (fun x => ρ (f x) * ENNReal.ofReal ‖v x‖)
      (volume.restrict (Icc 0 (period (N).left (N).first (N).second))) :=
    (hρ.comp_aemeasurable ((segment_continuousOn hR M hleft hright hy).aemeasurable
      measurableSet_Icc)).mul ((ENNReal.continuous_ofReal.comp_continuousOn
      (velocity_continuousOn hR M hleft hright hy).norm).aemeasurable measurableSet_Icc)
  calc
    _ ≤ SlitWaveModulus.lineLength ρ (f '' Icc 0 (period (N).left (N).first (N).second)) +
        SlitWaveModulus.lineLength ρ ((fun x => (starRingEnd ℂ) (f x)) ''
          Icc 0 (period (N).left (N).first (N).second)) := lintegral_union_le _ _ _
    _ ≤ (∫⁻ x in Icc 0 (period (N).left (N).first (N).second), ρ (f x) * ENNReal.ofReal ‖v x‖) +
        ∫⁻ x in Icc 0 (period (N).left (N).first (N).second),
          ρ ((starRingEnd ℂ) (f x)) * ENNReal.ofReal ‖v x‖ :=
      add_le_add (segment_lineLength_le hR M hleft hright hy hρ)
        (reflected_segment_lineLength_le hR M hleft hright hy hρ)
    _ = ∫⁻ x in Icc 0 (period (N).left (N).first (N).second),
        (ρ (f x) + ρ ((starRingEnd ℂ) (f x))) * ENNReal.ofReal ‖v x‖ := by
      rw [← lintegral_add_left' hm]
      congr 1
      funext x
      exact (add_mul _ _ _).symm
    _ = composedSliceLength R (N).left (N).first (N).second ρ y :=
      setLIntegral_congr MeasureTheory.Ioo_ae_eq_Icc.symm

/-- Weighted Hausdorff length of the actual finite-disk leaf is bounded
by its two explicit inverse-horizontal parameter integrals. -/
theorem curve_lineLength_le_composedSliceLength {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (trace (SlitDiskWaves.curve hR M hleft hright hy)) ≤
      composedSliceLength R (N).left (N).first (N).second ρ y := by
  have hsub := SlitDiskWaves.trace_curve_subset_conjugate_segments hR M hleft hright hy
  exact (lintegral_mono_set hsub).trans
    (segments_lineLength_le_composedSliceLength hR M hleft hright hy hρ)

theorem composedSliceLength_eq_inverseSliceLength {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) (ρ : ℂ → ℝ≥0∞) :
    composedSliceLength R (N).left (N).first (N).second ρ y =
      SlitRectangleLowerEnergy.sliceLength
        (SlitDiskLowerChart.inverseConformal hR (N).left_lt_first (N).first_lt_second)
        (period (N).left (N).first (N).second) ρ y := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  simp only [segment, velocity,
    SlitCubicLeafLength.segment_eq_rectangleChart_symm (N).left_lt_first (N).first_lt_second hy hx,
    SlitCubicLeafLength.velocity_eq_inverseVelocity (N).left_lt_first (N).first_lt_second hy hx,
    SlitDiskLowerChart.inverseConformal_apply, SlitDiskLowerChart.inverseConformal_derivative]

/-- The physical finite-disk leaf supplies the exact slice condition for
the Jacobian and two-copy Cauchy--Schwarz lower bound. -/
theorem curve_lineLength_le_inverseSliceLength {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (trace (SlitDiskWaves.curve hR M hleft hright hy)) ≤
      SlitRectangleLowerEnergy.sliceLength
        (SlitDiskLowerChart.inverseConformal hR (N).left_lt_first (N).first_lt_second)
        (period (N).left (N).first (N).second) ρ y :=
  (curve_lineLength_le_composedSliceLength hR M hleft hright hy hρ).trans_eq
    (composedSliceLength_eq_inverseSliceLength hR M hleft hright hy ρ)

end
end SlitDiskLeafLength
