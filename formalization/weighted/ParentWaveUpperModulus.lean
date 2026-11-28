import ParentWaveUpperLength
import ParentWaveHalfPlane
import CrestConformalModulus

/-!
# The exact physical upper metric for the complete canonical path family

Every continuous closed-upper path between the physical electrodes is
tested against the literal cubic differential.  The energy is computed
through the actual conformal chart and planar change of variables.
-/

namespace ParentWaveUpperModulus

open Set Complex Metric MeasureTheory Measure
open MarkedSlitTransport SlitWaveModulus ParentWaveElliptic
open ParentWaveHalfPlane ParentWaveUpperLength
open scoped ENNReal NNReal Topology

noncomputable section

theorem closure_upperHalfPlane :
    closure upperHalfPlane = {z : ℂ | 0 ≤ z.im} :=
  Complex.closure_setOf_lt_im 0

theorem volume_real_axis : volume {z : ℂ | z.im = 0} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton (0 : ℝ))).nullMeasurableSet
  have hp : Complex.measurableEquivRealProd ⁻¹' (univ ×ˢ {(0 : ℝ)}) =
      {z : ℂ | z.im = 0} := by ext z; simp
  rw [hp] at h
  simpa [Measure.volume_eq_prod,Measure.prod_prod] using h

theorem closure_upperHalfPlane_ae_eq :
    closure upperHalfPlane =ᵐ[volume] upperHalfPlane := by
  have haway : ∀ᵐ z : ℂ ∂volume, z ∉ {z : ℂ | z.im = 0} := by
    rw [ae_iff]
    simpa only [not_not,Set.setOf_mem_eq] using volume_real_axis
  filter_upwards [haway] with z hz
  rw [closure_upperHalfPlane]
  change (0 ≤ z.im) = (0 < z.im)
  apply propext
  constructor
  · intro h
    exact lt_of_le_of_ne h (fun he => hz he.symm)
  · exact le_of_lt

/-- The density includes the real boundary, so arbitrary canonical
traces touching that boundary retain their literal metric lengths. -/
def density (M : Marking) (I : ℝ) : ℂ → ℝ≥0∞ :=
  (closure upperHalfPlane).indicator
    (fun z => (ENNReal.ofReal I)⁻¹ *
      ENNReal.ofReal ‖upperDifferential M.left M.first M.second z‖)

theorem density_measurable (M : Marking) (I : ℝ) : Measurable (density M I) :=
  (measurable_const.mul (measurable_upperDensity M.left M.first M.second)).indicator
    isClosed_closure.measurableSet

theorem density_admissible (M : Marking) {I : ℝ} (hI : 0 < I) {F E : ℂ → ℂ}
    (hF : ∀ z ∈ upperHalfPlane,
      HasDerivAt F (upperDifferential M.left M.first M.second z) z)
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hFE : EqOn F E upperHalfPlane)
    (hends : ∀ z, M.ends z → (E z).re = 0)
    (hleft : ∀ z, z.im = 0 → z.re < M.left → (E z).re = I) :
    Admissible (halfPlaneTraces M) (density M I) := by
  refine ⟨density_measurable M I,?_⟩
  rintro S ⟨γ,hγ,rfl⟩
  change HalfPlaneLeaf M γ at hγ
  have hclosed : trace γ ⊆ closure upperHalfPlane := by
    rintro z ⟨t,rfl⟩
    rw [closure_upperHalfPlane]
    exact hγ.upper t
  have hd := canonical_endpoint_distance_le_upperLength M.left M.first M.second
    hF hE hFE γ hclosed
  have hre : I ≤ ‖E (γ terminal)-E (γ initial)‖ := by
    calc
      I = (E (γ terminal)-E (γ initial)).re := by
        rw [Complex.sub_re,hends _ hγ.first_end,hleft _ hγ.last_im hγ.last_re,sub_zero]
      _ ≤ ‖E (γ terminal)-E (γ initial)‖ := Complex.re_le_norm _
  have hlen : lineLength (density M I) (trace γ) =
      (ENNReal.ofReal I)⁻¹ *
        lineLength (fun z => ENNReal.ofReal
          ‖upperDifferential M.left M.first M.second z‖) (trace γ) := by
    unfold lineLength density
    rw [setLIntegral_congr_fun (trace_isCompact γ).measurableSet
      (fun z hz => indicator_of_mem (hclosed hz) _)]
    exact lintegral_const_mul _ (measurable_upperDensity M.left M.first M.second)
  rw [hlen]
  calc
    1 = (ENNReal.ofReal I)⁻¹ * ENNReal.ofReal I :=
      (ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hI).ne' ENNReal.ofReal_ne_top).symm
    _ ≤ _ := mul_le_mul_right ((ENNReal.ofReal_le_ofReal hre).trans hd) _

theorem openRectangle_volume (I J : ℝ) :
    volume {z : ℂ | z.re ∈ Ioo 0 I ∧ z.im ∈ Ioo (-J) 0} =
      ENNReal.ofReal I * ENNReal.ofReal J := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet
    (s := Ioo (0 : ℝ) I ×ˢ Ioo (-J) 0)
  have hp : Complex.measurableEquivRealProd ⁻¹' (Ioo (0 : ℝ) I ×ˢ Ioo (-J) 0) =
      {z : ℂ | z.re ∈ Ioo 0 I ∧ z.im ∈ Ioo (-J) 0} := by ext z; simp
  rw [hp] at h
  simpa [Measure.volume_eq_prod,Measure.prod_prod] using h

/-- The energy uses the exact target of the actual chart. -/
theorem density_area (M : Marking) {I J : ℝ} (hI : 0 < I)
    (C : CrestConformalModulus.ConformalChart)
    (hsource : C.homeomorph.source = upperHalfPlane)
    (htarget : C.homeomorph.target =
      {z : ℂ | z.re ∈ Ioo 0 I ∧ z.im ∈ Ioo (-J) 0})
    (hderiv : ∀ z ∈ upperHalfPlane,
      ‖C.derivative z‖ = ‖upperDifferential M.left M.first M.second z‖) :
    area (density M I) = ENNReal.ofReal (J/I) := by
  have hae : density M I =ᵐ[volume] C.pullDensity (fun _ => (ENNReal.ofReal I)⁻¹) := by
    filter_upwards [closure_upperHalfPlane_ae_eq] with z hz
    by_cases hu : z ∈ upperHalfPlane
    · have hc : z ∈ closure upperHalfPlane := subset_closure hu
      simp only [density,CrestConformalModulus.ConformalChart.pullDensity,
        CrestConformalModulus.ConformalChart.factor,hsource,indicator_of_mem hu,
        indicator_of_mem hc,hderiv z hu]
    · have hc : z ∉ closure upperHalfPlane := fun h => hu (Eq.mp hz h)
      simp [density,CrestConformalModulus.ConformalChart.pullDensity,hsource,hu,hc]
  calc
    area (density M I) =
        CrestConformalModulus.area (C.pullDensity (fun _ => (ENNReal.ofReal I)⁻¹)) := by
      apply lintegral_congr_ae
      filter_upwards [hae] with z hz
      exact congrArg (fun t : ℝ≥0∞ => t^2) hz
    _ = ∫⁻ _w in C.homeomorph.target,((ENNReal.ofReal I)⁻¹)^2 :=
      C.area_pull _
    _ = ((ENNReal.ofReal I)⁻¹)^2 * (ENNReal.ofReal I * ENNReal.ofReal J) := by
      rw [lintegral_const,Measure.restrict_apply_univ,htarget,openRectangle_volume]
    _ = ENNReal.ofReal (J/I) := by
      rw [ENNReal.ofReal_div_of_pos hI,div_eq_mul_inv]
      calc
        ((ENNReal.ofReal I)⁻¹)^2 * (ENNReal.ofReal I * ENNReal.ofReal J) =
            ENNReal.ofReal J * (ENNReal.ofReal I)⁻¹ *
              ((ENNReal.ofReal I)⁻¹ * ENNReal.ofReal I) := by ring
        _ = ENNReal.ofReal J * (ENNReal.ofReal I)⁻¹ := by
          rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hI).ne'
            ENNReal.ofReal_ne_top,mul_one]

/-- Sharp upper control of the entire canonical half-plane path family,
including all continuous paths with infinite Hausdorff length. -/
theorem halfPlaneWidth_le_rectangleRatio (M : Marking) {I J : ℝ} (hI : 0 < I)
    {F E : ℂ → ℂ}
    (hF : ∀ z ∈ upperHalfPlane,
      HasDerivAt F (upperDifferential M.left M.first M.second z) z)
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hFE : EqOn F E upperHalfPlane)
    (hends : ∀ z, M.ends z → (E z).re = 0)
    (hleft : ∀ z, z.im = 0 → z.re < M.left → (E z).re = I)
    (C : CrestConformalModulus.ConformalChart)
    (hsource : C.homeomorph.source = upperHalfPlane)
    (htarget : C.homeomorph.target =
      {z : ℂ | z.re ∈ Ioo 0 I ∧ z.im ∈ Ioo (-J) 0})
    (hderiv : ∀ z ∈ upperHalfPlane,
      ‖C.derivative z‖ = ‖upperDifferential M.left M.first M.second z‖) :
    halfPlaneWidth M ≤ ENNReal.ofReal (J/I) := by
  exact (modulus_le_area (density_admissible M hI hF hE hFE hends hleft)).trans_eq
    (density_area M hI C hsource htarget hderiv)

end
end ParentWaveUpperModulus

