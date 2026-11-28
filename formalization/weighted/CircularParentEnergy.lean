import CircularCrestEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The complete circular parent family

This is the all-density metric problem for the full circular leaves,
including both semicircles as one closed path. Its normalization is
computed independently of the selected descendant collar.
-/

namespace CircularParentEnergy

open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Classical
open CircularCrestEnergy (point point_continuous)

noncomputable section

def leafLength (m : ℂ) (r : ℝ) (ρ : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (-Real.pi) Real.pi, ρ (point m r t) * ENNReal.ofReal r

def Admissible (m : ℂ) (I : Set ℝ) (ρ : ℂ → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ r ∈ I, 1 ≤ leafLength m r ρ

def modulus (m : ℂ) (I : Set ℝ) : ℝ≥0∞ :=
  ⨅ (ρ : ℂ → ℝ≥0∞) (_ : Admissible m I ρ), CircularCrestEnergy.area ρ

theorem angular_energy_lower {m : ℂ} {r : ℝ} (hr : 0 < r)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (hlength : 1 ≤ leafLength m r ρ) :
    ENNReal.ofReal (1/(r*(2*Real.pi))) ≤
      ENNReal.ofReal r * ∫⁻ t in Ioo (-Real.pi) Real.pi, (ρ (point m r t))^2 := by
  have hp : Measurable (fun t : ℝ => ρ (point m r t)) :=
    hρ.comp ((point_continuous m).comp (continuous_const.prodMk continuous_id)).measurable
  have hmass : (volume.restrict (Ioo (-Real.pi) Real.pi)) univ =
      ENNReal.ofReal (2*Real.pi) := by
    simp only [Measure.restrict_apply_univ,Real.volume_Ioo,sub_neg_eq_add,two_mul]
  have hT : 0 < 2*Real.pi := by positivity
  have h := CollarMetricEnergy.reciprocal_mass_le_square_integral
    (μ := volume.restrict (Ioo (-Real.pi) Real.pi))
    (f := fun t => ρ (point m r t) * ENNReal.ofReal r)
    (hp.mul measurable_const).aemeasurable
    (by rw [hmass]; exact (ENNReal.ofReal_pos.mpr hT).ne')
    (by rw [hmass]; exact ENNReal.ofReal_ne_top) hlength
  simp only [hmass,mul_pow] at h
  rw [lintegral_mul_const _ (hp.pow_const 2)] at h
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have he : ENNReal.ofReal (1/(r*(2*Real.pi))) =
      (ENNReal.ofReal (2*Real.pi))⁻¹ / ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_inv_of_pos hT,← ENNReal.ofReal_div_of_pos hr]
    congr 1
    field_simp
  rw [he]
  apply (ENNReal.div_le_iff hr0 ENNReal.ofReal_ne_top).mpr
  simpa only [pow_two,mul_assoc,mul_left_comm,mul_comm] using h

theorem radial_integral_le_area {m : ℂ} {I : Set ℝ}
    (hI : MeasurableSet I) (hIp : I ⊆ Ioi 0)
    {ρ : ℂ → ℝ≥0∞} (hρ : Admissible m I ρ) :
    (∫⁻ r in I, ENNReal.ofReal (1/(r*(2*Real.pi)))) ≤ CircularCrestEnergy.area ρ := by
  calc
    _ ≤ ∫⁻ r in I, ENNReal.ofReal r *
        ∫⁻ t in Ioo (-Real.pi) Real.pi, (ρ (point m r t))^2 := by
      apply setLIntegral_mono' hI
      intro r hr
      exact angular_energy_lower (hIp hr) hρ.1 (hρ.2 r hr)
    _ ≤ CircularCrestEnergy.area ρ :=
      CircularCrestEnergy.polar_energy_le_area hI measurableSet_Ioo hIp Subset.rfl hρ.1

def extremalDensity (m : ℂ) (I : Set ℝ) : ℂ → ℝ≥0∞ :=
  {z | ‖z-m‖ ∈ I}.indicator (fun z => ENNReal.ofReal (1/(‖z-m‖*(2*Real.pi))))

theorem extremalDensity_measurable {m : ℂ} {I : Set ℝ}
    (hI : MeasurableSet I) : Measurable (extremalDensity m I) := by
  have hn : Measurable (fun z : ℂ => ‖z-m‖) := (continuous_id.sub continuous_const).norm.measurable
  exact (ENNReal.measurable_ofReal.comp
    (measurable_const.div (hn.mul measurable_const))).indicator (hI.preimage hn)

theorem extremalDensity_point {m : ℂ} {I : Set ℝ} {r : ℝ} (hr : 0 < r) (t : ℝ) :
    extremalDensity m I (point m r t) =
      I.indicator (fun r => ENNReal.ofReal (1/(r*(2*Real.pi)))) r := by
  have hn : ‖point m r t-m‖ = r := by
    simp [point,Complex.norm_polarCoord_symm,abs_of_pos hr]
  simp only [extremalDensity,indicator,mem_setOf_eq,hn]

theorem extremalDensity_leafLength {m : ℂ} {I : Set ℝ}
    {r : ℝ} (hrI : r ∈ I) (hr : 0 < r) :
    leafLength m r (extremalDensity m I) = 1 := by
  have hT : 0 < 2*Real.pi := by positivity
  unfold leafLength
  simp_rw [extremalDensity_point hr,indicator_of_mem hrI]
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
  rw [show Real.pi - -Real.pi = 2*Real.pi by ring,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(r*(2*Real.pi))),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (1/(r*(2*Real.pi)))*r)]
  have he : (1/(r*(2*Real.pi)))*r*(2*Real.pi) = (1 : ℝ) := by
    field_simp [hr.ne',Real.pi_pos.ne']
  rw [he,ENNReal.ofReal_one]

theorem extremalDensity_admissible {m : ℂ} {I : Set ℝ}
    (hI : MeasurableSet I) (hIp : I ⊆ Ioi 0) :
    Admissible m I (extremalDensity m I) := by
  refine ⟨extremalDensity_measurable hI,?_⟩
  intro r hr
  rw [extremalDensity_leafLength hr (hIp hr)]

private theorem slice_energy {m : ℂ} {I : Set ℝ} {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r * (extremalDensity m I (point m r t))^2) =
      I.indicator (fun r => ENNReal.ofReal (1/(r*(2*Real.pi)))) r := by
  simp_rw [extremalDensity_point hr]
  by_cases hrI : r ∈ I
  · rw [indicator_of_mem hrI]
    simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
    rw [show Real.pi - -Real.pi = 2*Real.pi by ring,
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1/(r*(2*Real.pi))),
      ← ENNReal.ofReal_mul hr.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ r*(1/(r*(2*Real.pi)))^2)]
    congr 1
    field_simp [hr.ne',Real.pi_pos.ne']
  · simp [indicator_of_notMem hrI]

theorem extremalDensity_area {m : ℂ} {I : Set ℝ}
    (hI : MeasurableSet I) (hIp : I ⊆ Ioi 0) :
    CircularCrestEnergy.area (extremalDensity m I) =
      ∫⁻ r in I, ENNReal.ofReal (1/(r*(2*Real.pi))) := by
  let ρ := extremalDensity m I
  have hm : Measurable ρ := extremalDensity_measurable hI
  have hf : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (ρ (point m p.1 p.2))^2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((hm.comp (point_continuous m).measurable).pow_const 2)
  calc
    CircularCrestEnergy.area ρ = ∫⁻ z : ℂ, (ρ (m+z))^2 :=
      (lintegral_add_left_eq_self (fun z : ℂ => (ρ z)^2) m).symm
    _ = ∫⁻ p : ℝ × ℝ in _root_.polarCoord.target,
        ENNReal.ofReal p.1 * (ρ (point m p.1 p.2))^2 := by
      simpa only [point,smul_eq_mul] using
        (Complex.lintegral_comp_polarCoord_symm (fun z => (ρ (m+z))^2)).symm
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * (ρ (point m r t))^2 := by
      rw [_root_.polarCoord_target,volume_eq_prod,setLIntegral_prod _ hf.aemeasurable]
    _ = ∫⁻ r in Ioi (0 : ℝ), I.indicator (fun r => ENNReal.ofReal (1/(r*(2*Real.pi)))) r := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact slice_energy hr
    _ = ∫⁻ r in I, ENNReal.ofReal (1/(r*(2*Real.pi))) := by
      rw [setLIntegral_indicator hI,inter_eq_left.mpr hIp]

theorem modulus_eq_radial_integral {m : ℂ} {I : Set ℝ}
    (hI : MeasurableSet I) (hIp : I ⊆ Ioi 0) :
    modulus m I = ∫⁻ r in I, ENNReal.ofReal (1/(r*(2*Real.pi))) := by
  apply le_antisymm
  · have h : modulus m I ≤ CircularCrestEnergy.area (extremalDensity m I) := by
      unfold modulus
      exact iInf₂_le _ (extremalDensity_admissible hI hIp)
    exact h.trans_eq (extremalDensity_area hI hIp)
  · apply le_iInf₂
    intro ρ hρ
    exact radial_integral_le_area hI hIp hρ

/-- The complete circular parent width is evaluated from its metric
problem, including every measurable density on the physical plane. -/
theorem modulus_Ioo_eq_ofReal_log (m : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    modulus m (Ioo a b) = ENNReal.ofReal (Real.log (b/a)/(2*Real.pi)) := by
  have hb : 0 < b := ha.trans_le hab
  have hcont : ContinuousOn (fun r : ℝ => 1/(r*(2*Real.pi))) (Icc a b) := by
    apply continuousOn_const.div (continuousOn_id.mul continuousOn_const)
    intro r hr
    exact (mul_pos (ha.trans_le hr.1) (by positivity)).ne'
  have hfi : IntegrableOn (fun r : ℝ => 1/(r*(2*Real.pi))) (Ioo a b) volume :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo a b)] (fun r : ℝ => 1/(r*(2*Real.pi))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hr0 : 0 < r := ha.trans hr.1
    positivity
  rw [modulus_eq_radial_integral measurableSet_Ioo (fun r hr => ha.trans hr.1),
    ← ofReal_integral_eq_lintegral_ofReal hfi hnn,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  congr 1
  have he : (fun r : ℝ => 1/(r*(2*Real.pi))) = (fun r : ℝ => (1/r)/(2*Real.pi)) := by
    funext r
    rw [div_div]
  rw [he,intervalIntegral.integral_div,integral_one_div_of_pos ha hb]

theorem modulus_Ioo_toReal (m : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (modulus m (Ioo a b)).toReal = Real.log (b/a)/(2*Real.pi) := by
  rw [modulus_Ioo_eq_ofReal_log m ha hab,ENNReal.toReal_ofReal]
  have hlog : 0 ≤ Real.log (b/a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  positivity

end
end CircularParentEnergy
