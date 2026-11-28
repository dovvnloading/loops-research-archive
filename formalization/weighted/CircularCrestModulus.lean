import CircularCrestEnergy
import CrestConformalModulus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Circular leaves as actual smooth arcs

This module identifies the angular density problem with the ordinary
parametrized arclength modulus.  It also preserves that modulus under
a concrete conformal chart, including the final physical complex scaling.
-/

namespace CrestConformalModulus.ConformalChart

open Set

noncomputable section

/-- Postcompose a chart by a nonzero complex scaling.  Its source is
definitionally unchanged, so the same closed arcs remain in the chart. -/
def postScale (C : CrestConformalModulus.ConformalChart) (d : ℂ) (hd : d ≠ 0) :
    CrestConformalModulus.ConformalChart where
  homeomorph :=
    ((Homeomorph.mulLeft₀ d hd).symm.transOpenPartialHomeomorph C.homeomorph.symm).symm
  derivative := fun z => d * C.derivative z
  hasDeriv := by
    intro z hz
    exact (C.hasDeriv z hz).const_mul d
  derivative_continuous := continuousOn_const.mul C.derivative_continuous
  derivative_ne_zero := fun z hz => mul_ne_zero hd (C.derivative_ne_zero z hz)

@[simp] theorem postScale_source (C : CrestConformalModulus.ConformalChart)
    (d : ℂ) (hd : d ≠ 0) : (C.postScale d hd).homeomorph.source = C.homeomorph.source := rfl

@[simp] theorem postScale_apply (C : CrestConformalModulus.ConformalChart)
    (d : ℂ) (hd : d ≠ 0) (z : ℂ) :
    (C.postScale d hd).homeomorph z = d * C.homeomorph z := rfl

@[simp] theorem postScale_derivative (C : CrestConformalModulus.ConformalChart)
    (d : ℂ) (hd : d ≠ 0) (z : ℂ) :
    (C.postScale d hd).derivative z = d * C.derivative z := rfl

end
end CrestConformalModulus.ConformalChart

namespace CircularCrestModulus

open Set MeasureTheory CrestConformalModulus
open scoped ENNReal NNReal

noncomputable section

theorem point_hasDerivAt (m : ℂ) (r t : ℝ) :
    HasDerivAt (CircularCrestEnergy.point m r)
      (Complex.I * Complex.polarCoord.symm (r,t)) t := by
  have hc := (Real.hasDerivAt_cos t).ofReal_comp
  have hs := (Real.hasDerivAt_sin t).ofReal_comp
  have h := ((hc.add (hs.mul_const Complex.I)).const_mul (r : ℂ)).const_add m
  convert! h using 1
  · funext u
    simp [CircularCrestEnergy.point, Complex.polarCoord_symm_apply]
  · simp only [Complex.polarCoord_symm_apply, Complex.ofReal_neg]
    ring_nf
    simp [Complex.I_sq, sub_eq_add_neg]

/-- The actual circular arc, with angle itself as parameter. -/
def circleArc (m : ℂ) (r T : ℝ) (hT : 0 < T) : SmoothArc where
  toFun := CircularCrestEnergy.point m r
  velocity := fun t => Complex.I * Complex.polarCoord.symm (r,t)
  duration := T
  duration_pos := hT
  continuous :=
    ((CircularCrestEnergy.point_continuous m).comp
      (continuous_const.prodMk continuous_id)).continuousOn
  hasDeriv := fun t _ => point_hasDerivAt m r t
  velocity_continuous := by
    apply Continuous.continuousOn
    simp only [Complex.polarCoord_symm_apply]
    fun_prop

@[simp] theorem circleArc_apply (m : ℂ) (r T : ℝ) (hT : 0 < T) (t : ℝ) :
    circleArc m r T hT t = CircularCrestEnergy.point m r t := rfl

@[simp] theorem circleArc_duration (m : ℂ) (r T : ℝ) (hT : 0 < T) :
    (circleArc m r T hT).duration = T := rfl

theorem circleArc_speed (m : ℂ) {r T : ℝ} (hr : 0 ≤ r) (hT : 0 < T) (t : ℝ) :
    ‖(circleArc m r T hT).velocity t‖ = r := by
  simp only [circleArc, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_polarCoord_symm, abs_of_nonneg hr]

theorem lineLength_circleArc (m : ℂ) {r T : ℝ} (hr : 0 ≤ r) (hT : 0 < T)
    (ρ : ℂ → ℝ≥0∞) :
    lineLength ρ (circleArc m r T hT) = CircularCrestEnergy.leafLength m r T ρ := by
  simp only [lineLength, circleArc_duration, circleArc_apply,
    circleArc_speed m hr hT, CircularCrestEnergy.leafLength]

/-- Every circular leaf, with its own true duration, occurs in this family. -/
def circleFamily (m : ℂ) (I : Set ℝ) (θ : ℝ → ℝ) : Set SmoothArc :=
  {γ | ∃ r ∈ I, ∃ hT : 0 < θ r, circleArc m r (θ r) hT = γ}

theorem circleArc_mem_circleFamily {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    {r : ℝ} (hr : r ∈ I) (hT : 0 < θ r) :
    circleArc m r (θ r) hT ∈ circleFamily m I θ := ⟨r,hr,hT,rfl⟩

theorem admissible_iff {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hIp : I ⊆ Ioi 0) (hθ : ∀ r ∈ I, 0 < θ r) (ρ : ℂ → ℝ≥0∞) :
    CrestConformalModulus.Admissible (circleFamily m I θ) ρ ↔
      CircularCrestEnergy.Admissible m I θ ρ := by
  constructor
  · intro hρ
    refine ⟨hρ.1, ?_⟩
    intro r hr
    have h := hρ.2 _ (circleArc_mem_circleFamily hr (hθ r hr))
    simpa only [lineLength_circleArc m (hIp hr).le (hθ r hr)] using h
  · intro hρ
    refine ⟨hρ.1, ?_⟩
    rintro γ ⟨r,hr,hT,rfl⟩
    rw [lineLength_circleArc m (hIp hr).le hT]
    exact hρ.2 r hr

theorem modulus_eq_circularEnergy {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hIp : I ⊆ Ioi 0) (hθ : ∀ r ∈ I, 0 < θ r) :
    CrestConformalModulus.modulus (circleFamily m I θ) =
      CircularCrestEnergy.modulus m I θ := by
  unfold CrestConformalModulus.modulus CircularCrestEnergy.modulus
  simp only [admissible_iff hIp hθ, CrestConformalModulus.area, CircularCrestEnergy.area]

theorem modulus_eq_radial_integral {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hθm : Measurable θ) (hIp : I ⊆ Ioi 0)
    (hθ : ∀ r ∈ I, 0 < θ r ∧ θ r ≤ Real.pi) :
    CrestConformalModulus.modulus (circleFamily m I θ) =
      ∫⁻ r in I, ENNReal.ofReal (1/(r*θ r)) := by
  rw [modulus_eq_circularEnergy hIp (fun r hr => (hθ r hr).1)]
  exact CircularCrestEnergy.modulus_eq_radial_integral hI hθm hIp hθ

theorem transport_modulus_eq_radial_integral
    (C : CrestConformalModulus.ConformalChart) {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hθm : Measurable θ) (hIp : I ⊆ Ioi 0)
    (hθ : ∀ r ∈ I, 0 < θ r ∧ θ r ≤ Real.pi)
    (hΓ : ∀ γ ∈ circleFamily m I θ, γ.LiesIn C.homeomorph.source) :
    CrestConformalModulus.modulus (C.transportFamily (circleFamily m I θ)) =
      ∫⁻ r in I, ENNReal.ofReal (1/(r*θ r)) := by
  rw [C.modulus_transport _ hΓ]
  exact modulus_eq_radial_integral hI hθm hIp hθ

theorem radialIntegrand_integrableOn {a b : ℝ} {θ : ℝ → ℝ}
    (ha : 0 < a) (hθc : Continuous θ)
    (hθp : ∀ r ∈ Icc a b, 0 < θ r) :
    IntegrableOn (fun r => 1/(r*θ r)) (Ioo a b) := by
  have hc : ContinuousOn (fun r => 1/(r*θ r)) (Icc a b) := by
    apply continuousOn_const.div (continuousOn_id.mul hθc.continuousOn)
    intro r hr
    exact mul_ne_zero (ha.trans_le hr.1).ne' (hθp r hr).ne'
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem modulus_ne_top {m : ℂ} {a b : ℝ} {θ : ℝ → ℝ}
    (ha : 0 < a) (hθc : Continuous θ)
    (hθ : ∀ r ∈ Icc a b, 0 < θ r ∧ θ r ≤ Real.pi) :
    CrestConformalModulus.modulus (circleFamily m (Ioo a b) θ) ≠ ⊤ := by
  rw [modulus_eq_radial_integral measurableSet_Ioo hθc.measurable
    (fun r hr => ha.trans hr.1) (fun r hr => hθ r ⟨hr.1.le,hr.2.le⟩)]
  have hi := radialIntegrand_integrableOn ha hθc (fun r hr => (hθ r hr).1)
  apply (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable ?_).mpr hi
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact (one_div_pos.mpr (mul_pos (ha.trans hr.1) (hθ r ⟨hr.1.le,hr.2.le⟩).1)).le

/-- The finite smooth-arc modulus is exactly the real radial integral,
with the same endpoints used by the crest-limit analysis. -/
theorem toReal_modulus_eq_integral {m : ℂ} {a b : ℝ} {θ : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hθc : Continuous θ)
    (hθ : ∀ r ∈ Icc a b, 0 < θ r ∧ θ r ≤ Real.pi) :
    (CrestConformalModulus.modulus (circleFamily m (Ioo a b) θ)).toReal =
      ∫ r in a..b, 1/(r*θ r) := by
  rw [modulus_eq_radial_integral measurableSet_Ioo hθc.measurable
    (fun r hr => ha.trans hr.1) (fun r hr => hθ r ⟨hr.1.le,hr.2.le⟩)]
  have hi := radialIntegrand_integrableOn ha hθc (fun r hr => (hθ r hr).1)
  have hn : 0 ≤ᵐ[volume.restrict (Ioo a b)] (fun r => 1/(r*θ r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (one_div_pos.mpr (mul_pos (ha.trans hr.1) (hθ r ⟨hr.1.le,hr.2.le⟩).1)).le
  calc
    _ = ∫ r in Ioo a b, 1/(r*θ r) :=
      (integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable).symm
    _ = ∫ r in a..b, 1/(r*θ r) := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem toReal_transport_modulus_eq_integral
    (C : CrestConformalModulus.ConformalChart) {m : ℂ} {a b : ℝ} {θ : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hθc : Continuous θ)
    (hθ : ∀ r ∈ Icc a b, 0 < θ r ∧ θ r ≤ Real.pi)
    (hΓ : ∀ γ ∈ circleFamily m (Ioo a b) θ, γ.LiesIn C.homeomorph.source) :
    (CrestConformalModulus.modulus (C.transportFamily (circleFamily m (Ioo a b) θ))).toReal =
      ∫ r in a..b, 1/(r*θ r) := by
  rw [C.modulus_transport _ hΓ]
  exact toReal_modulus_eq_integral ha hab hθc hθ

end
end CircularCrestModulus
