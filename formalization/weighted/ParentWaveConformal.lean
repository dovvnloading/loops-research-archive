import ParentWaveLocalLength
import CrestConformalModulus
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Conformal transport of the canonical Hausdorff-trace modulus

The local weighted Hausdorff theorem supplies length change for every
measurable trace and every measurable extended density. Inverse charts
give equality, including infinite-length traces. The actual Jacobian
formula supplies area change.
-/

namespace ParentWaveConformal

open Set MeasureTheory SlitWaveModulus
open scoped ENNReal

noncomputable section

abbrev Chart := CrestConformalModulus.ConformalChart

def inverse (C : Chart) : Chart where
  homeomorph := C.homeomorph.symm
  derivative := fun w => (C.derivative (C.homeomorph.symm w))⁻¹
  hasDeriv := by
    intro w hw
    exact C.homeomorph.hasDerivAt_symm hw
      (C.derivative_ne_zero _ (C.homeomorph.map_target hw))
      (C.hasDeriv _ (C.homeomorph.map_target hw))
  derivative_continuous := by
    exact (C.derivative_continuous.comp C.homeomorph.continuousOn_symm
      (fun w hw => C.homeomorph.map_target hw)).inv₀
        (fun w hw => C.derivative_ne_zero _ (C.homeomorph.map_target hw))
  derivative_ne_zero := by
    intro w hw
    exact inv_ne_zero (C.derivative_ne_zero _ (C.homeomorph.map_target hw))

private theorem image_length_le_pull (C : Chart) {S : Set ℂ} {ρ : ℂ → ℝ≥0∞}
    (hS : S ⊆ C.homeomorph.source) (hSm : MeasurableSet S) (hρ : Measurable ρ) :
    lineLength ρ (C.homeomorph '' S) ≤ lineLength (C.pullDensity ρ) S := by
  have h := ParentWaveLocalLength.lineLength_image_le_of_hasDerivOn
    C.homeomorph.open_source C.hasDeriv C.derivative_continuous
    C.derivative_ne_zero hS hSm hρ
  refine h.trans_eq ?_
  apply setLIntegral_congr_fun hSm
  intro z hz
  simp only [CrestConformalModulus.ConformalChart.pullDensity,
    indicator_of_mem (hS hz),CrestConformalModulus.ConformalChart.factor,mul_comm]

private theorem inverse_pull_pull (C : Chart) (ρ : ℂ → ℝ≥0∞) {w : ℂ}
    (hw : w ∈ C.homeomorph.target) :
    (inverse C).pullDensity (C.pullDensity ρ) w = ρ w := by
  have hz := C.homeomorph.map_target hw
  have hn : 0 < ‖C.derivative (C.homeomorph.symm w)‖ :=
    norm_pos_iff.mpr (C.derivative_ne_zero _ hz)
  change C.homeomorph.target.indicator
    (fun v => C.pullDensity ρ (C.homeomorph.symm v) *
      ENNReal.ofReal ‖(C.derivative (C.homeomorph.symm v))⁻¹‖) w = ρ w
  rw [indicator_of_mem hw,CrestConformalModulus.ConformalChart.pullDensity,
    indicator_of_mem hz,C.homeomorph.right_inv hw,
    CrestConformalModulus.ConformalChart.factor,norm_inv,ENNReal.ofReal_inv_of_pos hn]
  rw [mul_assoc, ENNReal.mul_inv_cancel
    (ENNReal.ofReal_pos.mpr hn).ne' ENNReal.ofReal_ne_top, mul_one]

/-- Exact weighted H¹ transport for arbitrary measurable traces. -/
theorem lineLength_pull_eq (C : Chart) {S : Set ℂ} {ρ : ℂ → ℝ≥0∞}
    (hS : S ⊆ C.homeomorph.source) (hSm : MeasurableSet S) (hρ : Measurable ρ) :
    lineLength (C.pullDensity ρ) S = lineLength ρ (C.homeomorph '' S) := by
  apply le_antisymm
  · have hT : C.homeomorph '' S ⊆ C.homeomorph.target := by
      rintro w ⟨z,hz,rfl⟩
      exact C.homeomorph.map_source (hS hz)
    have hTm : MeasurableSet (C.homeomorph '' S) :=
      hSm.image_of_continuousOn_injOn (C.homeomorph.continuousOn.mono hS)
        (C.homeomorph.injOn.mono hS)
    have hi := image_length_le_pull (inverse C) hT hTm (C.pullDensity_measurable hρ)
    have he : C.homeomorph.symm '' (C.homeomorph '' S) = S := by
      ext z
      constructor
      · rintro ⟨w,⟨v,hv,rfl⟩,rfl⟩
        simpa only [C.homeomorph.left_inv (hS hv)] using hv
      · intro hz
        exact ⟨C.homeomorph z,⟨z,hz,rfl⟩,C.homeomorph.left_inv (hS hz)⟩
    change lineLength (C.pullDensity ρ) (C.homeomorph.symm '' (C.homeomorph '' S)) ≤ _ at hi
    rw [he] at hi
    refine hi.trans_eq ?_
    exact setLIntegral_congr_fun hTm (fun w hw => inverse_pull_pull C ρ (hT hw))
  · exact image_length_le_pull C hS hSm hρ

private theorem pull_push (C : Chart) (ρ : ℂ → ℝ≥0∞) {z : ℂ}
    (hz : z ∈ C.homeomorph.source) : C.pullDensity (C.pushDensity ρ) z = ρ z := by
  simp only [CrestConformalModulus.ConformalChart.pullDensity,
    indicator_of_mem hz,CrestConformalModulus.ConformalChart.pushDensity,
    indicator_of_mem (C.homeomorph.map_source hz), C.homeomorph.left_inv hz,
    mul_assoc, ENNReal.inv_mul_cancel (C.factor_ne_zero hz) (C.factor_ne_top _), mul_one]

theorem lineLength_push_eq (C : Chart) {S : Set ℂ} {ρ : ℂ → ℝ≥0∞}
    (hS : S ⊆ C.homeomorph.source) (hSm : MeasurableSet S) (hρ : Measurable ρ) :
    lineLength (C.pushDensity ρ) (C.homeomorph '' S) = lineLength ρ S := by
  rw [← lineLength_pull_eq C hS hSm (C.pushDensity_measurable hρ)]
  exact setLIntegral_congr_fun hSm (fun z hz => pull_push C ρ (hS hz))

/-- Exact conformal invariance of the archive's canonical trace modulus.
This does not replace the family by its rectifiable or smooth subfamily. -/
theorem modulus_image_eq (C : Chart) {Γ : Set (Set ℂ)}
    (hΓ : ∀ S ∈ Γ, S ⊆ C.homeomorph.source)
    (hMeas : ∀ S ∈ Γ, MeasurableSet S) :
    modulus ((fun S => C.homeomorph '' S) '' Γ) = modulus Γ := by
  apply le_antisymm
  · unfold modulus
    apply le_iInf₂
    intro ρ hρ
    have ha : Admissible ((fun S => C.homeomorph '' S) '' Γ) (C.pushDensity ρ) := by
      refine ⟨C.pushDensity_measurable hρ.1,?_⟩
      rintro T ⟨S,hS,rfl⟩
      rw [lineLength_push_eq C (hΓ S hS) (hMeas S hS) hρ.1]
      exact hρ.2 S hS
    refine (modulus_le_area ha).trans ?_
    change CrestConformalModulus.area (C.pushDensity ρ) ≤ CrestConformalModulus.area ρ
    rw [C.area_push]
    exact setLIntegral_le_lintegral _ _
  · unfold modulus
    apply le_iInf₂
    intro ρ hρ
    have ha : Admissible Γ (C.pullDensity ρ) := by
      refine ⟨C.pullDensity_measurable hρ.1,?_⟩
      intro S hS
      rw [lineLength_pull_eq C (hΓ S hS) (hMeas S hS) hρ.1]
      exact hρ.2 _ ⟨S,hS,rfl⟩
    refine (modulus_le_area ha).trans ?_
    change CrestConformalModulus.area (C.pullDensity ρ) ≤ CrestConformalModulus.area ρ
    rw [C.area_pull]
    exact setLIntegral_le_lintegral _ _

end
end ParentWaveConformal

