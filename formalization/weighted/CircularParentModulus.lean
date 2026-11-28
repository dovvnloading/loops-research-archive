import CircularParentEnergy
import CircularCrestModulus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Full circular parents based at the positive radial point

The smooth circular path starts and ends at the positive radial point,
with parameter interval `[0, 2π]`.  Periodicity identifies its ordinary
metric length with the angular integral on `(-π, π)` used in the parent
energy calculation.  Thus both parent and descendant widths use exactly
the same smooth-arc modulus and the same class of planar densities.
-/

namespace CircularParentModulus

open Set MeasureTheory MeasureTheory.Measure
open CrestConformalModulus CircularCrestModulus
open scoped ENNReal NNReal

noncomputable section

theorem point_periodic (m : ℂ) (r : ℝ) :
    Function.Periodic (CircularCrestEnergy.point m r) (2*Real.pi) := by
  intro t
  simp only [CircularCrestEnergy.point,Complex.polarCoord_symm_apply,
    Real.cos_add_two_pi,Real.sin_add_two_pi]

/-- Integration over a full period is independent of the cut, including
for unbounded extended nonnegative functions. -/
theorem lintegral_full_period {f : ℝ → ℝ≥0∞}
    (hf : Function.Periodic f (2*Real.pi)) :
    (∫⁻ t in Ioo (0 : ℝ) (2*Real.pi), f t) =
      ∫⁻ t in Ioo (-Real.pi) Real.pi, f t := by
  letI : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
  have h0 := AddCircle.lintegral_preimage (2*Real.pi) 0 hf.lift
  have h1 := AddCircle.lintegral_preimage (2*Real.pi) (-Real.pi) hf.lift
  simp only [Function.Periodic.lift_coe,zero_add] at h0 h1
  rw [show -Real.pi+2*Real.pi = Real.pi by ring] at h1
  rw [restrict_Ioo_eq_restrict_Ioc,restrict_Ioo_eq_restrict_Ioc]
  exact h0.trans h1.symm

theorem leafLength_eq_parentEnergy (m : ℂ) (r : ℝ) (ρ : ℂ → ℝ≥0∞) :
    CircularCrestEnergy.leafLength m r (2*Real.pi) ρ =
      CircularParentEnergy.leafLength m r ρ := by
  apply lintegral_full_period
  intro t
  dsimp only
  rw [point_periodic m r t]

/-- The full parent circle based at its positive radial point. -/
def fullCircle (m : ℂ) (r : ℝ) : SmoothArc :=
  circleArc m r (2*Real.pi) (by positivity)

@[simp] theorem fullCircle_zero (m : ℂ) (r : ℝ) :
    fullCircle m r 0 = m+(r : ℂ) := by
  simp [fullCircle,circleArc_apply,CircularCrestEnergy.point,
    Complex.polarCoord_symm_apply]

@[simp] theorem fullCircle_finish (m : ℂ) (r : ℝ) :
    fullCircle m r (2*Real.pi) = m+(r : ℂ) := by
  simp [fullCircle,circleArc_apply,CircularCrestEnergy.point,
    Complex.polarCoord_symm_apply]

theorem fullCircle_lineLength (m : ℂ) {r : ℝ} (hr : 0 ≤ r) (ρ : ℂ → ℝ≥0∞) :
    lineLength ρ (fullCircle m r) = CircularParentEnergy.leafLength m r ρ := by
  rw [fullCircle,lineLength_circleArc m hr,leafLength_eq_parentEnergy]

theorem admissible_iff {m : ℂ} {I : Set ℝ} (hIp : I ⊆ Ioi 0)
    (ρ : ℂ → ℝ≥0∞) :
    CrestConformalModulus.Admissible (circleFamily m I (fun _ => 2*Real.pi)) ρ ↔
      CircularParentEnergy.Admissible m I ρ := by
  rw [CircularCrestModulus.admissible_iff hIp (fun _ _ => by positivity)]
  simp only [CircularCrestEnergy.Admissible,CircularParentEnergy.Admissible,
    leafLength_eq_parentEnergy]

/-- The full-circle family based at the positive radial point has precisely the previously
computed all-density parent modulus. -/
theorem modulus_eq_parentEnergy {m : ℂ} {I : Set ℝ} (hIp : I ⊆ Ioi 0) :
    CrestConformalModulus.modulus (circleFamily m I (fun _ => 2*Real.pi)) =
      CircularParentEnergy.modulus m I := by
  unfold CrestConformalModulus.modulus CircularParentEnergy.modulus
  simp only [admissible_iff hIp,CrestConformalModulus.area,CircularCrestEnergy.area]

theorem modulus_Ioo_eq_ofReal_log (m : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    CrestConformalModulus.modulus (circleFamily m (Ioo a b) (fun _ => 2*Real.pi)) =
      ENNReal.ofReal (Real.log (b/a)/(2*Real.pi)) := by
  rw [modulus_eq_parentEnergy (fun _ hr => ha.trans hr.1)]
  exact CircularParentEnergy.modulus_Ioo_eq_ofReal_log m ha hab

theorem modulus_Ioo_ne_top (m : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    CrestConformalModulus.modulus (circleFamily m (Ioo a b) (fun _ => 2*Real.pi)) ≠ ⊤ := by
  rw [modulus_Ioo_eq_ofReal_log m ha hab]
  exact ENNReal.ofReal_ne_top

theorem modulus_Ioo_toReal (m : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (CrestConformalModulus.modulus (circleFamily m (Ioo a b) (fun _ => 2*Real.pi))).toReal =
      Real.log (b/a)/(2*Real.pi) := by
  rw [modulus_eq_parentEnergy (fun _ hr => ha.trans hr.1)]
  exact CircularParentEnergy.modulus_Ioo_toReal m ha hab

end
end CircularParentModulus
