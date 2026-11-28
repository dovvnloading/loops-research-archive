import SlitWaveLimit
import MarkedSlitCompression
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Exact positive scaling of the complete marked Wave supremum

Both real coordinates are multiplied by the same positive scalar. This
is a conformal dilation; it is distinct from horizontal mark motion,
which changes only the real coordinate. The general Hausdorff modulus
transport factors cancel exactly for the dilation and its inverse.
-/

namespace SlitWaveScaling

open Set Function MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus SlitWaveLimit
open scoped ENNReal NNReal Topology Pointwise

noncomputable section

def dilation (d : ℝ) (hd : 0 < d) : ℂ ≃ₜ ℂ :=
  Homeomorph.smulOfNeZero d hd.ne'

@[simp] theorem dilation_apply (d : ℝ) (hd : 0 < d) (z : ℂ) :
    dilation d hd z = d • z := rfl

@[simp] theorem dilation_symm_apply (d : ℝ) (hd : 0 < d) (z : ℂ) :
    (dilation d hd).symm z = d⁻¹ • z := rfl

def scalarCoordinate (d : ℝ) (hd : 0 < d) : CoordinateEmbedding where
  toFun x := d*x
  continuous := continuous_const.mul continuous_id
  strictMono := fun _ _ h => mul_lt_mul_of_pos_left h hd
  map_zero := mul_zero d

theorem scalar_plane (d : ℝ) (hd : 0 < d) :
    ((scalarCoordinate d hd).plane : ℂ → ℂ) = dilation d hd := by
  funext z
  apply Complex.ext <;> simp [scalarCoordinate]

theorem scalar_marking (M : Marking) (d : ℝ) (hd : 0 < d) :
    M.coordinateMap (scalarCoordinate d hd) = M.map (OrderIso.mulLeft₀ d hd) := rfl

private theorem dilation_factor (d : ℝ) (hd : 0 < d) :
    ((‖d⁻¹‖₊ : ℝ≥0∞)^2 * (‖d‖₊ : ℝ≥0∞)^2) = 1 := by
  have hnorm : ‖d⁻¹‖₊*‖d‖₊ = 1 := by
    rw [← nnnorm_mul,inv_mul_cancel₀ hd.ne']
    simp
  rw [← mul_pow,← ENNReal.coe_mul,hnorm]
  simp

/-- Exact conformal invariance is proved for every geometric curve
family, including infinite-length curves. -/
theorem modulus_dilation (d : ℝ) (hd : 0 < d) (Γ : Set (Set ℂ)) :
    modulus (transportFamily (dilation d hd) Γ) = modulus Γ := by
  have hL : LipschitzWith ‖d‖₊ (dilation d hd) := lipschitzWith_smul d
  have hK : LipschitzWith ‖d⁻¹‖₊ (dilation d hd).symm := lipschitzWith_smul d⁻¹
  have hL0 : ‖d‖₊ ≠ 0 := by simpa using hd.ne'
  have hK0 : ‖d⁻¹‖₊ ≠ 0 := by simpa using inv_ne_zero hd.ne'
  have hu := modulus_transport_le (dilation d hd) hL hK hL0 hK0 Γ
  have hl := modulus_le_mul_transport (dilation d hd) hL hK hL0 hK0 Γ
  rw [dilation_factor d hd,one_mul] at hu hl
  exact le_antisymm hu hl

theorem trace_scalarCurve (d : ℝ) (hd : 0 < d) (γ : Curve) :
    trace (coordinateCurve (scalarCoordinate d hd) γ) = dilation d hd '' trace γ := by
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨γ t,⟨t,rfl⟩,(congrFun (scalar_plane d hd) (γ t)).symm⟩
  · rintro ⟨_,⟨t,rfl⟩,rfl⟩
    exact ⟨t,congrFun (scalar_plane d hd) (γ t)⟩

theorem traces_scalarCurve (d : ℝ) (hd : 0 < d) (Γ : Set Curve) :
    traces (coordinateCurve (scalarCoordinate d hd) '' Γ) =
      transportFamily (dilation d hd) (traces Γ) := by
  ext S
  constructor
  · rintro ⟨_,⟨γ,hγ,rfl⟩,rfl⟩
    exact ⟨trace γ,⟨γ,hγ,rfl⟩,(trace_scalarCurve d hd γ).symm⟩
  · rintro ⟨_,⟨γ,hγ,rfl⟩,rfl⟩
    exact ⟨coordinateCurve (scalarCoordinate d hd) γ,⟨γ,hγ,rfl⟩,
      trace_scalarCurve d hd γ⟩

theorem width_le_dilation (M : Marking) (D : Set ℂ) (d : ℝ) (hd : 0 < d) :
    width M D ≤ width (M.map (OrderIso.mulLeft₀ d hd)) (dilation d hd '' D) := by
  apply iSup₂_le
  intro Γ hΓ
  have hw : ParentWave (M.map (OrderIso.mulLeft₀ d hd)) (dilation d hd '' D)
      (coordinateCurve (scalarCoordinate d hd) '' Γ) := by
    simpa only [scalar_marking,scalar_plane] using hΓ.coordinateMap (scalarCoordinate d hd)
  calc
    modulus (traces Γ) = modulus (traces (coordinateCurve (scalarCoordinate d hd) '' Γ)) := by
      rw [traces_scalarCurve,modulus_dilation]
    _ ≤ _ := modulus_le_width hw

private theorem marking_ext {M A : Marking}
    (hl : M.left = A.left) (ha : M.first = A.first)
    (hb : M.second = A.second) (hr : M.right = A.right) : M = A := by
  cases M
  cases A
  simp_all

theorem scalar_marking_inverse (M : Marking) (d : ℝ) (hd : 0 < d) :
    (M.map (OrderIso.mulLeft₀ d hd)).map (OrderIso.mulLeft₀ d⁻¹ (inv_pos.mpr hd)) = M := by
  apply marking_ext <;> simp [Marking.map,hd.ne']

/-- Positive physical rescaling preserves the entire supremum, because
it transports the complete lamination class in both directions. -/
theorem width_dilation (M : Marking) (D : Set ℂ) (d : ℝ) (hd : 0 < d) :
    width (M.map (OrderIso.mulLeft₀ d hd)) (dilation d hd '' D) = width M D := by
  apply le_antisymm
  · have h := width_le_dilation (M.map (OrderIso.mulLeft₀ d hd))
      (dilation d hd '' D) d⁻¹ (inv_pos.mpr hd)
    have hinv : dilation d⁻¹ (inv_pos.mpr hd) = (dilation d hd).symm := by ext z; rfl
    have himage : dilation d⁻¹ (inv_pos.mpr hd) '' (dilation d hd '' D) = D := by
      rw [hinv]
      exact (dilation d hd).toEquiv.symm_image_image D
    rw [scalar_marking_inverse,himage] at h
    exact h
  · exact width_le_dilation M D d hd

theorem dilation_image_ball (d : ℝ) (hd : 0 < d) (R : ℝ) :
    dilation d hd '' ball (0 : ℂ) R = ball (0 : ℂ) (d*R) := by
  change d • ball (0 : ℂ) R = ball (0 : ℂ) (d*R)
  rw [_root_.smul_ball hd.ne',smul_zero,Real.norm_eq_abs,abs_of_pos hd]

theorem width_dilation_ball (M : Marking) (R d : ℝ) (hd : 0 < d) :
    width (M.map (OrderIso.mulLeft₀ d hd)) (ball (0 : ℂ) (d*R)) =
      width M (ball (0 : ℂ) R) := by
  simpa only [dilation_image_ball] using width_dilation M (ball (0 : ℂ) R) d hd

end
end SlitWaveScaling
