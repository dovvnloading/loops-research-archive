import ChildSlitCompression
import SlitWaveScaling

/-!
# Exact physical scaling of complete child optima

A positive conformal dilation transports both child ending intervals,
their upper accesses, and the entire source-contained relative homotopy.
It transports every geometric Borel Wave in both directions. The
Hausdorff modulus factors cancel exactly, so the full physical supremum
equals its normalized counterpart.
-/

namespace ChildSlitScaling

open Set Function MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus ChildSlitModel
open SlitWaveScaling
open scoped ENNReal NNReal Topology Pointwise

noncomputable section

theorem scalar_marking (M : ChildMarking) (d : ℝ) (hd : 0 < d) :
    M.coordinateMap (scalarCoordinate d hd) = M.map (OrderIso.mulLeft₀ d hd) := rfl

theorem width_le_dilation (M : ChildMarking) (D : Set ℂ) (d : ℝ) (hd : 0 < d) :
    width M D ≤ width (M.map (OrderIso.mulLeft₀ d hd)) (dilation d hd '' D) := by
  apply iSup₂_le
  intro Γ hΓ
  have hw : ChildWave (M.map (OrderIso.mulLeft₀ d hd)) (dilation d hd '' D)
      (coordinateCurve (scalarCoordinate d hd) '' Γ) := by
    simpa only [scalar_marking,scalar_plane] using hΓ.coordinateMap (scalarCoordinate d hd)
  calc
    modulus (traces Γ) = modulus (traces (coordinateCurve (scalarCoordinate d hd) '' Γ)) := by
      rw [traces_scalarCurve,modulus_dilation]
    _ ≤ _ := modulus_le_width hw

theorem scalar_marking_inverse (M : ChildMarking) (d : ℝ) (hd : 0 < d) :
    (M.map (OrderIso.mulLeft₀ d hd)).map (OrderIso.mulLeft₀ d⁻¹ (inv_pos.mpr hd)) = M := by
  apply ChildSlitTransport.marking_ext <;> simp [ChildMarking.map,hd.ne']

/-- The equality is between full family suprema, not chosen witnesses. -/
theorem width_dilation (M : ChildMarking) (D : Set ℂ) (d : ℝ) (hd : 0 < d) :
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

theorem width_dilation_ball (M : ChildMarking) (R d : ℝ) (hd : 0 < d) :
    width (M.map (OrderIso.mulLeft₀ d hd)) (ball (0 : ℂ) (d*R)) =
      width M (ball (0 : ℂ) R) := by
  simpa only [dilation_image_ball] using width_dilation M (ball (0 : ℂ) R) d hd

end
end ChildSlitScaling
