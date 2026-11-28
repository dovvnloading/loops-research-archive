import ParentWavePhysicalInverse
import ParentWaveEllipticExistence

/-!
# The actual elliptic parent foliation

The inverse of the explicitly proved physical chart sends every
horizontal rectangle segment to an upper crosscut between the original
marked ending atom and the exterior left ray. Reflection produces a full
Borel parent wave in the repository's original homotopy class, and its
canonical Hausdorff-trace modulus is exactly half the rectangle ratio.
-/

namespace ParentWaveCanonicalFoliation

open Set Function MarkedSlitTransport SlitWaveModulus
open ParentWaveElliptic ParentWaveRectangle ParentWavePhysicalChart
open ParentWavePhysicalInverse ParentWaveRectangleTransport
open scoped ENNReal NNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The complete analytic data exist for every pair of literal positive
ordered branch gaps. Finite and infinite boundary behavior are proved
properties of the actual primitive, not additional hypotheses on a wave. -/
theorem exists_elliptic_extension (B C : ℝ) (hB : 0 < B) (hBC : B < C) :
    ∃ (E : ℂ → ℂ) (L : ℂ),
      (∀ t ∈ quadrant,HasDerivAt E (differential B C t) t) ∧
      ContinuousOn E (closure quadrant) ∧ UniformLimitAtInfinity E (closure quadrant) L := by
  exact ParentWaveEllipticExistence.exists_closed_primitive B C hB hBC

/-- The actual elliptic inverse foliation realizes its exact width as a
canonical parent wave. Every analytic hypothesis concerns the literal
cubic differential and is supplied by the proved primitive construction. -/
theorem exists_parentWave_of_elliptic (M : Marking)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E
      (differential (M.first-M.left) (M.second-M.left) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    ∃ Γ : Set Curve,ParentWave M univ Γ ∧
      modulus (traces Γ) = (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal
        (height (M.first-M.left) (M.second-M.left) E / width (M.first-M.left) E) := by
  have hB := sub_pos.mpr M.left_lt_first
  have hBC := sub_lt_sub_right M.first_lt_second M.left
  have hR := (dimensions_pos (M.first-M.left) (M.second-M.left) hB hBC hE hc).1
  let C := ParentWaveConformal.inverse (conformalChart M.left M.first M.second E hE)
  have hF := physicalInverse_continuous M.left (M.first-M.left) (M.second-M.left)
    hB hBC hE hc hinfty
  have hFinj := physicalInverse_injective M.left (M.first-M.left) (M.second-M.left)
    hB hBC hE hc hinfty
  have hsource : rectangleInterior (width (M.first-M.left) E)
      (-height (M.first-M.left) (M.second-M.left) E) 0 ⊆ C.homeomorph.source := by
    rw [show C.homeomorph.source = rectangleInterior (width (M.first-M.left) E)
      (-height (M.first-M.left) (M.second-M.left) E) 0 from
      inverse_chart_source M.left M.first M.second M.left_lt_first M.first_lt_second hE hc hinfty]
  have hFC : EqOn (physicalInverse M.left (M.first-M.left) E) C.homeomorph
      (rectangleInterior (width (M.first-M.left) E)
        (-height (M.first-M.left) (M.second-M.left) E) 0) :=
    physicalInverse_eq_chart_inverse M.left M.first M.second
      M.left_lt_first M.first_lt_second hE hc hinfty
  have hfirst := fun y hy => physicalInverse_ending_atom M hE hc hinfty (y := y) hy
  have hlast := fun y hy => physicalInverse_left_ray M hE hc hinfty (y := y) hy
  have hupper : ∀ z : ℂ,z.re ∈ Ioo 0 (width (M.first-M.left) E) →
      z.im ∈ Ioo (-height (M.first-M.left) (M.second-M.left) E) 0 →
      0 < (physicalInverse M.left (M.first-M.left) E z).im := by
    intro z hzre hzim
    exact physicalInverse_upper M.left M.first M.second M.left_lt_first M.first_lt_second
      hE hc hinfty ⟨hzre,hzim⟩
  obtain ⟨Γ,hΓ,hwidth⟩ := exists_parentWave_of_chart C hF hR hFinj hsource hFC hfirst hlast hupper
  refine ⟨Γ,hΓ,?_⟩
  simpa only [zero_sub,neg_neg] using hwidth

/-- A sharp lower bound for the full supremum over Borel parent waves,
realized by the actual inverse elliptic foliation. -/
theorem parent_width_lower_of_elliptic (M : Marking)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E
      (differential (M.first-M.left) (M.second-M.left) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal
      (height (M.first-M.left) (M.second-M.left) E / width (M.first-M.left) E) ≤
        SlitWaveLimit.width M univ := by
  obtain ⟨Γ,hΓ,hwidth⟩ := exists_parentWave_of_elliptic M hE hc hinfty
  rw [← hwidth]
  exact SlitWaveLimit.modulus_le_width hΓ

end
end ParentWaveCanonicalFoliation
