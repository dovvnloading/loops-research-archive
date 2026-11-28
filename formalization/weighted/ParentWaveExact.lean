import ParentWavePhysicalChart
import ParentWaveUpperModulus
import ParentWaveEllipticIntegrals
import ParentWaveCanonicalFoliation
import ParentWaveEllipticK

/-! # The exact canonical parent Wave optimum -/

namespace ParentWaveExact
open Set MarkedSlitTransport SlitWaveModulus ParentWaveElliptic
open ParentWavePhysicalChart ParentWaveRectangle ParentWaveEllipticIntegrals
open scoped ENNReal Topology
noncomputable section

/-- The coefficient in terms of the actual three left marks. -/
def coefficient (a b c : ℝ) : ℝ :=
  verticalIntegral (b-a) (c-a) / (2 * horizontalIntegral (b-a) (c-a))

/-- The actual elliptic density bounds the complete canonical supremum. -/
theorem parent_width_upper_of_elliptic (M : Marking) {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant,
      HasDerivAt E (differential (M.first-M.left) (M.second-M.left) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    SlitWaveLimit.width M univ ≤ (2 : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal (height (M.first-M.left) (M.second-M.left) E /
        ParentWavePhysicalChart.width (M.first-M.left) E) := by
  let C := conformalChart M.left M.first M.second E hE
  let F := forward M.left (M.first-M.left) E
  have hI := (dimensions_pos (M.first-M.left) (M.second-M.left)
    (sub_pos.mpr M.left_lt_first) (sub_lt_sub_right M.first_lt_second M.left) hE hc).1
  have hFc : ContinuousOn F (closure upperHalfPlane) := by
    rw [ParentWaveUpperModulus.closure_upperHalfPlane]
    exact forward_continuous_closed M.left (M.first-M.left) hc
  have hends : ∀ z, M.ends z → (F z).re = 0 := by
    intro z hz
    have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hz.1)
    rw [he]
    exact (forward_ending_atom M.left M.first M.second M.left_lt_first
      M.first_lt_second hE hc ⟨hz.2.1,hz.2.2⟩).1
  have hleft : ∀ z : ℂ, z.im = 0 → z.re < M.left →
      (F z).re = ParentWavePhysicalChart.width (M.first-M.left) E := by
    intro z hzi hzr
    have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hzi)
    rw [he]
    exact (forward_left_ray M.left M.first M.second M.left_lt_first
      M.first_lt_second hE hc hinfty hzr).1
  have hu := ParentWaveUpperModulus.halfPlaneWidth_le_rectangleRatio M hI
    (fun z hz => forward_hasDeriv M.left M.first M.second hE hz)
    hFc (fun _ _ => rfl) hends hleft C rfl
    (conformalChart_target M.left M.first M.second M.left_lt_first
      M.first_lt_second hE hc hinfty) (fun _ _ => rfl)
  exact (ParentWaveHalfPlane.parent_width_le_halfPlane M univ).trans
    (mul_le_mul_right hu _)

/-- The actual period ratio equals the explicit real coefficient. -/
theorem period_ratio_eq_coefficient (M : Marking) {E : ℂ → ℂ}
    (hE : ∀ t ∈ quadrant,
      HasDerivAt E (differential (M.first-M.left) (M.second-M.left) t) t)
    (hc : ContinuousOn E (closure quadrant)) :
    (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal
      (height (M.first-M.left) (M.second-M.left) E /
        ParentWavePhysicalChart.width (M.first-M.left) E) =
      ENNReal.ofReal (coefficient M.left M.first M.second) := by
  have hB := sub_pos.mpr M.left_lt_first
  have hBC := sub_lt_sub_right M.first_lt_second M.left
  have hI := horizontal_side_eq_integral _ _ hB hBC hE hc (fun _ _ => rfl)
  have hJ := vertical_side_eq_integral _ _ hB hBC hE hc (fun _ _ => rfl)
  change (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal
    (((E (Real.sqrt (M.first-M.left):ℂ)).im - (E (Real.sqrt (M.second-M.left):ℂ)).im) /
      ((E 0).re - (E (Real.sqrt (M.first-M.left):ℂ)).re)) = _
  rw [hI,hJ]
  rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1/2 : ℝ) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num [one_div],
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
  congr 1
  dsimp [coefficient]
  ring

/-- Exact optimum of all original canonical Borel parent waves. -/
theorem parent_width_eq_coefficient (M : Marking) :
    SlitWaveLimit.width M univ = ENNReal.ofReal (coefficient M.left M.first M.second) := by
  obtain ⟨E,L,hE,hc,hinfty⟩ := ParentWaveCanonicalFoliation.exists_elliptic_extension
    (M.first-M.left) (M.second-M.left) (sub_pos.mpr M.left_lt_first)
    (sub_lt_sub_right M.first_lt_second M.left)
  rw [← period_ratio_eq_coefficient M hE hc]
  exact le_antisymm (parent_width_upper_of_elliptic M hE hc hinfty)
    (ParentWaveCanonicalFoliation.parent_width_lower_of_elliptic M hE hc hinfty)

/-- Attainment by a Borel wave of disjoint leaves in the original left class. -/
theorem exists_parentWave_attaining_width (M : Marking) :
    ∃ Γ : Set Curve, ParentWave M univ Γ ∧
      modulus (traces Γ) = SlitWaveLimit.width M univ := by
  obtain ⟨E,L,hE,hc,hinfty⟩ := ParentWaveCanonicalFoliation.exists_elliptic_extension
    (M.first-M.left) (M.second-M.left) (sub_pos.mpr M.left_lt_first)
    (sub_lt_sub_right M.first_lt_second M.left)
  obtain ⟨Γ,hΓ,hΓvalue⟩ := ParentWaveCanonicalFoliation.exists_parentWave_of_elliptic M hE hc hinfty
  refine ⟨Γ,hΓ,?_⟩
  rw [hΓvalue,period_ratio_eq_coefficient M hE hc,parent_width_eq_coefficient]

theorem coefficient_pos (M : Marking) : 0 < coefficient M.left M.first M.second := by
  have hB := sub_pos.mpr M.left_lt_first
  have hBC := sub_lt_sub_right M.first_lt_second M.left
  obtain ⟨E,L,hE,hc,hinfty⟩ := ParentWaveCanonicalFoliation.exists_elliptic_extension
    (M.first-M.left) (M.second-M.left) hB hBC
  have hpos := dimensions_pos (M.first-M.left) (M.second-M.left) hB hBC hE hc
  have hI := horizontal_side_eq_integral _ _ hB hBC hE hc (fun _ _ => rfl)
  have hJ := vertical_side_eq_integral _ _ hB hBC hE hc (fun _ _ => rfl)
  change 0 < (E 0).re - (E (Real.sqrt (M.first-M.left):ℂ)).re ∧
    0 < (E (Real.sqrt (M.first-M.left):ℂ)).im -
      (E (Real.sqrt (M.second-M.left):ℂ)).im at hpos
  rw [hI,hJ] at hpos
  exact div_pos hpos.2 (mul_pos (by norm_num) hpos.1)

theorem parent_width_toReal (M : Marking) :
    (SlitWaveLimit.width M univ).toReal = coefficient M.left M.first M.second := by
  rw [parent_width_eq_coefficient,ENNReal.toReal_ofReal (coefficient_pos M).le]

/-- K uses the parameter convention. -/
theorem coefficient_eq_K (M : Marking) :
    coefficient M.left M.first M.second =
      ParentWaveEllipticK.K (1-(M.first-M.left)/(M.second-M.left)) /
        (2 * ParentWaveEllipticK.K ((M.first-M.left)/(M.second-M.left))) :=
  ParentWaveEllipticK.ratio_eq_K _ _ (sub_pos.mpr (M.left_lt_first.trans M.first_lt_second))

theorem parent_width_eq_K (M : Marking) :
    SlitWaveLimit.width M univ = ENNReal.ofReal
      (ParentWaveEllipticK.K (1-(M.first-M.left)/(M.second-M.left)) /
        (2 * ParentWaveEllipticK.K ((M.first-M.left)/(M.second-M.left)))) := by
  rw [parent_width_eq_coefficient,coefficient_eq_K]

end
end ParentWaveExact



