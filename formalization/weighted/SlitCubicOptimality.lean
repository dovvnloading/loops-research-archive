import SlitCubicUpperBound
import SlitCubicLeafLength

/-!
# Exact optimum and attainment for the complete marked parent problem

The actual reflected inverse-horizontal family is a Borel parent Wave.
Every admissible geometric density satisfies its explicit parameter-length
constraints, and hence the matching area lower bound. This attains the
unconditional upper certificate for the full supremum over all Waves.
-/

namespace SlitCubicOptimality

open Set MeasureTheory MarkedSlitTransport SlitWaveModulus SlitWaveLimit
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open SlitCubicWaves SlitCubicLowerEnergy
noncomputable section

/-- Exact all-density modulus of the constructed complete parent Wave. -/
theorem family_modulus_eq (M : Marking) :
    modulus (traces (family M)) = ENNReal.ofReal
      (height M.left M.first M.second / (2*period M.left M.first M.second)) := by
  apply le_antisymm
  · exact (modulus_le_width (family_parentWave M)).trans
      (SlitCubicUpperBound.width_le_period_ratio M univ)
  · apply le_iInf₂
    intro ρ hρ
    apply area_lower_of_inverse_slices M.left_lt_first M.first_lt_second hρ.1
    intro y hy
    have hmem : curve M.left_lt_first M.first_lt_second hy ∈ family M :=
      ⟨⟨y,hy⟩,rfl⟩
    have hlength := hρ.2 (trace (curve M.left_lt_first M.first_lt_second hy))
      (show trace (curve M.left_lt_first M.first_lt_second hy) ∈ traces (family M) from
        ⟨curve M.left_lt_first M.first_lt_second hy,hmem,rfl⟩)
    exact hlength.trans (SlitCubicLeafLength.curve_lineLength_le_inverseSliceLength
      M.left_lt_first M.first_lt_second hy hρ.1)

/-- The complete Borel parent-Wave supremum is exactly the cubic-period
ratio. The fourth slit endpoint is absent from the exact value. -/
theorem width_eq_period_ratio (M : Marking) :
    width M univ = ENNReal.ofReal
      ((∫ x in Ioo M.first M.second, realDensity M.left M.first M.second x) /
        (2 * ∫ x in Ioo M.left M.first, realDensity M.left M.first M.second x)) := by
  apply le_antisymm (SlitCubicUpperBound.width_le_period_ratio M univ)
  change ENNReal.ofReal (height M.left M.first M.second /
    (2*period M.left M.first M.second)) ≤ width M univ
  rw [← family_modulus_eq M]
  exact modulus_le_width (family_parentWave M)

/-- A specified actual Wave, not merely an approximating sequence,
attains the complete supremum. -/
theorem family_attains_width (M : Marking) :
    ParentWave M univ (family M) ∧ modulus (traces (family M)) = width M univ := by
  refine ⟨family_parentWave M,?_⟩
  rw [family_modulus_eq,width_eq_period_ratio]
  rfl

theorem exists_parentWave_attaining_width (M : Marking) :
    ∃ Γ : Set Curve, ParentWave M univ Γ ∧ modulus (traces Γ) = width M univ :=
  ⟨family M,family_attains_width M⟩

end
end SlitCubicOptimality
