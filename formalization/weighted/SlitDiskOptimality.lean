import SlitDiskUpperBound
import SlitDiskLeafLength
import SlitDiskLowerChart

/-!
# Exact optimal width and attainment in a finite disk

The transformed periods determine the complete parent supremum in the
original disk. The maximizing family consists of the actual reflected
inverse-rectangle leaves pulled back by the explicit inverse Cayley map.
-/

namespace SlitDiskOptimality

open Set MeasureTheory MarkedSlitTransport SlitWaveModulus SlitWaveLimit
open SlitCubicBoundary SlitCubicBoundaryRange SlitDiskMarking
noncomputable section

variable {R : ℝ} (hR : 0 < R) (M : Marking)
  (hleft : -R < M.left) (hright : M.right < R)

local notation "N" => transformedMarking hR M hleft hright

/-- Every measurable density admissible for the actual inverse family
has the exact transformed-period energy lower bound. -/
theorem family_modulus_eq :
    modulus (traces (SlitDiskWaves.family hR M hleft hright)) =
      ENNReal.ofReal (height (N).left (N).first (N).second /
        (2*period (N).left (N).first (N).second)) := by
  apply le_antisymm
  · exact (modulus_le_width (SlitDiskWaves.family_parentWave hR M hleft hright)).trans
      (SlitDiskUpperBound.width_le_period_ratio hR M hleft hright)
  · apply le_iInf₂
    intro ρ hρ
    apply SlitDiskLowerChart.area_lower_of_inverse_slices hR
      (N).left_lt_first (N).first_lt_second hρ.1
    intro y hy
    have hmem : SlitDiskWaves.curve hR M hleft hright hy ∈
        SlitDiskWaves.family hR M hleft hright := ⟨⟨y,hy⟩,rfl⟩
    have hlength := hρ.2 (trace (SlitDiskWaves.curve hR M hleft hright hy))
      (show trace (SlitDiskWaves.curve hR M hleft hright hy) ∈
          traces (SlitDiskWaves.family hR M hleft hright) from
        ⟨SlitDiskWaves.curve hR M hleft hright hy,hmem,rfl⟩)
    exact hlength.trans (SlitDiskLeafLength.curve_lineLength_le_inverseSliceLength
      hR M hleft hright hy hρ.1)

/-- Exact unrestricted parent-Wave width in the original disk. -/
theorem width_eq_period_ratio :
    width M (Metric.ball (0 : ℂ) R) = ENNReal.ofReal
      (height (N).left (N).first (N).second /
        (2*period (N).left (N).first (N).second)) := by
  apply le_antisymm (SlitDiskUpperBound.width_le_period_ratio hR M hleft hright)
  have h := modulus_le_width (SlitDiskWaves.family_parentWave hR M hleft hright)
  rw [family_modulus_eq] at h
  exact h

/-- A specified geometric Borel parent Wave attains the finite-disk
supremum; attainment is not an additional compactness premise. -/
theorem family_attains_width :
    ParentWave M (Metric.ball (0 : ℂ) R) (SlitDiskWaves.family hR M hleft hright) ∧
      modulus (traces (SlitDiskWaves.family hR M hleft hright)) =
        width M (Metric.ball (0 : ℂ) R) := by
  refine ⟨SlitDiskWaves.family_parentWave hR M hleft hright,?_⟩
  rw [family_modulus_eq,width_eq_period_ratio]

include hR hleft hright in
theorem exists_parentWave_attaining_width :
    ∃ Γ : Set Curve, ParentWave M (Metric.ball (0 : ℂ) R) Γ ∧
      modulus (traces Γ) = width M (Metric.ball (0 : ℂ) R) :=
  ⟨SlitDiskWaves.family hR M hleft hright,family_attains_width hR M hleft hright⟩

end
end SlitDiskOptimality
