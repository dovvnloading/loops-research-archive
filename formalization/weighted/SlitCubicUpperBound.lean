import SlitCubicMetricArea
import SlitCubicEnergy

/-!
# An unconditional cubic-period bound for the complete parent supremum

The right endpoint of the slit does not occur in this explicit bound.
It applies to every literal Borel parent Wave, with arbitrary continuous
simple leaves.  No conformal rectangle, optimizer, or unproved energy
identity is assumed.  Equality and attainment are separate questions.
-/

namespace SlitCubicUpperBound

open Set MeasureTheory MarkedSlitTransport SlitCubicCalibration SlitCubicBoundary
  SlitCubicAdmissible SlitWaveModulus
noncomputable section

/-- The exactly evaluated area of the constructed admissible metric. -/
theorem density_area_exact (M : Marking) :
    area (density M) = ENNReal.ofReal
      ((∫ x in Ioo M.first M.second, realDensity M.left M.first M.second x) /
        (2 * period M.left M.first M.second)) := by
  rw [SlitCubicMetricArea.area_eq_upper_energy,
    SlitCubicEnergy.integral_upper_densitySq M.left_lt_first M.first_lt_second]
  congr 1
  have hB := (period_pos M.left_lt_first M.first_lt_second).ne'
  field_simp

/-- The supremum over every Borel parent Wave is bounded by a ratio of
actual cubic periods, independently of the fourth slit endpoint. -/
theorem width_le_period_ratio (M : Marking) (D : Set ℂ) :
    SlitWaveLimit.width M D ≤ ENNReal.ofReal
      ((∫ x in Ioo M.first M.second, realDensity M.left M.first M.second x) /
        (2 * ∫ x in Ioo M.left M.first, realDensity M.left M.first M.second x)) := by
  exact (width_le_density_area M D).trans_eq (density_area_exact M)

end
end SlitCubicUpperBound
