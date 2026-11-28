import SlitCubicOptimality
import ActualParentSupremum

/-!
# Exact limiting optimum for the actual quadratic parent problem

The three entries in the cubic periods are the actual limiting critical
orbit cuts. The maximizer is the specified reflected inverse-horizontal
Wave, with geometric admissibility already proved in the full parent class.
-/

namespace ActualParentOptimality

open Set Filter MarkedSlitTransport SlitWaveModulus SlitWaveLimit
open ActualParentSupremum ActualParentMarks LoopsLimitingCrestParameter
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open scoped Topology ENNReal
noncomputable section

/-- The exact optimal value, expressed only in the three limiting
critical-orbit cuts and ordinary real integrals. -/
theorem limitingParentWidth_eq_period_ratio (k : ℝ) (hk : k ∈ parameterInterval) :
    limitingParentWidth k hk = ENNReal.ofReal
      ((∫ x in Ioo (limitCuts k 1) (limitCuts k 2),
          realDensity (limitCuts k 0) (limitCuts k 1) (limitCuts k 2) x) /
        (2 * ∫ x in Ioo (limitCuts k 0) (limitCuts k 1),
          realDensity (limitCuts k 0) (limitCuts k 1) (limitCuts k 2) x)) :=
  SlitCubicOptimality.width_eq_period_ratio (limitMarking k hk)

/-- The full limiting supremum of the actual marked problem is attained
by the explicitly constructed inverse-horizontal parent Wave. -/
theorem limitingParentWave_attains (k : ℝ) (hk : k ∈ parameterInterval) :
    ParentWave (limitMarking k hk) univ (SlitCubicWaves.family (limitMarking k hk)) ∧
      modulus (traces (SlitCubicWaves.family (limitMarking k hk))) =
        limitingParentWidth k hk :=
  SlitCubicOptimality.family_attains_width (limitMarking k hk)

end
end ActualParentOptimality
