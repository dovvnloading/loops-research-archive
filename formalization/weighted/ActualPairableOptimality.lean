import ActualPairableUpperBound
import ActualPairableLeafLength
import ActualPairableElectrodes

/-!
# Exact optimum and attainment for the actual two-child geometric problem

A common quadrilateral metric controls every proper temporal pair, and
the actual reflected inverse-horizontal Wave has the matching all-density
lower bound. Both sides use the whole archived quadratic source and the
literal physical parent domain. No optimizer or conformal chart is an
additional hypothesis. Native ideal-boundary equivalence is not asserted.
-/

namespace ActualPairableOptimality

open Set Metric MarkedSlitTransport SlitWaveModulus
open NearTwoTip
open ActualPairableSource ActualPairablePorts ActualPairableMarking
open ActualPairableWaves ActualPairableClosedChart
open scoped ENNReal
noncomputable section

/-- The actual reflected family has exactly the common-quadrilateral
modulus, with the infimum over all measurable extended densities. -/
theorem family_modulus_eq_period_ratio {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    modulus (traces (family hp hc)) = ENNReal.ofReal (height hp hc/(2*width hp hc)) := by
  apply le_antisymm
  · exact (SlitPairableWaves.modulus_le_width (family_pairableWave hp hc)).trans
      (ActualPairableUpperBound.pairable_width_le_period_ratio hp hc
        (parentMarking hp hc) (ball 0 (radius p)))
  · exact ActualPairableLeafLength.family_modulus_lower hp hc

/-- Exact optimization over every actual geometric pairable Wave, allowing
arbitrary child excursions and parents whose middle segment leaves V. -/
theorem pairableWidth_eq_period_ratio {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    pairableWidth hp hc = ENNReal.ofReal (height hp hc/(2*width hp hc)) := by
  apply le_antisymm
  · exact ActualPairableUpperBound.pairable_width_le_period_ratio hp hc
      (parentMarking hp hc) (ball 0 (radius p))
  · rw [← family_modulus_eq_period_ratio hp hc]
    exact SlitPairableWaves.modulus_le_width (family_pairableWave hp hc)

/-- The value is given explicitly by real radicals of the actual return
values, followed by specified cubic integrals. -/
theorem pairableWidth_eq_explicit_actual_periods {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    pairableWidth hp hc = ENNReal.ofReal (ActualPairableElectrodes.periodRatio hp hc) := by
  rw [pairableWidth_eq_period_ratio hp hc,ActualPairableElectrodes.height_div_width_eq hp hc]

/-- A specified complete Borel Wave attains the full constrained optimum. -/
theorem family_attains_pairableWidth {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    SlitPairableWaves.PairableWave (parentMarking hp hc) (ball 0 (radius p))
      (source c p) (sourceSlit c p) (leftPort c p) (rightPort hp hc) (family hp hc) ∧
      modulus (traces (family hp hc)) = pairableWidth hp hc := by
  refine ⟨family_pairableWave hp hc,?_⟩
  rw [family_modulus_eq_period_ratio hp hc,pairableWidth_eq_period_ratio hp hc]

theorem exists_pairableWave_attaining_width {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ∃ Γ : Set Curve,
      SlitPairableWaves.PairableWave (parentMarking hp hc) (ball 0 (radius p))
        (source c p) (sourceSlit c p) (leftPort c p) (rightPort hp hc) Γ ∧
      modulus (traces Γ) = pairableWidth hp hc :=
  ⟨family hp hc,family_attains_pairableWidth hp hc⟩

theorem pairableWidth_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    0 < pairableWidth hp hc := by
  rw [pairableWidth_eq_explicit_actual_periods hp hc]
  exact ENNReal.ofReal_pos.mpr (ActualPairableElectrodes.periodRatio_pos hp hc)

theorem pairableWidth_ne_top {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    pairableWidth hp hc ≠ ⊤ := by
  rw [pairableWidth_eq_explicit_actual_periods hp hc]
  exact ENNReal.ofReal_ne_top

end
end ActualPairableOptimality
