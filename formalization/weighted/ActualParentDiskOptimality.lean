import SlitDiskOptimality
import ActualParentDiskMarking

/-!
# Exact finite-period optima in the actual quadratic dynamical plane

The finite-disk theorem is instantiated at literal critical-orbit cuts
and the literal target radius. Both normalized and original physical
problems have specified geometric maximizing parent Waves.
-/

namespace ActualParentDiskOptimality

open Set Metric MarkedSlitTransport SlitWaveModulus SlitWaveLimit
open ActualParentMarks ActualParentSupremum ActualParentDiskMarking
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter LimitingCrestQuadraticReturn
open SlitCubicBoundary SlitCubicBoundaryRange
noncomputable section

/-- The exact complete optimum for every actual normalized period. -/
theorem actualParentWidth_eq_period_ratio {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    actualParentWidth hp hc hk hroot = ENNReal.ofReal
      (height (actualTransformedMarking hp hc hk hroot).left
          (actualTransformedMarking hp hc hk hroot).first
          (actualTransformedMarking hp hc hk hroot).second /
        (2*period (actualTransformedMarking hp hc hk hroot).left
          (actualTransformedMarking hp hc hk hroot).first
          (actualTransformedMarking hp hc hk hroot).second)) :=
  SlitDiskOptimality.width_eq_period_ratio (actualMarking_fits_disk hp hc hk hroot).1
    (actualMarking hp hc hk hroot) (actualMarking_fits_disk hp hc hk hroot).2.1
    (actualMarking_fits_disk hp hc hk hroot).2.2

/-- The same exact value belongs to the original, unscaled physical
target disk; the scaling is the archive's proved all-Wave identity. -/
theorem physicalParentWidth_eq_period_ratio {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalParentWidth hp hc hk hroot = ENNReal.ofReal
      (height (actualTransformedMarking hp hc hk hroot).left
          (actualTransformedMarking hp hc hk hroot).first
          (actualTransformedMarking hp hc hk hroot).second /
        (2*period (actualTransformedMarking hp hc hk hroot).left
          (actualTransformedMarking hp hc hk hroot).first
          (actualTransformedMarking hp hc hk hroot).second)) := by
  rw [physicalParentWidth_eq_actual]
  exact actualParentWidth_eq_period_ratio hp hc hk hroot

def actualFamily {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : Set Curve :=
  SlitDiskWaves.family (actualMarking_fits_disk hp hc hk hroot).1
    (actualMarking hp hc hk hroot) (actualMarking_fits_disk hp hc hk hroot).2.1
    (actualMarking_fits_disk hp hc hk hroot).2.2

theorem actualFamily_attains {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    ParentWave (actualMarking hp hc hk hroot) (ball (0 : ℂ) (targetRadius c p))
      (actualFamily hp hc hk hroot) ∧
      modulus (traces (actualFamily hp hc hk hroot)) = actualParentWidth hp hc hk hroot :=
  SlitDiskOptimality.family_attains_width (actualMarking_fits_disk hp hc hk hroot).1
    (actualMarking hp hc hk hroot) (actualMarking_fits_disk hp hc hk hroot).2.1
    (actualMarking_fits_disk hp hc hk hroot).2.2

theorem physicalMarking_fits_disk {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    0 < (1/2 : ℝ)^p ∧ -(1/2 : ℝ)^p < (physicalMarking hp hc hk hroot).left ∧
      (physicalMarking hp hc hk hroot).right < (1/2 : ℝ)^p := by
  have hd := hc.2.1
  have hscale : criticalValue c p * targetRadius c p = (1/2 : ℝ)^p := by
    unfold targetRadius
    field_simp [hd.ne']
  have hfit := actualMarking_fits_disk hp hc hk hroot
  refine ⟨by positivity,?_,?_⟩
  · change -(1/2 : ℝ)^p < physicalCuts c p 0
    rw [← physicalCuts_scale hd.ne' 0,← hscale,← mul_neg]
    exact mul_lt_mul_of_pos_left hfit.2.1 hd
  · change physicalCuts c p 3 < (1/2 : ℝ)^p
    rw [← physicalCuts_scale hd.ne' 3,← hscale]
    exact mul_lt_mul_of_pos_left hfit.2.2 hd

def physicalFamily {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : Set Curve :=
  SlitDiskWaves.family (physicalMarking_fits_disk hp hc hk hroot).1
    (physicalMarking hp hc hk hroot) (physicalMarking_fits_disk hp hc hk hroot).2.1
    (physicalMarking_fits_disk hp hc hk hroot).2.2

/-- A literal Borel parent Wave in the original quadratic plane attains
the complete physical finite-period optimum. -/
theorem physicalFamily_attains {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    ParentWave (physicalMarking hp hc hk hroot) (ball (0 : ℂ) ((1/2 : ℝ)^p))
      (physicalFamily hp hc hk hroot) ∧
      modulus (traces (physicalFamily hp hc hk hroot)) = physicalParentWidth hp hc hk hroot :=
  SlitDiskOptimality.family_attains_width (physicalMarking_fits_disk hp hc hk hroot).1
    (physicalMarking hp hc hk hroot) (physicalMarking_fits_disk hp hc hk hroot).2.1
    (physicalMarking_fits_disk hp hc hk hroot).2.2

end
end ActualParentDiskOptimality
