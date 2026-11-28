import ActualPairableOptimality
import ActualPairableElectrodeLimit
import ActualPairablePortLimit
import SlitFourPointLimit

/-!
# Convergence of the actual geometric pairable optima

The exact finite optimum is normalized by one common positive electrode
scale.  The complete actual critical-return and fixed-cut estimates give
the four limiting electrodes, and the proved four-point modulus
continuity passes to the limit.  The final common square-root factor is
removed by exact scale invariance.
-/

namespace ActualPairableConvergence

open Set Filter
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualPairableSource ActualPairablePorts ActualPairableElectrodes
open ActualPairableElectrodeLimit ActualPairablePortLimit ActualPairableMarking
open LoopsLimitingCrestParameter
open scoped Topology ENNReal

noncomputable section

def electrodes {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : Fin 4 → ℝ :=
  fun i => electrodeAt c p (physicalImageCuts hp hc i)

def normalizedElectrodes {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : Fin 4 → ℝ :=
  fun i => normalizingScale c p * electrodes hp hc i

theorem electrodes_ordered {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    electrodes hp hc 0 < electrodes hp hc 1 ∧
      electrodes hp hc 1 < electrodes hp hc 2 ∧ electrodes hp hc 2 < electrodes hp hc 3 := by
  have h := ActualPairableClosedChart.electrodes_ordered hp hc
  simpa [electrodes,physicalImageCuts,
    electrode0_eq hp hc,electrode1_eq hp hc,electrode2_eq hp hc,electrode3_eq hp hc] using h

theorem normalizedElectrodes_ordered {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    normalizedElectrodes hp hc 0 < normalizedElectrodes hp hc 1 ∧
      normalizedElectrodes hp hc 1 < normalizedElectrodes hp hc 2 ∧
      normalizedElectrodes hp hc 2 < normalizedElectrodes hp hc 3 :=
  ⟨mul_lt_mul_of_pos_left (electrodes_ordered hp hc).1 (normalizingScale_pos hc),
    mul_lt_mul_of_pos_left (electrodes_ordered hp hc).2.1 (normalizingScale_pos hc),
    mul_lt_mul_of_pos_left (electrodes_ordered hp hc).2.2 (normalizingScale_pos hc)⟩

/-- The shrinking physical electrode scale cancels exactly before the
limit is taken. -/
theorem pairableWidth_eq_normalized_ratio {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : pairableWidth hp hc =
      ENNReal.ofReal (SlitFourPointLimit.ratio
        (normalizedElectrodes hp hc 0) (normalizedElectrodes hp hc 1)
        (normalizedElectrodes hp hc 2) (normalizedElectrodes hp hc 3)) := by
  rw [ActualPairableOptimality.pairableWidth_eq_explicit_actual_periods hp hc]
  congr 1
  exact (SlitFourPointLimit.ratio_scale (normalizingScale_pos hc)
    (electrodes_ordered hp hc).1 (electrodes_ordered hp hc).2.1
    (electrodes_ordered hp hc).2.2).symm

theorem normalizedElectrodes_tendsto {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n))
    (i : Fin 4) :
    Tendsto (fun n => normalizedElectrodes (by omega : 17 ≤ n+17) (hc n) i)
      atTop (𝓝 (Real.sqrt k * limitingSourcePorts k hk i)) := by
  have himage : Tendsto
      (fun n => physicalImageCuts (by omega : 17 ≤ n+17) (hc n) i /
        criticalValue (c n) (n+17)) atTop (𝓝 (limitingImageCuts k hk i)) := by
    simpa only [physicalImageCuts_div] using normalizedImageCuts_tendsto hk hroot c hc i
  have h := normalized_electrode_tendsto c
    (fun n => physicalImageCuts (by omega : 17 ≤ n+17) (hc n) i) hc
    (fun n => physicalImageCuts_lt_criticalValue (by omega) (hc n) i) himage
  simpa only [normalizedElectrodes,electrodes,sqrt_limitingImageCuts_eq hk i] using h

/-- For every sequence of actual signed tips, the full actual geometric
pairable supremum tends to the explicit limiting physical four-port
value.  Optimizers and domains need no additional convergence premise. -/
theorem pairableWidth_tendsto {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => pairableWidth (by omega : 17 ≤ n+17) (hc n)) atTop
      (𝓝 (ENNReal.ofReal (SlitFourPointLimit.ratio
        (-criticalOrbit k 4) (criticalOrbit k 2)
        (criticalOrbit k 5) (-limitingAlpha k hk)))) := by
  have hkpos : 0 < k := by
    have h := hk.1
    change 17903/10000 ≤ k at h
    linarith
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
  have h01 := limitingSourcePorts_strictMono hk (show (0 : Fin 4) < 1 by decide)
  have h12 := limitingSourcePorts_strictMono hk (show (1 : Fin 4) < 2 by decide)
  have h23 := limitingSourcePorts_strictMono hk (show (2 : Fin 4) < 3 by decide)
  have h := SlitFourPointLimit.ofReal_ratio_tendsto
    (mul_lt_mul_of_pos_left h01 hs) (mul_lt_mul_of_pos_left h12 hs)
    (mul_lt_mul_of_pos_left h23 hs)
    (fun n => normalizedElectrodes (by omega : 17 ≤ n+17) (hc n) 0)
    (fun n => normalizedElectrodes (by omega : 17 ≤ n+17) (hc n) 1)
    (fun n => normalizedElectrodes (by omega : 17 ≤ n+17) (hc n) 2)
    (fun n => normalizedElectrodes (by omega : 17 ≤ n+17) (hc n) 3)
    (fun n => (normalizedElectrodes_ordered (by omega) (hc n)).1)
    (fun n => (normalizedElectrodes_ordered (by omega) (hc n)).2.1)
    (fun n => (normalizedElectrodes_ordered (by omega) (hc n)).2.2)
    (normalizedElectrodes_tendsto hk hroot c hc 0)
    (normalizedElectrodes_tendsto hk hroot c hc 1)
    (normalizedElectrodes_tendsto hk hroot c hc 2)
    (normalizedElectrodes_tendsto hk hroot c hc 3)
  rw [SlitFourPointLimit.ratio_scale hs h01 h12 h23] at h
  exact h.congr' (Filter.Eventually.of_forall fun n =>
    (pairableWidth_eq_normalized_ratio (by omega : 17 ≤ n+17) (hc n)).symm)

end
end ActualPairableConvergence
