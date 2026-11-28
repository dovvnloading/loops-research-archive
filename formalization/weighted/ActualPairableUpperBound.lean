import ActualPairableClosedChart
import SlitFourPointMetric

/-!
# The common-quadrilateral upper bound for actual pairable parents

All four electrodes, the full source component, and its conformal
coordinate are the actual quadratic-return objects.  The supremum covers
arbitrary Borel parent Waves with the two designated proper restrictions.
-/

namespace ActualPairableUpperBound

open Set Function Metric MarkedSlitTransport
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualPairableSource ActualPairablePorts ActualPairableClosedChart
open ActualPairableCoordinate SlitPairableWaves
noncomputable section

theorem region_ne_endpoints {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    {z : ℂ} (hz : z ∈ calibrationRegion (source c p) (sourceSlit c p)
      (leftPort c p) (rightPort hp hc)) :
    z ≠ (-cut c p 4 : ℝ) ∧ z ≠ (cut c p 2 : ℂ) ∧
      z ≠ (cut c p 5 : ℂ) ∧ z ≠ (-alpha hp hc : ℝ) := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := source_ports_ordered hp hc
  have hd := hc.2.1
  have hz' := hz.2
  refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> subst z <;>
    rcases hz' with hn | hj | hj
  all_goals
    simp only [sourceSlit,leftPort,rightPort,mem_setOf_eq,Complex.ofReal_im,
      Complex.ofReal_re,true_and,mem_Icc,mem_Ioo] at *
  all_goals first
    | (apply hn; constructor <;> linarith)
    | (rcases hj with ⟨hj0,hj1⟩; linarith)

theorem coordinate_ne_realCoordinate {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} {x : ℝ} (hz : z ∈ source c p)
    (hx : (x:ℂ) ∈ source c p) (hne : z ≠ (x:ℂ)) :
    coordinate c p z ≠ (realCoordinate c p x : ℂ) := by
  intro he
  apply hne
  apply coordinate_injOn hp hc hz hx
  exact he.trans (coordinate_ofReal hp hc hx).symm

theorem coordinate_avoids_electrodes {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hz : z ∈ calibrationRegion (source c p) (sourceSlit c p)
      (leftPort c p) (rightPort hp hc)) :
    coordinate c p z ≠ (electrode0 c p : ℂ) ∧
      coordinate c p z ≠ (electrode1 c p : ℂ) ∧
      coordinate c p z ≠ (electrode2 c p : ℂ) ∧
      coordinate c p z ≠ (electrode3 hp hc : ℂ) := by
  obtain ⟨he0,he1,he2,he3⟩ := region_ne_endpoints hp hc hz
  obtain ⟨h0,h1,h2,h3⟩ := physical_endpoints_mem_interval hp hc
  exact ⟨coordinate_ne_realCoordinate hp hc hz.1 (negativeInterval_mem_source hp hc h0) he0,
    coordinate_ne_realCoordinate hp hc hz.1 (negativeInterval_mem_source hp hc h1) he1,
    coordinate_ne_realCoordinate hp hc hz.1 (negativeInterval_mem_source hp hc h2) he2,
    coordinate_ne_realCoordinate hp hc hz.1 (negativeInterval_mem_source hp hc h3) he3⟩

/-- The single actual source quadrilateral controls every pairable parent,
even if the middle portion leaves the source component. -/
theorem pairable_width_le_period_ratio {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (M : Marking) (D : Set ℂ) :
    SlitPairableWaves.width M D (source c p) (sourceSlit c p)
      (leftPort c p) (rightPort hp hc) ≤
    ENNReal.ofReal (ActualPairableClosedChart.height hp hc /
      (2*ActualPairableClosedChart.width hp hc)) := by
  obtain ⟨h01,h12,h23⟩ := electrodes_ordered hp hc
  apply SlitFourPointMetric.pairable_width_le (ActualPairableCoordinate.conformalChart hp hc)
    M D (source c p) (sourceSlit c p) (leftPort c p) (rightPort hp hc) h01 h12 h23
  · intro z hz
    exact hz.1
  · intro z hz
    exact coordinate_avoids_electrodes hp hc hz
  · intro z hz
    have h := mem_image_of_mem (coordinate c p) hz
    rw [coordinate_leftPort_image hp hc] at h
    exact h
  · intro z hz
    have h := mem_image_of_mem (coordinate c p) hz
    rw [coordinate_rightPort_image hp hc] at h
    exact h

end
end ActualPairableUpperBound
