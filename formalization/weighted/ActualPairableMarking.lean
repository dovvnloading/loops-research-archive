import ActualPairablePortImages
import SlitPairableWaves

/-! # Literal physical marking of the actual pairable parent problem -/

namespace ActualPairableMarking

open Set Metric MarkedSlitTransport
open NearTwoTip LimitingCrestQuadraticReturn ActualParentMarks
open ActualPairableSource ActualPairablePorts
open scoped ENNReal NNReal

noncomputable section

theorem negative_alpha_lt_third_cut {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : -alpha hp hc < cut c p 3 := by
  have ha := normalizedAlpha_bounds hp hc
  have h3 := (normalized_cut_boxes hp hc).2.1
  rw [cut_eq_scale_mul_normalized c p 3 hc.2.1.ne',alpha]
  have h := mul_lt_mul_of_pos_left (show -normalizedAlpha hp hc < normalizedCut c p 3 by
    linarith [ha.1,h3.1]) hc.2.1
  simpa only [mul_neg] using h

theorem third_cut_lt_criticalValue {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : cut c p 3 < criticalValue c p := by
  have h3 := (normalized_cut_boxes hp hc).2.1
  rw [cut_eq_scale_mul_normalized c p 3 hc.2.1.ne']
  exact mul_lt_of_lt_one_right hc.2.1 (by linarith [h3.2])

def parentMarking {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : Marking where
  left := cut c p 2
  first := cut c p 5
  second := cut c p 3
  right := criticalValue c p
  left_lt_first := (source_ports_ordered hp hc).2.2.1
  first_lt_second := (target_ports_ordered hp hc).1
  second_lt_right := third_cut_lt_criticalValue hp hc

theorem parentMarking_eq_physicalMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ LoopsLimitingCrestParameter.parameterInterval)
    (hroot : LoopsLimitingCrestParameter.relation k = 0) :
    parentMarking hp hc = ActualParentSupremum.physicalMarking hp hc hk hroot := by
  ext <;> rfl

theorem leftPort_re_lt_left {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    {z : ℂ} (hz : z ∈ leftPort c p) : z.re < (parentMarking hp hc).left := hz.2.2

theorem rightPort_ends {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    {z : ℂ} (hz : z ∈ rightPort hp hc) : (parentMarking hp hc).ends z :=
  ⟨hz.1,hz.2.1,hz.2.2.trans (negative_alpha_lt_third_cut hp hc)⟩

theorem parentSlit_subset_sourceSlit {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (parentMarking hp hc).slit ⊆ sourceSlit c p := by
  intro z hz
  have ho := source_ports_ordered hp hc
  exact ⟨hz.1,((ho.1.trans ho.2.1).le.trans hz.2.1),hz.2.2⟩

theorem source_subset_disk {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    source c p ⊆ ball 0 (radius p) :=
  subset_closure.trans (source_closure_inside hp hc)

/-- The physical two-port problem on the complete actual archived source.
No native ideal-boundary equivalence is asserted by this definition. -/
def pairableWidth {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ℝ≥0∞ :=
  SlitPairableWaves.width (parentMarking hp hc) (ball 0 (radius p)) (source c p)
    (sourceSlit c p) (leftPort c p) (rightPort hp hc)

end
end ActualPairableMarking
