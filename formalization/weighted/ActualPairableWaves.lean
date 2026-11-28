import ActualPairableClosedChart
import ActualPairableMarking
import SlitReflectedRectangles

/-!
# Complete pairable Waves in the actual archived quadratic source

Every horizontal height of the constructed actual rectangle is reflected
through the real axis.  Each parent has the two designated proper source
restrictions, whose common inner contact lies in the actual left port.
The full family is Borel and has disjoint simple interiors.
-/

namespace ActualPairableWaves

open Set Function Metric MeasureTheory MarkedSlitTransport
open NearTwoTip LimitingCrestQuadraticReturn
open ActualPairableSource ActualPairablePorts ActualPairableMarking
open SlitCubicClosedChart SlitPairableWaves
open scoped ENNReal NNReal

noncomputable section

def inverseData {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    SlitReflectedRectangles.InverseData
      (ActualPairableClosedChart.width hp hc) (ActualPairableClosedChart.height hp hc) where
  toFun := ActualPairableClosedChart.closedInverse hp hc
  width_pos := ActualPairableClosedChart.width_pos hp hc
  height_pos := ActualPairableClosedChart.height_pos hp hc
  continuous := ActualPairableClosedChart.closedInverse_continuousOn hp hc
  injective := ActualPairableClosedChart.closedInverse_injOn hp hc
  upper := fun _ hw => (ActualPairableClosedChart.closedInverse_mem_upperSource hp hc hw).2
  left_real := fun _ hy => (ActualPairableClosedChart.closedInverse_left_edge hp hc hy).1
  right_real := fun _ hy => (ActualPairableClosedChart.closedInverse_right_edge hp hc hy).1

def curve {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) {y : ℝ}
    (hy : y ∈ Ioo (-ActualPairableClosedChart.height hp hc) 0) : Curve :=
  SlitReflectedRectangles.curve (inverseData hp hc) hy

def family {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : Set Curve :=
  SlitReflectedRectangles.family (inverseData hp hc)

@[simp] theorem curve_apply {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) {y : ℝ}
    (hy : y ∈ Ioo (-ActualPairableClosedChart.height hp hc) 0) (t : Parameter) :
    curve hp hc hy t = SlitCubicWaves.rawCurve (ActualPairableClosedChart.closedInverse hp hc)
      (ActualPairableClosedChart.width hp hc) y t := rfl

theorem curve_mem_family {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) {y : ℝ}
    (hy : y ∈ Ioo (-ActualPairableClosedChart.height hp hc) 0) :
    curve hp hc hy ∈ family hp hc := ⟨⟨y,hy⟩,rfl⟩

private theorem inverseData_mapsTo_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : MapsTo (inverseData hp hc)
      (closedHorizontalBand (ActualPairableClosedChart.width hp hc) (ActualPairableClosedChart.height hp hc))
      (source c p) := fun _ hz => ActualPairableClosedChart.closedInverse_mem_source hp hc hz

private theorem source_conj_mapsTo {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    MapsTo (starRingEnd ℂ) (source c p) (source c p) :=
  fun _ hz => source_conj hp hc hz

private theorem inverse_left_conditions {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {y : ℝ} (hy : y ∈ Ioo (-ActualPairableClosedChart.height hp hc) 0) :
    ((inverseData hp hc) ((y : ℂ)*Complex.I)).re < (parentMarking hp hc).left ∧
      (inverseData hp hc) ((y : ℂ)*Complex.I) ∈ sourceSlit c p ∩ leftPort c p := by
  have hz := ActualPairableClosedChart.closedInverse_left_edge hp hc hy
  exact ⟨leftPort_re_lt_left hp hc hz,leftPort_subset_sourceSlit hp hc hz,hz⟩

private theorem inverse_right_conditions {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {y : ℝ} (hy : y ∈ Ioo (-ActualPairableClosedChart.height hp hc) 0) :
    (parentMarking hp hc).ends ((inverseData hp hc)
      ((ActualPairableClosedChart.width hp hc : ℂ)+(y : ℂ)*Complex.I)) ∧
      (inverseData hp hc) ((ActualPairableClosedChart.width hp hc : ℂ)+(y : ℂ)*Complex.I) ∈
        sourceSlit c p ∩ rightPort hp hc := by
  have hz := ActualPairableClosedChart.closedInverse_right_edge hp hc hy
  exact ⟨rightPort_ends hp hc hz,rightPort_subset_sourceSlit hp hc hz,hz⟩

/-- The two designated actual child restrictions meet at the midpoint,
with the required lower and upper source-bank accesses. -/
theorem curve_temporalPair {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) {y : ℝ}
    (hy : y ∈ Ioo (-ActualPairableClosedChart.height hp hc) 0) :
    TemporalPair (source c p) (sourceSlit c p) (leftPort c p) (rightPort hp hc)
      (curve hp hc hy) middle middle :=
  SlitReflectedRectangles.curve_temporalPair (inverseData hp hc)
    (inverseData_mapsTo_source hp hc) (source_conj_mapsTo hp hc) (fun _ hz => hz.1) hy
    (inverse_left_conditions hp hc hy).2 (inverse_right_conditions hp hc hy).2

/-- The actual all-height reflected family is a pairable Wave in the
literal physical target disk and complete archived source. -/
theorem family_pairableWave {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    PairableWave (parentMarking hp hc) (ball 0 (radius p)) (source c p)
      (sourceSlit c p) (leftPort c p) (rightPort hp hc) (family hp hc) := by
  have h := SlitReflectedRectangles.family_pairableWave (inverseData hp hc) (parentMarking hp hc)
    (inverseData_mapsTo_source hp hc) (source_conj_mapsTo hp hc) (fun _ hz => hz.1)
    (fun _ hy => inverse_left_conditions hp hc hy) (fun _ hy => inverse_right_conditions hp hc hy)
  exact ⟨⟨h.borel,fun _ hγ => (h.leaf _ hγ).mono (source_subset_disk hp hc),h.disjoint⟩,h.pair⟩

theorem family_parentWave {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    ParentWave (parentMarking hp hc) (ball 0 (radius p)) (family hp hc) :=
  (family_pairableWave hp hc).toParentWave

theorem curve_pairableLeaf {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) {y : ℝ}
    (hy : y ∈ Ioo (-ActualPairableClosedChart.height hp hc) 0) :
    PairableLeaf (parentMarking hp hc) (ball 0 (radius p)) (source c p)
      (sourceSlit c p) (leftPort c p) (rightPort hp hc) (curve hp hc hy) :=
  (family_pairableWave hp hc).pairable_leaf (curve_mem_family hp hc hy)

theorem family_nonempty {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    (family hp hc).Nonempty := by
  have hy : -ActualPairableClosedChart.height hp hc/2 ∈
      Ioo (-ActualPairableClosedChart.height hp hc) 0 := by
    constructor <;> linarith [ActualPairableClosedChart.height_pos hp hc]
  exact ⟨curve hp hc hy,curve_mem_family hp hc hy⟩

/-- The complete physical trace is covered by the two actual inverse
horizontal segments, for the all-density lower energy estimate. -/
theorem trace_curve_subset_segments {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {y : ℝ} (hy : y ∈ Ioo (-ActualPairableClosedChart.height hp hc) 0) :
    trace (curve hp hc hy) ⊆
      (fun x : ℝ => ActualPairableClosedChart.closedInverse hp hc ((x : ℂ)+(y : ℂ)*Complex.I)) ''
        Icc 0 (ActualPairableClosedChart.width hp hc) ∪
      (fun x : ℝ => starRingEnd ℂ (ActualPairableClosedChart.closedInverse hp hc
        ((x : ℂ)+(y : ℂ)*Complex.I))) '' Icc 0 (ActualPairableClosedChart.width hp hc) :=
  SlitReflectedRectangles.trace_curve_subset_segments (inverseData hp hc) hy

end
end ActualPairableWaves
