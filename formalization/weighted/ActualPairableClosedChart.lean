import ActualPairableCoordinate
import ActualPairablePortImages
import SlitFourPointChart

/-!
# The actual source rectangle and its two physical endpoint intervals

The regular source coordinate has an ordinary inverse at every point of
the two real ports.  Its real order and exact port images are proved
before transporting the four-electrode rectangle back to the source.
-/

namespace ActualPairableClosedChart

open Set Function Metric
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualPairableSource ActualPairablePorts ActualPairableCoordinate
open SlitCubicCalibration SlitCubicRectangle
open scoped Topology

noncomputable section

def realCoordinate (c : ℝ) (p : ℕ) (x : ℝ) : ℝ := (coordinate c p (x : ℂ)).re

theorem negativeInterval_mem_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {x : ℝ} (hx : x ∈ Icc (-criticalValue c p) 0) :
    (x : ℂ) ∈ source c p := by
  apply closedBall_criticalValue_subset_source hp hc
  rw [mem_closedBall_zero_iff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos hx.2]
  linarith [hx.1]

theorem coordinate_ofReal {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {x : ℝ} (hx : (x : ℂ) ∈ source c p) :
    coordinate c p (x : ℂ) = (realCoordinate c p x : ℂ) := by
  apply Complex.ext
  · rfl
  · exact coordinate_real_im hp hc hx rfl

theorem realCoordinate_continuousOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ContinuousOn (realCoordinate c p) (Icc (-criticalValue c p) 0) :=
  Complex.continuous_re.comp_continuousOn
    ((coordinate_continuousOn hp hc).comp Complex.continuous_ofReal.continuousOn
      (fun _ hx => negativeInterval_mem_source hp hc hx))

theorem realCoordinate_injOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : InjOn (realCoordinate c p) (Icc (-criticalValue c p) 0) := by
  intro x hx y hy he
  apply Complex.ofReal_injective
  apply coordinate_injOn hp hc (negativeInterval_mem_source hp hc hx)
    (negativeInterval_mem_source hp hc hy)
  rw [coordinate_ofReal hp hc (negativeInterval_mem_source hp hc hx),
    coordinate_ofReal hp hc (negativeInterval_mem_source hp hc hy),he]

@[simp] theorem realCoordinate_zero (c : ℝ) (p : ℕ) : realCoordinate c p 0 = 0 := by
  simp [realCoordinate]

theorem realCoordinate_strictMonoOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : StrictMonoOn (realCoordinate c p) (Icc (-criticalValue c p) 0) := by
  apply ContinuousOn.strictMonoOn_of_injOn_Icc (by linarith [hc.2.1]) ?_
    (realCoordinate_continuousOn hp hc) (realCoordinate_injOn hp hc)
  rw [realCoordinate_zero]
  exact (coordinate_real_neg hp hc
    (negativeInterval_mem_source hp hc ⟨le_rfl,by linarith [hc.2.1]⟩)
    (neg_neg_of_pos hc.2.1)).le

def electrode0 (c : ℝ) (p : ℕ) : ℝ := realCoordinate c p (-cut c p 4)
def electrode1 (c : ℝ) (p : ℕ) : ℝ := realCoordinate c p (cut c p 2)
def electrode2 (c : ℝ) (p : ℕ) : ℝ := realCoordinate c p (cut c p 5)
def electrode3 {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ℝ :=
  realCoordinate c p (-alpha hp hc)

theorem physical_endpoints_mem_interval {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    -cut c p 4 ∈ Icc (-criticalValue c p) 0 ∧
      cut c p 2 ∈ Icc (-criticalValue c p) 0 ∧
      cut c p 5 ∈ Icc (-criticalValue c p) 0 ∧
      -alpha hp hc ∈ Icc (-criticalValue c p) 0 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := source_ports_ordered hp hc
  exact ⟨⟨h0.le,(h1.trans (h2.trans (h3.trans h4))).le⟩,
    ⟨(h0.trans h1).le,(h2.trans (h3.trans h4)).le⟩,
    ⟨(h0.trans (h1.trans h2)).le,(h3.trans h4).le⟩,
    ⟨(h0.trans (h1.trans (h2.trans h3))).le,h4.le⟩⟩

theorem electrodes_ordered {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    electrode0 c p < electrode1 c p ∧ electrode1 c p < electrode2 c p ∧
      electrode2 c p < electrode3 hp hc := by
  have hm := realCoordinate_strictMonoOn hp hc
  obtain ⟨h0,h1,h2,h3⟩ := physical_endpoints_mem_interval hp hc
  obtain ⟨_,h01,h12,h23,_⟩ := source_ports_ordered hp hc
  exact ⟨hm h0 h1 h01,hm h1 h2 h12,hm h2 h3 h23⟩

theorem electrode3_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : electrode3 hp hc < 0 :=
  coordinate_real_neg hp hc
    (negativeInterval_mem_source hp hc (physical_endpoints_mem_interval hp hc).2.2.2)
    (neg_neg_of_pos (alpha_pos hp hc))

theorem realCoordinate_image_Ioo {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {s t : ℝ} (hst : s < t)
    (hs : s ∈ Icc (-criticalValue c p) 0) (ht : t ∈ Icc (-criticalValue c p) 0) :
    realCoordinate c p '' Ioo s t = Ioo (realCoordinate c p s) (realCoordinate c p t) := by
  have hsub : Icc s t ⊆ Icc (-criticalValue c p) 0 := Icc_subset_Icc hs.1 ht.2
  exact ContinuousOn.image_Ioo_of_strictMonoOn hst.le
    ((realCoordinate_continuousOn hp hc).mono hsub)
    ((realCoordinate_strictMonoOn hp hc).mono hsub)

theorem coordinate_leftPort_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    coordinate c p '' leftPort c p =
      {z : ℂ | z.im = 0 ∧ z.re ∈ Ioo (electrode0 c p) (electrode1 c p)} := by
  have hi := realCoordinate_image_Ioo hp hc (source_ports_ordered hp hc).2.1
    (physical_endpoints_mem_interval hp hc).1 (physical_endpoints_mem_interval hp hc).2.1
  ext z
  constructor
  · rintro ⟨q,hq,rfl⟩
    have hqV := leftPort_subset_source hp hc hq
    have he : q = (q.re : ℂ) := by apply Complex.ext <;> simp [hq.1]
    refine ⟨coordinate_real_im hp hc hqV hq.1,?_⟩
    have h := mem_image_of_mem (realCoordinate c p) hq.2
    rw [hi] at h
    rw [he]
    exact h
  · intro hz
    have hz' : z.re ∈ realCoordinate c p '' Ioo (-cut c p 4) (cut c p 2) := by
      rw [hi]
      exact hz.2
    obtain ⟨x,hx,he⟩ := hz'
    have hxV : (x : ℂ) ∈ source c p := leftPort_subset_source hp hc ⟨rfl,hx⟩
    refine ⟨(x : ℂ),⟨rfl,hx⟩,?_⟩
    rw [coordinate_ofReal hp hc hxV,he]
    apply Complex.ext <;> simp [hz.1]

theorem coordinate_rightPort_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    coordinate c p '' rightPort hp hc =
      {z : ℂ | z.im = 0 ∧ z.re ∈ Ioo (electrode2 c p) (electrode3 hp hc)} := by
  have hi := realCoordinate_image_Ioo hp hc (source_ports_ordered hp hc).2.2.2.1
    (physical_endpoints_mem_interval hp hc).2.2.1 (physical_endpoints_mem_interval hp hc).2.2.2
  ext z
  constructor
  · rintro ⟨q,hq,rfl⟩
    have hqV := rightPort_subset_source hp hc hq
    have he : q = (q.re : ℂ) := by apply Complex.ext <;> simp [hq.1]
    refine ⟨coordinate_real_im hp hc hqV hq.1,?_⟩
    have h := mem_image_of_mem (realCoordinate c p) hq.2
    rw [hi] at h
    rw [he]
    exact h
  · intro hz
    have hz' : z.re ∈ realCoordinate c p '' Ioo (cut c p 5) (-alpha hp hc) := by
      rw [hi]
      exact hz.2
    obtain ⟨x,hx,he⟩ := hz'
    have hxV : (x : ℂ) ∈ source c p := rightPort_subset_source hp hc ⟨rfl,hx⟩
    refine ⟨(x : ℂ),⟨rfl,hx⟩,?_⟩
    rw [coordinate_ofReal hp hc hxV,he]
    apply Complex.ext <;> simp [hz.1]

def width {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ℝ :=
  SlitFourPointChart.width (electrode0 c p) (electrode1 c p) (electrode2 c p) (electrode3 hp hc)

def height {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ℝ :=
  SlitFourPointChart.height (electrode0 c p) (electrode1 c p) (electrode2 c p) (electrode3 hp hc)

theorem width_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : 0 < width hp hc :=
  SlitFourPointChart.width_pos (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2

theorem height_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : 0 < height hp hc :=
  SlitFourPointChart.height_pos (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2

private def inverseChart (C : CrestConformalModulus.ConformalChart) :
    CrestConformalModulus.ConformalChart where
  homeomorph := C.homeomorph.symm
  derivative := fun z => (C.derivative (C.homeomorph.symm z))⁻¹
  hasDeriv := fun _ hz => C.homeomorph.hasDerivAt_symm hz
    (C.derivative_ne_zero _ (C.homeomorph.map_target hz))
    (C.hasDeriv _ (C.homeomorph.map_target hz))
  derivative_continuous :=
    (C.derivative_continuous.comp C.homeomorph.continuousOn_symm
      (fun _ hz => C.homeomorph.map_target hz)).inv₀
        (fun _ hz => C.derivative_ne_zero _ (C.homeomorph.map_target hz))
  derivative_ne_zero := fun _ hz => inv_ne_zero
    (C.derivative_ne_zero _ (C.homeomorph.map_target hz))

private def composeCharts (C D : CrestConformalModulus.ConformalChart) :
    CrestConformalModulus.ConformalChart where
  homeomorph := C.homeomorph.trans D.homeomorph
  derivative := fun z => D.derivative (C.homeomorph z)*C.derivative z
  hasDeriv := fun z hz => (D.hasDeriv _ hz.2).comp z (C.hasDeriv z hz.1)
  derivative_continuous := (D.derivative_continuous.comp
    (C.homeomorph.continuousOn.mono inter_subset_left) (fun _ hz => hz.2)).mul
      (C.derivative_continuous.mono inter_subset_left)
  derivative_ne_zero := fun _ hz =>
    mul_ne_zero (D.derivative_ne_zero _ hz.2) (C.derivative_ne_zero _ hz.1)

private def planeRectangle {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    CrestConformalModulus.ConformalChart :=
  SlitFourPointChart.inverseConformal (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2

private def planeClosedInverse {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ℂ → ℂ :=
  SlitFourPointChart.closedInverse (electrode0 c p) (electrode1 c p)
    (electrode2 c p) (electrode3 hp hc)

private def planeClosedVelocity {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ℂ → ℂ :=
  SlitFourPointChart.closedVelocity (electrode0 c p) (electrode1 c p)
    (electrode2 c p) (electrode3 hp hc)

private theorem planeClosedInverse_continuousOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ContinuousOn (planeClosedInverse hp hc)
      (SlitCubicClosedChart.closedHorizontalBand (width hp hc) (height hp hc)) :=
  SlitFourPointChart.closedInverse_continuousOn (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2

private theorem planeClosedInverse_mem_upper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {ζ : ℂ} (hζ : ζ ∈ openRectangle (width hp hc) (height hp hc)) :
    planeClosedInverse hp hc ζ ∈ upper :=
  SlitFourPointChart.closedInverse_mem_upper (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2 hζ

private theorem planeClosedInverse_left_edge {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0) :
    (planeClosedInverse hp hc ((y : ℂ)*Complex.I)).im = 0 ∧
      (planeClosedInverse hp hc ((y : ℂ)*Complex.I)).re ∈ Ioo (electrode0 c p) (electrode1 c p) :=
  SlitFourPointChart.closedInverse_left_edge (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2 hy

private theorem planeClosedInverse_right_edge {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0) :
    (planeClosedInverse hp hc ((width hp hc : ℂ)+(y : ℂ)*Complex.I)).im = 0 ∧
      (planeClosedInverse hp hc ((width hp hc : ℂ)+(y : ℂ)*Complex.I)).re ∈
        Ioo (electrode2 c p) (electrode3 hp hc) :=
  SlitFourPointChart.closedInverse_right_edge (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2 hy

theorem coordinate_mem_upper_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    coordinate c p z ∈ upper ↔ z ∈ upperSource c p := by
  constructor
  · intro hj
    obtain ⟨q,hq,he⟩ := (coordinate_image_upperSource hp hc).symm ▸ hj
    have hqz := coordinate_injOn hp hc hq.1 hz he
    simpa only [hqz] using hq
  · exact coordinate_mem_upper hp hc

theorem upper_subset_coordinate_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : upper ⊆
      (ActualPairableCoordinate.conformalChart hp hc).homeomorph.target := by
  intro z hz
  obtain ⟨q,hq,rfl⟩ := (coordinate_image_upperSource hp hc).symm ▸ hz
  exact (ActualPairableCoordinate.conformalChart hp hc).homeomorph.map_source hq.1

theorem coordinate_inverse_mem_upperSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ upper) :
    (ActualPairableCoordinate.conformalChart hp hc).homeomorph.symm z ∈ upperSource c p := by
  obtain ⟨q,hq,rfl⟩ := (coordinate_image_upperSource hp hc).symm ▸ hz
  have he := (ActualPairableCoordinate.conformalChart hp hc).homeomorph.left_inv hq.1
  rw [ActualPairableCoordinate.conformalChart_apply] at he
  rwa [he]

theorem left_electrode_mem_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hz : z.im = 0 ∧ z.re ∈ Ioo (electrode0 c p) (electrode1 c p)) :
    z ∈ (ActualPairableCoordinate.conformalChart hp hc).homeomorph.target := by
  have hz' : z ∈ coordinate c p '' leftPort c p := by rw [coordinate_leftPort_image hp hc]; exact hz
  obtain ⟨q,hq,rfl⟩ := hz'
  exact (ActualPairableCoordinate.conformalChart hp hc).homeomorph.map_source
    (leftPort_subset_source hp hc hq)

theorem right_electrode_mem_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hz : z.im = 0 ∧ z.re ∈ Ioo (electrode2 c p) (electrode3 hp hc)) :
    z ∈ (ActualPairableCoordinate.conformalChart hp hc).homeomorph.target := by
  have hz' : z ∈ coordinate c p '' rightPort hp hc := by rw [coordinate_rightPort_image hp hc]; exact hz
  obtain ⟨q,hq,rfl⟩ := hz'
  exact (ActualPairableCoordinate.conformalChart hp hc).homeomorph.map_source
    (rightPort_subset_source hp hc hq)

theorem coordinate_inverse_mem_leftPort {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hz : z.im = 0 ∧ z.re ∈ Ioo (electrode0 c p) (electrode1 c p)) :
    (ActualPairableCoordinate.conformalChart hp hc).homeomorph.symm z ∈ leftPort c p := by
  have hz' : z ∈ coordinate c p '' leftPort c p := by rw [coordinate_leftPort_image hp hc]; exact hz
  obtain ⟨q,hq,rfl⟩ := hz'
  have he := (ActualPairableCoordinate.conformalChart hp hc).homeomorph.left_inv
    (leftPort_subset_source hp hc hq)
  rw [ActualPairableCoordinate.conformalChart_apply] at he
  rwa [he]

theorem coordinate_inverse_mem_rightPort {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hz : z.im = 0 ∧ z.re ∈ Ioo (electrode2 c p) (electrode3 hp hc)) :
    (ActualPairableCoordinate.conformalChart hp hc).homeomorph.symm z ∈ rightPort hp hc := by
  have hz' : z ∈ coordinate c p '' rightPort hp hc := by rw [coordinate_rightPort_image hp hc]; exact hz
  obtain ⟨q,hq,rfl⟩ := hz'
  have he := (ActualPairableCoordinate.conformalChart hp hc).homeomorph.left_inv
    (rightPort_subset_source hp hc hq)
  rw [ActualPairableCoordinate.conformalChart_apply] at he
  rwa [he]

private theorem planeClosedInverse_mem_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {ζ : ℂ}
    (hζ : ζ ∈ SlitCubicClosedChart.closedHorizontalBand (width hp hc) (height hp hc)) :
    planeClosedInverse hp hc ζ ∈
      (ActualPairableCoordinate.conformalChart hp hc).homeomorph.target := by
  by_cases h0 : ζ.re = 0
  · have he : ζ = (ζ.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [h0]
    rw [he]
    exact left_electrode_mem_target hp hc (planeClosedInverse_left_edge hp hc hζ.2.2)
  by_cases hB : ζ.re = width hp hc
  · have he : ζ = (width hp hc : ℂ)+(ζ.im : ℂ)*Complex.I := by
      apply Complex.ext <;> simp [hB]
    rw [he]
    exact right_electrode_mem_target hp hc (planeClosedInverse_right_edge hp hc hζ.2.2)
  exact upper_subset_coordinate_target hp hc (planeClosedInverse_mem_upper hp hc
    ⟨lt_of_le_of_ne hζ.1 (Ne.symm h0),lt_of_le_of_ne hζ.2.1 hB,hζ.2.2⟩)

/-- The actual rectangle inverse, including its two physical endpoint edges. -/
def closedInverse {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) (ζ : ℂ) : ℂ :=
  (ActualPairableCoordinate.conformalChart hp hc).homeomorph.symm (planeClosedInverse hp hc ζ)

theorem closedInverse_mem_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {ζ : ℂ}
    (hζ : ζ ∈ SlitCubicClosedChart.closedHorizontalBand (width hp hc) (height hp hc)) :
    closedInverse hp hc ζ ∈ source c p :=
  (ActualPairableCoordinate.conformalChart hp hc).homeomorph.map_target
    (planeClosedInverse_mem_target hp hc hζ)

theorem closedInverse_continuousOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ContinuousOn (closedInverse hp hc)
      (SlitCubicClosedChart.closedHorizontalBand (width hp hc) (height hp hc)) :=
  (ActualPairableCoordinate.conformalChart hp hc).homeomorph.continuousOn_symm.comp
    (planeClosedInverse_continuousOn hp hc) (fun _ hz => planeClosedInverse_mem_target hp hc hz)

theorem closedInverse_mem_upperSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {ζ : ℂ} (hζ : ζ ∈ openRectangle (width hp hc) (height hp hc)) :
    closedInverse hp hc ζ ∈ upperSource c p :=
  coordinate_inverse_mem_upperSource hp hc (planeClosedInverse_mem_upper hp hc hζ)

theorem closedInverse_left_edge {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0) :
    closedInverse hp hc ((y : ℂ)*Complex.I) ∈ leftPort c p :=
  coordinate_inverse_mem_leftPort hp hc (planeClosedInverse_left_edge hp hc hy)

theorem closedInverse_right_edge {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {y : ℝ} (hy : y ∈ Ioo (-height hp hc) 0) :
    closedInverse hp hc ((width hp hc : ℂ)+(y : ℂ)*Complex.I) ∈ rightPort hp hc :=
  coordinate_inverse_mem_rightPort hp hc (planeClosedInverse_right_edge hp hc hy)

theorem closedInverse_mem_closedUpper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {ζ : ℂ}
    (hζ : ζ ∈ SlitCubicClosedChart.closedHorizontalBand (width hp hc) (height hp hc)) :
    0 ≤ (closedInverse hp hc ζ).im := by
  by_cases h0 : ζ.re = 0
  · have he : ζ = (ζ.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [h0]
    rw [he,(closedInverse_left_edge hp hc hζ.2.2).1]
  by_cases hB : ζ.re = width hp hc
  · have he : ζ = (width hp hc : ℂ)+(ζ.im : ℂ)*Complex.I := by
      apply Complex.ext <;> simp [hB]
    rw [he,(closedInverse_right_edge hp hc hζ.2.2).1]
  exact (closedInverse_mem_upperSource hp hc
    ⟨lt_of_le_of_ne hζ.1 (Ne.symm h0),lt_of_le_of_ne hζ.2.1 hB,hζ.2.2⟩).2.le

theorem closedInverse_injOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : InjOn (closedInverse hp hc)
      (SlitCubicClosedChart.closedHorizontalBand (width hp hc) (height hp hc)) := by
  intro ζ hζ η hη he
  apply SlitFourPointChart.closedInverse_injOn (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2 hζ hη
  exact (ActualPairableCoordinate.conformalChart hp hc).homeomorph.symm.injOn
    (planeClosedInverse_mem_target hp hc hζ) (planeClosedInverse_mem_target hp hc hη) he

def closedVelocity {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) (ζ : ℂ) : ℂ :=
  ((ActualPairableCoordinate.conformalChart hp hc).derivative (closedInverse hp hc ζ))⁻¹ *
    planeClosedVelocity hp hc ζ

theorem closedVelocity_continuousOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ContinuousOn (closedVelocity hp hc)
      (SlitCubicClosedChart.closedHorizontalBand (width hp hc) (height hp hc)) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.inv₀
    · exact (ActualPairableCoordinate.conformalChart hp hc).derivative_continuous.comp
        (closedInverse_continuousOn hp hc) (fun _ hz => closedInverse_mem_source hp hc hz)
    · intro ζ hζ
      exact (ActualPairableCoordinate.conformalChart hp hc).derivative_ne_zero _
        (closedInverse_mem_source hp hc hζ)
  · exact SlitFourPointChart.closedVelocity_continuousOn (electrodes_ordered hp hc).1
      (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2

theorem closedInverse_hasDerivAt {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {ζ : ℂ} (hζ : ζ ∈ openRectangle (width hp hc) (height hp hc)) :
    HasDerivAt (closedInverse hp hc) (closedVelocity hp hc ζ) ζ := by
  exact ((inverseChart (ActualPairableCoordinate.conformalChart hp hc)).hasDeriv _
    (planeClosedInverse_mem_target hp hc
      (SlitCubicClosedChart.openRectangle_subset_closedHorizontalBand _ _ hζ))).comp ζ
        (SlitFourPointChart.closedInverse_hasDerivAt (electrodes_ordered hp hc).1
          (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2 hζ)

def inverseConformal {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    CrestConformalModulus.ConformalChart :=
  composeCharts (planeRectangle hp hc) (inverseChart (ActualPairableCoordinate.conformalChart hp hc))

@[simp] theorem inverseConformal_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (inverseConformal hp hc).homeomorph.source =
      openRectangle (width hp hc) (height hp hc) := by
  change (planeRectangle hp hc).homeomorph.source ∩
    (planeRectangle hp hc).homeomorph ⁻¹'
      (ActualPairableCoordinate.conformalChart hp hc).homeomorph.target = _
  rw [show (planeRectangle hp hc).homeomorph.source = openRectangle (width hp hc) (height hp hc)
    from SlitFourPointChart.inverseConformal_source (electrodes_ordered hp hc).1
      (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2]
  apply inter_eq_left.mpr
  intro ζ hζ
  apply upper_subset_coordinate_target hp hc
  have hζ' : ζ ∈ (planeRectangle hp hc).homeomorph.source := by
    simpa only [planeRectangle,SlitFourPointChart.inverseConformal_source,width,height] using hζ
  have hm := (planeRectangle hp hc).homeomorph.map_source hζ'
  rwa [show (planeRectangle hp hc).homeomorph.target = upper from
    SlitFourPointChart.inverseConformal_target (electrodes_ordered hp hc).1
      (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2] at hm

@[simp] theorem inverseConformal_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (inverseConformal hp hc).homeomorph.target = upperSource c p := by
  change (ActualPairableCoordinate.conformalChart hp hc).homeomorph.source ∩
    (ActualPairableCoordinate.conformalChart hp hc).homeomorph ⁻¹'
      (planeRectangle hp hc).homeomorph.target = _
  rw [show (planeRectangle hp hc).homeomorph.target = upper from
    SlitFourPointChart.inverseConformal_target (electrodes_ordered hp hc).1
      (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2]
  change source c p ∩ coordinate c p ⁻¹' upper = upperSource c p
  ext z
  exact ⟨fun hz => (coordinate_mem_upper_iff hp hc hz.1).mp hz.2,
    fun hz => ⟨hz.1,coordinate_mem_upper hp hc hz⟩⟩

theorem inverseConformal_target_subset_upper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (inverseConformal hp hc).homeomorph.target ⊆ upper := by
  rw [inverseConformal_target]
  exact inter_subset_right

@[simp] theorem inverseConformal_apply {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (ζ : ℂ) : (inverseConformal hp hc).homeomorph ζ =
      (ActualPairableCoordinate.conformalChart hp hc).homeomorph.symm
        ((SlitFourPointChart.inverseConformal (electrodes_ordered hp hc).1
          (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2).homeomorph ζ) := rfl

theorem closedInverse_eq_inverseConformal {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {ζ : ℂ} (hζ : ζ ∈ openRectangle (width hp hc) (height hp hc)) :
    closedInverse hp hc ζ = (inverseConformal hp hc).homeomorph ζ := by
  change (ActualPairableCoordinate.conformalChart hp hc).homeomorph.symm
      (planeClosedInverse hp hc ζ) =
    (ActualPairableCoordinate.conformalChart hp hc).homeomorph.symm
      ((planeRectangle hp hc).homeomorph ζ)
  congr 1
  exact SlitFourPointChart.closedInverse_eq_inverseConformal (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2 hζ

theorem inverseConformal_derivative {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {ζ : ℂ} (hζ : ζ ∈ openRectangle (width hp hc) (height hp hc)) :
    (inverseConformal hp hc).derivative ζ = closedVelocity hp hc ζ := by
  change ((ActualPairableCoordinate.conformalChart hp hc).derivative
      ((inverseConformal hp hc).homeomorph ζ))⁻¹ * (planeRectangle hp hc).derivative ζ = _
  rw [← closedInverse_eq_inverseConformal hp hc hζ]
  change _ * (planeRectangle hp hc).derivative ζ = _ * planeClosedVelocity hp hc ζ
  congr 1
  exact SlitFourPointChart.inverseConformal_derivative (electrodes_ordered hp hc).1
    (electrodes_ordered hp hc).2.1 (electrodes_ordered hp hc).2.2 hζ

end
end ActualPairableClosedChart
