import ThreeReturnDegree
import ThreeReturnDomain
import CrestConformalModulus
import ActualCrestPaths

/-!
# An actual conformal chart for the fourfold crest image

The source is an open subset of the complex plane defined by the complete
normalized polynomial and its first three iterates.  A tilted half-plane
at the first image contains both ends of each closed upper q-side arc.
Exact signed fibers prove injectivity on the whole open source, and the
complete diagonal divided difference proves that its derivative never
vanishes there.  The inverse chart is consequently constructed from the
actual polynomial, rather than supplied as a geometric hypothesis.
-/

namespace ActualCrestConformalChart

open Set Function
open LimitingCrestQuadraticReturn QuadraticCrestDividedDifference
open NearTwoTip NearTwoShooting ThreeReturnDegree ThreeReturnDomain
open CrestConformalModulus
open LimitingCrest GlobalCrestCrossing ActualCrestPaths

noncomputable section

/-- An open common chart for the upper q-side leaves, including their
real initial ends and their imaginary-axis crossing ends. -/
def chartSource (c : ℝ) (p : ℕ) : Set ℂ :=
  {z | (∀ m ≤ 3, ‖((normalizedReturn c p)^[m]) z‖ < 23/20) ∧
    z.re < 0 ∧
    0 < (normalizedReturn c p z).re + (normalizedReturn c p z).im ∧
    0 < (((normalizedReturn c p)^[2]) z).re ∧
    (((normalizedReturn c p)^[3]) z).re < 0}

private theorem return_continuous (c : ℝ) (p : ℕ) :
    Continuous (normalizedReturn c p) := by
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  exact ((hf.iterate p).comp (continuous_const.mul continuous_id)).div_const _

theorem chartSource_isOpen (c : ℝ) (p : ℕ) : IsOpen (chartSource c p) := by
  have hH := return_continuous c p
  have hn : IsOpen (⋂ m : Fin 4,
      {z : ℂ | ‖((normalizedReturn c p)^[m.val]) z‖ < 23/20}) :=
    isOpen_iInter_of_finite (fun m => isOpen_lt (hH.iterate m.val).norm continuous_const)
  have hn' : IsOpen {z : ℂ |
      ∀ m ≤ 3, ‖((normalizedReturn c p)^[m]) z‖ < 23/20} := by
    convert hn using 1
    ext z
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro h m
      exact h m.val (by have := m.isLt; omega)
    · intro h m hm
      exact h ⟨m, by omega⟩
  exact hn'.inter ((isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const
      ((Complex.continuous_re.comp hH).add (Complex.continuous_im.comp hH))).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp (hH.iterate 2))).inter
        (isOpen_lt (Complex.continuous_re.comp (hH.iterate 3)) continuous_const))))

private theorem actual_collision {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20)
    (he : normalizedReturn c p z = normalizedReturn c p w) : z = w ∨ z = -w := by
  have hb := parameter_band hp hc.1
  have hd : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  exact (normalized_return_collision_iff c p (by omega)
    ⟨hb.1, by linarith [hb.2]⟩ hc.2.1 hd hc.2.2.2.1 hz hw).mp he

/-- Every collision of the literal fourth return is excluded on the
whole open chart, including across different circular leaves. -/
theorem actual_fourfold_injective {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    InjOn ((normalizedReturn c p)^[4]) (chartSource c p) := by
  intro z hz w hw he
  have h3 : ((normalizedReturn c p)^[3]) z =
      ((normalizedReturn c p)^[3]) w := by
    rcases actual_collision hp hc ((hz.1 3 (by omega)).le)
      ((hw.1 3 (by omega)).le) he with h | h
    · exact h
    · have hr := congrArg Complex.re h
      simp only [Complex.neg_re] at hr
      linarith [hz.2.2.2.2, hw.2.2.2.2]
  have h2 : ((normalizedReturn c p)^[2]) z =
      ((normalizedReturn c p)^[2]) w := by
    rcases actual_collision hp hc ((hz.1 2 (by omega)).le)
      ((hw.1 2 (by omega)).le) h3 with h | h
    · exact h
    · have hr := congrArg Complex.re h
      simp only [Complex.neg_re] at hr
      linarith [hz.2.2.2.1, hw.2.2.2.1]
  have h1 : normalizedReturn c p z = normalizedReturn c p w := by
    rcases actual_collision hp hc
      (by simpa using (hz.1 1 (by omega)).le)
      (by simpa using (hw.1 1 (by omega)).le) h2 with h | h
    · exact h
    · have hr := congrArg Complex.re h
      have hi := congrArg Complex.im h
      simp only [Complex.neg_re] at hr
      simp only [Complex.neg_im] at hi
      linarith [hz.2.2.1, hw.2.2.1]
  rcases actual_collision hp hc
    (by simpa using (hz.1 0 (by omega)).le)
    (by simpa using (hw.1 0 (by omega)).le) h1 with h | h
  · exact h
  · have hr := congrArg Complex.re h
    simp only [Complex.neg_re] at hr
    linarith [hz.2.1, hw.2.1]

/-- The derivative retains every term in the complete normalized return. -/
def returnDerivative (c : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  2*z*normalizedSecant c p z z

def fourfoldDerivative (c : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  returnDerivative c p (((normalizedReturn c p)^[3]) z) *
    (returnDerivative c p (((normalizedReturn c p)^[2]) z) *
      (returnDerivative c p (normalizedReturn c p z) * returnDerivative c p z))

private theorem diagonal_evenSecant_continuous (c : ℝ) (n : ℕ) :
    Continuous (fun z : ℂ => evenSecant c n z z) := by
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  induction n with
  | zero => simpa only [evenSecant] using (continuous_const : Continuous (fun _ : ℂ => (1 : ℂ)))
  | succ n ih =>
    exact ((hf.iterate (n+1)).add (hf.iterate (n+1))).mul ih

theorem returnDerivative_continuous (c : ℝ) (p : ℕ) :
    Continuous (returnDerivative c p) := by
  exact (continuous_const.mul continuous_id).mul
    (continuous_const.mul ((diagonal_evenSecant_continuous c (p-1)).comp
      (continuous_const.mul continuous_id)))

theorem fourfoldDerivative_continuous (c : ℝ) (p : ℕ) :
    Continuous (fourfoldDerivative c p) := by
  have hH := return_continuous c p
  have hD := returnDerivative_continuous c p
  exact (hD.comp (hH.iterate 3)).mul
    ((hD.comp (hH.iterate 2)).mul ((hD.comp hH).mul hD))

theorem fourfold_hasDerivAt (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0) (z : ℂ) :
    HasDerivAt ((normalizedReturn c p)^[4]) (fourfoldDerivative c p z) z := by
  have h0 := normalized_return_hasDerivAt c p hp hd z
  have h1 := normalized_return_hasDerivAt c p hp hd (normalizedReturn c p z)
  have h2 := normalized_return_hasDerivAt c p hp hd (((normalizedReturn c p)^[2]) z)
  have h3 := normalized_return_hasDerivAt c p hp hd (((normalizedReturn c p)^[3]) z)
  exact h3.comp z (h2.comp z (h1.comp z h0))

private theorem returnDerivative_ne_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20) (hz0 : z ≠ 0) :
    returnDerivative c p z ≠ 0 := by
  have hb := parameter_band hp hc.1
  have hd : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have hn := (normalizedSecant_norm_bounds c p (by omega)
    ⟨hb.1, by linarith [hb.2]⟩ hc.2.1 hd hc.2.2.2.1 hz hz).1
  have hs : normalizedSecant c p z z ≠ 0 := by
    intro he
    rw [he, norm_zero] at hn
    norm_num at hn
  exact mul_ne_zero (mul_ne_zero (by norm_num) hz0) hs

/-- No critical point of the fourth return occurs anywhere in the
open chart; each of its four complete derivative factors is nonzero. -/
theorem fourfoldDerivative_ne_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ chartSource c p) :
    fourfoldDerivative c p z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro he
    have hh := hz.2.1
    simp only [he, Complex.zero_re, lt_self_iff_false] at hh
  have hz1 : normalizedReturn c p z ≠ 0 := by
    intro he
    have hh := hz.2.2.1
    simp only [he, Complex.zero_re, Complex.zero_im, add_zero, lt_self_iff_false] at hh
  have hz2 : ((normalizedReturn c p)^[2]) z ≠ 0 := by
    intro he
    have hh := hz.2.2.2.1
    simp only [he, Complex.zero_re, lt_self_iff_false] at hh
  have hz3 : ((normalizedReturn c p)^[3]) z ≠ 0 := by
    intro he
    have hh := hz.2.2.2.2
    simp only [he, Complex.zero_re, lt_self_iff_false] at hh
  exact mul_ne_zero (returnDerivative_ne_zero hp hc (hz.1 3 (by omega)).le hz3)
    (mul_ne_zero (returnDerivative_ne_zero hp hc (hz.1 2 (by omega)).le hz2)
      (mul_ne_zero (returnDerivative_ne_zero hp hc
        (by simpa using (hz.1 1 (by omega)).le) hz1)
        (returnDerivative_ne_zero hp hc (by simpa using (hz.1 0 (by omega)).le) hz0)))

/-- The inverse is obtained from injectivity and openness of the actual
polynomial, on the proved open source. -/
def chart {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ConformalChart where
  homeomorph := OpenPartialHomeomorph.ofContinuousOpen
    ((actual_fourfold_injective hp hc).toPartialEquiv
      ((normalizedReturn c p)^[4]) (chartSource c p))
    ((return_continuous c p).iterate 4).continuousOn
    (by
      have ho := normalized_return_open c p hc.2.1.ne'
      exact ho.comp (ho.comp (ho.comp ho)))
    (chartSource_isOpen c p)
  derivative := fourfoldDerivative c p
  hasDeriv := fun z _ => fourfold_hasDerivAt c p (by omega) hc.2.1.ne' z
  derivative_continuous := (fourfoldDerivative_continuous c p).continuousOn
  derivative_ne_zero := fun _ hz => fourfoldDerivative_ne_zero hp hc hz

theorem chart_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    (chart hp hc).homeomorph.source = chartSource c p := rfl

theorem chart_apply {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) (z : ℂ) :
    (chart hp hc).homeomorph z = ((normalizedReturn c p)^[4]) z := rfl

/-- The complete closed q-side circular trace lies in the constructed
open chart.  The terminal point is retained even though its first image
has zero real part. -/
theorem circlePoint_mem_chartSource {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000))
    (hu : u ∈ Icc (realAngle F s) 1) :
    circlePoint s u ∈ chartSource c p := by
  have hsR : s ∈ Radius := ⟨hs.1, by linarith [hs.2]⟩
  have hu0 : u ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [(realAngle_mem F s).1, hu.1], hu.2⟩
  have hz := circlePoint_initialDisk hs hu0
  have hb := hS (circlePoint s u) hz
  exact ⟨fun m hm => hb.1 m (by omega), circlePoint_re_neg hsR hu0,
    closed_q_side_first_sum_pos hp hc F hsR hu, hb.2.1, hb.2.2⟩

theorem qArc_mem_chartSource {p : ℕ} (hp : 17 ≤ p) {c s t : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (ht : t ∈ Icc (0 : ℝ) 1) :
    qArc F s t ∈ (chart hp hc).homeomorph.source :=
  circlePoint_mem_chartSource hp hc hS F hs (qArc_parameter_mem_closed F ht)

/-- Distinct input radii remain distinct throughout the complete fourth
images.  A continuum of leaves therefore shares one injective chart;
leafwise univalence has not been substituted for joint univalence. -/
theorem fourth_image_radius_eq {p : ℕ} (hp : 17 ≤ p) {c s r u v : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000))
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000))
    (hu : u ∈ Icc (realAngle F s) 1) (hv : v ∈ Icc (realAngle F r) 1)
    (he : ((normalizedReturn c p)^[4]) (circlePoint s u) =
      ((normalizedReturn c p)^[4]) (circlePoint r v)) : s = r := by
  have hz := actual_fourfold_injective hp hc
    (circlePoint_mem_chartSource hp hc hS F hs hu)
    (circlePoint_mem_chartSource hp hc hS F hr hv) he
  have hu0 : u ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [(realAngle_mem F s).1, hu.1], hu.2⟩
  have hv0 : v ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [(realAngle_mem F r).1, hv.1], hv.2⟩
  have hnorm := congrArg (fun z : ℂ => ‖z+(3/4 : ℂ)‖) hz
  rwa [circle_radius (by linarith [hs.1]) hu0,
    circle_radius (by linarith [hr.1]) hv0] at hnorm

end
end ActualCrestConformalChart
