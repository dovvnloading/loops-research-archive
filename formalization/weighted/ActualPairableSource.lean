import ActualPairableSourceBounds
import ThreeReturnParent
import CrestConformalModulus
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# The complete archived upper source of an actual tip

The source is the existing component of the complete polynomial pullback
of the physical disk of radius `2⁻ᵖ`.  A whole-circle barrier and the
complete divided difference identify its two sheets.  The upper sheet
maps bijectively to the disk slit from the left boundary to the actual
critical value, and the resulting conformal chart has an actual inverse.
-/

namespace ActualPairableSource

open Set Function Metric Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open QuadraticCrestDividedDifference ActualPairableSourceBounds
open LoopsQuadraticCylinderCensus ThreeReturnDomain ThreeReturnDegree

noncomputable section

def radius (p : ℕ) : ℝ := (1/2 : ℝ)^p

def returnMap (c : ℝ) (p : ℕ) : ℂ → ℂ := (quadraticMap c)^[p]

def source (c : ℝ) (p : ℕ) : Set ℂ := ThreeReturnParent.archivedParentSource c p

def upperSource (c : ℝ) (p : ℕ) : Set ℂ := source c p ∩ {z | 0 < z.im}

def slitTarget (c : ℝ) (p : ℕ) : Set ℂ :=
  ball 0 (radius p) ∩ {w | criticalValue c p < w.re ∨ w.im ≠ 0}

def derivative (c : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  2 * z * evenSecant c (p-1) z z

theorem radius_pos (p : ℕ) : 0 < radius p := by unfold radius; positivity

theorem radius_eq_archived {p : ℕ} (hp : 17 ≤ p) :
    radius p = ThreeReturnParent.archivedTargetRadius p := by
  simp [radius, ThreeReturnParent.archivedTargetRadius, show p ≠ 3 by omega]

theorem source_eq_component {p : ℕ} (hp : 17 ≤ p) (c : ℝ) :
    source c p = connectedComponentIn (returnMap c p ⁻¹' ball 0 (radius p)) 0 := by
  rw [radius_eq_archived hp]
  rfl

theorem returnMap_continuous (c : ℝ) (p : ℕ) : Continuous (returnMap c p) :=
  (quadratic_iterate_proper (c : ℂ) p).continuous

theorem returnMap_open (c : ℝ) (p : ℕ) : IsOpenMap (returnMap c p) :=
  quadratic_iterate_open (c : ℂ) p

@[simp] theorem returnMap_zero (c : ℝ) (p : ℕ) :
    returnMap c p 0 = (criticalValue c p : ℂ) :=
  ThreeReturnParent.quadratic_iterate_zero c p

theorem returnMap_neg (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    returnMap c p (-z) = returnMap c p z := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  simp only [returnMap, iterate_succ_apply, quadraticMap, neg_sq]

theorem returnMap_conj (c : ℝ) (p : ℕ) (z : ℂ) :
    returnMap c p (star z) = star (returnMap c p z) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [returnMap,iterate_succ_apply']
    change quadraticMap c (returnMap c p (star z)) = star (quadraticMap c (returnMap c p z))
    rw [ih]
    simp [quadraticMap]

theorem criticalValue_lt_radius {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : criticalValue c p < radius p := by
  have hr := radius_pos p
  have hsmall : radius p ≤ (1/2 : ℝ)^17 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  have hs : scale p = (radius p)^2 := by
    simp only [scale, radius, pow_two, ← mul_pow]
    norm_num
  have hd := hc.2.2.1
  rw [hs] at hd
  norm_num at hsmall
  nlinarith

theorem zero_mem_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (0 : ℂ) ∈ source c p := by
  rw [source_eq_component hp]
  apply mem_connectedComponentIn
  simpa [returnMap_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc.2.1] using
    criticalValue_lt_radius hp hc

theorem source_isOpen {p : ℕ} (hp : 17 ≤ p) (c : ℝ) : IsOpen (source c p) := by
  rw [source_eq_component hp]
  exact (isOpen_ball.preimage (returnMap_continuous c p)).connectedComponentIn

theorem source_isConnected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsConnected (source c p) := by
  refine ⟨⟨0,zero_mem_source hp hc⟩,?_⟩
  rw [source_eq_component hp]
  exact isPreconnected_connectedComponentIn

theorem source_closure_inside {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : closure (source c p) ⊆ ball 0 (radius p) := by
  rw [source_eq_component hp]
  exact (component_closure_inside_barrier (returnMap c p) (returnMap_continuous c p)
    (radius p) (radius p) (radius_pos p)
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc.2.1] using
      criticalValue_lt_radius hp hc)
    (fun z hz => archived_boundary_barrier hp hc hz)).1

theorem source_compact_closure {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsCompact (closure (source c p)) := by
  exact (isCompact_closedBall (0 : ℂ) (radius p)).of_isClosed_subset isClosed_closure
    ((source_closure_inside hp hc).trans ball_subset_closedBall)

theorem norm_lt_radius_of_mem_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) : ‖z‖ < radius p := by
  simpa using source_closure_inside hp hc (subset_closure hz)

theorem returnMap_mem_ball {p : ℕ} (hp : 17 ≤ p) {c : ℝ} {z : ℂ}
    (hz : z ∈ source c p) : returnMap c p z ∈ ball 0 (radius p) := by
  rw [source_eq_component hp] at hz
  exact connectedComponentIn_subset (returnMap c p ⁻¹' ball 0 (radius p)) 0 hz

/-- The complete actual component covers the whole physical target disk. -/
theorem returnMap_image_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : returnMap c p '' source c p = ball 0 (radius p) := by
  rw [source_eq_component hp]
  exact localized_component_image (returnMap c p)
    (returnMap c p ⁻¹' ball 0 (radius p)) (ball 0 (radius p))
    (returnMap_open c p) (quadratic_iterate_proper (c : ℂ) p).isClosedMap
    (isOpen_ball.preimage (returnMap_continuous c p))
    (convex_ball (0 : ℂ) (radius p)).isPreconnected
    (fun _ hz => hz) (fun _ hz => hz.2) 0
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc.2.1] using
      criticalValue_lt_radius hp hc)

theorem source_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) : -z ∈ source c p := by
  have hconn : IsPreconnected ((fun z : ℂ => -z) '' source c p) :=
    (source_isConnected hp hc).isPreconnected.image _ continuous_neg.continuousOn
  have hhit : (0 : ℂ) ∈ (fun z : ℂ => -z) '' source c p :=
    ⟨0, zero_mem_source hp hc, neg_zero⟩
  have hsub : (fun z : ℂ => -z) '' source c p ⊆ returnMap c p ⁻¹' ball 0 (radius p) := by
    rintro _ ⟨w,hw,rfl⟩
    change returnMap c p (-w) ∈ ball 0 (radius p)
    rw [returnMap_neg c (by omega)]
    exact returnMap_mem_ball hp hw
  rw [source_eq_component hp]
  exact hconn.subset_connectedComponentIn hhit hsub ⟨z,hz,rfl⟩

theorem source_conj {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) : star z ∈ source c p := by
  have hconn : IsPreconnected (star '' source c p) :=
    (source_isConnected hp hc).isPreconnected.image _ continuous_star.continuousOn
  have hhit : (0 : ℂ) ∈ star '' source c p := ⟨0,zero_mem_source hp hc,star_zero _⟩
  have hsub : star '' source c p ⊆ returnMap c p ⁻¹' ball 0 (radius p) := by
    rintro _ ⟨w,hw,rfl⟩
    change returnMap c p (star w) ∈ ball 0 (radius p)
    rw [returnMap_conj,mem_ball_zero_iff,norm_star]
    exact mem_ball_zero_iff.mp (returnMap_mem_ball hp hw)
  rw [source_eq_component hp]
  exact hconn.subset_connectedComponentIn hhit hsub ⟨z,hz,rfl⟩

/-- The only branched fiber is the actual critical value; every other
target point has exactly two points in the archived component. -/
theorem returnMap_fiber_ncard {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {w : ℂ} (hw : w ∈ ball 0 (radius p)) :
    {z : ℂ | z ∈ source c p ∧ returnMap c p z = w}.ncard =
      if w = (criticalValue c p : ℂ) then 1 else 2 := by
  have hsurj : SurjOn (returnMap c p) (source c p) (ball 0 (radius p)) := by
    rw [SurjOn,returnMap_image_source hp hc]
  have h := fiber_ncard (returnMap c p) (source c p) (ball 0 (radius p))
    (zero_mem_source hp hc)
    (fun hz hw => archived_collision_iff hp hc
      (norm_lt_radius_of_mem_source hp hc hz).le (norm_lt_radius_of_mem_source hp hc hw).le)
    (fun _ hz => source_neg hp hc hz) hsurj hw
  simpa only [returnMap_zero] using h

/-- Within the physical control disk, no further source component is missed. -/
theorem mem_source_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ radius p) :
    z ∈ source c p ↔ returnMap c p z ∈ ball 0 (radius p) := by
  refine ⟨returnMap_mem_ball hp,?_⟩
  intro hfz
  obtain ⟨w,hw,he⟩ := (show SurjOn (returnMap c p) (source c p) (ball 0 (radius p)) by
    rw [SurjOn,returnMap_image_source hp hc]) hfz
  rcases (archived_collision_iff hp hc (norm_lt_radius_of_mem_source hp hc hw).le hz).mp he with he | he
  · exact he ▸ hw
  · have hz' : z = -w := by rw [he,neg_neg]
    rw [hz']
    exact source_neg hp hc hw

theorem upperSource_isOpen {p : ℕ} (hp : 17 ≤ p) (c : ℝ) :
    IsOpen (upperSource c p) :=
  (source_isOpen hp c).inter (isOpen_lt continuous_const Complex.continuous_im)

theorem returnMap_injOn_upperSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : InjOn (returnMap c p) (upperSource c p) := by
  intro z hz w hw he
  rcases (archived_collision_iff hp hc
    (norm_lt_radius_of_mem_source hp hc hz.1).le
    (norm_lt_radius_of_mem_source hp hc hw.1).le).mp he with he | he
  · exact he
  · have hi := congrArg Complex.im he
    simp only [Complex.neg_im] at hi
    have hz' : 0 < z.im := hz.2
    have hw' : 0 < w.im := hw.2
    linarith

private theorem returnMap_difference_zero (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    returnMap c p z - (criticalValue c p : ℂ) = z^2 * evenSecant c (p-1) z 0 := by
  have h := iterate_difference c (p-1) z 0
  rw [Nat.sub_add_cancel hp] at h
  change returnMap c p z - returnMap c p 0 = _ at h
  simpa only [zero_pow (by norm_num : 2 ≠ 0),sub_zero,returnMap_zero] using h

theorem returnMap_real_of_real (c : ℝ) (p : ℕ) {z : ℂ} (hz : z.im = 0) :
    (returnMap c p z).im = 0 := by
  have he : star z = z := by apply Complex.ext <;> simp [hz]
  have h := congrArg Complex.im (returnMap_conj c p z)
  rw [he] at h
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

/-- Every real point of the actual source maps to the critical value or its left. -/
theorem returnMap_re_le_of_real {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) (him : z.im = 0) :
    (returnMap c p z).re ≤ criticalValue c p := by
  have hs := evenSecant_re_neg hp hc (norm_lt_radius_of_mem_source hp hc hz).le
    (show ‖(0 : ℂ)‖ ≤ (1/2 : ℝ)^p by simp)
  have h := congrArg Complex.re (returnMap_difference_zero c (p := p) (by omega) z)
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,pow_two,
    Complex.mul_im,him,mul_zero,zero_mul,sub_zero,add_zero] at h
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z.re) hs.le]

/-- A real image of the upper sheet is strictly to the right of the critical value. -/
theorem criticalValue_lt_returnMap_re_of_upper_real {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ upperSource c p)
    (him : (returnMap c p z).im = 0) : criticalValue c p < (returnMap c p z).re := by
  have hn := (norm_lt_radius_of_mem_source hp hc hz.1).le
  have hF : returnMap c p (star z) = returnMap c p z := by
    rw [returnMap_conj]
    apply Complex.ext <;> simp [him]
  have hconjn : ‖star z‖ ≤ (1/2 : ℝ)^p := by simpa only [norm_star,radius] using hn
  have hre : z.re = 0 := by
    rcases (archived_collision_iff hp hc hn hconjn).mp hF.symm with he | he
    · have hi := congrArg Complex.im he
      simp only [Complex.star_def,Complex.conj_im] at hi
      have hz' : 0 < z.im := hz.2
      linarith
    · have hr := congrArg Complex.re he
      simp only [Complex.neg_re,Complex.star_def,Complex.conj_re] at hr
      linarith
  have hs := evenSecant_re_neg hp hc hn
    (show ‖(0 : ℂ)‖ ≤ (1/2 : ℝ)^p by simp)
  have h := congrArg Complex.re (returnMap_difference_zero c (p := p) (by omega) z)
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,pow_two,
    Complex.mul_im,hre,mul_zero,zero_mul,sub_zero,add_zero,zero_sub] at h
  have hz' : 0 < z.im := hz.2
  have hpos := mul_pos (sq_pos_of_pos hz') (neg_pos.mpr hs)
  nlinarith

theorem returnMap_mapsTo_slitTarget {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : MapsTo (returnMap c p) (upperSource c p) (slitTarget c p) := by
  intro z hz
  refine ⟨returnMap_mem_ball hp hz.1,?_⟩
  by_cases him : (returnMap c p z).im = 0
  · exact Or.inl (criticalValue_lt_returnMap_re_of_upper_real hp hc hz him)
  · exact Or.inr him

/-- Every point of the slit disk has exactly one upper-sheet preimage. -/
theorem returnMap_surjOn_slitTarget {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : SurjOn (returnMap c p) (upperSource c p) (slitTarget c p) := by
  intro w hw
  obtain ⟨z,hz,he⟩ := (show SurjOn (returnMap c p) (source c p) (ball 0 (radius p)) by
    rw [SurjOn,returnMap_image_source hp hc]) hw.1
  have him : z.im ≠ 0 := by
    intro him
    have hreal := returnMap_real_of_real c p him
    have hleft := returnMap_re_le_of_real hp hc hz him
    rw [he] at hreal hleft
    rcases hw.2 with h | h
    · exact (not_lt_of_ge hleft) h
    · exact h hreal
  rcases lt_or_gt_of_ne him with hneg | hpos
  · refine ⟨-z,⟨source_neg hp hc hz,?_⟩,?_⟩
    · simpa only [mem_setOf_eq,Complex.neg_im,neg_pos] using hneg
    · exact (returnMap_neg c (by omega) z).trans he
  · exact ⟨z,⟨hz,hpos⟩,he⟩

theorem returnMap_image_upperSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : returnMap c p '' upperSource c p = slitTarget c p :=
  (returnMap_mapsTo_slitTarget hp hc).image_subset.antisymm (returnMap_surjOn_slitTarget hp hc)

private theorem diagonal_evenSecant_continuous (c : ℝ) (n : ℕ) :
    Continuous (fun z : ℂ => evenSecant c n z z) := by
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  induction n with
  | zero => simpa only [evenSecant] using (continuous_const : Continuous (fun _ : ℂ => (1 : ℂ)))
  | succ n ih => exact ((hf.iterate (n+1)).add (hf.iterate (n+1))).mul ih

theorem derivative_continuous (c : ℝ) (p : ℕ) : Continuous (derivative c p) :=
  (continuous_const.mul continuous_id).mul (diagonal_evenSecant_continuous c (p-1))

theorem returnMap_hasDerivAt (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    HasDerivAt (returnMap c p) (derivative c p z) z := archived_hasDerivAt c hp z

theorem derivative_ne_zero_of_upperSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ upperSource c p) : derivative c p z ≠ 0 := by
  apply archived_derivative_ne_zero hp hc (norm_lt_radius_of_mem_source hp hc hz.1).le
  intro he
  have hi : 0 < z.im := hz.2
  simp [he] at hi

/-- The genuine complete p-return, bundled as a conformal chart of its upper sheet. -/
def conformalChart {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    CrestConformalModulus.ConformalChart :=
  CrestConformalModulus.ConformalChart.ofInjectiveOpenMap
    (upperSource_isOpen hp c) (returnMap_open c p) (returnMap_injOn_upperSource hp hc)
    (fun z _ => returnMap_hasDerivAt c (by omega) z)
    (derivative_continuous c p).continuousOn
    (fun _ hz => derivative_ne_zero_of_upperSource hp hc hz)

@[simp] theorem conformalChart_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    (conformalChart hp hc).homeomorph.source = upperSource c p := rfl

theorem conformalChart_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    (conformalChart hp hc).homeomorph.target = slitTarget c p :=
  returnMap_image_upperSource hp hc

@[simp] theorem conformalChart_apply {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) : (conformalChart hp hc).homeomorph z = returnMap c p z := rfl

@[simp] theorem conformalChart_derivative {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) : (conformalChart hp hc).derivative z = derivative c p z := rfl

theorem inverse_mem_upperSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {w : ℂ} (hw : w ∈ slitTarget c p) :
    (conformalChart hp hc).homeomorph.symm w ∈ upperSource c p := by
  exact (conformalChart hp hc).homeomorph.map_target (by rwa [conformalChart_target])

theorem returnMap_inverse {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {w : ℂ} (hw : w ∈ slitTarget c p) :
    returnMap c p ((conformalChart hp hc).homeomorph.symm w) = w :=
  (conformalChart hp hc).homeomorph.right_inv (by rwa [conformalChart_target])

theorem inverse_returnMap {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ upperSource c p) :
    (conformalChart hp hc).homeomorph.symm (returnMap c p z) = z :=
  (conformalChart hp hc).homeomorph.left_inv hz

theorem inverse_hasDerivAt {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {w : ℂ} (hw : w ∈ slitTarget c p) :
    HasDerivAt (conformalChart hp hc).homeomorph.symm
      (derivative c p ((conformalChart hp hc).homeomorph.symm w))⁻¹ w := by
  have hz := inverse_mem_upperSource hp hc hw
  exact (conformalChart hp hc).homeomorph.hasDerivAt_symm
    (by rwa [conformalChart_target]) (derivative_ne_zero_of_upperSource hp hc hz)
    (returnMap_hasDerivAt c (by omega) _)

end
end ActualPairableSource
