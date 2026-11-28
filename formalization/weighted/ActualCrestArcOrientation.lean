import ActualCrestArcCensus
import ActualCrestQuantitativeSupport

/-!
# Oriented actual crest arcs at every period from seventeen onward

The real part of the even divided difference has a fixed negative sign.
Comparing a point with its complex conjugate therefore gives an exact
orientation rule for the actual normalized polynomial.  On the selected
open crest arcs the first four imaginary signs are positive, negative,
positive, positive.  The effective complete-support theorem makes the
full real-intersection census, closed-arc disjointness, rectifiability,
and upper-half-plane conclusion valid for every period at least seventeen.
-/

namespace ActualCrestArcOrientation

open Set Function ComplexConjugate
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter QuadraticCrestDividedDifference
open ActualCrestCrossingWindow ActualCrestArcCensus ActualCrestQuantitativeSupport

noncomputable section

private theorem actual_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : c ∈ Icc (-2 : ℝ) 0 := by
  have hb := parameter_band hp hc.1
  exact ⟨hb.1, by linarith [hb.2]⟩

private theorem actual_small {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    criticalValue c p ≤ 12/(4 : ℝ)^p := by
  simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1

private theorem iterate_conj (c : ℝ) (n : ℕ) (z : ℂ) :
    ((quadraticMap c)^[n]) (conj z) = conj (((quadraticMap c)^[n]) z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp [quadraticMap]

private theorem normalizedReturn_conj (c : ℝ) (p : ℕ) (z : ℂ) :
    normalizedReturn c p (conj z) = conj (normalizedReturn c p z) := by
  have hm : (criticalValue c p : ℂ)*conj z =
      conj ((criticalValue c p : ℂ)*z) := by simp
  unfold normalizedReturn
  rw [hm, iterate_conj]
  simp

private theorem normalizedSecant_re_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    (normalizedSecant c p z w).re < 0 := by
  have he := normalizedSecant_error_small c p (by omega) (actual_band hp hc)
    hc.2.1 (actual_small hc) hz hw
  have hr := (Complex.re_le_norm (normalizedSecant c p z w -
    ((quadraticCoefficient c (p-1)*criticalValue c p : ℝ) : ℂ))).trans he
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  have hk := hc.2.2.2.1.1
  change (17903/10000 : ℝ) ≤ -quadraticCoefficient c (p-1)*criticalValue c p at hk
  nlinarith only [hr, hk]

private theorem normalizedReturn_im_factor {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) :
    (normalizedReturn c p z).im =
      2*(z.re*z.im)*(normalizedSecant c p z (conj z)).re := by
  have hr : (z^2-(conj z)^2).re = 0 := by
    simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hi : (z^2-(conj z)^2).im = 4*z.re*z.im := by
    simp only [pow_two, Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hd := congrArg Complex.im (normalized_difference c p (by omega) hc.2.1.ne'
    z (conj z))
  rw [Complex.sub_im, Complex.mul_im, normalizedReturn_conj, Complex.conj_im,
    hr, hi, zero_mul, zero_add] at hd
  nlinarith only [hd]

/-- The actual normalized return sends the second and fourth open
quadrants of the certified disk into the upper half-plane. -/
theorem normalized_return_im_pos_of_product_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20) (hxy : z.re*z.im < 0) :
    0 < (normalizedReturn c p z).im := by
  rw [normalizedReturn_im_factor hp hc]
  exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by norm_num) hxy)
    (normalizedSecant_re_neg hp hc hz (by simpa using hz))

/-- The actual normalized return sends the first and third open
quadrants of the certified disk into the lower half-plane. -/
theorem normalized_return_im_neg_of_product_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20) (hxy : 0 < z.re*z.im) :
    (normalizedReturn c p z).im < 0 := by
  rw [normalizedReturn_im_factor hp hc]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hxy)
    (normalizedSecant_re_neg hp hc hz (by simpa using hz))

private theorem circlePoint_im_pos (s : Radius) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) : 0 < (circlePoint s u).im := by
  have hs : 0 < (s : ℝ) := by linarith [s.property.1]
  have hsq : 0 < 1-u^2 := by
    have hm := mul_pos (show 0 < 1-u by linarith [hu.2])
      (show 0 < 1+u by linarith [hu.1])
    nlinarith only [hm]
  simpa [circlePoint] using mul_pos hs (Real.sqrt_pos.mpr hsq)

/-- The complete open upper semicircle, including both sides of the
crossing, has positive imaginary first image at every admissible period. -/
theorem first_image_im_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (s : Radius) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    0 < (normalizedReturn c p (circlePoint s u)).im := by
  have hu' : u ∈ Icc (-1 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hzD := circlePoint_mem_initialDisk s hu'
  have hr : (circlePoint s u).re < 0 := by
    have h := (Complex.re_le_norm (circlePoint s u+(3/4 : ℂ))).trans hzD
    norm_num at h
    linarith
  exact normalized_return_im_pos_of_product_neg hp hc (circlePoint_full_disk s.property hu')
    (mul_neg_of_neg_of_pos hr (circlePoint_im_pos s hu))

/-- On every selected open actual crest arc, the four consecutive image
half-planes have signs positive, negative, positive, positive. -/
theorem selected_arc_image_signs {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (s : Radius) {u : ℝ}
    (hu : u ∈ Ioo (F.angle s) 1) :
    0 < (normalizedReturn c p (circlePoint s u)).im ∧
      (((normalizedReturn c p)^[2]) (circlePoint s u)).im < 0 ∧
      0 < (((normalizedReturn c p)^[3]) (circlePoint s u)).im ∧
      0 < (((normalizedReturn c p)^[4]) (circlePoint s u)).im := by
  let H := normalizedReturn c p
  let z := circlePoint s u
  have hu1 : u ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [(F.angle_mem s).1, hu.1], hu.2⟩
  have hb := actual_complete_support_all_periods hp hc z
    (circlePoint_mem_initialDisk s ⟨hu1.1.le, hu1.2.le⟩)
  have h1 : 0 < (H z).im := first_image_im_pos hp hc s hu1
  have h1r : 0 < (H z).re := first_image_re_pos hp hc F s ⟨hu.1, hu.2.le⟩
  have h2 : ((H^[2]) z).im < 0 :=
    normalized_return_im_neg_of_product_pos hp hc
      (by simpa only [iterate_one] using hb.1 1 (by omega)) (mul_pos h1r h1)
  have h3 : 0 < ((H^[3]) z).im :=
    normalized_return_im_pos_of_product_neg hp hc (hb.1 2 (by omega))
      (mul_neg_of_pos_of_neg hb.2.1 h2)
  have h4 : 0 < ((H^[4]) z).im :=
    normalized_return_im_pos_of_product_neg hp hc (hb.1 3 (by omega))
      (mul_neg_of_neg_of_pos hb.2.2 h3)
  exact ⟨h1, h2, h3, h4⟩

/-- The actual fourth image of each selected angular arc lies strictly
in the upper half-plane at every interior parameter. -/
theorem selected_fourth_image_upper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (s : Radius) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.arccos (F.angle s))) :
    0 < (((normalizedReturn c p)^[4]) (angularPoint s t)).im := by
  have ha : F.angle s ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(F.angle_mem s).1, (F.angle_mem s).2]
  have htπ : t ∈ Icc (0 : ℝ) Real.pi :=
    ⟨ht.1.le, ht.2.le.trans (Real.arccos_le_pi _)⟩
  have hleft : F.angle s < Real.cos t := by
    have h := Real.strictAntiOn_cos htπ
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ ht.2
    simpa only [Real.cos_arccos ha.1 ha.2] using h
  have hright : Real.cos t < 1 := by
    have h := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Icc (0 : ℝ) Real.pi from ⟨le_rfl, Real.pi_pos.le⟩) htπ ht.1
    simpa only [Real.cos_zero] using h
  exact (selected_arc_image_signs hp hc F s ⟨hleft, hright⟩).2.2.2

/-- The closed leaf used by the collision theorem is exactly the image
of the angular parametrization used for rectifiability and orientation. -/
theorem finalClosedLeaf_eq_angular_image {p : ℕ} {c : ℝ}
    (F : Family p c) (s : Radius) :
    finalClosedLeaf F s =
      (fun t : ℝ => ((normalizedReturn c p)^[4]) (angularPoint s t)) ''
        Icc (0 : ℝ) (Real.arccos (F.angle s)) := by
  have ha : F.angle s ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(F.angle_mem s).1, (F.angle_mem s).2]
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Real.arccos u, ⟨Real.arccos_nonneg _, Real.arccos_le_arccos hu.1⟩, ?_⟩
    change ((normalizedReturn c p)^[4]) (circlePoint s (Real.cos (Real.arccos u))) = _
    rw [Real.cos_arccos (ha.1.trans hu.1) hu.2]
  · rintro ⟨t, ht, rfl⟩
    have htπ : t ∈ Icc (0 : ℝ) Real.pi :=
      ⟨ht.1, ht.2.trans (Real.arccos_le_pi _)⟩
    have hleft : F.angle s ≤ Real.cos t := by
      have h := Real.antitoneOn_cos htπ
        ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ ht.2
      simpa only [Real.cos_arccos ha.1 ha.2] using h
    exact ⟨Real.cos t, ⟨hleft, Real.cos_le_one t⟩, rfl⟩

/-- Complete actual crest-arc geometry at every period `p ≥ 17`:
the real-intersection census, joint closed-arc injectivity, pairwise
closed-leaf disjointness, rectifiability, and strict upper-half-plane
location of the selected fourth-image interiors hold simultaneously. -/
theorem all_period_actual_arc_geometry {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    (∀ s : Radius, ∀ t ∈ Icc (0 : ℝ) Real.pi, ∀ m : ℕ, 2 ≤ m → m ≤ 4 →
      ((((normalizedReturn c p)^[m]) (angularPoint s t)).im = 0 ↔
        t = 0 ∨ t = Real.arccos (F.angle s) ∨ t = Real.pi)) ∧
    (∀ s t : Radius, ∀ u ∈ Icc (F.angle s) 1, ∀ v ∈ Icc (F.angle t) 1,
      (((normalizedReturn c p)^[4]) (circlePoint s u) =
        ((normalizedReturn c p)^[4]) (circlePoint t v) ↔ s = t ∧ u = v)) ∧
    (∀ s t : Radius, s ≠ t → Disjoint (finalClosedLeaf F s) (finalClosedLeaf F t)) ∧
    (∀ s : Radius,
      BoundedVariationOn (fun t : ℝ => ((normalizedReturn c p)^[4]) (angularPoint s t))
        (Icc (0 : ℝ) (Real.arccos (F.angle s))) ∧
      ∀ t ∈ Ioo (0 : ℝ) (Real.arccos (F.angle s)),
        0 < (((normalizedReturn c p)^[4]) (angularPoint s t)).im) := by
  have hB := actual_complete_support_all_periods hp hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t ht m hm hm'
    exact full_angle_real_census hp hc F hB s ht hm hm'
  · intro s t u hu v hv
    exact selected_closed_arc_collision_iff hp hc F hB s t hu hv
  · intro s t hst
    exact finalClosedLeaf_disjoint hp hc F hB hst
  · intro s
    exact ⟨selected_fourth_image_boundedVariation hp hc F hB s,
      fun _ ht => selected_fourth_image_upper hp hc F s ht⟩

end
end ActualCrestArcOrientation
