import ActualPairablePorts

/-! # Exact images and orientation of the actual two source ports -/

namespace ActualPairablePorts

open Set Function Metric
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualPairableSource ActualParentMarks QuadraticCrestDividedDifference
open ActualPairableSourceBounds

noncomputable section

def realReturn (c : ℝ) (p : ℕ) (x : ℝ) : ℝ := (returnMap c p (x : ℂ)).re

theorem realReturn_continuous (c : ℝ) (p : ℕ) : Continuous (realReturn c p) :=
  Complex.continuous_re.comp ((returnMap_continuous c p).comp Complex.continuous_ofReal)

theorem returnMap_ofReal (c : ℝ) (p : ℕ) (x : ℝ) :
    returnMap c p (x : ℂ) = (realReturn c p x : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using returnMap_real_of_real c p (z := (x : ℂ)) rfl

/-- The entire negative physical branch has the strict real orientation
required by the two designated source ports. -/
theorem realReturn_strictMonoOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    StrictMonoOn (realReturn c p) (Icc (-radius p) 0) := by
  intro x hx y hy hxy
  have hnorm {t : ℝ} (ht : t ∈ Icc (-radius p) 0) : ‖(t : ℂ)‖ ≤ (1/2 : ℝ)^p := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos ht.2]
    change -t ≤ radius p
    linarith [ht.1]
  have hs := evenSecant_re_neg hp hc (hnorm hx) (hnorm hy)
  have h := iterate_difference c (p-1) (x : ℂ) (y : ℂ)
  rw [Nat.sub_add_cancel (show 1 ≤ p by omega)] at h
  have hr := congrArg Complex.re h
  change (returnMap c p (x : ℂ)-returnMap c p (y : ℂ)).re = _ at hr
  simp only [Complex.sub_re,Complex.sub_im,pow_two,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,sub_self] at hr
  have hsq : 0 < x^2-y^2 := by
    have hm := mul_pos (sub_pos.mpr hxy) (show 0 < -(x+y) by linarith [hy.2])
    nlinarith
  have hprod := mul_neg_of_pos_of_neg hsq hs
  change (returnMap c p (x : ℂ)).re < (returnMap c p (y : ℂ)).re
  nlinarith

theorem negative_branch_derivative_re_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {x : ℝ} (hx : x ∈ Ioo (-radius p) 0) :
    0 < (ActualPairableSource.derivative c p (x : ℂ)).re := by
  have hnorm : ‖(x : ℂ)‖ ≤ (1/2 : ℝ)^p := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_neg hx.2]
    change -x ≤ radius p
    linarith [hx.1]
  have hs := evenSecant_re_neg hp hc hnorm hnorm
  simpa [ActualPairableSource.derivative,Complex.mul_re,Complex.mul_im] using
    mul_pos_of_neg_of_neg (show 2*x < 0 by linarith [hx.2]) hs

theorem closed_source_port_hull_subset_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    {z : ℂ | z.im = 0 ∧ z.re ∈ Icc (-cut c p 4) (-alpha hp hc)} ⊆ source c p := by
  intro z hz
  apply sourceSlit_subset_source hp hc
  have ho := source_ports_ordered hp hc
  refine ⟨hz.1,ho.1.le.trans hz.2.1,?_⟩
  have ha := alpha_pos hp hc
  linarith [hz.2.2,hc.2.1]

theorem closed_source_port_hull_subset_negative {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : Icc (-cut c p 4) (-alpha hp hc) ⊆ Ioo (-radius p) 0 := by
  intro x hx
  have ho := source_ports_ordered hp hc
  constructor
  · linarith [criticalValue_lt_radius hp hc,ho.1,hx.1]
  · exact hx.2.trans_lt ho.2.2.2.2

theorem target_ports_ordered {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    cut c p 5 < cut c p 3 ∧ cut c p 3 < cut c p 6 ∧
      cut c p 6 < alpha hp hc ∧ alpha hp hc < criticalValue c p := by
  obtain ⟨h2,h3,h4,h5,h6⟩ := normalized_cut_boxes hp hc
  have ha := normalizedAlpha_bounds hp hc
  rw [cut_eq_scale_mul_normalized c p 5 hc.2.1.ne',
    cut_eq_scale_mul_normalized c p 3 hc.2.1.ne',
    cut_eq_scale_mul_normalized c p 6 hc.2.1.ne',alpha]
  refine ⟨mul_lt_mul_of_pos_left (by linarith [h5.2,h3.1]) hc.2.1,
    mul_lt_mul_of_pos_left (by linarith [h3.2,h6.1]) hc.2.1,
    mul_lt_mul_of_pos_left (by linarith [h6.2,ha.1]) hc.2.1,?_⟩
  exact mul_lt_of_lt_one_right hc.2.1 (by linarith [ha.2])

theorem realReturn_leftPort_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    realReturn c p '' Ioo (-cut c p 4) (cut c p 2) = Ioo (cut c p 5) (cut c p 3) := by
  have ho := source_ports_ordered hp hc
  have hsub : Icc (-cut c p 4) (cut c p 2) ⊆ Icc (-radius p) 0 := by
    intro x hx
    exact Ioo_subset_Icc_self (closed_source_port_hull_subset_negative hp hc
      ⟨hx.1,hx.2.trans (ho.2.2.1.trans ho.2.2.2.1).le⟩)
  have h := ContinuousOn.image_Ioo_of_strictMonoOn ho.2.1.le
    (realReturn_continuous c p).continuousOn ((realReturn_strictMonoOn hp hc).mono hsub)
  have hL : realReturn c p (-cut c p 4) = cut c p 5 := by
    simpa only [realReturn,Complex.ofReal_neg,Complex.ofReal_re] using
      congrArg Complex.re (returnMap_neg_cut c (p := p) (by omega) 4)
  have hR : realReturn c p (cut c p 2) = cut c p 3 := by
    exact congrArg Complex.re (returnMap_cut c p 2)
  simpa only [hL,hR] using h

theorem realReturn_rightPort_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    realReturn c p '' Ioo (cut c p 5) (-alpha hp hc) = Ioo (cut c p 6) (alpha hp hc) := by
  have ho := source_ports_ordered hp hc
  have hsub : Icc (cut c p 5) (-alpha hp hc) ⊆ Icc (-radius p) 0 := by
    intro x hx
    exact Ioo_subset_Icc_self (closed_source_port_hull_subset_negative hp hc
      ⟨(ho.2.1.trans ho.2.2.1).le.trans hx.1,hx.2⟩)
  have h := ContinuousOn.image_Ioo_of_strictMonoOn ho.2.2.2.1.le
    (realReturn_continuous c p).continuousOn ((realReturn_strictMonoOn hp hc).mono hsub)
  have hL : realReturn c p (cut c p 5) = cut c p 6 :=
    congrArg Complex.re (returnMap_cut c p 5)
  have hR : realReturn c p (-alpha hp hc) = alpha hp hc := by
    simpa only [realReturn,Complex.ofReal_neg,Complex.ofReal_re] using
      congrArg Complex.re (returnMap_neg_alpha hp hc)
  simpa only [hL,hR] using h

theorem leftPort_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    returnMap c p '' leftPort c p = {w : ℂ | w.im = 0 ∧ w.re ∈ Ioo (cut c p 5) (cut c p 3)} := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz.1]
    refine ⟨returnMap_real_of_real c p hz.1,?_⟩
    have h := mem_image_of_mem (realReturn c p) hz.2
    rw [realReturn_leftPort_image hp hc] at h
    change (returnMap c p (z.re : ℂ)).re ∈ _ at h
    rw [← he] at h
    exact h
  · intro hw
    obtain ⟨x,hx,he⟩ := (realReturn_leftPort_image hp hc).symm ▸ hw.2
    refine ⟨(x : ℂ),⟨by simp,hx⟩,?_⟩
    rw [returnMap_ofReal,he]
    apply Complex.ext <;> simp [hw.1]

theorem rightPort_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    returnMap c p '' rightPort hp hc = {w : ℂ | w.im = 0 ∧ w.re ∈ Ioo (cut c p 6) (alpha hp hc)} := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz.1]
    refine ⟨returnMap_real_of_real c p hz.1,?_⟩
    have h := mem_image_of_mem (realReturn c p) hz.2
    rw [realReturn_rightPort_image hp hc] at h
    change (returnMap c p (z.re : ℂ)).re ∈ _ at h
    rw [← he] at h
    exact h
  · intro hw
    obtain ⟨x,hx,he⟩ := (realReturn_rightPort_image hp hc).symm ▸ hw.2
    refine ⟨(x : ℂ),⟨by simp,hx⟩,?_⟩
    rw [returnMap_ofReal,he]
    apply Complex.ext <;> simp [hw.1]

end
end ActualPairablePorts
