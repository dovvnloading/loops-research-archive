import ActualPairableSource
import ActualParentDiskMarking
import GlobalCrestSourceGates

/-!
# The actual fixed cut and the two designated source ports

The dividing fixed cut is chosen from its proved unique interval root.
Every other endpoint is a literal critical iterate.  Both closed source
ports lie in the full archived source, and the complete return maps them
in their actual increasing order to their specified target intervals.
-/

namespace ActualPairablePorts

open Set Function Metric
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualPairableSource ActualParentMarks ActualParentDiskMarking
open GlobalCrestSourceGates LoopsLimitingCrestParameter QuadraticCrestDividedDifference

noncomputable section

def normalizedAlpha {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ℝ :=
  Classical.choose (actual_positive_fixed_cut hp hc)

theorem normalizedAlpha_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    normalizedAlpha hp hc ∈ Ioo (518/1000 : ℝ) (519/1000) :=
  (Classical.choose_spec (actual_positive_fixed_cut hp hc)).1

theorem normalizedAlpha_fixed {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    normalizedReturn c p (normalizedAlpha hp hc : ℂ) = (normalizedAlpha hp hc : ℂ) :=
  (Classical.choose_spec (actual_positive_fixed_cut hp hc)).2.1

theorem normalizedAlpha_unique {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (23/20))
    (hfix : normalizedReturn c p (x : ℂ) = (x : ℂ)) : x = normalizedAlpha hp hc :=
  (Classical.choose_spec (actual_positive_fixed_cut hp hc)).2.2 x hx hfix

def alpha {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ℝ :=
  criticalValue c p * normalizedAlpha hp hc

def cut (c : ℝ) (p j : ℕ) : ℝ := criticalValue c (j*p)

theorem cut_eq_scale_mul_normalized (c : ℝ) (p j : ℕ)
    (hd : criticalValue c p ≠ 0) : cut c p j = criticalValue c p * normalizedCut c p j := by
  simp only [cut,normalizedCut]
  field_simp

theorem alpha_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    0 < alpha hp hc := mul_pos hc.2.1 (by linarith [(normalizedAlpha_bounds hp hc).1])

theorem alpha_lt_criticalValue {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    alpha hp hc < criticalValue c p := by
  unfold alpha
  exact mul_lt_of_lt_one_right hc.2.1 (by linarith [(normalizedAlpha_bounds hp hc).2])

theorem returnMap_alpha {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    returnMap c p (alpha hp hc : ℂ) = (alpha hp hc : ℂ) := by
  have h := normalized_iterate_scale c p hc.2.1.ne' 1 (normalizedAlpha hp hc : ℂ)
  simp only [iterate_one,one_mul,normalizedAlpha_fixed hp hc] at h
  simpa only [alpha,Complex.ofReal_mul,returnMap] using h.symm

theorem returnMap_neg_alpha {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    returnMap c p (-alpha hp hc : ℂ) = (alpha hp hc : ℂ) := by
  rw [returnMap_neg c (by omega),returnMap_alpha hp hc]

theorem returnMap_cut (c : ℝ) (p j : ℕ) :
    returnMap c p (cut c p j : ℂ) = (cut c p (j+1) : ℂ) := by
  rw [cut,← returnMap_zero]
  change ((quadraticMap c)^[p]) (((quadraticMap c)^[j*p]) 0) =
    (criticalValue c ((j+1)*p) : ℂ)
  rw [← iterate_add_apply,show p+j*p=(j+1)*p by ring]
  exact returnMap_zero c ((j+1)*p)

theorem returnMap_neg_cut (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (j : ℕ) :
    returnMap c p (-cut c p j : ℂ) = (cut c p (j+1) : ℂ) := by
  rw [returnMap_neg c hp,returnMap_cut]

theorem normalized_cut_six_eq_neg_three {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    normalizedCut c p 6 = -normalizedCut c p 3 := by
  unfold normalizedCut
  have he : criticalValue c (6*p) = -criticalValue c (3*p) := by linarith [hc.2.2.2.2.1]
  rw [he,neg_div]

/-- Coarse actual orbit boxes, with the limiting root eliminated internally. -/
theorem normalized_cut_boxes {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    normalizedCut c p 2 ∈ Ioo (-81/100 : ℝ) (-78/100) ∧
    normalizedCut c p 3 ∈ Ioo (-13/100 : ℝ) (-10/100) ∧
    normalizedCut c p 4 ∈ Ioo (96/100 : ℝ) (99/100) ∧
    normalizedCut c p 5 ∈ Ioo (-76/100 : ℝ) (-65/100) ∧
    normalizedCut c p 6 ∈ Ioo (10/100 : ℝ) (13/100) := by
  obtain ⟨k,⟨hk,hr⟩,_⟩ := exists_unique_limiting_parameter
  have he (j : ℕ) (hj : j ≤ 6) : |normalizedCut c p j-criticalOrbit k j| < 1/100 := by
    have h := normalizedCut_error_uniform hp hj hc hk hr
    nlinarith [scale_small hp]
  have h2 := abs_lt.mp (he 2 (by norm_num))
  have h3 := abs_lt.mp (he 3 (by norm_num))
  have h4 := abs_lt.mp (he 4 (by norm_num))
  have h5 := abs_lt.mp (he 5 (by norm_num))
  obtain ⟨h2l,h2u,h5l,h5u,h3l,h3u⟩ := limit_cut_boxes hk
  have h4b := parameter_orbit_bounds hk
  rw [normalized_cut_six_eq_neg_three hc]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

private theorem normalizedReturn_norm_lt_three {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖normalizedReturn c p z‖ < 3 := by
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1
  have he := normalized_return_error c p (by omega) hc.2.2.2.2.2.2 hc.2.1 hsmall
    z (by linarith)
  change ‖normalizedReturn c p z-LimitingCrest.complexMap (kappa p c) z‖ ≤ _ at he
  have he' : ‖normalizedReturn c p z-LimitingCrest.complexMap (kappa p c) z‖ ≤
      24*scale p := by simpa only [scale,one_div_pow,mul_one_div] using he
  have hk := hc.2.2.2.1
  have hk0 : 0 < kappa p c := by have h:=hk.1; change 17903/10000 ≤ kappa p c at h; linarith
  have hmodel := norm_sub_le (1 : ℂ) ((kappa p c : ℂ)*z^2)
  rw [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk0,norm_pow] at hmodel
  have hz2 : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hprod := mul_le_mul_of_nonneg_left hz2 hk0.le
  have ht := norm_le_norm_sub_add (normalizedReturn c p z) (LimitingCrest.complexMap (kappa p c) z)
  change ‖1-(kappa p c : ℂ)*z^2‖ ≤ _ at hmodel
  change ‖normalizedReturn c p z‖ ≤ ‖normalizedReturn c p z-LimitingCrest.complexMap (kappa p c) z‖+
    ‖1-(kappa p c : ℂ)*z^2‖ at ht
  have hku := hk.2
  change kappa p c ≤ 17904/10000 at hku
  nlinarith [scale_small hp]

/-- The entire physical critical-scale disk belongs to the full archived source. -/
theorem closedBall_criticalValue_subset_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : closedBall 0 (criticalValue c p) ⊆ source c p := by
  intro z hz
  have hzn : ‖z‖ ≤ criticalValue c p := mem_closedBall_zero_iff.mp hz
  have hR : 4*criticalValue c p < radius p := by
    have h := targetRadius_gt_four hp hc
    exact (lt_div_iff₀ hc.2.1).mp h
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  have hu : ‖z/(criticalValue c p : ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.2.1]
    exact (div_le_one hc.2.1).mpr hzn
  have hnorm := normalizedReturn_norm_lt_three hp hc hu
  have he : returnMap c p z = (criticalValue c p : ℂ)*
      normalizedReturn c p (z/(criticalValue c p : ℂ)) := by
    unfold normalizedReturn returnMap
    field_simp [hdC]
  apply (mem_source_iff hp hc (by linarith [hc.2.1])).mpr
  rw [mem_ball_zero_iff,he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.2.1]
  have hb := mul_lt_mul_of_pos_left hnorm hc.2.1
  linarith [hc.2.1]

def leftPort (c : ℝ) (p : ℕ) : Set ℂ :=
  {z | z.im = 0 ∧ z.re ∈ Ioo (-cut c p 4) (cut c p 2)}

def rightPort {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : Set ℂ :=
  {z | z.im = 0 ∧ z.re ∈ Ioo (cut c p 5) (-alpha hp hc)}

def sourceSlit (c : ℝ) (p : ℕ) : Set ℂ :=
  {z | z.im = 0 ∧ z.re ∈ Icc (-criticalValue c p) (criticalValue c p)}

/-- The four source electrode endpoints have their genuine strict order. -/
theorem source_ports_ordered {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    -criticalValue c p < -cut c p 4 ∧ -cut c p 4 < cut c p 2 ∧
      cut c p 2 < cut c p 5 ∧ cut c p 5 < -alpha hp hc ∧ -alpha hp hc < 0 := by
  obtain ⟨h2,h3,h4,h5,h6⟩ := normalized_cut_boxes hp hc
  have ha := normalizedAlpha_bounds hp hc
  rw [cut_eq_scale_mul_normalized c p 4 hc.2.1.ne',
    cut_eq_scale_mul_normalized c p 2 hc.2.1.ne',
    cut_eq_scale_mul_normalized c p 5 hc.2.1.ne',alpha]
  constructor
  · have h := mul_lt_mul_of_pos_left (show normalizedCut c p 4 < 1 by linarith [h4.2]) hc.2.1
    nlinarith
  constructor
  · have h := mul_lt_mul_of_pos_left (show -normalizedCut c p 4 < normalizedCut c p 2 by linarith [h4.1,h2.1]) hc.2.1
    simpa only [mul_neg] using h
  constructor
  · exact mul_lt_mul_of_pos_left (by linarith [h2.2,h5.1]) hc.2.1
  constructor
  · have h := mul_lt_mul_of_pos_left (show normalizedCut c p 5 < -normalizedAlpha hp hc by linarith [h5.2,ha.2]) hc.2.1
    simpa only [mul_neg] using h
  · exact neg_neg_of_pos (mul_pos hc.2.1 (by linarith [ha.1]))

theorem sourceSlit_subset_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    sourceSlit c p ⊆ source c p := by
  intro z hz
  apply closedBall_criticalValue_subset_source hp hc
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz.1]
  rw [mem_closedBall_zero_iff,he,Complex.norm_real,Real.norm_eq_abs]
  exact abs_le.mpr hz.2

theorem leftPort_subset_sourceSlit {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    leftPort c p ⊆ sourceSlit c p := by
  intro z hz
  have ho := source_ports_ordered hp hc
  refine ⟨hz.1,?_,?_⟩
  · exact ho.1.le.trans hz.2.1.le
  · have hx2 : cut c p 2 < 0 := lt_trans ho.2.2.1 (lt_trans ho.2.2.2.1 ho.2.2.2.2)
    linarith [hz.2.2,hc.2.1]

theorem rightPort_subset_sourceSlit {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    rightPort hp hc ⊆ sourceSlit c p := by
  intro z hz
  have ho := source_ports_ordered hp hc
  refine ⟨hz.1,?_,?_⟩
  · exact (ho.1.trans (ho.2.1.trans ho.2.2.1)).le.trans hz.2.1.le
  · linarith [hz.2.2,ho.2.2.2.2,hc.2.1]

theorem leftPort_subset_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    leftPort c p ⊆ source c p :=
  (leftPort_subset_sourceSlit hp hc).trans (sourceSlit_subset_source hp hc)

theorem rightPort_subset_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    rightPort hp hc ⊆ source c p :=
  (rightPort_subset_sourceSlit hp hc).trans (sourceSlit_subset_source hp hc)

end
end ActualPairablePorts
