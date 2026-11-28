import GlobalCrestOrder
import LimitingCrestPerturbation
import LimitingCrestArcGates

/-!
# Explicit actual terminal tests from period seventeen

The comparison here uses the quadratic coefficient of the actual return,
rather than first passing to its limiting parameter.  This retains enough
numerical margin to orient the globally selected terminal curve at every
period covered by the signed-tip construction.  The rational model
estimates are supporting bounds for the actual polynomial conclusions.
-/

namespace GlobalCrestEndpointValues

open Set Function LimitingCrest LimitingCrestQuadraticReturn
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter
open GlobalCrestCrossing GlobalCrestEstimates GlobalCrestOrder

noncomputable section

private theorem actual_coefficient_angle_error {p : ℕ} (hp : 17 ≤ p)
    {c s u : ℝ} (hc : ActualTip p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10))
    (hzero : (normalizedReturn c p (circlePoint s u)).re = 0) :
    |u-crossingCos (kappa p c) s| ≤ 1/10000000 := by
  have hk := hc.2.2.2.1
  have hmap := actual_return_error_small hp hc
    ((circlePoint_disk hs hu).trans (by norm_num : (23/20 : ℝ) ≤ 3/2))
  have hreal := (Complex.abs_re_le_norm
    (normalizedReturn c p (circlePoint s u)-
      complexMap (kappa p c) (circlePoint s u))).trans hmap
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1,hu.2]
  have hq : (complexMap (kappa p c) (circlePoint s u)).re =
      crossing (kappa p c) s u := by
    rw [circle_image (kappa p c) s hu1]
    simp
  simp only [Complex.sub_re,hzero,hq,zero_sub,abs_neg] at hreal
  have hspec := GlobalCrestCrossing.crossingCos_spec hk hs
  have hv : crossingCos (kappa p c) s ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hspec.1.1,hspec.1.2]
  rcases le_total u (crossingCos (kappa p c) s) with hle | hle
  · have hg := crossing_global_growth hk hs hu1 hv hle
    rw [hspec.2] at hg
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith only [hg,(abs_le.mp hreal).1]
  · have hg := crossing_global_growth hk hs hv hu1 hle
    rw [hspec.2] at hg
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith only [hg,(abs_le.mp hreal).2]

private theorem actual_coefficient_point_error {p : ℕ} (hp : 17 ≤ p)
    {c s : ℝ} (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    ‖F.point ⟨s,⟨hs.1,by linarith [hs.2]⟩⟩-
      radialPoint (kappa p c) s‖ ≤ 2/100000000 := by
  have hsfull : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  let ss : Radius := ⟨s,hsfull⟩
  have hu : F.angle ss ∈ Icc (-1/10 : ℝ) (1/10) :=
    ⟨(F.angle_mem ss).1.le,(F.angle_mem ss).2.le⟩
  have hv := (GlobalCrestCrossing.crossingCos_spec hc.2.2.2.1 hsfull).1
  have hang := actual_coefficient_angle_error hp hc hsfull hu (F.crossing ss)
  have hcircle := circlePoint_angle_bound s hu ⟨hv.1.le,hv.2.le⟩
  rw [abs_of_pos (by linarith [hs.1] : 0 < s)] at hcircle
  have hm := mul_le_mul (show 2*s ≤ (1/5 : ℝ) by linarith [hs.2]) hang
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/5)
  change ‖circlePoint s (F.angle ss)-radialPoint (kappa p c) s‖ ≤ _
  rw [GlobalCrestCrossing.radialPoint_eq_circlePoint hc.2.2.2.1 hsfull]
  linarith

private theorem quadratic_large_lipschitz {κ : ℝ}
    (hk0 : 0 ≤ κ) (hk2 : κ ≤ 2) {z w : ℂ}
    (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 3/2) :
    ‖complexMap κ z-complexMap κ w‖ ≤ 6*‖z-w‖ := by
  have hid : complexMap κ z-complexMap κ w =
      -(κ : ℂ)*(z-w)*(z+w) := by unfold complexMap; ring
  have hsum : κ*(‖z‖+‖w‖) ≤ 6 := by
    calc
      _ ≤ 2*(‖z‖+‖w‖) := mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ ≤ 6 := by linarith
  calc
    _ = κ*‖z-w‖*‖z+w‖ := by
      rw [hid,norm_mul,norm_mul,norm_neg,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg hk0]
    _ ≤ κ*‖z-w‖*(‖z‖+‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le z w) (by positivity)
    _ = (κ*(‖z‖+‖w‖))*‖z-w‖ := by ring
    _ ≤ 6*‖z-w‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

private theorem actual_quadratic_step {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ}
    (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 3/2) :
    ‖normalizedReturn c p z-complexMap (kappa p c) w‖ ≤
      1/100000000+6*‖z-w‖ := by
  have hk := hc.2.2.2.1
  have he := actual_return_error_small hp hc hz
  have hl := quadratic_large_lipschitz (κ := kappa p c) (by linarith [hk.1])
    (by linarith [hk.2]) hz hw
  calc
    _ ≤ ‖normalizedReturn c p z-complexMap (kappa p c) z‖+
        ‖complexMap (kappa p c) z-complexMap (kappa p c) w‖ := by
      simpa only [dist_eq_norm] using dist_triangle (normalizedReturn c p z)
        (complexMap (kappa p c) z) (complexMap (kappa p c) w)
    _ ≤ _ := add_le_add he hl

/-- The actual terminal curve is within one hundred-thousandth of the
quadratic with its own actual coefficient on the endpoint collar.  Every
intermediate evaluation is justified in the enlarged approximation disk. -/
theorem actual_coefficient_terminal_error {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    |terminal F s-crestTerminal (kappa p c) s| ≤ 1/100000 := by
  have hsfull : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  let ss : Radius := ⟨s,hsfull⟩
  let z := F.point ss
  let w := radialPoint (kappa p c) s
  let H := normalizedReturn c p
  let Q := complexMap (kappa p c)
  have hmodel := radial_model_realization hc.2.2.2.1 hsfull
  have hwmem : w ∈ initialDisk := by
    change ‖radialPoint (kappa p c) s+(3/4 : ℂ)‖ ≤ 133/2000
    rw [hmodel.1]
    exact hs.2
  have hwb := (whole_support_bounds hc.2.2.2.1 hwmem).1
  have hz0 : ‖z‖ ≤ 3/2 := (F.point_parent_disk ss).trans (by norm_num)
  have hz1 : ‖H z‖ ≤ 3/2 := (first_image_small hp hc (by
    change ‖F.point ss+(3/4 : ℂ)‖ ≤ 1/8
    rw [F.point_radius]
    exact hsfull.2)).le.trans (by norm_num)
  have hz2 : ‖H (H z)‖ ≤ 3/2 :=
    (second_image_bounds hp hc F ss).2.2.le.trans (by norm_num)
  have hw0 : ‖w‖ ≤ 3/2 := (hwb 0 (by omega)).le.trans (by norm_num)
  have hw1 : ‖Q w‖ ≤ 3/2 := (hwb 1 (by omega)).le.trans (by norm_num)
  have hw2 : ‖Q (Q w)‖ ≤ 3/2 := (hwb 2 (by omega)).le.trans (by norm_num)
  have h0 : ‖z-w‖ ≤ 2/100000000 := actual_coefficient_point_error hp hc F hs
  have hs1 := actual_quadratic_step hp hc hz0 hw0
  have h1 : ‖H z-Q w‖ ≤ 13/100000000 := by linarith
  have hs2 := actual_quadratic_step hp hc hz1 hw1
  have h2 : ‖H (H z)-Q (Q w)‖ ≤ 79/100000000 := by linarith
  have hs3 := actual_quadratic_step hp hc hz2 hw2
  have h3 : ‖(H^[3]) z-(Q^[3]) w‖ ≤ 1/100000 := by
    change ‖H (H (H z))-Q (Q (Q w))‖ ≤ _
    linarith
  have hr := (Complex.abs_re_le_norm ((H^[3]) z-(Q^[3]) w)).trans h3
  change |(((normalizedReturn c p)^[3]) (F.point ⟨s,hsfull⟩)-
    ((complexMap (kappa p c))^[3]) (radialPoint (kappa p c) s)).re| ≤ _ at hr
  rw [hmodel.2.2.2] at hr
  simpa only [terminal,point,radiusProjection_eq hsfull,Complex.sub_re,
    Complex.ofReal_re] using hr

/- The following rational bounds sharpen the margins already used for
the archived model endpoint. Their role here is to absorb actual errors. -/

private theorem reciprocal_bounds {κ : ℝ} (hk : κ ∈ parameterInterval) :
    (223/50 : ℝ) ≤ 8/κ ∧ 8/κ ≤ 447/100 := by
  have hk0 : 0 < κ := by linarith [hk.1]
  constructor
  · apply (le_div_iff₀ hk0).2
    nlinarith [hk.2]
  · apply (div_le_iff₀ hk0).2
    nlinarith [hk.1]

private theorem ordinate_lower {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    s^2-1/1000000 ≤ radialOrdinateSq κ s := by
  have hsfull : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  have hr := reciprocal_bounds hk
  have hsqlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/16) hs.1 2
  have hsqup := pow_le_pow_left₀ (by linarith [hs.1] : 0 ≤ s) hs.2 2
  have hd : (56/25 : ℝ) ≤ radialDiscriminant κ s := by
    unfold radialDiscriminant
    nlinarith only [hr.1,hsqlo]
  have hdu : radialDiscriminant κ s ≤ (2256/1000 : ℝ) := by
    unfold radialDiscriminant
    nlinarith only [hr.2,hsqup]
  have he := Real.sq_sqrt (show 0 ≤ radialDiscriminant κ s by linarith)
  have hn := Real.sqrt_nonneg (radialDiscriminant κ s)
  have hrl : (1496/1000 : ℝ) ≤ Real.sqrt (radialDiscriminant κ s) := by
    nlinarith only [hd,he,hn]
  have hru : Real.sqrt (radialDiscriminant κ s) ≤ (1504/1000 : ℝ) := by
    nlinarith only [hdu,he,hn]
  have hxl : (-1/1000 : ℝ) ≤ radialAbscissa κ s+3/4 := by
    unfold radialAbscissa
    linarith
  have hxu : radialAbscissa κ s+3/4 ≤ (1/1000 : ℝ) := by
    unfold radialAbscissa
    linarith
  have hx2 := sq_le_sq' (show -(1/1000 : ℝ) ≤ radialAbscissa κ s+3/4 by
    linarith only [hxl]) hxu
  have hc := radial_circle_identity hk hsfull
  nlinarith only [hx2,hc]

private theorem radialTerminal_antitone {κ k₂ v w : ℝ}
    (hk : 0 ≤ κ) (hkl : κ ≤ k₂) (hv : 0 ≤ v) (hvw : v ≤ w) :
    radialTerminal k₂ w ≤ radialTerminal κ v := by
  have hl : 0 ≤ k₂ := hk.trans hkl
  have hw : 0 ≤ w := hv.trans hvw
  have hav : 0 ≤ κ*v := mul_nonneg hk hv
  have ha := mul_le_mul hkl hvw hv hl
  have ha2 := pow_le_pow_left₀ hav ha 2
  have hy : 4*(κ*v)+4*(κ*v)^2 ≤ 4*(k₂*w)+4*(k₂*w)^2 := by linarith
  have hy0 : 0 ≤ 4*(κ*v)+4*(κ*v)^2 := by positivity
  have hb := mul_le_mul hkl hy hy0 hl
  have hb0 : 0 ≤ 1+κ*(4*(κ*v)+4*(κ*v)^2) := by positivity
  have hb2 := pow_le_pow_left₀ hb0
    (show 1+κ*(4*(κ*v)+4*(κ*v)^2) ≤ 1+k₂*(4*(k₂*w)+4*(k₂*w)^2) by linarith) 2
  have hf := mul_le_mul hkl hb2 (sq_nonneg _) hl
  unfold radialTerminal
  linarith

private theorem model_endpoint_margins {κ : ℝ} (hk : κ ∈ parameterInterval) :
    -1+1/10000 < crestTerminal κ (663/10000) ∧
      crestTerminal κ (133/2000) < -1-1/10000 := by
  have hsi : (663/10000 : ℝ) ∈ Radius := by constructor <;> norm_num
  have hso : (133/2000 : ℝ) ∈ Radius := by constructor <;> norm_num
  have hcircle := radial_circle_identity hk hsi
  have hu : radialOrdinateSq κ (663/10000) ≤ (663/10000 : ℝ)^2 := by
    nlinarith only [hcircle,sq_nonneg (radialAbscissa κ (663/10000)+3/4)]
  have hl := ordinate_lower hk
    (show (133/2000 : ℝ) ∈ Icc (1/16 : ℝ) (133/2000) by constructor <;> norm_num)
  have hi := radialTerminal_antitone (by linarith [hk.1]) hk.2
    (radial_ordinate_pos hk hsi).le hu
  have ho := radialTerminal_antitone (by norm_num : (0 : ℝ) ≤ 17903/10000) hk.1
    (by norm_num : (0 : ℝ) ≤ (133/2000 : ℝ)^2-1/1000000) hl
  have hri : (-1+1/10000 : ℝ) < radialTerminal (17904/10000) ((663/10000)^2) := by
    norm_num [radialTerminal]
  have hro : radialTerminal (17903/10000) ((133/2000)^2-1/1000000) <
      (-1-1/10000 : ℝ) := by norm_num [radialTerminal]
  exact ⟨hri.trans_le hi,ho.trans_lt hro⟩

private theorem model_initial_upper_margin {κ : ℝ} (hk : κ ∈ parameterInterval) :
    crestTerminal κ (1/16) < (-9753/10000 : ℝ) := by
  have hl := ordinate_lower hk
    (show (1/16 : ℝ) ∈ Icc (1/16 : ℝ) (133/2000) by constructor <;> norm_num)
  have hm := radialTerminal_antitone (by norm_num : (0 : ℝ) ≤ 17903/10000) hk.1
    (by norm_num : (0 : ℝ) ≤ (1/16 : ℝ)^2-1/1000000) hl
  have hr : radialTerminal (17903/10000) ((1/16)^2-1/1000000) <
      (-9753/10000 : ℝ) := by norm_num [radialTerminal]
  exact hm.trans_lt hr

private theorem fourth_critical_upper {κ : ℝ} (hk : κ ∈ parameterInterval) :
    (realMap κ)^[4] 0 < (9751/10000 : ℝ) := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have ha : (7903/10000 : ℝ) ≤ κ-1 := by linarith [hk.1]
  have ha2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7903/10000) ha 2
  have hp := mul_le_mul hk.1 ha2 (by norm_num) hk0
  have hb : (1181/10000 : ℝ) ≤ -(1-κ*(1-κ)^2) := by nlinarith only [hp]
  have hb2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1181/10000) hb 2
  have hq := mul_le_mul hk.1 hb2 (by norm_num) hk0
  change 1-κ*(1-κ*(1-κ*(1-κ*0^2)^2)^2)^2 < 9751/10000
  norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,sub_zero,one_pow,mul_one]
  nlinarith only [hq]

private theorem model_critical_cast (κ : ℝ) (n : ℕ) :
    ((complexMap κ)^[n]) (0 : ℂ) = (((realMap κ)^[n]) (0 : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',ih,complexMap_real]

private theorem actual_fourth_cut_error {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    |(((normalizedReturn c p)^[4]) 0).re-((realMap (kappa p c))^[4]) 0| ≤
      1/100000 := by
  have hk := hc.2.2.2.1
  have he := LimitingCrestPerturbation.quadratic_fourth_cut_error (kappa p c)
    (by linarith [hk.1]) (by linarith [hk.2])
    (normalizedReturn c p) (1/100000000) (by norm_num) (by norm_num)
    (by
      intro w hw
      simpa only [complexMap] using actual_return_error_small hp hc
        (hw.trans (by norm_num : (23/20 : ℝ) ≤ 3/2)))
  have hn : ‖((normalizedReturn c p)^[4]) 0-
      ((complexMap (kappa p c))^[4]) 0‖ ≤ 1/100000 :=
    he.1.trans (by norm_num)
  have hr := (Complex.abs_re_le_norm
    (((normalizedReturn c p)^[4]) 0-((complexMap (kappa p c))^[4]) 0)).trans hn
  rw [model_critical_cast] at hr
  simpa only [Complex.sub_re,Complex.ofReal_re] using hr

/-- Both strict endpoint tests hold for the actual global crossing family
at every period at least seventeen, with no eventual-period premise. -/
theorem actual_endpoint_signs {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    -1 < terminal F (663/10000) ∧ terminal F (133/2000) < -1 := by
  have hm := model_endpoint_margins hc.2.2.2.1
  have hi := abs_le.mp (actual_coefficient_terminal_error hp hc F
    (show (663/10000 : ℝ) ∈ Icc (1/16 : ℝ) (133/2000) by constructor <;> norm_num))
  have ho := abs_le.mp (actual_coefficient_terminal_error hp hc F
    (show (133/2000 : ℝ) ∈ Icc (1/16 : ℝ) (133/2000) by constructor <;> norm_num))
  constructor <;> linarith [hm.1,hm.2]

/-- The initial point already lies strictly below the opposite actual
critical cut. Global strict radial order will propagate this inequality. -/
theorem actual_initial_upper_gate {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    terminal F (1/16) < -(((normalizedReturn c p)^[4]) 0).re := by
  have ht := abs_le.mp (actual_coefficient_terminal_error hp hc F
    (show (1/16 : ℝ) ∈ Icc (1/16 : ℝ) (133/2000) by constructor <;> norm_num))
  have hcerror := abs_le.mp (actual_fourth_cut_error hp hc)
  have hbase := model_initial_upper_margin hc.2.2.2.1
  have hcut := fourth_critical_upper hc.2.2.2.1
  linarith

end
end GlobalCrestEndpointValues
