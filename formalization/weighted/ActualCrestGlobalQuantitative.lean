import ActualCrestGlobalModel

/-!
# Quantitative exclusion of late terminal gates for every period at least seventeen

The comparison is made with the actual quadratic coefficient, rather than
with the limiting coefficient.  Its remainder is small enough already at
period seventeen.  Explicit angular inversion and a rational terminal
margin replace the nonquantitative compactness threshold.
-/

namespace ActualCrestGlobalQuantitative

open Set Function
open LimitingCrest NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter ActualCrestGlobalModel

set_option autoImplicit false

noncomputable section

private theorem reciprocal_bounds {κ : ℝ} (hk : κ ∈ parameterInterval) :
    (223/50 : ℝ) ≤ 8/κ ∧ 8/κ ≤ 447/100 := by
  have hk0 : 0 < κ := by linarith [hk.1]
  constructor
  · apply (le_div_iff₀ hk0).mpr
    nlinarith [hk.2]
  · apply (div_le_iff₀ hk0).mpr
    nlinarith [hk.1]

private theorem model_parent_root {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) :
    ∃ v ∈ Icc (-1/4 : ℝ) (1/4), crossing κ s v = 0 := by
  have hspos : 0 < s := by linarith [hs.1]
  obtain ⟨hrecL,hrecU⟩ := reciprocal_bounds hk
  have hsqL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/16) hs.1 2
  have hsqU := pow_le_pow_left₀ hspos.le hs.2 2
  have hdL : (56/25 : ℝ) ≤ radialDiscriminant κ s := by
    unfold radialDiscriminant
    nlinarith only [hrecL,hsqL]
  have hdU : radialDiscriminant κ s ≤ (2345/1000 : ℝ) := by
    unfold radialDiscriminant
    nlinarith only [hrecU,hsqU]
  have hr := Real.sq_sqrt (show 0 ≤ radialDiscriminant κ s by linarith)
  have hn := Real.sqrt_nonneg (radialDiscriminant κ s)
  have hrL : (1496/1000 : ℝ) ≤ Real.sqrt (radialDiscriminant κ s) := by
    nlinarith only [hdL,hr,hn]
  have hrU : Real.sqrt (radialDiscriminant κ s) ≤ (1532/1000 : ℝ) := by
    nlinarith only [hdU,hr,hn]
  have hxL : (-1/100 : ℝ) ≤ radialAbscissa κ s+3/4 := by
    unfold radialAbscissa
    linarith
  have hxU : radialAbscissa κ s+3/4 ≤ (1/100 : ℝ) := by
    unfold radialAbscissa
    linarith
  let v := (radialAbscissa κ s+3/4)/s
  have hv : v ∈ Icc (-1/4 : ℝ) (1/4) := by
    constructor
    · apply (le_div_iff₀ hspos).mpr
      linarith [hs.1]
    · apply (div_le_iff₀ hspos).mpr
      linarith [hs.1]
  have hvfull : v ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have hcoord : -3/4+s*v = radialAbscissa κ s := by
    dsimp [v]
    field_simp
    ring
  have hp := radialPoint_eq_circlePoint hk hs hvfull hcoord
  have himage := (radial_model_realization hk hs).2.2.1
  rw [hp,circle_image κ s hvfull] at himage
  have hreal := congrArg Complex.re himage
  refine ⟨v,hv,?_⟩
  simpa using hreal

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
  have hb2 := pow_le_pow_left₀ hb0 (show
      1+κ*(4*(κ*v)+4*(κ*v)^2) ≤ 1+k₂*(4*(k₂*w)+4*(k₂*w)^2) by linarith) 2
  have hf := mul_le_mul hkl hb2 (sq_nonneg _) hl
  unfold radialTerminal
  linarith

private theorem radial_ordinate_lower_short {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    s^2-1/1000000 ≤ radialOrdinateSq κ s := by
  obtain ⟨hrecL,hrecU⟩ := reciprocal_bounds hk
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/16) hs.1 2
  have hsU := pow_le_pow_left₀ hs0 hs.2 2
  have hdL : (56/25 : ℝ) ≤ radialDiscriminant κ s := by
    unfold radialDiscriminant
    nlinarith only [hrecL,hsL]
  have hdU : radialDiscriminant κ s ≤ (2256/1000 : ℝ) := by
    unfold radialDiscriminant
    nlinarith only [hrecU,hsU]
  have hr := Real.sq_sqrt (show 0 ≤ radialDiscriminant κ s by linarith)
  have hn := Real.sqrt_nonneg (radialDiscriminant κ s)
  have hrL : (1496/1000 : ℝ) ≤ Real.sqrt (radialDiscriminant κ s) := by
    nlinarith only [hdL,hr,hn]
  have hrU : Real.sqrt (radialDiscriminant κ s) ≤ (1504/1000 : ℝ) := by
    nlinarith only [hdU,hr,hn]
  have hxL : (-1/1000 : ℝ) ≤ radialAbscissa κ s+3/4 := by
    unfold radialAbscissa
    linarith
  have hxU : radialAbscissa κ s+3/4 ≤ (1/1000 : ℝ) := by
    unfold radialAbscissa
    linarith
  have hxsq := sq_le_sq'
    (show -(1/1000 : ℝ) ≤ radialAbscissa κ s+3/4 by linarith only [hxL]) hxU
  have hcircle := radial_circle_identity hk
    (show s ∈ Icc (1/16 : ℝ) (1/8) from ⟨hs.1,by linarith [hs.2]⟩)
  nlinarith only [hxsq,hcircle]

/-- A rational terminal gap, uniform over the coefficient interval and
the whole outer part of the original parent. -/
theorem model_tail_terminal_margin {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Icc (133/2000 : ℝ) (1/8)) :
    crestTerminal κ s < -1-7/10000 := by
  have hb : (133/2000 : ℝ) ∈ Icc (1/16 : ℝ) (1/8) := by
    constructor <;> norm_num
  have hv := radial_ordinate_lower_short hk
    (show (133/2000 : ℝ) ∈ Icc (1/16 : ℝ) (133/2000) by constructor <;> norm_num)
  have hbound := radialTerminal_antitone (by norm_num : (0 : ℝ) ≤ 17903/10000)
    hk.1 (by norm_num : (0 : ℝ) ≤ (133/2000 : ℝ)^2-1/1000000) hv
  have hrat : radialTerminal (17903/10000) ((133/2000)^2-1/1000000) <
      (-1-7/10000 : ℝ) := by
    norm_num [radialTerminal]
  have hbase : crestTerminal κ (133/2000) < (-1-7/10000 : ℝ) := hbound.trans_lt hrat
  have hs' : s ∈ Icc (1/16 : ℝ) (1/8) := ⟨by linarith [hs.1],hs.2⟩
  exact ((crestTerminal_strictAnti hk).antitoneOn hb hs' hs.1).trans_lt hbase

/-- The inner endpoint of the terminal bracket has a uniform rational
margin on the admissible side of the lower cut. -/
theorem model_inner_terminal_margin {κ : ℝ} (hk : κ ∈ parameterInterval) :
    -1+4/10000 < crestTerminal κ (663/10000) := by
  have hs : (663/10000 : ℝ) ∈ Icc (1/16 : ℝ) (1/8) := by
    constructor <;> norm_num
  have hc := radial_circle_identity hk hs
  have hv : radialOrdinateSq κ (663/10000) ≤ (663/10000 : ℝ)^2 := by
    nlinarith only [hc,sq_nonneg (radialAbscissa κ (663/10000)+3/4)]
  have hbound := radialTerminal_antitone (by linarith [hk.1]) hk.2
    (radial_ordinate_pos hk hs).le hv
  have hrat : (-1+4/10000 : ℝ) < radialTerminal (17904/10000) ((663/10000)^2) := by
    norm_num [radialTerminal]
  exact hrat.trans_le hbound

/-- An explicit upper terminal bound holds on the entire original
parent, leaving enough room for both actual perturbation errors. -/
theorem model_uniform_upper_margin {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) :
    crestTerminal κ s < -97537/100000 := by
  have hb : (1/16 : ℝ) ∈ Icc (1/16 : ℝ) (1/8) := by
    constructor <;> norm_num
  have hv := radial_ordinate_lower_short hk
    (show (1/16 : ℝ) ∈ Icc (1/16 : ℝ) (133/2000) by constructor <;> norm_num)
  have hbound := radialTerminal_antitone (by norm_num : (0 : ℝ) ≤ 17903/10000)
    hk.1 (by norm_num : (0 : ℝ) ≤ (1/16 : ℝ)^2-1/1000000) hv
  have hrat : radialTerminal (17903/10000) ((1/16)^2-1/1000000) <
      (-97537/100000 : ℝ) := by
    norm_num [radialTerminal]
  have hbase : crestTerminal κ (1/16) < (-97537/100000 : ℝ) := hbound.trans_lt hrat
  exact ((crestTerminal_strictAnti hk).antitoneOn hb hs hs.1).trans_lt hbase

/-- The sharp model fourth-cut bound used to certify the opposite
terminal inequality after perturbation. -/
theorem model_fourth_cut_margin {κ : ℝ} (hk : κ ∈ parameterInterval) :
    (realMap κ)^[4] 0 < 9751/10000 := by
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

private theorem sqrt_semicircle_difference {u v : ℝ}
    (hu : u ∈ Icc (-1/2 : ℝ) (1/2)) (hv : v ∈ Icc (-1/2 : ℝ) (1/2)) :
    |Real.sqrt (1-u^2)-Real.sqrt (1-v^2)| ≤ |u-v| := by
  have hu2 := sq_le_sq' (show -(1/2 : ℝ) ≤ u by linarith [hu.1]) hu.2
  have hv2 := sq_le_sq' (show -(1/2 : ℝ) ≤ v by linarith [hv.1]) hv.2
  have hru := Real.sq_sqrt (show 0 ≤ 1-u^2 by nlinarith)
  have hrv := Real.sq_sqrt (show 0 ≤ 1-v^2 by nlinarith)
  have hnu := Real.sqrt_nonneg (1-u^2)
  have hnv := Real.sqrt_nonneg (1-v^2)
  have hlu : (1/2 : ℝ) ≤ Real.sqrt (1-u^2) := by nlinarith
  have hlv : (1/2 : ℝ) ≤ Real.sqrt (1-v^2) := by nlinarith
  have hid : (Real.sqrt (1-u^2)-Real.sqrt (1-v^2))*
      (Real.sqrt (1-u^2)+Real.sqrt (1-v^2)) = (u-v)*(-(u+v)) := by
    nlinarith only [hru,hrv]
  have ha := congrArg abs hid
  rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg (add_nonneg hnu hnv)] at ha
  have hsum : |u+v| ≤ (1 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg (u-v))
  nlinarith only [ha,hm,hlu,hlv,abs_nonneg
    (Real.sqrt (1-u^2)-Real.sqrt (1-v^2))]

private theorem circlePoint_distance {s u v : ℝ}
    (hs : s ∈ Icc (1/16 : ℝ) (1/8))
    (hu : u ∈ Icc (-1/2 : ℝ) (1/2)) (hv : v ∈ Icc (-1/2 : ℝ) (1/2)) :
    ‖circlePoint s u-circlePoint s v‖ ≤ (1/4 : ℝ)*|u-v| := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hroot := sqrt_semicircle_difference hu hv
  have he : circlePoint s u-circlePoint s v =
      ((s*(u-v) : ℝ) : ℂ)+
        ((s*(Real.sqrt (1-u^2)-Real.sqrt (1-v^2)) : ℝ) : ℂ)*Complex.I := by
    unfold circlePoint
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖((s*(u-v) : ℝ) : ℂ)‖+
        ‖((s*(Real.sqrt (1-u^2)-Real.sqrt (1-v^2)) : ℝ) : ℂ)*Complex.I‖ :=
      norm_add_le _ _
    _ = s*|u-v|+s*|Real.sqrt (1-u^2)-Real.sqrt (1-v^2)| := by
      simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
        Real.norm_eq_abs,abs_mul,abs_of_nonneg hs0]
    _ ≤ s*|u-v|+s*|u-v| :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hroot hs0)
    _ ≤ (1/4 : ℝ)*|u-v| := by
      have hm := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg (u-v))
      linarith

private theorem model_lipschitz_two {κ : ℝ} (hk : κ ∈ parameterInterval)
    {z w : ℂ} (hz : ‖z‖ ≤ 2) (hw : ‖w‖ ≤ 2) :
    ‖complexMap κ z-complexMap κ w‖ ≤ 8*‖z-w‖ := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hk2 : κ ≤ 2 := by linarith [hk.2]
  have hid : complexMap κ z-complexMap κ w = -(κ : ℂ)*(z-w)*(z+w) := by
    unfold complexMap
    ring
  have hsum : κ*(‖z‖+‖w‖) ≤ 8 := by
    calc
      κ*(‖z‖+‖w‖) ≤ 2*(‖z‖+‖w‖) :=
        mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ ≤ 8 := by linarith
  calc
    _ = κ*‖z-w‖*‖z+w‖ := by
      rw [hid,norm_mul,norm_mul,norm_neg,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg hk0]
    _ ≤ κ*‖z-w‖*(‖z‖+‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = (κ*(‖z‖+‖w‖))*‖z-w‖ := by ring
    _ ≤ 8*‖z-w‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

private theorem model_third_circle_difference {κ s u v : ℝ}
    (hk : κ ∈ parameterInterval) (hs : s ∈ Icc (1/16 : ℝ) (1/8))
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    ‖((complexMap κ)^[3]) (circlePoint s u)-
      ((complexMap κ)^[3]) (circlePoint s v)‖ ≤
        512*‖circlePoint s u-circlePoint s v‖ := by
  let z := circlePoint s u
  let w := circlePoint s v
  let Q := complexMap κ
  have hz : ‖z‖ ≤ 2 := (parent_circle_norm hs hu).trans (by norm_num)
  have hw : ‖w‖ ≤ 2 := (parent_circle_norm hs hv).trans (by norm_num)
  have hzD : ‖z+(3/4 : ℂ)‖ ≤ 1/8 := by
    rw [circle_radius (by linarith [hs.1] : 0 ≤ s) hu]
    exact hs.2
  have hwD : ‖w+(3/4 : ℂ)‖ ≤ 1/8 := by
    rw [circle_radius (by linarith [hs.1] : 0 ≤ s) hv]
    exact hs.2
  obtain ⟨hz1,hz2⟩ := model_parent_intermediate_bounds hk hzD
  obtain ⟨hw1,hw2⟩ := model_parent_intermediate_bounds hk hwD
  have h0 := model_lipschitz_two hk hz hw
  have h1 := model_lipschitz_two hk (show ‖Q z‖ ≤ 2 by linarith)
    (show ‖Q w‖ ≤ 2 by linarith)
  have h2 := model_lipschitz_two hk (show ‖Q (Q z)‖ ≤ 2 by linarith)
    (show ‖Q (Q w)‖ ≤ 2 by linarith)
  change ‖Q z-Q w‖ ≤ 8*‖z-w‖ at h0
  change ‖Q (Q z)-Q (Q w)‖ ≤ 8*‖Q z-Q w‖ at h1
  change ‖Q (Q (Q z))-Q (Q (Q w))‖ ≤ 8*‖Q (Q z)-Q (Q w)‖ at h2
  change ‖Q (Q (Q z))-Q (Q (Q w))‖ ≤ 512*‖z-w‖
  linarith

/-- Every actual crossing in the complete parent has an explicit
third-image error from the exact radical model, uniformly in both coordinates. -/
theorem quantitative_crossing_error {κ : ℝ} (hk : κ ∈ parameterInterval)
    (H : ℂ → ℂ)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 2 → ‖H w-complexMap κ w‖ ≤ 1/10000000)
    {s u : ℝ} (hs : s ∈ Icc (1/16 : ℝ) (1/8))
    (hu : u ∈ Icc (-1 : ℝ) 1) (hzero : (H (circlePoint s u)).re = 0) :
    ‖((H^[3]) (circlePoint s u))-(crestTerminal κ s : ℂ)‖ ≤ 1609/10000000 := by
  have hs' := hs
  have hz2 : ‖circlePoint s u‖ ≤ 2 := (parent_circle_norm hs' hu).trans (by norm_num)
  have hre := (Complex.abs_re_le_norm
    (H (circlePoint s u)-complexMap κ (circlePoint s u))).trans (hclose _ hz2)
  simp only [Complex.sub_re,hzero,zero_sub,abs_neg] at hre
  have hcre : (complexMap κ (circlePoint s u)).re = crossing κ s u := by
    rw [circle_image κ s hu]
    simp
  rw [hcre] at hre
  obtain ⟨v,hv,hvz⟩ := model_parent_root hk hs'
  have hvfull : v ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have huv : |u-v| ≤ (1/1000000 : ℝ) := by
    rcases le_total u v with h | h
    · have hg := crossing_global_growth hk hs' hu hvfull h
      rw [hvz] at hg
      rw [abs_of_nonpos (by linarith : u-v ≤ 0)]
      linarith [(abs_le.mp hre).1]
    · have hg := crossing_global_growth hk hs' hvfull hu h
      rw [hvz] at hg
      rw [abs_of_nonneg (by linarith : 0 ≤ u-v)]
      linarith [(abs_le.mp hre).2]
  have huhalf : u ∈ Icc (-1/2 : ℝ) (1/2) := by
    constructor <;> linarith [hv.1,hv.2,(abs_le.mp huv).1,(abs_le.mp huv).2]
  have hvhalf : v ∈ Icc (-1/2 : ℝ) (1/2) := ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have hpoint : ‖circlePoint s u-circlePoint s v‖ ≤ (3/10000000 : ℝ) := by
    have hd := circlePoint_distance hs' huhalf hvhalf
    linarith
  have hmodelError := (model_third_circle_difference hk hs' hu hvfull).trans
    (mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 512))
  have hvzero : (complexMap κ (circlePoint s v)).re = 0 := by
    rw [circle_image κ s hvfull]
    simpa using hvz
  have hmodelThird := model_crossing_third_image hk hs' hvfull hvzero
  have hradius : ‖circlePoint s u+(3/4 : ℂ)‖ ≤ 1/8 := by
    rw [circle_radius (by linarith [hs.1] : 0 ≤ s) hu]
    exact hs.2
  have hactualError := parent_third_iterate_error hk H
    (by norm_num : (0 : ℝ) ≤ 1/10000000)
    (by norm_num : (1/10000000 : ℝ) ≤ 1/100) hclose hradius
  rw [← hmodelThird]
  have htri : ‖(H^[3]) (circlePoint s u)-((complexMap κ)^[3]) (circlePoint s v)‖ ≤
      ‖(H^[3]) (circlePoint s u)-((complexMap κ)^[3]) (circlePoint s u)‖+
        ‖((complexMap κ)^[3]) (circlePoint s u)-((complexMap κ)^[3]) (circlePoint s v)‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      ((H^[3]) (circlePoint s u)) (((complexMap κ)^[3]) (circlePoint s u))
        (((complexMap κ)^[3]) (circlePoint s v))
  linarith

/-- The explicit perturbation tolerance has a positive terminal margin
on every late radius and every angle of the upper semicircle. -/
theorem quantitative_tail_exclusion {κ : ℝ} (hk : κ ∈ parameterInterval)
    (H : ℂ → ℂ)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 2 → ‖H w-complexMap κ w‖ ≤ 1/10000000)
    {s u : ℝ} (hs : s ∈ Icc (133/2000 : ℝ) (1/8))
    (hu : u ∈ Icc (-1 : ℝ) 1) (hzero : (H (circlePoint s u)).re = 0) :
    ((H^[3]) (circlePoint s u)).re < -1-1/2000 := by
  have hs' : s ∈ Icc (1/16 : ℝ) (1/8) := ⟨by linarith [hs.1],hs.2⟩
  have he := quantitative_crossing_error hk H hclose hs' hu hzero
  have hr := (Complex.re_le_norm
    ((H^[3]) (circlePoint s u)-(crestTerminal κ s : ℂ))).trans he
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  have hm := model_tail_terminal_margin hk hs
  linarith

/-- The actual quadratic coefficient gives the required explicit disk
error for every period at least seventeen. -/
theorem actual_map_error_small {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ∀ w : ℂ, ‖w‖ ≤ 2 →
      ‖normalizedReturn c p w-complexMap (kappa p c) w‖ ≤ 1/10000000 := by
  intro w hw
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1
  have he := ActualCrestLargeDisk.normalized_return_error_two c p hp
    hc.2.2.2.2.2.2 hc.2.1 hsmall w hw
  change ‖normalizedReturn c p w-complexMap (kappa p c) w‖ ≤ _ at he
  have hpowers := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
  have hbound : 216/(4 : ℝ)^p ≤ (1/10000000 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4^p)).mpr
    norm_num at hpowers
    linarith
  exact he.trans hbound

/-- No late terminal gate exists for any actual signed-tip parameter of
any period at least seventeen.  The strict margin is uniform in all
parameters, all late radii, and all upper-semicircle angles. -/
theorem all_actual_tips_no_reentry {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {s u : ℝ}
    (hs : s ∈ Icc (133/2000 : ℝ) (1/8)) (hu : u ∈ Icc (-1 : ℝ) 1)
    (hzero : (normalizedReturn c p (circlePoint s u)).re = 0) :
    (((normalizedReturn c p)^[3]) (circlePoint s u)).re < -1-1/2000 := by
  exact quantitative_tail_exclusion hc.2.2.2.1 (normalizedReturn c p)
    (actual_map_error_small hp hc) hs hu hzero

end
end ActualCrestGlobalQuantitative
