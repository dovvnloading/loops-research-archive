import ActualCrestLargeDisk
import LimitingCrestModelGates
import Mathlib.Topology.Order.Compact

/-!
# Exclusion of every later actual terminal gate on the original parent

The earlier actual endpoint theorem controls only the short interval ending
at 133/2000.  Here the complement of that interval, all the way to the
original parent radius 1/8, is treated simultaneously.  Compactness is
applied to the entire radius-angle rectangle, not to a previously selected
actual crossing curve.  Thus the conclusion excludes additional
terminal-admissible crossings and disconnected late gate components as well.

The three-fold comparison proves the required intermediate-domain bounds
before evaluating the enlarged actual return estimate at those points.
-/

namespace ActualCrestGlobalModel

open Set Function Filter
open scoped Topology
open LimitingCrest NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter

noncomputable section

/-- Every point of the complete parent circle lies in one fixed disk. -/
theorem parent_circle_norm {s u : ℝ}
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖circlePoint s u‖ ≤ 7/8 := by
  have hr := circle_radius (show 0 ≤ s by linarith [hs.1]) hu
  calc
    ‖circlePoint s u‖ = ‖(circlePoint s u + (3/4 : ℂ)) - (3/4 : ℂ)‖ := by
      congr 1
      ring
    _ ≤ ‖circlePoint s u + (3/4 : ℂ)‖ + ‖(3/4 : ℂ)‖ := norm_sub_le _ _
    _ = s+3/4 := by rw [hr]; norm_num
    _ ≤ 7/8 := by linarith [hs.2]

/-- An arbitrary model crossing on the whole upper semicircle is the
radical branch.  No preselected angular root is a premise. -/
theorem model_crossing_third_image {κ s u : ℝ}
    (hk : κ ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) (hu : u ∈ Icc (-1 : ℝ) 1)
    (hzero : (complexMap κ (circlePoint s u)).re = 0) :
    ((complexMap κ)^[3]) (circlePoint s u) = (crestTerminal κ s : ℂ) := by
  have hk0 : κ ≠ 0 := by linarith [hk.1]
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hcross : crossing κ s u = 0 := by
    rw [circle_image κ s hu] at hzero
    simpa using hzero
  have hsu := mul_le_mul_of_nonneg_left hu.2 hs0
  have hpos : 0 ≤ (3/2 : ℝ)-4*s*u := by linarith [hs.2]
  have hdisc : radialDiscriminant κ s = (3/2-4*s*u)^2 := by
    unfold radialDiscriminant
    dsimp [crossing] at hcross
    field_simp [hk0]
    nlinarith [hcross]
  have hcoord : -3/4+s*u = radialAbscissa κ s := by
    unfold radialAbscissa
    rw [hdisc, Real.sqrt_sq_eq_abs, abs_of_nonneg hpos]
    ring
  have hpoint := LimitingCrest.radialPoint_eq_circlePoint hk hs hu hcoord
  rw [← hpoint]
  exact (radial_model_realization hk hs).2.2.2

/-- Every exact model crossing after the certified endpoint bracket has
already crossed the lower terminal cut, throughout the original parent. -/
theorem model_tail_crossing_below_cut {κ s u : ℝ}
    (hk : κ ∈ parameterInterval)
    (hs : s ∈ Icc (133/2000 : ℝ) (1/8)) (hu : u ∈ Icc (-1 : ℝ) 1)
    (hzero : (complexMap κ (circlePoint s u)).re = 0) :
    (((complexMap κ)^[3]) (circlePoint s u)).re < -1 := by
  have hs' : s ∈ Icc (1/16 : ℝ) (1/8) := ⟨by linarith [hs.1], hs.2⟩
  have he := model_crossing_third_image hk hs' hu hzero
  have hbase : (133/2000 : ℝ) ∈ Icc (1/16 : ℝ) (1/8) := by
    constructor <;> norm_num
  have hm := (crestTerminal_strictAnti hk).antitoneOn hbase hs' hs.1
  rw [he]
  simpa only [Complex.ofReal_re] using hm.trans_lt (crestTerminal_endpoint_signs hk).2

/-- Uniform strict separation from a terminal gate holds even for
approximate angular crossings.  This is a compactness statement about the
whole radius-angle rectangle, including all possible unselected roots. -/
theorem model_tail_crossing_gap {κ : ℝ} (hk : κ ∈ parameterInterval) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc (133/2000 : ℝ) (1/8), ∀ u ∈ Icc (-1 : ℝ) 1,
        |(complexMap κ (circlePoint s u)).re| < δ →
          (((complexMap κ)^[3]) (circlePoint s u)).re ≤ -1-δ := by
  let K : Set (ℝ × ℝ) := Icc (133/2000 : ℝ) (1/8) ×ˢ Icc (-1 : ℝ) 1
  let defect : ℝ × ℝ → ℝ := fun w =>
    max |(complexMap κ (circlePoint w.1 w.2)).re|
      (-1-(((complexMap κ)^[3]) (circlePoint w.1 w.2)).re)
  have hQ : Continuous (complexMap κ) := by unfold complexMap; fun_prop
  have hcircle : Continuous (fun w : ℝ × ℝ => circlePoint w.1 w.2) := by
    unfold circlePoint
    fun_prop
  have hdefect : Continuous defect :=
    (Complex.continuous_re.comp (hQ.comp hcircle)).abs.max
      (continuous_const.sub (Complex.continuous_re.comp ((hQ.iterate 3).comp hcircle)))
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨(133/2000, 0), ?_⟩
    change (133/2000 : ℝ) ∈ Icc (133/2000) (1/8) ∧ (0 : ℝ) ∈ Icc (-1) 1
    constructor <;> constructor <;> norm_num
  have hpositive (w : ℝ × ℝ) (hw : w ∈ K) : 0 < defect w := by
    by_cases hz : (complexMap κ (circlePoint w.1 w.2)).re = 0
    · have hterm := model_tail_crossing_below_cut hk hw.1 hw.2 hz
      exact lt_of_lt_of_le (by linarith : 0 <
        -1-(((complexMap κ)^[3]) (circlePoint w.1 w.2)).re) (le_max_right _ _)
    · exact lt_of_lt_of_le (abs_pos.mpr hz) (le_max_left _ _)
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hKne hdefect.continuousOn
  refine ⟨defect w, hpositive w hw, ?_⟩
  intro s hs u hu hsmall
  have hm := hmin (show (s,u) ∈ K from ⟨hs,hu⟩)
  change defect w ≤ max |(complexMap κ (circlePoint s u)).re|
    (-1-(((complexMap κ)^[3]) (circlePoint s u)).re) at hm
  rcases le_max_iff.mp hm with hfirst | hthird
  · exact False.elim (not_lt_of_ge hfirst hsmall)
  · linarith

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
    ‖complexMap κ z-complexMap κ w‖ = κ*‖z-w‖*‖z+w‖ := by
      rw [hid, norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hk0]
    _ ≤ κ*‖z-w‖*(‖z‖+‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = (κ*(‖z‖+‖w‖))*‖z-w‖ := by ring
    _ ≤ 8*‖z-w‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-- The first two complete model images of the full parent disk stay
strictly inside the radius-two approximation disk. -/
theorem model_parent_intermediate_bounds {κ : ℝ} (hk : κ ∈ parameterInterval)
    {z : ℂ} (hz : ‖z+(3/4 : ℂ)‖ ≤ 1/8) :
    ‖complexMap κ z‖ ≤ 2/5 ∧ ‖complexMap κ (complexMap κ z)‖ ≤ 3/2 := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hkU : κ ≤ (9/5 : ℝ) := by linarith [hk.2]
  have hzsum : ‖z-(3/4 : ℂ)‖ ≤ 13/8 := by
    calc
      ‖z-(3/4 : ℂ)‖ = ‖(z+(3/4 : ℂ))-(3/2 : ℂ)‖ := by congr 1; ring
      _ ≤ ‖z+(3/4 : ℂ)‖+‖(3/2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 13/8 := by norm_num; linarith
  have hcenter : ‖complexMap κ (-(3/4 : ℂ))‖ ≤ (1/100 : ℝ) := by
    have he : complexMap κ (-(3/4 : ℂ)) = ((1-κ*(3/4)^2 : ℝ) : ℂ) := by
      simp only [complexMap, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [hk.1,hk.2]
  have hdiff : ‖complexMap κ z-complexMap κ (-(3/4 : ℂ))‖ ≤
      (9/5 : ℝ)*(1/8)*(13/8) := by
    have he : complexMap κ z-complexMap κ (-(3/4 : ℂ)) =
        -(κ : ℂ)*(z+(3/4 : ℂ))*(z-(3/4 : ℂ)) := by
      unfold complexMap
      ring
    rw [he, norm_mul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hk0]
    exact mul_le_mul (mul_le_mul hkU hz (norm_nonneg _) (by norm_num)) hzsum
      (norm_nonneg _) (by norm_num)
  have hfirst : ‖complexMap κ z‖ ≤ 2/5 := by
    have htri : ‖complexMap κ z‖ ≤
        ‖complexMap κ z-complexMap κ (-(3/4 : ℂ))‖+
          ‖complexMap κ (-(3/4 : ℂ))‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (complexMap κ z-complexMap κ (-(3/4 : ℂ)))
          (complexMap κ (-(3/4 : ℂ)))
    linarith
  refine ⟨hfirst, ?_⟩
  have hsquare := pow_le_pow_left₀ (norm_nonneg (complexMap κ z)) hfirst 2
  have hprod := mul_le_mul hkU hsquare (sq_nonneg _) (by norm_num)
  have htri := norm_sub_le (1 : ℂ) ((κ : ℂ)*(complexMap κ z)^2)
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hk0, norm_pow] at htri
  change ‖1-(κ : ℂ)*(complexMap κ z)^2‖ ≤ 3/2
  nlinarith only [htri,hprod]

/-- Three actual compositions are compared without assuming any bound
on an actual intermediate iterate.  The first two domain checks follow
from the model bounds and the errors at preceding stages. -/
theorem parent_third_iterate_error {κ ε : ℝ} (hk : κ ∈ parameterInterval)
    (H : ℂ → ℂ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/100)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 2 → ‖H w-complexMap κ w‖ ≤ ε)
    {z : ℂ} (hz : ‖z+(3/4 : ℂ)‖ ≤ 1/8) :
    ‖(H^[3]) z-((complexMap κ)^[3]) z‖ ≤ 73*ε := by
  let Q := complexMap κ
  have hz2 : ‖z‖ ≤ 2 := by
    have htri : ‖z‖ ≤ ‖z+(3/4 : ℂ)‖+‖(3/4 : ℂ)‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (z+(3/4 : ℂ)) (3/4 : ℂ)
    norm_num at htri
    linarith
  obtain ⟨hQ1,hQ2⟩ := model_parent_intermediate_bounds hk hz
  change ‖Q z‖ ≤ 2/5 at hQ1
  change ‖Q (Q z)‖ ≤ 3/2 at hQ2
  have h1 : ‖H z-Q z‖ ≤ ε := hclose z hz2
  have hH1 : ‖H z‖ ≤ 2 := by
    have ht : ‖H z‖ ≤ ‖H z-Q z‖+‖Q z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (H z-Q z) (Q z)
    linarith
  have h2 : ‖H (H z)-Q (Q z)‖ ≤ 9*ε := by
    have he := hclose (H z) hH1
    have hl := model_lipschitz_two hk hH1 (show ‖Q z‖ ≤ 2 by linarith)
    have ht : ‖H (H z)-Q (Q z)‖ ≤ ‖H (H z)-Q (H z)‖+‖Q (H z)-Q (Q z)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (H (H z)) (Q (H z)) (Q (Q z))
    change ‖Q (H z)-Q (Q z)‖ ≤ 8*‖H z-Q z‖ at hl
    linarith
  have hH2 : ‖H (H z)‖ ≤ 2 := by
    have ht : ‖H (H z)‖ ≤ ‖H (H z)-Q (Q z)‖+‖Q (Q z)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (H (H z)-Q (Q z)) (Q (Q z))
    linarith
  have he := hclose (H (H z)) hH2
  have hl := model_lipschitz_two hk hH2 (show ‖Q (Q z)‖ ≤ 2 by linarith)
  have ht : ‖H (H (H z))-Q (Q (Q z))‖ ≤
      ‖H (H (H z))-Q (H (H z))‖+‖Q (H (H z))-Q (Q (Q z))‖ := by
    simpa only [dist_eq_norm] using
      dist_triangle (H (H (H z))) (Q (H (H z))) (Q (Q (Q z)))
  change ‖Q (H (H z))-Q (Q (Q z))‖ ≤ 8*‖H (H z)-Q (Q z)‖ at hl
  change ‖H (H (H z))-Q (Q (Q z))‖ ≤ 73*ε
  linarith

/-- There is a full-disk perturbation tolerance that excludes every late
terminal gate, without selecting or assuming an actual crossing family. -/
theorem robust_tail_exclusion {κ : ℝ} (hk : κ ∈ parameterInterval) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ 2 → ‖H w-complexMap κ w‖ ≤ ε) →
      ∀ s ∈ Icc (133/2000 : ℝ) (1/8), ∀ u ∈ Icc (-1 : ℝ) 1,
        (H (circlePoint s u)).re = 0 →
          ((H^[3]) (circlePoint s u)).re < -1 := by
  obtain ⟨δ,hδ,hgap⟩ := model_tail_crossing_gap hk
  let ε : ℝ := min (1/100) (δ/100)
  have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεsmall : ε ≤ 1/100 := min_le_left _ _
  have hεδ : ε ≤ δ/100 := min_le_right _ _
  refine ⟨ε,hεpos,?_⟩
  intro H hclose s hs u hu hzero
  have hs' : s ∈ Icc (1/16 : ℝ) (1/8) := ⟨by linarith [hs.1],hs.2⟩
  have hz2 : ‖circlePoint s u‖ ≤ 2 := (parent_circle_norm hs' hu).trans (by norm_num)
  have hre := (Complex.abs_re_le_norm
    (H (circlePoint s u)-complexMap κ (circlePoint s u))).trans (hclose _ hz2)
  simp only [Complex.sub_re,hzero,zero_sub,abs_neg] at hre
  have hmodel := hgap s hs u hu (by linarith)
  have hradius : ‖circlePoint s u+(3/4 : ℂ)‖ ≤ 1/8 := by
    rw [circle_radius (show 0 ≤ s by linarith [hs.1]) hu]
    exact hs.2
  have herr := parent_third_iterate_error hk H hεpos.le hεsmall hclose hradius
  have hthird := (Complex.re_le_norm
    ((H^[3]) (circlePoint s u)-((complexMap κ)^[3]) (circlePoint s u))).trans herr
  simp only [Complex.sub_re] at hthird
  linarith

/-- One eventual period threshold excludes every late terminal crossing
for every actual signed-tip parameter.  Neither a global angular family
nor an a priori actual intermediate-domain bound is assumed. -/
theorem eventually_all_actual_tips_no_reentry :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ActualTip (n+17) c →
      ∀ s ∈ Icc (133/2000 : ℝ) (1/8), ∀ u ∈ Icc (-1 : ℝ) 1,
        (normalizedReturn c (n+17) (circlePoint s u)).re = 0 →
          (((normalizedReturn c (n+17))^[3]) (circlePoint s u)).re < -1 := by
  obtain ⟨κ,⟨hk,hroot⟩,_⟩ := exists_unique_limiting_parameter
  obtain ⟨ε,hε,hstable⟩ := robust_tail_exclusion hk
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzero : Tendsto (fun n : ℕ => 63208*scale (n+17)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [scale,pow_add,mul_zero,zero_mul] using
      (hbase.mul_const ((1/4 : ℝ)^17)).const_mul (63208 : ℝ)
  filter_upwards [(tendsto_order.mp hzero).2 ε hε] with n hn
  intro c hc
  apply hstable (normalizedReturn c (n+17))
  intro w hw
  exact (ActualCrestLargeDisk.actual_tip_limit_map_error (by omega) hc hk hroot hw).trans hn.le

end
end ActualCrestGlobalModel
