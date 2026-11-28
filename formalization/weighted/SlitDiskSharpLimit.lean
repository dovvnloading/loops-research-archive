import SlitDiskPeriodExpansion
import SlitDiskRate
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Positive first-order finite-disk deficit

The derivative of the fixed-interval period ratio is controlled by the
strictly separated first moments of the two cubic periods.
-/

namespace SlitDiskSharpLimit

open Set Filter MeasureTheory SlitCubicCalibration SlitCubicBoundary
  SlitCubicBoundaryRange SlitDiskPeriodExpansion
open scoped Topology
noncomputable section

theorem moment_integrableOn {a b c : ℝ} (hab : a < b) (hbc : b < c) (l u : ℝ) :
    IntegrableOn (fun x => x*realDensity a b c x) (Ioo l u) :=
  IntegrableOn.continuousOn_mul_of_subset continuousOn_id
    (realDensity_integrable hab hbc).integrableOn isCompact_Icc measurableSet_Ioo
    Ioo_subset_Icc_self

theorem first_moment_lt {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    moment a b c a b < b*period a b c := by
  have hi := (realDensity_integrable hab hbc).integrableOn (s := Ioo a b)
  have hm := moment_integrableOn hab hbc a b
  have hg : IntegrableOn (fun x => (b-x)*realDensity a b c x) (Ioo a b) := by
    have he : (fun x => (b-x)*realDensity a b c x) =
        (fun x => b*realDensity a b c x)-(fun x => x*realDensity a b c x) := by
      funext x
      change (b-x)*realDensity a b c x = b*realDensity a b c x-x*realDensity a b c x
      ring
    rw [he]
    exact (hi.const_mul b).sub hm
  have hp : 0 < ∫ x in Ioo a b, (b-x)*realDensity a b c x := by
    have hn : 0 ≤ᵐ[volume.restrict (Ioo a b)] (fun x => (b-x)*realDensity a b c x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (sub_nonneg.mpr hx.2.le) (SlitCubicIntegrability.kernel_nonneg _ _ _ _)
    have hs : Ioo a b ⊆ Function.support (fun x => (b-x)*realDensity a b c x) := by
      intro x hx
      exact (mul_pos (sub_pos.mpr hx.2)
        (SlitCubicIntegrability.kernel_pos hx.1.ne' hx.2.ne (hx.2.trans hbc).ne)).ne'
    rw [setIntegral_pos_iff_support_of_nonneg_ae hn hg,
      inter_eq_self_of_subset_right hs,Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have he : (∫ x in Ioo a b, (b-x)*realDensity a b c x) =
      b*period a b c-moment a b c a b := by
    simp_rw [sub_mul]
    rw [integral_sub (hi.const_mul b) hm,integral_const_mul]
    rfl
  rw [he] at hp
  linarith

theorem second_moment_gt {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    b*height a b c < moment a b c b c := by
  have hi := (realDensity_integrable hab hbc).integrableOn (s := Ioo b c)
  have hm := moment_integrableOn hab hbc b c
  have hg : IntegrableOn (fun x => (x-b)*realDensity a b c x) (Ioo b c) := by
    have he : (fun x => (x-b)*realDensity a b c x) =
        (fun x => x*realDensity a b c x)-(fun x => b*realDensity a b c x) := by
      funext x
      change (x-b)*realDensity a b c x = x*realDensity a b c x-b*realDensity a b c x
      ring
    rw [he]
    exact hm.sub (hi.const_mul b)
  have hp : 0 < ∫ x in Ioo b c, (x-b)*realDensity a b c x := by
    have hn : 0 ≤ᵐ[volume.restrict (Ioo b c)] (fun x => (x-b)*realDensity a b c x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (sub_nonneg.mpr hx.1.le) (SlitCubicIntegrability.kernel_nonneg _ _ _ _)
    have hs : Ioo b c ⊆ Function.support (fun x => (x-b)*realDensity a b c x) := by
      intro x hx
      exact (mul_pos (sub_pos.mpr hx.1)
        (SlitCubicIntegrability.kernel_pos (hab.trans hx.1).ne' hx.1.ne' hx.2.ne)).ne'
    rw [setIntegral_pos_iff_support_of_nonneg_ae hn hg,
      inter_eq_self_of_subset_right hs,Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hbc)
  have he : (∫ x in Ioo b c, (x-b)*realDensity a b c x) =
      moment a b c b c-b*height a b c := by
    simp_rw [sub_mul]
    rw [integral_sub hm (hi.const_mul b),integral_const_mul]
    rfl
  rw [he] at hp
  linarith

def boundaryCoefficient (a b c : ℝ) : ℝ :=
  (moment a b c b c * period a b c-height a b c * moment a b c a b) /
    (2*(period a b c)^2)

theorem boundaryCoefficient_pos {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    0 < boundaryCoefficient a b c := by
  have hA := height_pos hab hbc
  have hB := period_pos hab hbc
  have h1 := mul_lt_mul_of_pos_left (first_moment_lt hab hbc) hA
  have h2 := mul_lt_mul_of_pos_right (second_moment_gt hab hbc) hB
  apply div_pos _ (by positivity)
  nlinarith only [h1,h2]

def weightedRatio (a b c q : ℝ) : ℝ :=
  weightedInterval a b c b c q / (2*weightedInterval a b c a b q)

@[simp] theorem weightedRatio_zero (a b c : ℝ) :
    weightedRatio a b c 0 = height a b c/(2*period a b c) := by
  simp only [weightedRatio,weightedInterval_zero,height,period]

theorem weightedRatio_hasDerivAt_zero {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    HasDerivAt (weightedRatio a b c) (-boundaryCoefficient a b c) 0 := by
  have hd := (weightedInterval_hasDerivAt_zero hab hbc b c).div
    ((weightedInterval_hasDerivAt_zero hab hbc a b).const_mul 2)
    (show 2*weightedInterval a b c a b 0 ≠ 0 from by
      rw [weightedInterval_zero]
      exact mul_ne_zero (by norm_num) (period_pos hab hbc).ne')
  apply hd.congr_deriv
  simp only [weightedInterval_zero]
  change _ = -((moment a b c b c * period a b c-height a b c*moment a b c a b) /
    (2*(period a b c)^2))
  change ((-moment a b c b c)*(2*period a b c)-height a b c*(2*(-moment a b c a b))) /
    (2*period a b c)^2 = _
  field_simp [(period_pos hab hbc).ne']
  ring

theorem weighted_deficit_quotient_tendsto {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    Tendsto (fun q => (height a b c/(2*period a b c)-weightedRatio a b c q)/q)
      (𝓝[>] (0 : ℝ)) (𝓝 (boundaryCoefficient a b c)) := by
  have hd := (hasDerivAt_const (0 : ℝ) (height a b c/(2*period a b c))).sub
    (weightedRatio_hasDerivAt_zero hab hbc)
  simpa only [Pi.sub_apply,zero_sub,neg_neg,zero_add,weightedRatio_zero,sub_self,sub_zero,
    smul_eq_mul,div_eq_mul_inv,mul_comm] using hd.tendsto_slope_zero_right

open MarkedSlitTransport SlitWaveLimit SlitDiskMarking

theorem plane_width_real_eq (M : Marking) :
    (width M univ).toReal = height M.left M.first M.second/(2*period M.left M.first M.second) := by
  have he : width M univ = ENNReal.ofReal
      (height M.left M.first M.second/(2*period M.left M.first M.second)) :=
    SlitCubicOptimality.width_eq_period_ratio M
  rw [he,ENNReal.toReal_ofReal (div_nonneg (height_pos M.left_lt_first M.first_lt_second).le
    (mul_nonneg (by norm_num) (period_pos M.left_lt_first M.first_lt_second).le))]

theorem normalizedCut_eq_normalizedMap {R x : ℝ} (hR : 0 < R) (hx : x ∈ Ioo (-R) R) :
    SlitDiskRate.normalizedCut R x = normalizedMap (1/R) x := by
  rw [SlitDiskRate.normalizedCut_eq (by linarith [hx.1] : R+x ≠ 0),normalizedMap_inv_eq hR.ne']

theorem disk_width_real_eq_weightedRatio {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    (width M (Metric.ball (0 : ℂ) R)).toReal = weightedRatio M.left M.first M.second (1/R) := by
  let N := SlitDiskRate.normalizedMarking hR M hleft hright
  have hleft' : N.left = normalizedMap (1/R) M.left :=
    (SlitDiskRate.markCoords_normalizedMarking hR M hleft hright 0).trans
      (normalizedCut_eq_normalizedMap hR (marking_left_mem_Ioo M hleft hright))
  have hfirst' : N.first = normalizedMap (1/R) M.first :=
    (SlitDiskRate.markCoords_normalizedMarking hR M hleft hright 1).trans
      (normalizedCut_eq_normalizedMap hR (marking_first_mem_Ioo M hleft hright))
  have hsecond' : N.second = normalizedMap (1/R) M.second :=
    (SlitDiskRate.markCoords_normalizedMarking hR M hleft hright 2).trans
      (normalizedCut_eq_normalizedMap hR (marking_second_mem_Ioo M hleft hright))
  rw [SlitDiskRate.width_disk_eq_normalized_plane hR M hleft hright,plane_width_real_eq]
  change height N.left N.first N.second/(2*period N.left N.first N.second) = _
  rw [hleft',hfirst',hsecond']
  exact normalized_ratio_eq M.left_lt_first M.first_lt_second
    (invRadius_small hR (marking_left_mem_Ioo M hleft hright))
    (invRadius_small hR (marking_first_mem_Ioo M hleft hright))
    (invRadius_small hR (marking_second_mem_Ioo M hleft hright))

/-- The exact first-order deficit of the complete finite-disk optimum.
The coefficient is strictly positive by `boundaryCoefficient_pos`. -/
theorem width_deficit_mul_radius_tendsto (M : Marking) :
    Tendsto (fun R : ℝ => R*((width M univ).toReal-
      (width M (Metric.ball (0 : ℂ) R)).toReal)) atTop
      (𝓝 (boundaryCoefficient M.left M.first M.second)) := by
  have hq : Tendsto (fun R : ℝ => 1/R) atTop (𝓝[>] (0 : ℝ)) := by
    simpa only [one_div] using (tendsto_inv_atTop_nhdsGT_zero :
      Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝[>] (0 : ℝ)))
  have hh := (weighted_deficit_quotient_tendsto M.left_lt_first M.first_lt_second).comp hq
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (|M.left|+|M.right|+1)] with R hR
  have hp : 0 < R := by linarith [abs_nonneg M.left,abs_nonneg M.right]
  have hl : -R < M.left := by linarith [neg_abs_le M.left,abs_nonneg M.right]
  have hr : M.right < R := by linarith [le_abs_self M.right,abs_nonneg M.left]
  rw [plane_width_real_eq,disk_width_real_eq_weightedRatio hp M hl hr]
  simp only [Function.comp_def,one_div,div_inv_eq_mul,mul_comm]

end
end SlitDiskSharpLimit
