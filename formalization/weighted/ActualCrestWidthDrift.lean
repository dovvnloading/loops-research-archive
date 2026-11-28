import ActualCrestEndpointDrift
import ActualCrestAngularDrift

/-!
# The actual selected transport approaches its limit from above

Both new geometric signs enter the existing all-density modulus formula:
the actual crossing angle is smaller on the common collar, and its actual
maximal radius is larger.  The integral comparison is transferred back to
the literal polynomial-image path families and their physical parent.
-/

namespace ActualCrestWidthDrift

open Set Function MeasureTheory
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter GlobalCrestCrossing GlobalCrestOrder
open ActualCrestWidth ActualCrestParentPaths CrestConformalModulus
open CrestIntegralLimit ActualCrestEndpointDrift ActualCrestAngularDrift

noncomputable section

private theorem actual_integrand_ge_one {p : ℕ} {c s : ℝ}
    (F : Family p c) (hs : s ∈ radiusInterval) :
    (1 : ℝ) ≤ radialIntegrand (realAngle F) s := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hang := angle_bounds F s
  change 0 < Real.arccos (realAngle F s) ∧
    Real.arccos (realAngle F s) ≤ Real.pi at hang
  have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_d4]
  have hprod := mul_le_mul_of_nonneg_left hang.2 hs0.le
  have hcap := mul_le_mul hs.2 hpi Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 133/2000)
  have hden : s*Real.arccos (realAngle F s) ≤ 1 := by
    linarith only [hprod,hcap]
  have hpos := mul_pos hs0 hang.1
  have h := one_div_le_one_div_of_le hpos hden
  simpa only [one_div_one,radialIntegrand] using h

/-- The complete actual radial integral exceeds its limiting integral
by a positive multiple of the first dynamical scale.  The sign uses
both the actual angular displacement and the actual maximal endpoint. -/
theorem actual_integral_signed_gap {p : ℕ} (hp : 100 ≤ p) {c k₀ r r₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    (3/50 : ℝ)*scale p <
      (∫ s in (1/16 : ℝ)..r, radialIntegrand (realAngle F) s)-
      (∫ s in (1/16 : ℝ)..r₀, radialIntegrand (crossingCos k₀) s) := by
  have hb := actual_endpoint_signed_bounds hp hc hk₀ hroot F hr he hr₀ he₀
  have horder : r₀ < r := by linarith only [hb.1,scale_pos p]
  have hcont := GlobalCrestCoefficient.actual_integrand_continuousOn (by omega) hc F
  have hact0 : IntervalIntegrable (radialIntegrand (realAngle F)) volume (1/16) r₀ :=
    (hcont.mono (fun s hs => ⟨hs.1,hs.2.trans hr₀.2⟩)).intervalIntegrable_of_Icc hr₀.1
  have htail : IntervalIntegrable (radialIntegrand (realAngle F)) volume r₀ r :=
    (hcont.mono (fun s hs => ⟨hr₀.1.trans hs.1,hs.2.trans hr.2⟩)).intervalIntegrable_of_Icc horder.le
  have hmodel : IntervalIntegrable (radialIntegrand (crossingCos k₀)) volume (1/16) r₀ :=
    ((full_integrand_continuousOn hk₀).mono
      (fun s hs => ⟨hs.1,by linarith [hs.2,hr₀.2]⟩)).intervalIntegrable_of_Icc hr₀.1
  have hcommon := intervalIntegral.integral_mono_on hr₀.1 hmodel hact0
    (fun s hs => (actual_radialIntegrand_gt hp hc hk₀ hroot F
      (show s ∈ Icc (1/16 : ℝ) (1/8) from
        ⟨hs.1,by linarith [hs.2,hr₀.2]⟩)).le)
  have htailbound : r-r₀ ≤ ∫ s in r₀..r, radialIntegrand (realAngle F) s := by
    have h := intervalIntegral.integral_mono_on horder.le
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume r₀ r)
      htail (fun s hs => actual_integrand_ge_one F
        (show s ∈ radiusInterval from ⟨hr₀.1.trans hs.1,hs.2.trans hr.2⟩))
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_one] using h
  have hsum := intervalIntegral.integral_add_adjacent_intervals hact0 htail
  linarith only [hcommon,htailbound,hsum,hb.1]

/-- The new signed gap holds for the independently defined all-density
modulus of the actual polynomial-image descendant family. -/
theorem actual_descendant_modulus_signed_gap {p : ℕ} (hp : 100 ≤ p)
    {c k₀ r r₀ : ℝ} (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    (3/50 : ℝ)*scale p <
      (modulus (descendants (by omega) hc F r)).toReal-
      (∫ s in (1/16 : ℝ)..r₀, radialIntegrand (crossingCos k₀) s) := by
  rw [descendants_width_eq_integral (by omega) hc
    (UniformCrestSupport.actual_strict_support (by omega) hc) F hr]
  exact actual_integral_signed_gap hp hc hk₀ hroot F hr he hr₀ he₀

/-- The literal selected transport ratio lies strictly above its existing
limiting coefficient.  Both numerator and denominator are the archive's
all-density physical path-family moduli. -/
theorem actual_physical_ratio_gt_limit {p : ℕ} (hp : 100 ≤ p)
    {c k₀ r r₀ : ℝ} (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    fullModelCoefficient k₀ r₀ <
      (modulus (descendants (by omega) hc F r)).toReal /
        (modulus (parentFamily c p)).toReal := by
  have hp17 : 17 ≤ p := by omega
  have hS := UniformCrestSupport.actual_strict_support hp17 hc
  have hratio : (modulus (descendants (by omega) hc F r)).toReal /
      (modulus (parentFamily c p)).toReal = radialCoefficient p (realAngle F) r := by
    calc
      _ = widthRatio hp17 hc F r := by
        unfold widthRatio
        rw [parentWidth_eq_modulus hp17 hc]
      _ = _ := widthRatio_eq_radialCoefficient hp17 hc hS F hr
  rw [hratio]
  let I₀ : ℝ := ∫ s in (1/16 : ℝ)..r₀, radialIntegrand (crossingCos k₀) s
  let I : ℝ := ∫ s in (1/16 : ℝ)..r, radialIntegrand (realAngle F) s
  have hgap := actual_integral_signed_gap hp hc hk₀ hroot F hr he hr₀ he₀
  have hstrict : I₀ < I := by
    change (3/50 : ℝ)*scale p < I-I₀ at hgap
    linarith only [hgap,scale_pos p]
  have hmodel : IntervalIntegrable (radialIntegrand (crossingCos k₀)) volume (1/16) r₀ :=
    ((full_integrand_continuousOn hk₀).mono
      (fun s hs => ⟨hs.1,by linarith [hs.2,hr₀.2]⟩)).intervalIntegrable_of_Icc hr₀.1
  have hI₀ : 0 ≤ I₀ := by
    have h := intervalIntegral.integral_mono_on hr₀.1
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (1/16) r₀)
      hmodel (fun s hs => by
        have hs0 : 0 < s := by linarith [hs.1]
        have hsfull : s ∈ Icc (1/16 : ℝ) (1/8) :=
          ⟨hs.1,by linarith [hs.2,hr₀.2]⟩
        have ha : 0 < Real.arccos (crossingCos k₀ s) :=
          Real.arccos_pos.mpr (full_crossingCos_bounds hk₀ hsfull).2
        dsimp [radialIntegrand]
        positivity)
    simpa only [intervalIntegral.integral_zero] using h
  have hpR : (100 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith only [hpR]
  have hdiv : 2/(p : ℝ) < 1 := (div_lt_one hp0).mpr (by linarith only [hpR])
  have hbase : 0 < 2-2/(p : ℝ) := by linarith only [hdiv]
  have hbase2 : 2-2/(p : ℝ) < 2 := by
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) hp0]
  have hlog := (GlobalCrestCoefficient.parent_log_bounds hp17).1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs := Real.log_lt_log hbase hbase2
  have hfactor : 2*Real.pi/Real.log 2 ≤ 2*Real.pi/Real.log (2-2/(p : ℝ)) := by
    apply (div_le_div_iff₀ hlog2 hlog).mpr
    exact mul_le_mul_of_nonneg_left hlogs.le (by positivity)
  have hfactorPos : 0 < 2*Real.pi/Real.log (2-2/(p : ℝ)) := by positivity
  change (2*Real.pi/Real.log 2)*I₀ < (2*Real.pi/Real.log (2-2/(p : ℝ)))*I
  exact (mul_le_mul_of_nonneg_right hfactor hI₀).trans_lt
    (mul_lt_mul_of_pos_left hstrict hfactorPos)

end
end ActualCrestWidthDrift
