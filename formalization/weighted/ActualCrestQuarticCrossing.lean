import ActualCrestQuarticRelation

/-!
# The side of every limiting crossing under the actual return

At a crossing of the limiting quadratic, the real part of the square
is fixed by its parameter. The real quartic term is bounded above by
the square of that real part. The proved correlation of the two actual
coefficients therefore moves the entire limiting crossing arc strictly
to the negative side of the actual imaginary-axis preimage.
-/

namespace ActualCrestQuarticCrossing

open Set
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter
open ActualCrestQuartic ActualCrestQuarticScale ActualCrestQuarticRelation

noncomputable section

/-- A uniform signed margin for the literal actual return on every
limiting crossing in the established approximation disk. -/
theorem actual_return_real_at_model_crossing_lt {p : ℕ} (hp : 100 ≤ p)
    {c k₀ : ℝ} (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) {z : ℂ} (hz : ‖z‖ ≤ 3/2)
    (hQre : (complexMap k₀ z).re = 0) :
    (normalizedReturn c p z).re < -(1/10 : ℝ)*normalizedQuartic c p := by
  let b := normalizedQuartic c p
  let t : ℝ := (z^2).re
  let s : ℝ := (z^4).re
  have hβ := normalized_quartic_scale_bounds (by omega : 17 ≤ p) hc
  change 3*scale p < b ∧ b < 7*scale p at hβ
  have hq := scale_pos p
  have hb : 0 < b := by linarith [hβ.1]
  have hkpos : 0 < k₀ := by linarith [hk₀.1]
  have hkt : k₀*t = 1 := by
    have h : 1-k₀*t = 0 := by
      simpa only [complexMap,Complex.sub_re,Complex.one_re,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hQre
    linarith only [h]
  have htpos : 0 < t := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos hkpos.le (le_of_not_gt h)
    rw [hkt] at hn
    norm_num at hn
  have hklo : (5/3 : ℝ) ≤ k₀ := by linarith [hk₀.1]
  have hkhi : k₀ ≤ 2 := by linarith [hk₀.2]
  have hlo := mul_le_mul_of_nonneg_right hklo htpos.le
  have hhi := mul_le_mul_of_nonneg_right hkhi htpos.le
  have ht : (1/2 : ℝ) ≤ t ∧ t ≤ 3/5 := by
    constructor <;> linarith only [hlo,hhi,hkt]
  have hs : s ≤ (9/25 : ℝ) := by
    have hid : (z^4).re = ((z^2).re)^2-((z^2).im)^2 := by
      calc
        (z^4).re = ((z^2)*(z^2)).re := by congr 1; ring
        _ = _ := by rw [Complex.mul_re]; ring
    have hreal : s ≤ t^2 := by
      dsimp only [s,t]
      rw [hid]
      nlinarith only [sq_nonneg ((z^2).im)]
    have hsq := pow_le_pow_left₀ htpos.le ht.2 2
    nlinarith only [hreal,hsq]
  have hcorr := actual_quartic_parameter_correlation hp hc hk₀ hroot
  change (93/100 : ℝ)*b < kappa p c-k₀ ∧
    kappa p c-k₀ < (95/100 : ℝ)*b at hcorr
  have hgap1 := mul_le_mul_of_nonneg_right hcorr.1.le htpos.le
  have hgap2 := mul_le_mul_of_nonneg_left ht.1
    (show 0 ≤ (93/100 : ℝ)*b by positivity)
  have hgap : (93/200 : ℝ)*b ≤ (kappa p c-k₀)*t := by
    nlinarith only [hgap1,hgap2]
  have hquartic := mul_le_mul_of_nonneg_left hs hb.le
  have hsmall := scale_small_hundred hp
  have hsmallprod := mul_le_mul_of_nonneg_right hsmall hq.le
  have herror : 400*(scale p)^2 ≤ b/1000 := by
    norm_num at hsmallprod
    nlinarith only [hsmallprod,hβ.1,hq]
  have herr := normalized_quartic_error (by omega : 17 ≤ p) hc hz
  have hre := (Complex.re_le_norm
    (normalizedReturn c p z-(complexMap (kappa p c) z+(b : ℂ)*z^4))).trans herr
  have hreal : (normalizedReturn c p z).re-(1-kappa p c*t+b*s) ≤
      400*(scale p)^2 := by
    simpa only [complexMap,Complex.sub_re,Complex.add_re,Complex.one_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre
  change (normalizedReturn c p z).re < -(1/10 : ℝ)*b
  nlinarith only [hreal,herror,hgap,hquartic,hkt,hb]

/-- Every limiting crossing in the complex approximation disk lies on
the negative side of the actual crossing, with no replacement map. -/
theorem actual_return_negative_at_model_crossing {p : ℕ} (hp : 100 ≤ p)
    {c k₀ : ℝ} (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) {z : ℂ} (hz : ‖z‖ ≤ 3/2)
    (hQre : (complexMap k₀ z).re = 0) :
    (normalizedReturn c p z).re < 0 := by
  have h := actual_return_real_at_model_crossing_lt hp hc hk₀ hroot hz hQre
  have hb := (normalized_quartic_scale_bounds (by omega : 17 ≤ p) hc).1
  have hq := scale_pos p
  linarith only [h,hb,hq]

end
end ActualCrestQuarticCrossing
