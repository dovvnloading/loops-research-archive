import NearTwoTip

/-!
# Uniform whole-disk estimates for the actual three-return

The outer radius is 1/6 of the actual positive first critical return.
The entire closed annulus from radius 3/20 to radius 1/6 is excluded
from the three-return preimage of the outer disk.  The first two phase
images are controlled on the entire outer disk, before any restriction
or choice of a component.
-/

namespace ThreeReturnEstimates

open Set Function
open LimitingCrest LimitingCrestPerturbation LimitingCrestQuadraticReturn
open NearTwoShooting NearTwoTip

noncomputable section

def outerRadius : ℝ := 1 / 6
def innerRadius : ℝ := 3 / 20

private def thirdConstant (k : ℝ) : ℝ := 1-k*(1-k)^2
private def thirdQuadratic (k : ℝ) : ℝ := 4*k^3*(k-1)
private def thirdQuartic (k : ℝ) : ℝ := k^4*(6*k-2)
private def thirdSextic (k : ℝ) : ℝ := 4*k^6
private def thirdOctic (k : ℝ) : ℝ := k^7

private theorem third_coefficient_bounds {k : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5)) :
    |thirdConstant k| ≤ 4/25 ∧
    18 ≤ thirdQuadratic k ∧ thirdQuadratic k ≤ 19 ∧
    0 ≤ thirdQuartic k ∧ thirdQuartic k ≤ 93 ∧
    0 ≤ thirdSextic k ∧ thirdSextic k ≤ 137 ∧
    0 ≤ thirdOctic k ∧ thirdOctic k ≤ 62 := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hkm : 0 ≤ k-1 := by linarith [hk.1]
  have hslo : (79/100 : ℝ)^2 ≤ (k-1)^2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [hk.1]) 2
  have hshi : (k-1)^2 ≤ (4/5 : ℝ)^2 :=
    pow_le_pow_left₀ hkm (by linarith [hk.2]) 2
  have hlo := mul_le_mul hk.1 hslo (by norm_num : (0 : ℝ) ≤ (79/100)^2) hk0
  have hhi := mul_le_mul hk.2 hshi (sq_nonneg (k-1)) (by norm_num : (0 : ℝ) ≤ 9/5)
  have hsq : (1-k)^2 = (k-1)^2 := by ring
  have hc : |thirdConstant k| ≤ 4/25 := by
    dsimp [thirdConstant]
    rw [hsq,abs_le]
    constructor <;> norm_num at hlo hhi ⊢ <;> linarith
  have hbLo : (4 : ℝ)*(179/100)^3*(79/100) ≤ thirdQuadratic k := by
    dsimp [thirdQuadratic]
    gcongr <;> linarith [hk.1]
  have hbHi : thirdQuadratic k ≤ (4 : ℝ)*(9/5)^3*(4/5) := by
    dsimp [thirdQuadratic]
    gcongr <;> linarith [hk.1,hk.2]
  have hd0 : 0 ≤ thirdQuartic k := by
    dsimp [thirdQuartic]
    exact mul_nonneg (by positivity) (by linarith [hk.1])
  have hdHi : thirdQuartic k ≤ (9/5 : ℝ)^4*(6*(9/5)-2) := by
    dsimp [thirdQuartic]
    gcongr <;> linarith [hk.1,hk.2]
  have he0 : 0 ≤ thirdSextic k := by dsimp [thirdSextic]; positivity
  have heHi : thirdSextic k ≤ (4 : ℝ)*(9/5)^6 := by
    dsimp [thirdSextic]
    gcongr
    exact hk.2
  have hf0 : 0 ≤ thirdOctic k := by dsimp [thirdOctic]; positivity
  have hfHi : thirdOctic k ≤ (9/5 : ℝ)^7 :=
    pow_le_pow_left₀ hk0 hk.2 7
  norm_num at hbLo hbHi hdHi heHi hfHi
  exact ⟨hc,by linarith,by linarith,hd0,by linarith,he0,by linarith,hf0,by linarith⟩

private theorem third_expansion (k : ℝ) (z : ℂ) :
    ((complexMap k)^[3]) z - (thirdQuadratic k : ℂ)*z^2 =
      (thirdConstant k : ℂ) - (thirdQuartic k : ℂ)*z^4 +
        (thirdSextic k : ℂ)*z^6 - (thirdOctic k : ℂ)*z^8 := by
  norm_num [iterate_succ_apply',complexMap,thirdConstant,thirdQuadratic,
    thirdQuartic,thirdSextic,thirdOctic]
  ring

private theorem model_residual_bound {k R : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5)) (_hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖((complexMap k)^[3]) z-(thirdQuadratic k : ℂ)*z^2‖ ≤
      4/25+93*R^4+137*R^6+62*R^8 := by
  obtain ⟨hc,hbLo,hbHi,hd0,hd,he0,he,hf0,hf⟩ := third_coefficient_bounds hk
  have h4 : ‖(thirdQuartic k : ℂ)*z^4‖ ≤ 93*R^4 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd0]
    exact mul_le_mul hd (pow_le_pow_left₀ (norm_nonneg _) hz 4)
      (by positivity) (by norm_num)
  have h6 : ‖(thirdSextic k : ℂ)*z^6‖ ≤ 137*R^6 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he0]
    exact mul_le_mul he (pow_le_pow_left₀ (norm_nonneg _) hz 6)
      (by positivity) (by norm_num)
  have h8 : ‖(thirdOctic k : ℂ)*z^8‖ ≤ 62*R^8 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hf0]
    exact mul_le_mul hf (pow_le_pow_left₀ (norm_nonneg _) hz 8)
      (by positivity) (by norm_num)
  have hc' : ‖(thirdConstant k : ℂ)‖ ≤ 4/25 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hc
  rw [third_expansion]
  calc
    _ ≤ ‖(thirdConstant k : ℂ)-(thirdQuartic k : ℂ)*z^4+
        (thirdSextic k : ℂ)*z^6‖+‖(thirdOctic k : ℂ)*z^8‖ := norm_sub_le _ _
    _ ≤ (‖(thirdConstant k : ℂ)-(thirdQuartic k : ℂ)*z^4‖+
        ‖(thirdSextic k : ℂ)*z^6‖)+‖(thirdOctic k : ℂ)*z^8‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ((‖(thirdConstant k : ℂ)‖+‖(thirdQuartic k : ℂ)*z^4‖)+
        ‖(thirdSextic k : ℂ)*z^6‖)+‖(thirdOctic k : ℂ)*z^8‖ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ _ := by linarith

private theorem model_first_bound {k : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5)) {z : ℂ}
    (hz : ‖z‖ ≤ outerRadius) : ‖complexMap k z-1‖ ≤ 1/20 := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have he : complexMap k z-1 = -(k : ℂ)*z^2 := by dsimp [complexMap]; ring
  rw [he,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk0,norm_pow]
  have hs := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hm := mul_le_mul hk.2 hs (sq_nonneg ‖z‖) (by norm_num : (0 : ℝ) ≤ 9/5)
  norm_num [outerRadius] at hm
  exact hm

private theorem model_second_bound {k : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5)) {z : ℂ}
    (hz : ‖z‖ ≤ outerRadius) :
    ‖((complexMap k)^[2]) z-((1-k : ℝ) : ℂ)‖ ≤ 37/200 := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have he : ((complexMap k)^[2]) z-((1-k : ℝ) : ℂ) =
      (2*k^2 : ℝ)*z^2-(k^3 : ℝ)*z^4 := by
    norm_num [iterate_succ_apply',complexMap]
    ring
  have h2 : ‖((2*k^2 : ℝ) : ℂ)*z^2‖ ≤ 9/50 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hpow := pow_le_pow_left₀ hk0 hk.2 2
    have hzpow := pow_le_pow_left₀ (norm_nonneg z) hz 2
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2))
      hzpow (sq_nonneg ‖z‖) (by positivity : (0 : ℝ) ≤ 2*(9/5)^2)
    norm_num [outerRadius] at hm
    exact hm
  have h4 : ‖((k^3 : ℝ) : ℂ)*z^4‖ ≤ 9/2000 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hm := mul_le_mul (pow_le_pow_left₀ hk0 hk.2 3)
      (pow_le_pow_left₀ (norm_nonneg z) hz 4) (by positivity : (0 : ℝ) ≤ ‖z‖^4)
      (by positivity : (0 : ℝ) ≤ (9/5)^3)
    norm_num [outerRadius] at hm
    exact hm
  rw [he]
  have ht := norm_sub_le (((2*k^2 : ℝ) : ℂ)*z^2) (((k^3 : ℝ) : ℂ)*z^4)
  linarith

private theorem model_third_bound {k : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5)) {z : ℂ}
    (hz : ‖z‖ ≤ outerRadius) : ‖((complexMap k)^[3]) z‖ ≤ 4/5 := by
  have hb := (third_coefficient_bounds hk).2.1
  have hb' := (third_coefficient_bounds hk).2.2.1
  have hlead : ‖(thirdQuadratic k : ℂ)*z^2‖ ≤ 19*outerRadius^2 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    exact mul_le_mul hb' (pow_le_pow_left₀ (norm_nonneg z) hz 2)
      (sq_nonneg _) (by norm_num)
  have hr := model_residual_bound hk (by norm_num [outerRadius]) z hz
  have ht := norm_le_norm_sub_add (((complexMap k)^[3]) z) ((thirdQuadratic k : ℂ)*z^2)
  norm_num only [outerRadius] at hlead hr
  linarith

private theorem model_orbit_bound {k : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5)) {z : ℂ}
    (hz : ‖z‖ ≤ outerRadius) :
    ∀ n : ℕ, n ≤ 3 → ‖((complexMap k)^[n]) z‖ ≤ 11/10 := by
  have h1 := model_first_bound hk hz
  have h2 := model_second_bound hk hz
  have h3 := model_third_bound hk hz
  have hkneg : 1-k ≤ 0 := by linarith [hk.1]
  have hc : ‖((1-k : ℝ) : ℂ)‖ ≤ 4/5 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos hkneg]
    linarith [hk.2]
  intro n hn
  interval_cases n
  · simpa using hz.trans (by norm_num [outerRadius] : outerRadius ≤ 11/10)
  · have ht := norm_le_norm_sub_add (complexMap k z) (1 : ℂ)
    norm_num at ht
    simpa using (show ‖complexMap k z‖ ≤ (11/10 : ℝ) by linarith)
  · have ht := norm_le_norm_sub_add (((complexMap k)^[2]) z) (((1-k : ℝ) : ℂ))
    linarith
  · linarith

private theorem three_composition_error
    (F : ℂ → ℂ) {k ε : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5))
    (hε : 0 ≤ ε) (hεmax : ε ≤ 1/100000)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 → ‖F w-complexMap k w‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ outerRadius) :
    ∀ n : ℕ, n ≤ 3 →
      ‖(F^[n]) z-((complexMap k)^[n]) z‖ ≤ errorCoefficient n*ε ∧
      ‖(F^[n]) z‖ < 23/20 := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hk2 : k ≤ 2 := by linarith [hk.2]
  have hmodel := model_orbit_bound hk hz
  intro n
  induction n with
  | zero =>
    intro hn
    refine ⟨by simp [errorCoefficient],?_⟩
    simpa using hz.trans_lt (by norm_num [outerRadius] : outerRadius < 23/20)
  | succ n ih =>
    intro hn
    obtain ⟨herr,hdisk⟩ := ih (by omega)
    have hQdisk : ‖((complexMap k)^[n]) z‖ ≤ 23/20 :=
      (hmodel n (by omega)).trans (by norm_num)
    have hnext : ‖(F^[n+1]) z-((complexMap k)^[n+1]) z‖ ≤
        errorCoefficient (n+1)*ε := by
      rw [iterate_succ_apply',iterate_succ_apply']
      calc
        _ ≤ ‖F ((F^[n]) z)-complexMap k ((F^[n]) z)‖+
            ‖complexMap k ((F^[n]) z)-complexMap k (((complexMap k)^[n]) z)‖ := by
              simpa only [dist_eq_norm] using
                dist_triangle (F ((F^[n]) z)) (complexMap k ((F^[n]) z))
                  (complexMap k (((complexMap k)^[n]) z))
        _ ≤ ε+5*(errorCoefficient n*ε) :=
          add_le_add (hclose _ hdisk.le)
            ((quadratic_disk_lipschitz k hk0 hk2 _ _ hdisk.le hQdisk).trans
              (mul_le_mul_of_nonneg_left herr (by norm_num)))
        _ = errorCoefficient (n+1)*ε := by simp only [errorCoefficient]; ring
    have hcoef : errorCoefficient (n+1) ≤ 31 := by
      have hn2 : n ≤ 2 := by omega
      interval_cases n <;> norm_num [errorCoefficient]
    have hsmall : errorCoefficient (n+1)*ε ≤ 31/100000 := by
      calc
        _ ≤ 31*ε := mul_le_mul_of_nonneg_right hcoef hε
        _ ≤ _ := by linarith
    have ht := norm_le_norm_sub_add ((F^[n+1]) z) (((complexMap k)^[n+1]) z)
    refine ⟨hnext,?_⟩
    linarith [hmodel (n+1) hn]

/-- A perturbation on the full fixed disk has disjoint quantitative
first and second phase enclosures on the entire outer disk. -/
theorem perturbed_phase_bounds (F : ℂ → ℂ) {k ε : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5))
    (hε : 0 ≤ ε) (hεmax : ε ≤ 1/100000)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 → ‖F w-complexMap k w‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ outerRadius) :
    ‖F z-1‖ < 51/1000 ∧
    ‖(F^[2]) z-((1-k : ℝ) : ℂ)‖ < 19/100 ∧
    ‖(F^[3]) z‖ < 81/100 ∧
    (∀ n : ℕ, n ≤ 3 → ‖(F^[n]) z‖ < 23/20) := by
  have he := three_composition_error F hk hε hεmax hclose hz
  have he1 := (he 1 (by omega)).1
  have he2 := (he 2 (by omega)).1
  have he3 := (he 3 (by omega)).1
  norm_num only [errorCoefficient, mul_zero, add_zero, one_mul] at he1 he2 he3
  change ‖F z-complexMap k z‖ ≤ ε at he1
  have h1 := model_first_bound hk hz
  have h2 := model_second_bound hk hz
  have h3 := model_third_bound hk hz
  have ht1 : ‖F z-1‖ ≤ ‖F z-complexMap k z‖+‖complexMap k z-1‖ := by
    simpa only [dist_eq_norm] using dist_triangle (F z) (complexMap k z) (1 : ℂ)
  have ht2 : ‖(F^[2]) z-((1-k : ℝ) : ℂ)‖ ≤
      ‖(F^[2]) z-((complexMap k)^[2]) z‖+
        ‖((complexMap k)^[2]) z-((1-k : ℝ) : ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle ((F^[2]) z)
      (((complexMap k)^[2]) z) (((1-k : ℝ) : ℂ))
  have ht3 := norm_le_norm_sub_add ((F^[3]) z) (((complexMap k)^[3]) z)
  exact ⟨by linarith only [he1,h1,ht1,hεmax],
    by linarith only [he2,h2,ht2,hεmax],
    by linarith only [he3,h3,ht3,hεmax],fun n hn => (he n hn).2⟩

/-- The complete closed radial band is mapped strictly outside the
target disk, with a fixed additional margin of 1/500. -/
theorem perturbed_annular_barrier (F : ℂ → ℂ) {k ε : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5))
    (hε : 0 ≤ ε) (hεmax : ε ≤ 1/100000)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 → ‖F w-complexMap k w‖ ≤ ε)
    {z : ℂ} (hzlo : innerRadius ≤ ‖z‖) (hzhi : ‖z‖ ≤ outerRadius) :
    outerRadius+1/500 < ‖(F^[3]) z‖ := by
  have hb := (third_coefficient_bounds hk).2.1
  have hlead : 18*innerRadius^2 ≤ ‖(thirdQuadratic k : ℂ)*z^2‖ := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    exact mul_le_mul hb (pow_le_pow_left₀ (by norm_num [innerRadius]) hzlo 2)
      (by positivity) (by linarith)
  have hres := model_residual_bound hk (by norm_num [outerRadius]) z hzhi
  have he := (three_composition_error F hk hε hεmax hclose hzhi 3 (by omega)).1
  norm_num only [errorCoefficient, mul_zero, add_zero, one_mul] at he
  have ht1 := norm_le_norm_sub_add ((thirdQuadratic k : ℂ)*z^2)
    (((complexMap k)^[3]) z)
  rw [norm_sub_rev ((thirdQuadratic k : ℂ)*z^2)] at ht1
  have ht2 := norm_le_norm_sub_add (((complexMap k)^[3]) z) ((F^[3]) z)
  rw [norm_sub_rev (((complexMap k)^[3]) z)] at ht2
  norm_num only [innerRadius,outerRadius] at hlead hres ⊢
  linarith

/-- The critical value is strictly inside the same target disk used
by the annular barrier. -/
theorem perturbed_critical_value_bound (F : ℂ → ℂ) {k ε : ℝ}
    (hk : k ∈ Icc (179/100 : ℝ) (9/5))
    (hε : 0 ≤ ε) (hεmax : ε ≤ 1/100000)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 → ‖F w-complexMap k w‖ ≤ ε) :
    ‖(F^[3]) 0‖ < outerRadius := by
  have he := (three_composition_error F hk hε hεmax hclose
    (show ‖(0 : ℂ)‖ ≤ outerRadius by norm_num [outerRadius]) 3 (by omega)).1
  have hres := model_residual_bound hk (show (0 : ℝ) ≤ 0 by norm_num)
    (0 : ℂ) (by norm_num)
  norm_num only [errorCoefficient, mul_zero, add_zero, one_mul] at he
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, sub_zero, add_zero] at hres
  have ht := norm_le_norm_sub_add ((F^[3]) 0) (((complexMap k)^[3]) 0)
  change ‖(F^[3]) 0‖ < (1/6 : ℝ)
  linarith

private theorem actual_error_data {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    kappa p c ∈ Icc (179/100 : ℝ) (9/5) ∧
    (0 : ℝ) ≤ 24/(4 : ℝ)^p ∧ 24/(4 : ℝ)^p ≤ 1/100000 ∧
    (∀ z : ℂ, ‖z‖ ≤ 23/20 →
      ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ 24/(4 : ℝ)^p) := by
  obtain ⟨hpar,hd,hsmall,hk,hzero,hneg,hcrit⟩ := hc
  have hp13 : 13 ≤ p := by omega
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp13
  norm_num at hpow
  have heps : 24/(4 : ℝ)^p ≤ 1/100000 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4^p)).mpr
    linarith
  have hsmall' : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hsmall
  refine ⟨⟨?_,?_⟩,by positivity,heps,?_⟩
  · have h := hk.1
    change 17903/10000 ≤ kappa p c at h
    linarith
  · have h := hk.2
    change kappa p c ≤ 17904/10000 at h
    linarith
  · exact normalized_return_error c p hp13 hcrit hd hsmall'

/-- Whole-disk phase enclosures for every actual signed tip. -/
theorem actual_phase_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ outerRadius) :
    ‖normalizedReturn c p z-1‖ < 51/1000 ∧
    ‖((normalizedReturn c p)^[2]) z-((1-kappa p c : ℝ) : ℂ)‖ < 19/100 ∧
    ‖((normalizedReturn c p)^[3]) z‖ < 81/100 ∧
    (∀ n : ℕ, n ≤ 3 → ‖((normalizedReturn c p)^[n]) z‖ < 23/20) := by
  obtain ⟨hk,hε,hεmax,hclose⟩ := actual_error_data hp hc
  exact perturbed_phase_bounds _ hk hε hεmax hclose hz

/-- Actual three-return exclusion on the entire closed annular band. -/
theorem actual_annular_barrier {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hzlo : innerRadius ≤ ‖z‖) (hzhi : ‖z‖ ≤ outerRadius) :
    outerRadius+1/500 < ‖((normalizedReturn c p)^[3]) z‖ := by
  obtain ⟨hk,hε,hεmax,hclose⟩ := actual_error_data hp hc
  exact perturbed_annular_barrier _ hk hε hεmax hclose hzlo hzhi

/-- The actual critical value lies in the target of the same restriction. -/
theorem actual_critical_value_bound {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ‖((normalizedReturn c p)^[3]) 0‖ < outerRadius := by
  obtain ⟨hk,hε,hεmax,hclose⟩ := actual_error_data hp hc
  exact perturbed_critical_value_bound _ hk hε hεmax hclose

end
end ThreeReturnEstimates
