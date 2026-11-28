import GlobalWindowBoundaryProduct
import GlobalWindowThickness

/-!
# Two-parameter inverse shape of the actual restrictive family

The full inverse secant product is retained as a function of the normalized
target.  Its variation controls the shape of the actual return when both
the parameter and the critical return scale change.
-/

namespace GlobalWindowInverseShape

open Set Function Finset NearTwoInverse NearTwoShooting
open LimitingCrestQuadraticReturn GlobalRestrictiveWindow
open GlobalWindowBoundaryProduct
open scoped BigOperators

noncomputable section

def phaseProduct (c : ℝ) (p : ℕ) (d y : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (p-1), (back c (j+1) d+back c (j+1) (d*y))/4

def inverseRatio (c : ℝ) (p : ℕ) (y : ℝ) : ℝ :=
  phaseProduct c p (criticalValue c p) y /
    phaseProduct c p (criticalValue c p) 1

private theorem broad_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (h : PositiveRestrictiveReturn c p) :
    c ∈ Icc (-2 : ℝ) (-2+20*scale p) :=
  ⟨h.parameter_band.1,(h.parameter_upper hp).le⟩

private theorem wide_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (h : PositiveRestrictiveReturn c p) :
    c ∈ Icc (-2 : ℝ) (-199/100) := by
  have hb := h.small_parameter_band hp
  exact ⟨hb.1,by linarith [hb.2]⟩

private theorem physical_scale {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (h : PositiveRestrictiveReturn c p) :
    criticalValue c p ∈ Icc (0 : ℝ) (14*scale p) :=
  ⟨h.return_pos.le,(h.return_scale hp).le⟩

private theorem terminal_image {p : ℕ} (hp : 17 ≤ p) {c y : ℝ}
    (h : PositiveRestrictiveReturn c p) (hy : y ∈ Icc (-1 : ℝ) 1) :
    criticalValue c p*y ∈ Icc (-1/100 : ℝ) 2 := by
  have hd := h.return_scale hp
  have hq := scale_small hp
  have hlo := mul_le_mul_of_nonneg_left hy.1 h.return_pos.le
  have hup := mul_le_mul_of_nonneg_left hy.2 h.return_pos.le
  constructor <;> nlinarith only [hlo,hup,hd,hq]

private theorem terminal_self {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (h : PositiveRestrictiveReturn c p) :
    criticalValue c p ∈ Icc (-1/100 : ℝ) 2 := by
  simpa only [mul_one] using terminal_image hp h
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)

/-- The actual shooting parameters move only at the inverse exponential
scale when their physical return values move. -/
theorem parameter_lipschitz {p : ℕ} (hp : 17 ≤ p) {c a : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p) :
    |c-a| ≤ 12*scale p*|criticalValue c p-criticalValue a p| := by
  have hbudget : ((p-2 : ℕ) : ℝ)*(c+2) ≤ 1/10000 := by
    have hn : ((p-2 : ℕ) : ℝ) ≤ (p-1 : ℕ) := by
      exact_mod_cast (show p-2 ≤ p-1 by omega)
    have hm := mul_le_mul_of_nonneg_right hn
      (show 0 ≤ c+2 by linarith [hc.parameter_band.1])
    exact hm.trans (hc.inverse_parameter_budget hp)
  have hcomp := GlobalWindowThickness.shooting_parameter_comparison hp
    (ha.small_parameter_band hp) (hc.small_parameter_band hp) hbudget
    ⟨hc.return_pos.le,(terminal_self hp hc).2⟩
    ⟨ha.return_pos.le,(terminal_self hp ha).2⟩
    (ha.shooting_identity hp) (hc.shooting_identity hp)
  have hq0 := (scale_pos p).le
  have hmul := mul_le_mul_of_nonneg_right hcomp hq0
  have hid : (4 : ℝ)^p*scale p=1 := by
    unfold scale
    rw [← mul_pow]
    norm_num
  have hleft : ((9/100 : ℝ)*4^p*|c-a|)*scale p=(9/100)*|c-a| := by
    calc
      _ = ((9/100 : ℝ)*|c-a|)*(4^p*scale p) := by ring
      _ = _ := by rw [hid]; ring
  rw [hleft] at hmul
  have hn : 0 ≤ scale p*|criticalValue c p-criticalValue a p| := by positivity
  nlinarith only [hmul,hn]

private theorem parameter_lipschitz_one {p : ℕ} (hp : 17 ≤ p) {c a : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p) :
    |c-a| ≤ |criticalValue c p-criticalValue a p| := by
  have hl := parameter_lipschitz hp hc ha
  have hq := scale_small hp
  have hm := mul_le_mul_of_nonneg_right
    (show 12*scale p ≤ 1 by linarith)
    (abs_nonneg (criticalValue c p-criticalValue a p))
  nlinarith only [hl,hm]

private theorem factor_bounds {p : ℕ} (hp : 17 ≤ p) {c y : ℝ}
    (hc : PositiveRestrictiveReturn c p) (hy : y ∈ Icc (-1 : ℝ) 1) (j : ℕ) :
    (back c (j+1) (criticalValue c p)+
      back c (j+1) (criticalValue c p*y))/4 ∈ Icc (0 : ℝ) 1 := by
  have h1 := inverse_positive_bounds (wide_band hp hc) (terminal_self hp hc) j
  have h2 := inverse_positive_bounds (wide_band hp hc) (terminal_image hp hc hy) j
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

/-- Uniform nondegeneracy for the full normalized inverse secant product. -/
theorem phaseProduct_bounds {p : ℕ} (hp : 17 ≤ p) {c y : ℝ}
    (hc : PositiveRestrictiveReturn c p) (hy : y ∈ Icc (-1 : ℝ) 1) :
    3/5 ≤ phaseProduct c p (criticalValue c p) y ∧
      phaseProduct c p (criticalValue c p) y ≤ 1 := by
  have hbase := endpointProduct_bounds hp (broad_band hp hc) (physical_scale hp hc)
  have hcomp : endpointProduct c p (criticalValue c p) ≤
      phaseProduct c p (criticalValue c p) y := by
    unfold endpointProduct phaseProduct
    apply Finset.prod_le_prod
    · intro j hj
      have hb := factor_bounds hp hc
        (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) j
      simpa only [mul_neg_one] using hb.1
    · intro j hj
      have hy' := mul_le_mul_of_nonneg_left hy.1 hc.return_pos.le
      have hm := back_mono_initial c (j+1)
        (show -criticalValue c p ≤ criticalValue c p*y by linarith only [hy'])
      linarith only [hm]
  refine ⟨hbase.1.trans hcomp,?_⟩
  unfold phaseProduct
  exact Finset.prod_le_one (fun j _ => (factor_bounds hp hc hy j).1)
    (fun j _ => (factor_bounds hp hc hy j).2)

private theorem product_input_difference {d e y v : ℝ}
    (he : 0 ≤ e) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |d*y-e*v| ≤ |d-e| + e*|y-v| := by
  have hid : d*y-e*v=(d-e)*y+e*(y-v) := by ring
  rw [hid]
  have htri := abs_add_le ((d-e)*y) (e*(y-v))
  rw [abs_mul,abs_mul,abs_of_nonneg he] at htri
  have hm := mul_le_mul_of_nonneg_left (abs_le.mpr hy) (abs_nonneg (d-e))
  nlinarith only [htri,hm]

private theorem factor_difference {p : ℕ} (hp : 17 ≤ p) {c a y v : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p)
    (hy : y ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) (j : ℕ) :
    |(back c (j+1) (criticalValue c p)+back c (j+1) (criticalValue c p*y))/4-
      (back a (j+1) (criticalValue a p)+back a (j+1) (criticalValue a p*v))/4| ≤
      |criticalValue c p-criticalValue a p| + 4*scale p*|y-v| := by
  have hq0 := scale_pos p
  have hpos := inverse_joint_bound (wide_band hp hc) (wide_band hp ha)
    (terminal_self hp hc) (terminal_self hp ha) (j+1)
  have htar := inverse_joint_bound (wide_band hp hc) (wide_band hp ha)
    (terminal_image hp hc hy) (terminal_image hp ha hv) (j+1)
  have hin := product_input_difference (d := criticalValue c p) ha.return_pos.le hy
    (v := v)
  have hpar := parameter_lipschitz_one hp hc ha
  have hscale := mul_le_mul_of_nonneg_right (ha.return_scale hp).le (abs_nonneg (y-v))
  have htri := abs_add_le
    (back c (j+1) (criticalValue c p)-back a (j+1) (criticalValue a p))
    (back c (j+1) (criticalValue c p*y)-back a (j+1) (criticalValue a p*v))
  have hid :
      (back c (j+1) (criticalValue c p)+back c (j+1) (criticalValue c p*y))/4-
        (back a (j+1) (criticalValue a p)+back a (j+1) (criticalValue a p*v))/4 =
      ((back c (j+1) (criticalValue c p)-back a (j+1) (criticalValue a p))+
        (back c (j+1) (criticalValue c p*y)-back a (j+1) (criticalValue a p*v)))/4 := by
    ring
  rw [hid,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<4)]
  have hn : 0 ≤ scale p*|y-v| := by positivity
  nlinarith only [hpos,htar,hin,hpar,hscale,htri,hn]

/-- Joint normalized-target and physical-scale secant control. -/
theorem phaseProduct_lipschitz {p : ℕ} (hp : 17 ≤ p) {c a y v : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p)
    (hy : y ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    |phaseProduct c p (criticalValue c p) y-phaseProduct a p (criticalValue a p) v| ≤
      (p : ℝ)*|criticalValue c p-criticalValue a p| + 4*(p : ℝ)*scale p*|y-v| := by
  have hq0 := scale_pos p
  have hprod := product_difference
    (fun j => (back c (j+1) (criticalValue c p)+back c (j+1) (criticalValue c p*y))/4)
    (fun j => (back a (j+1) (criticalValue a p)+back a (j+1) (criticalValue a p*v))/4)
    (p-1) (fun j _ => factor_bounds hp hc hy j) (fun j _ => factor_bounds hp ha hv j)
  have hsum : (∑ j ∈ Finset.range (p-1),
      |(back c (j+1) (criticalValue c p)+back c (j+1) (criticalValue c p*y))/4-
        (back a (j+1) (criticalValue a p)+back a (j+1) (criticalValue a p*v))/4|) ≤
      ((p-1 : ℕ) : ℝ)*(|criticalValue c p-criticalValue a p| + 4*scale p*|y-v|) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (p-1),
          (|criticalValue c p-criticalValue a p| + 4*scale p*|y-v|) :=
        Finset.sum_le_sum (fun j _ => factor_difference hp hc ha hy hv j)
      _ = _ := by simp <;> ring
  have hn : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hm := mul_le_mul_of_nonneg_right hn
    (show 0 ≤ |criticalValue c p-criticalValue a p| + 4*scale p*|y-v| by positivity)
  change |phaseProduct c p (criticalValue c p) y-
    phaseProduct a p (criticalValue a p) v| ≤ _ at hprod
  nlinarith only [hprod,hsum,hm]

private theorem ratio_difference {X X' Y Y' : ℝ}
    (hX' : X' ∈ Icc (0 : ℝ) 1)
    (hY : Y ∈ Icc (3/5 : ℝ) 1) (hY' : Y' ∈ Icc (3/5 : ℝ) 1) :
    |X/Y-X'/Y'| ≤ (5/3)*|X-X'| + (25/9)*|Y-Y'| := by
  have hY0 : 0<Y := by linarith [hY.1]
  have hY'0 : 0<Y' := by linarith [hY'.1]
  have hden : 9/25 ≤ Y*Y' := by
    have hm := mul_le_mul hY.1 hY'.1 (by norm_num : (0 : ℝ) ≤ 3/5) hY0.le
    norm_num at hm
    exact hm
  have hterm1 : |X-X'| / Y ≤ (5/3)*|X-X'| := by
    apply (div_le_iff₀ hY0).mpr
    have hm := mul_le_mul_of_nonneg_right hY.1 (abs_nonneg (X-X'))
    nlinarith only [hm]
  have hnum := mul_le_mul_of_nonneg_right hX'.2 (abs_nonneg (Y-Y'))
  have hterm2 : X'*|Y-Y'| / (Y*Y') ≤ (25/9)*|Y-Y'| := by
    apply (div_le_iff₀ (mul_pos hY0 hY'0)).mpr
    have hm := mul_le_mul_of_nonneg_right hden
      (show 0 ≤ (25/9)*|Y-Y'| by positivity)
    nlinarith only [hnum,hm]
  have hid : X/Y-X'/Y'=(X-X')/Y+X'*(Y'-Y)/(Y*Y') := by
    field_simp [hY0.ne',hY'0.ne']
    ring
  rw [hid]
  have htri := abs_add_le ((X-X')/Y) (X'*(Y'-Y)/(Y*Y'))
  rw [abs_div,abs_div,abs_mul,abs_of_nonneg hX'.1,
    abs_of_pos hY0,abs_of_pos (mul_pos hY0 hY'0),abs_sub_comm Y' Y] at htri
  linarith only [htri,hterm1,hterm2]

/-- The inverse return shape has a small joint variation after division
by its critical coefficient. -/
theorem inverseRatio_lipschitz {p : ℕ} (hp : 17 ≤ p) {c a y v : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p)
    (hy : y ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    |inverseRatio c p y-inverseRatio a p v| ≤
      5*(p : ℝ)*|criticalValue c p-criticalValue a p| + 
        7*(p : ℝ)*scale p*|y-v| := by
  have hq0 := scale_pos p
  have hunit : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hcy := phaseProduct_bounds hp hc hy
  have hav := phaseProduct_bounds hp ha hv
  have hc1 := phaseProduct_bounds hp hc hunit
  have ha1 := phaseProduct_bounds hp ha hunit
  have hr := ratio_difference (X := phaseProduct c p (criticalValue c p) y)
    ⟨by linarith [hav.1],hav.2⟩ hc1 ha1
  have hp1 := phaseProduct_lipschitz hp hc ha hunit hunit
  have hpy := phaseProduct_lipschitz hp hc ha hy hv
  simp only [sub_self,abs_zero,mul_zero,add_zero] at hp1
  change |inverseRatio c p y-inverseRatio a p v| ≤ _ at hr
  have hn1 : 0 ≤ (p : ℝ)*|criticalValue c p-criticalValue a p| := by positivity
  have hn2 : 0 ≤ (p : ℝ)*scale p*|y-v| := by positivity
  nlinarith only [hr,hp1,hpy,hn1,hn2]

theorem inverseRatio_near_one {p : ℕ} (hp : 17 ≤ p) {c y : ℝ}
    (hc : PositiveRestrictiveReturn c p) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |inverseRatio c p y-1| ≤ 14*(p : ℝ)*scale p := by
  have hq0 := scale_pos p
  have hunit : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hP := phaseProduct_bounds hp hc hunit
  have hP0 : phaseProduct c p (criticalValue c p) 1 ≠ 0 := by linarith [hP.1]
  have hr := inverseRatio_lipschitz hp hc hc hy hunit
  have hratio : inverseRatio c p 1=1 := by
    unfold inverseRatio
    exact div_self hP0
  rw [hratio,sub_self,abs_zero,mul_zero,zero_add] at hr
  have hdiff : |y-1| ≤ 2 := by apply abs_le.mpr; constructor <;> linarith [hy.1,hy.2]
  have hm := mul_le_mul_of_nonneg_left hdiff
    (show 0 ≤ 7*(p : ℝ)*scale p by positivity)
  nlinarith only [hr,hm]

theorem scale_power_identity {p : ℕ} (hp : 1 ≤ p) :
    (4 : ℝ)^(p-1)*scale p=1/4 := by
  have hpow : (4 : ℝ)^p=(4 : ℝ)^(p-1)*4 := by
    rw [← pow_succ,Nat.sub_add_cancel hp]
  have hid : (4 : ℝ)^p*scale p=1 := by
    unfold scale
    rw [← mul_pow]
    norm_num
  rw [hpow] at hid
  nlinarith only [hid]

/-- Exact identification of the inverse product with the actual
quadratic coefficient of the return map. -/
theorem kappa_product {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : PositiveRestrictiveReturn c p) :
    kappa p c = criticalValue c p*(4 : ℝ)^(p-1)*
      phaseProduct c p (criticalValue c p) 1 := by
  have hcoef := shooting_coefficient_product (parameter_band hp (broad_band hp hc))
    (show criticalValue c p ∈ Icc (0 : ℝ) 2 from
      ⟨hc.return_pos.le,(terminal_self hp hc).2⟩) (hc.shooting_identity hp)
  have hcoef' : -quadraticCoefficient c (p-1)*scale p =
      (-c)/8*∏ j ∈ Finset.range (p-2), back c (j+1) (criticalValue c p)/2 := by
    simpa only [show p-2+1=p-1 by omega,show p-2+2=p by omega] using hcoef
  have hP : phaseProduct c p (criticalValue c p) 1 =
      4*(-quadraticCoefficient c (p-1)*scale p) := by
    rw [hcoef']
    unfold phaseProduct
    simp only [mul_one]
    have hrewrite : (∏ j ∈ Finset.range (p-1),
        (back c (j+1) (criticalValue c p)+back c (j+1) (criticalValue c p))/4) =
        ∏ j ∈ Finset.range (p-1), back c (j+1) (criticalValue c p)/2 := by
      apply Finset.prod_congr rfl
      intro j hj
      ring
    rw [hrewrite,show p-1=(p-2)+1 by omega,Finset.prod_range_succ]
    rw [show p-2+1=p-1 by omega,hc.critical_inverse (by omega)]
    ring
  have hscale := scale_power_identity (p := p) (by omega)
  unfold kappa
  rw [hP]
  calc
    -quadraticCoefficient c (p-1)*criticalValue c p =
        (-quadraticCoefficient c (p-1)*criticalValue c p)*
          (4*((4 : ℝ)^(p-1)*scale p)) := by rw [hscale]; ring
    _ = _ := by ring

theorem kappa_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : PositiveRestrictiveReturn c p) : kappa p c ∈ Ioo (0 : ℝ) (7/2) := by
  have hP := phaseProduct_bounds hp hc (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  have hP0 : 0 < phaseProduct c p (criticalValue c p) 1 := by linarith [hP.1]
  rw [kappa_product hp hc]
  refine ⟨mul_pos (mul_pos hc.return_pos (by positivity)) hP0,?_⟩
  have hmul := mul_le_mul_of_nonneg_left hP.2
    (mul_nonneg hc.return_pos.le (by positivity : (0 : ℝ) ≤ 4^(p-1)))
  have hscale := mul_lt_mul_of_pos_right (hc.return_scale hp)
    (show (0 : ℝ)<4^(p-1) by positivity)
  have hid := scale_power_identity (p := p) (by omega)
  nlinarith only [hmul,hscale,hid]

/-- A strong secant estimate for the actual normalized coefficient. -/
theorem kappa_strong_secant {p : ℕ} (hp : 17 ≤ p) {c a : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p) :
    (1/2 : ℝ)*4^(p-1)*|criticalValue c p-criticalValue a p| ≤
      |kappa p c-kappa p a| := by
  let d := criticalValue c p
  let e := criticalValue a p
  let C := phaseProduct c p d 1
  let A := phaseProduct a p e 1
  have hunit : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hC := phaseProduct_bounds hp hc hunit
  have hA := phaseProduct_bounds hp ha hunit
  have hprod := phaseProduct_lipschitz hp hc ha hunit hunit
  simp only [sub_self,abs_zero,mul_zero,add_zero] at hprod
  change |C-A| ≤ (p : ℝ)*|d-e| at hprod
  have hClower : 3/5 ≤ C := hC.1
  have hC0 : 0 ≤ C := by linarith
  have he0 : 0 ≤ e := ha.return_pos.le
  have hid : (d-e)*C=(d*C-e*A)-e*(C-A) := by ring
  have htri := abs_sub (d*C-e*A) (e*(C-A))
  rw [← hid,abs_mul,abs_of_nonneg hC0,abs_mul,abs_of_nonneg he0] at htri
  have hmC := mul_le_mul_of_nonneg_left hClower (abs_nonneg (d-e))
  have hmP := mul_le_mul_of_nonneg_left hprod he0
  have heupper : e ≤ 14*scale p := (ha.return_scale hp).le
  have hmE := mul_le_mul_of_nonneg_right heupper
    (show 0 ≤ (p : ℝ)*|d-e| by positivity)
  have hbudget : 14*(p : ℝ)*scale p ≤ 1/10 := by
    have hq := horizon_scale_small hp
    linarith
  have hmb := mul_le_mul_of_nonneg_right hbudget (abs_nonneg (d-e))
  have hcore : (1/2 : ℝ)*|d-e| ≤ |d*C-e*A| := by
    nlinarith only [htri,hmC,hmP,hmE,hmb]
  have hm := mul_le_mul_of_nonneg_left hcore
    (show (0 : ℝ) ≤ 4^(p-1) by positivity)
  have hk : kappa p c-kappa p a=(4 : ℝ)^(p-1)*(d*C-e*A) := by
    rw [kappa_product hp hc,kappa_product hp ha]
    dsimp [d,e,C,A]
    ring
  rw [hk,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4^(p-1))]
  nlinarith only [hm]

/-- Critical-return separation is bounded in the normalized coefficient
coordinate, with no differentiability premise. -/
theorem return_scale_kappa_lipschitz {p : ℕ} (hp : 17 ≤ p) {c a : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p) :
    |criticalValue c p-criticalValue a p| ≤ 8*scale p*|kappa p c-kappa p a| := by
  have hq0 := scale_pos p
  have h := kappa_strong_secant hp hc ha
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ 8*scale p by positivity)
  have hid := scale_power_identity (p := p) (by omega)
  have hleft : ((1/2 : ℝ)*4^(p-1)*|criticalValue c p-criticalValue a p|)*(8*scale p)=
      |criticalValue c p-criticalValue a p| := by
    calc
      _ = (4*((4 : ℝ)^(p-1)*scale p))*|criticalValue c p-criticalValue a p| := by ring
      _ = _ := by rw [hid]; ring
  rw [hleft] at hm
  nlinarith only [hm]

end
end GlobalWindowInverseShape
