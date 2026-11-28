import GlobalWindowRootFactor

/-!
# Global localization of the signed sixth-versus-third root

Strict physical return signs first restrict the normalized coefficient.
The exactly canceled relation then excludes the remaining large pieces
using six rational intervals, including the neighborhood of the center.
-/

namespace GlobalWindowRootLocalization

open Set Function NearTwoShooting LimitingCrestQuadraticReturn
open GlobalRestrictiveWindow GlobalWindowSignedChart GlobalWindowRootFactor
open LoopsLimitingCrestParameter GlobalSignedModelFactor

noncomputable section

private theorem sq_lower_of_negative {x a : ℝ} (ha : 0≤a) (hx : x≤ -a) :
    a^2≤x^2 := by
  have he := pow_le_pow_left₀ ha (show a≤ -x by linarith) 2
  simpa only [neg_sq] using he

private theorem first_five_coefficient_bounds {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p)
    (hsecond : criticalValue c (2*p)<0) (hthird : criticalValue c (3*p)<0)
    (hfourth : 0<criticalValue c (4*p)) (hfifth : criticalValue c (5*p)<0) :
    kappa p c∈Ioo (7/4 : ℝ) (15/8) := by
  let k := kappa p c
  let x := returnOrbit c p 2
  let y := returnOrbit c p 3
  let w := returnOrbit c p 4
  let z := returnOrbit c p 5
  have hk := signed_coefficient_chart hp h hsecond hfourth
  have hx : x<0 := by
    dsimp [x]
    rw [returnOrbit_eq h.return_pos.ne']
    exact div_neg_of_neg_of_pos hsecond h.return_pos
  have hy : y<0 := by
    dsimp [y]
    rw [returnOrbit_eq h.return_pos.ne']
    exact div_neg_of_neg_of_pos hthird h.return_pos
  have hw : 0<w := by
    dsimp [w]
    rw [returnOrbit_eq h.return_pos.ne']
    exact div_pos hfourth h.return_pos
  have hz : z<0 := by
    dsimp [z]
    rw [returnOrbit_eq h.return_pos.ne']
    exact div_neg_of_neg_of_pos hfifth h.return_pos
  have hF1 : realReturn c p 1=x := by
    change realReturn c p 1=realReturn c p (realReturn c p 0)
    rw [realReturn_zero h.return_pos.ne']
  have e1 := abs_le.mp (realReturn_error hp h
    (show (1 : ℝ)∈Icc (-1 : ℝ) 1 by norm_num))
  rw [hF1] at e1
  have e2 := abs_le.mp (realReturn_error hp h (returnOrbit_mem h 2))
  have e3 := abs_le.mp (realReturn_error hp h (returnOrbit_mem h 3))
  have e4 := abs_le.mp (realReturn_error hp h (returnOrbit_mem h 4))
  change -(22*scale p)≤x-(1-k*1^2) ∧ x-(1-k*1^2)≤22*scale p at e1
  change -(22*scale p)≤y-(1-k*x^2) ∧ y-(1-k*x^2)≤22*scale p at e2
  change -(22*scale p)≤w-(1-k*y^2) ∧ w-(1-k*y^2)≤22*scale p at e3
  change -(22*scale p)≤z-(1-k*w^2) ∧ z-(1-k*w^2)≤22*scale p at e4
  have heps : 22*scale p≤1/1000 := by linarith [scale_small hp]
  constructor
  · by_contra hn
    have hku : k≤7/4 := le_of_not_gt hn
    have hxl : -751/1000≤x := by nlinarith only [e1.1,heps,hku]
    have hxsq : x^2≤(751/1000 : ℝ)^2 :=
      sq_le_sq' (by linarith only [hxl]) (by linarith only [hx])
    have hmul := mul_le_mul_of_nonneg_right hku (sq_nonneg x)
    nlinarith only [e2.1,heps,hxsq,hmul,hy]
  · by_contra hn
    have hkl : 15/8≤k := le_of_not_gt hn
    have hxu : x≤ -87/100 := by nlinarith only [e1.2,heps,hkl]
    have hxsq := sq_lower_of_negative (x := x)
      (by norm_num : (0 : ℝ)≤87/100) (by linarith only [hxu])
    have hmx := mul_le_mul_of_nonneg_right hkl (sq_nonneg x)
    have hyu : y≤ -41/100 := by nlinarith only [e2.2,heps,hxsq,hmx]
    have hysq := sq_lower_of_negative (x := y)
      (by norm_num : (0 : ℝ)≤41/100) (by linarith only [hyu])
    have hmy := mul_le_mul_of_nonneg_right hkl (sq_nonneg y)
    have hwu : w≤69/100 := by nlinarith only [e3.2,heps,hysq,hmy]
    have hwsq := pow_le_pow_left₀ hw.le hwu 2
    have hmk := mul_le_mul_of_nonneg_right hk.2.le (sq_nonneg w)
    change k*w^2≤2*w^2 at hmk
    nlinarith only [e4.1,heps,hwsq,hmk,hz]

private theorem third_model_bounds {k l u : ℝ} (hk : k∈Icc l u) (hl : 1≤l) :
    l*(l-1)^2-1≤ -criticalOrbit k 3 ∧
      -criticalOrbit k 3≤u*(u-1)^2-1 := by
  have hk0 : 0≤k := by linarith [hk.1]
  have hu0 : 0≤u := hk0.trans hk.2
  have hsl := pow_le_pow_left₀ (show 0≤l-1 by linarith)
    (show l-1≤k-1 by linarith [hk.1]) 2
  have hsu := pow_le_pow_left₀ (show 0≤k-1 by linarith [hk.1])
    (show k-1≤u-1 by linarith [hk.2]) 2
  have hml := mul_le_mul hk.1 hsl (sq_nonneg (l-1)) hk0
  have hmu := mul_le_mul hk.2 hsu (sq_nonneg (k-1)) hu0
  have hid : -criticalOrbit k 3=k*(k-1)^2-1 := by
    simp only [criticalOrbit,Q,zero_pow (by decide : 2≠0),mul_zero,sub_zero,one_pow,mul_one]
    ring
  rw [hid]
  constructor <;> linarith only [hml,hmu]

private theorem fourth_model_formula (k : ℝ) :
    criticalOrbit k 4=1-k*(-criticalOrbit k 3)^2 := by
  change 1-k*(criticalOrbit k 3)^2=1-k*(-criticalOrbit k 3)^2
  rw [neg_sq]

private theorem model_sum_formula (k : ℝ) :
    -(criticalOrbit k 2+criticalOrbit k 5)=k-2+k*(criticalOrbit k 4)^2 := by
  have h2 : criticalOrbit k 2=1-k := by norm_num [criticalOrbit,Q]
  have h5 : criticalOrbit k 5=1-k*(criticalOrbit k 4)^2 := rfl
  rw [h2,h5]
  ring

private theorem modelFactor_lower_cell {k l u Ulo Uhi Wlo Slo : ℝ}
    (hk : k∈Icc l u) (hl : 1≤l) (hUlo : 0≤Ulo)
    (hUl : Ulo≤l*(l-1)^2-1) (hUu : u*(u-1)^2-1≤Uhi)
    (hWlo : 0≤Wlo) (hWl : Wlo≤1-u*Uhi^2)
    (hSlo : 0≤Slo) (hSl : Slo≤l-2+l*Wlo^2)
    (hfinish : (21/10 : ℝ)≤l^3*Ulo*(1+Wlo)*Slo) :
    21/10≤modelFactor k := by
  let v := -criticalOrbit k 3
  let w := criticalOrbit k 4
  let s := -(criticalOrbit k 2+criticalOrbit k 5)
  have hvb := third_model_bounds hk hl
  have hvlo : Ulo≤v := hUl.trans hvb.1
  have hvhi : v≤Uhi := hvb.2.trans hUu
  have hv0 : 0≤v := hUlo.trans hvlo
  have hk0 : 0≤k := by linarith [hk.1]
  have hu0 : 0≤u := hk0.trans hk.2
  have hv2 := pow_le_pow_left₀ hv0 hvhi 2
  have hmul := mul_le_mul hk.2 hv2 (sq_nonneg v) hu0
  have hwlo : Wlo≤w := by
    have he := fourth_model_formula k
    change w=1-k*v^2 at he
    linarith only [hWl,hmul,he]
  have hw0 := hWlo.trans hwlo
  have hw2 := pow_le_pow_left₀ hWlo hwlo 2
  have hmuls := mul_le_mul hk.1 hw2 (sq_nonneg Wlo) hk0
  have hslo : Slo≤s := by
    have he := model_sum_formula k
    change s=k-2+k*w^2 at he
    linarith only [hSl,hk.1,hmuls,he]
  have hsl0 : 0≤s := hSlo.trans hslo
  have hpow := pow_le_pow_left₀ (show 0≤l by linarith) hk.1 3
  have hfirst := mul_le_mul hpow hvlo hUlo (pow_nonneg hk0 3)
  have hsecond := mul_le_mul hfirst (show 1+Wlo≤1+w by linarith)
    (show 0≤1+Wlo by linarith) (mul_nonneg (pow_nonneg hk0 3) hv0)
  have hthird := mul_le_mul hsecond hslo hSlo
    (mul_nonneg (mul_nonneg (pow_nonneg hk0 3) hv0) (by linarith))
  exact hfinish.trans hthird

private theorem modelFactor_large {k : ℝ} (hk : k∈Icc (359/200 : ℝ) (15/8)) :
    21/10≤modelFactor k := by
  by_cases h1 : k≤9/5
  · apply modelFactor_lower_cell (⟨hk.1,h1⟩ : k∈Icc (359/200 : ℝ) (9/5))
      (Ulo := 134/1000) (Uhi := 152/1000) (Wlo := 958/1000) (Slo := 144/100)
    all_goals norm_num
  by_cases h2 : k≤91/50
  · apply modelFactor_lower_cell (⟨by linarith,h2⟩ : k∈Icc (9/5 : ℝ) (91/50))
      (Ulo := 152/1000) (Uhi := 224/1000) (Wlo := 908/1000) (Slo := 128/100)
    all_goals norm_num
  by_cases h3 : k≤46/25
  · apply modelFactor_lower_cell (⟨by linarith,h3⟩ : k∈Icc (91/50 : ℝ) (46/25))
      (Ulo := 223/1000) (Uhi := 299/1000) (Wlo := 835/1000) (Slo := 108/100)
    all_goals norm_num
  by_cases h4 : k≤93/50
  · apply modelFactor_lower_cell (⟨by linarith,h4⟩ : k∈Icc (46/25 : ℝ) (93/50))
      (Ulo := 298/1000) (Uhi := 376/1000) (Wlo := 737/1000) (Slo := 83/100)
    all_goals norm_num
  · apply modelFactor_lower_cell (⟨by linarith,hk.2⟩ : k∈Icc (93/50 : ℝ) (15/8))
      (Ulo := 375/1000) (Uhi := 436/1000) (Wlo := 643/1000) (Slo := 62/100)
    all_goals norm_num

private theorem abs_product_bound {a b A B : ℝ} (ha : |a|≤A) (hb : |b|≤B) :
    |a*b|≤A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg a).trans ha)

private theorem modelFactor_small {k : ℝ} (hk : k∈Icc (7/4 : ℝ) (357/200)) :
    modelFactor k≤19/10 := by
  let v := -criticalOrbit k 3
  let w := criticalOrbit k 4
  let s := -(criticalOrbit k 2+criticalOrbit k 5)
  have hv := third_model_bounds hk (by norm_num : (1 : ℝ)≤7/4)
  have hvabs : |v|≤1/10 := by
    apply abs_le.mpr
    dsimp [v]
    constructor <;> norm_num at hv ⊢ <;> linarith [hv.1,hv.2]
  have hvsq : v^2≤(1/10 : ℝ)^2 := sq_le_sq' (abs_le.mp hvabs).1 (abs_le.mp hvabs).2
  have hk0 : 0≤k := by linarith [hk.1]
  have hmul := mul_le_mul_of_nonneg_left hvsq hk0
  have hvprod := mul_nonneg hk0 (sq_nonneg v)
  have hwform := fourth_model_formula k
  change w=1-k*v^2 at hwform
  have hwb : w∈Icc (49/50 : ℝ) 1 := by
    constructor <;> nlinarith only [hmul,hk.2,hvprod,hwform]
  have hwsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤49/50) hwb.1 2
  have hwsqu := pow_le_pow_left₀ (show 0≤w by linarith [hwb.1]) hwb.2 2
  have hsform := model_sum_formula k
  change s=k-2+k*w^2 at hsform
  have hslmul := mul_le_mul hk.1 hwsq (by positivity : (0 : ℝ)≤(49/50)^2) hk0
  have hsumul := mul_le_mul_of_nonneg_left hwsqu hk0
  have hsb : s∈Icc (0 : ℝ) (157/100) := by
    constructor <;> nlinarith only [hslmul,hsumul,hsform,hk.1,hk.2]
  have hkabs : |k|≤357/200 := by rw [abs_of_nonneg hk0]; exact hk.2
  have hkpow : |k^3|≤(357/200 : ℝ)^3 := by
    simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg k) hkabs 3
  have hwabs : |1+w|≤2 := by apply abs_le.mpr; constructor <;> linarith [hwb.1,hwb.2]
  have hsabs : |s|≤157/100 := by rw [abs_of_nonneg hsb.1]; exact hsb.2
  have hprod := abs_product_bound
    (abs_product_bound (abs_product_bound hkpow hvabs) hwabs) hsabs
  have hle := le_abs_self (modelFactor k)
  change |modelFactor k|≤(357/200 : ℝ)^3*(1/10)*2*(157/100) at hprod
  exact hle.trans (hprod.trans (by norm_num))

/-- Every literal signed root in the global physical class lies in the
same small coefficient interval, including parameters near the center
and near the restrictive boundary in the initial search. -/
theorem signed_root_coarse_interval {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p)
    (hsecond : criticalValue c (2*p)<0) (hthird : criticalValue c (3*p)<0)
    (hfourth : 0<criticalValue c (4*p)) (hfifth : criticalValue c (5*p)<0)
    (hroot : criticalValue c (6*p)+criticalValue c (3*p)=0) :
    kappa p c∈Icc (357/200 : ℝ) (359/200) := by
  have hk := signed_coefficient_chart hp h hsecond hfourth
  have hkc := first_five_coefficient_bounds hp h hsecond hthird hfourth hfifth
  have herr := signed_root_model_error hp h ⟨hk.1.le,hk.2.le⟩ hthird hroot
  have heps : 50000*scale p<1/1000 := by linarith [scale_small hp]
  have he := abs_lt.mp (herr.trans_lt heps)
  constructor
  · by_contra hn
    have hsmall := modelFactor_small
      (⟨hkc.1.le,le_of_not_ge hn⟩ : kappa p c∈Icc (7/4 : ℝ) (357/200))
    linarith only [hsmall,he.1]
  · by_contra hn
    have hlarge := modelFactor_large
      (⟨le_of_not_ge hn,hkc.2.le⟩ : kappa p c∈Icc (359/200 : ℝ) (15/8))
    linarith only [hlarge,he.2]

end
end GlobalWindowRootLocalization
