import GlobalCrestClassification
import ActualCrestLimit
import LimitingCrestArcGates

/-!
# Quantitative control of the actual maximal crest endpoint

These estimates concern the globally classified crossing of the literal
normalized return.  They supply uniform error bounds for the subsequent
signed endpoint response, retaining the same actual parameter and curve.
-/

namespace CrestEndpointQuantitative

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter GlobalCrestCrossing GlobalCrestOrder
open GlobalCrestEstimates

noncomputable section

/-- The limiting quadratic comparison on the enlarged return disk. -/
theorem actual_limit_large_error {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) {z : ℂ} (hz : ‖z‖ ≤ 3/2) :
    ‖normalizedReturn c p z-complexMap k₀ z‖ ≤ 35505*scale p := by
  have he := actual_return_error hp hc hz
  have hk := actual_tip_coefficient_error hp hc hk₀ hroot
  have hz2 : ‖z‖^2 ≤ (9/4 : ℝ) := by
    have hs := pow_le_pow_left₀ (norm_nonneg z) hz 2
    nlinarith only [hs]
  have hid : complexMap (kappa p c) z-complexMap k₀ z =
      ((k₀-kappa p c : ℝ) : ℂ)*z^2 := by
    unfold complexMap
    push_cast
    ring
  have hmodel : ‖complexMap (kappa p c) z-complexMap k₀ z‖ ≤ 35433*scale p := by
    rw [hid,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow,abs_sub_comm]
    have hm := mul_le_mul hk hz2 (sq_nonneg ‖z‖)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15748) (scale_pos p).le)
    nlinarith only [hm]
  have htri : ‖normalizedReturn c p z-complexMap k₀ z‖ ≤
      ‖normalizedReturn c p z-complexMap (kappa p c) z‖+
        ‖complexMap (kappa p c) z-complexMap k₀ z‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (normalizedReturn c p z) (complexMap (kappa p c) z) (complexMap k₀ z)
  linarith only [htri,he,hmodel]

private theorem quadratic_large_lipschitz {k : ℝ} (hk : k ∈ parameterInterval)
    {z w : ℂ} (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 3/2) :
    ‖complexMap k z-complexMap k w‖ ≤ 6*‖z-w‖ := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hk2 : k ≤ 2 := by linarith [hk.2]
  have hid : complexMap k z-complexMap k w = -(k : ℂ)*(z-w)*(z+w) := by
    unfold complexMap
    ring
  have hsum : k*(‖z‖+‖w‖) ≤ 6 := by
    calc
      _ ≤ 2*(‖z‖+‖w‖) := mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ ≤ 6 := by linarith
  calc
    _ = k*‖z-w‖*‖z+w‖ := by
      rw [hid,norm_mul,norm_mul,norm_neg,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg hk0]
    _ ≤ k*‖z-w‖*(‖z‖+‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le z w) (by positivity)
    _ = (k*(‖z‖+‖w‖))*‖z-w‖ := by ring
    _ ≤ 6*‖z-w‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

private theorem actual_model_step {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) {z w : ℂ}
    (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 3/2) :
    ‖normalizedReturn c p z-complexMap k₀ w‖ ≤
      35505*scale p+6*‖z-w‖ := by
  have he := actual_limit_large_error hp hc hk₀ hroot hz
  have hl := quadratic_large_lipschitz hk₀ hz hw
  calc
    _ ≤ ‖normalizedReturn c p z-complexMap k₀ z‖+
        ‖complexMap k₀ z-complexMap k₀ w‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (normalizedReturn c p z) (complexMap k₀ z) (complexMap k₀ w)
    _ ≤ _ := add_le_add he hl

/-- Quantitative convergence of the actual terminal coordinate on the
whole endpoint collar, with every intermediate input in the proved disk. -/
theorem actual_terminal_limit_error {p : ℕ} (hp : 17 ≤ p) {c k₀ s : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    |terminal F s-crestTerminal k₀ s| ≤ 15000000*scale p := by
  have hsfull : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  let ss : Radius := ⟨s,hsfull⟩
  let z := F.point ss
  let w := radialPoint k₀ s
  let H := normalizedReturn c p
  let Q := complexMap k₀
  have hmodel := radial_model_realization hk₀ hsfull
  have hwmem : w ∈ initialDisk := by
    change ‖radialPoint k₀ s+(3/4 : ℂ)‖ ≤ 133/2000
    rw [hmodel.1]
    exact hs.2
  have hwb := (whole_support_bounds hk₀ hwmem).1
  have hz0 : ‖z‖ ≤ 3/2 := (F.point_disk ss).trans (by norm_num)
  have hz1 : ‖H z‖ ≤ 3/2 := (first_image_small hp hc (by
    change ‖F.point ss+(3/4 : ℂ)‖ ≤ 1/8
    rw [F.point_radius]
    exact hsfull.2)).le.trans (by norm_num)
  have hz2 : ‖H (H z)‖ ≤ 3/2 :=
    (second_image_bounds hp hc F ss).2.2.le.trans (by norm_num)
  have hw0 : ‖w‖ ≤ 3/2 := (hwb 0 (by omega)).le.trans (by norm_num)
  have hw1 : ‖Q w‖ ≤ 3/2 := (hwb 1 (by omega)).le.trans (by norm_num)
  have hw2 : ‖Q (Q w)‖ ≤ 3/2 := (hwb 2 (by omega)).le.trans (by norm_num)
  have h0 : ‖z-w‖ ≤ 60000*scale p := F.point_error hp hc hk₀ hroot ss
  have hs1 := actual_model_step hp hc hk₀ hroot hz0 hw0
  have h1 : ‖H z-Q w‖ ≤ 395505*scale p := by linarith only [hs1,h0]
  have hs2 := actual_model_step hp hc hk₀ hroot hz1 hw1
  have h2 : ‖H (H z)-Q (Q w)‖ ≤ 2408535*scale p := by linarith only [hs2,h1]
  have hs3 := actual_model_step hp hc hk₀ hroot hz2 hw2
  have h3 : ‖(H^[3]) z-(Q^[3]) w‖ ≤ 15000000*scale p := by
    change ‖H (H (H z))-Q (Q (Q w))‖ ≤ _
    linarith only [hs3,h2,scale_pos p]
  have hr := (Complex.abs_re_le_norm ((H^[3]) z-(Q^[3]) w)).trans h3
  change |(((normalizedReturn c p)^[3]) (F.point ⟨s,hsfull⟩)-
    ((complexMap k₀)^[3]) (radialPoint k₀ s)).re| ≤ _ at hr
  rw [hmodel.2.2.2] at hr
  simpa only [terminal,point,radiusProjection_eq hsfull,Complex.sub_re,
    Complex.ofReal_re] using hr

private theorem radical_bounds {k s : ℝ} (hk : k ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) :
    (13/10 : ℝ) ≤ Real.sqrt (radialDiscriminant k s) ∧
      Real.sqrt (radialDiscriminant k s) ≤ 2 ∧
      radialAbscissa k s ≤ -(7/10 : ℝ) := by
  have hk0 : 0 < k := by linarith [hk.1]
  have hrecL : (4 : ℝ) ≤ 8/k := by
    apply (le_div_iff₀ hk0).mpr
    linarith [hk.2]
  have hrecU : 8/k ≤ (5 : ℝ) := by
    apply (div_le_iff₀ hk0).mpr
    linarith [hk.1]
  have hs2 : s^2 ≤ (1/8 : ℝ)^2 :=
    pow_le_pow_left₀ (by linarith [hs.1]) hs.2 2
  have hDlow : (7/4 : ℝ) ≤ radialDiscriminant k s := by
    unfold radialDiscriminant
    nlinarith only [hrecL,sq_nonneg s]
  have hDhigh : radialDiscriminant k s ≤ 4 := by
    unfold radialDiscriminant
    nlinarith only [hrecU,hs2]
  have hroot := Real.sqrt_nonneg (radialDiscriminant k s)
  have hsquare := Real.sq_sqrt (show 0 ≤ radialDiscriminant k s by linarith)
  have hlo : (13/10 : ℝ) ≤ Real.sqrt (radialDiscriminant k s) := by
    nlinarith only [hDlow,hsquare,hroot]
  have hup : Real.sqrt (radialDiscriminant k s) ≤ 2 := by
    nlinarith only [hDhigh,hsquare,hroot]
  refine ⟨hlo,hup,?_⟩
  unfold radialAbscissa
  linarith only [hlo]

private theorem radial_ordinate_growth {k s t : ℝ} (hk : k ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8))
    (ht : t ∈ Icc (1/16 : ℝ) (1/8)) (hst : s ≤ t) :
    (7/80 : ℝ)*(t-s) ≤ radialOrdinateSq k t-radialOrdinateSq k s := by
  let a := Real.sqrt (radialDiscriminant k s)
  let b := Real.sqrt (radialDiscriminant k t)
  have ha := radical_bounds hk hs
  have hb := radical_bounds hk ht
  have hab : a ≤ b := by
    apply Real.sqrt_le_sqrt
    unfold radialDiscriminant
    nlinarith only [hs.1,ht.1,hst]
  have hDa : 0 ≤ radialDiscriminant k s := by
    have hk0 : 0 < k := by linarith [hk.1]
    have hr : (4 : ℝ) ≤ 8/k := (le_div_iff₀ hk0).mpr (by linarith [hk.2])
    unfold radialDiscriminant
    nlinarith only [hr,sq_nonneg s]
  have hDb : 0 ≤ radialDiscriminant k t := by
    have hk0 : 0 < k := by linarith [hk.1]
    have hr : (4 : ℝ) ≤ 8/k := (le_div_iff₀ hk0).mpr (by linarith [hk.2])
    unfold radialDiscriminant
    nlinarith only [hr,sq_nonneg t]
  have ha2 : a^2 = radialDiscriminant k s := Real.sq_sqrt hDa
  have hb2 : b^2 = radialDiscriminant k t := Real.sq_sqrt hDb
  have hdiff : b^2-a^2 = 8*(t^2-s^2) := by
    rw [ha2,hb2]
    unfold radialDiscriminant
    ring
  have hsum : a+b ≤ 4 := by
    have haU : a ≤ 2 := ha.2.1
    have hbU : b ≤ 2 := hb.2.1
    linarith only [haU,hbU]
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hab)
  have hsqdiff : (t-s)/8 ≤ t^2-s^2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hst)
      (show 0 ≤ t+s-1/8 by linarith [hs.1,ht.1])
    nlinarith only [hm]
  have hxgap : (t-s)/16 ≤ radialAbscissa k s-radialAbscissa k t := by
    change (t-s)/16 ≤ (-3/8-a/4)-(-3/8-b/4)
    nlinarith only [hmul,hdiff,hsqdiff]
  have hxgap0 : 0 ≤ radialAbscissa k s-radialAbscissa k t := by
    linarith only [hxgap,hst]
  have hxsum : (7/5 : ℝ) ≤ -(radialAbscissa k s+radialAbscissa k t) := by
    linarith only [ha.2.2,hb.2.2]
  have hm1 := mul_le_mul_of_nonneg_left hxsum hxgap0
  have hm2 := mul_le_mul_of_nonneg_left hxgap (by norm_num : (0 : ℝ) ≤ 7/5)
  unfold radialOrdinateSq
  nlinarith only [hm1,hm2]

private theorem radial_terminal_growth {k v w : ℝ} (hk : k ∈ parameterInterval)
    (hv : 0 ≤ v) (hvw : v ≤ w) :
    40*(w-v) ≤ radialTerminal k v-radialTerminal k w := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hklo : (7/4 : ℝ) ≤ k := by linarith [hk.1]
  have hk2 : (3 : ℝ) ≤ k^2 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7/4) hklo 2
    nlinarith only [hs]
  have hw : 0 ≤ w := hv.trans hvw
  let A := 1+k*(4*(k*v)+4*(k*v)^2)
  let B := 1+k*(4*(k*w)+4*(k*w)^2)
  have hA : 1 ≤ A := by
    have hm : 0 ≤ k*(4*(k*v)+4*(k*v)^2) := by positivity
    dsimp [A]
    linarith only [hm]
  have hB : 1 ≤ B := by
    have hm : 0 ≤ k*(4*(k*w)+4*(k*w)^2) := by positivity
    dsimp [B]
    linarith only [hm]
  have hwsq : 0 ≤ w^2-v^2 := sub_nonneg.mpr (pow_le_pow_left₀ hv hvw 2)
  have hother : 0 ≤ 4*k^3*(w^2-v^2) := by positivity
  have hlinear := mul_le_mul_of_nonneg_right hk2 (sub_nonneg.mpr hvw)
  have hdiff : 12*(w-v) ≤ B-A := by
    dsimp [A,B]
    nlinarith only [hlinear,hother]
  have hdiff0 : 0 ≤ B-A := by linarith only [hdiff,hvw]
  have hquad : 2*(B-A) ≤ B^2-A^2 := by
    have hm := mul_nonneg hdiff0 (show 0 ≤ B+A-2 by linarith only [hA,hB])
    nlinarith only [hm]
  have hm := mul_le_mul hklo hquad (by linarith only [hdiff0] : 0 ≤ 2*(B-A)) hk0
  change 40*(w-v) ≤ (1-k*A^2)-(1-k*B^2)
  nlinarith only [hm,hdiff,hvw]

/-- A uniform lower secant bound for the literal limiting terminal
function.  This quantitative inverse bound holds on the full parent range. -/
theorem model_terminal_growth {k s t : ℝ} (hk : k ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8))
    (ht : t ∈ Icc (1/16 : ℝ) (1/8)) (hst : s ≤ t) :
    3*(t-s) ≤ crestTerminal k s-crestTerminal k t := by
  have hv := radial_ordinate_growth hk hs ht hst
  have hvw : radialOrdinateSq k s ≤ radialOrdinateSq k t := by linarith only [hv,hst]
  have hT := radial_terminal_growth hk (radial_ordinate_pos hk hs).le hvw
  change 3*(t-s) ≤ radialTerminal k (radialOrdinateSq k s)-
    radialTerminal k (radialOrdinateSq k t)
  linarith only [hv,hT,hst]

/-- The globally selected actual endpoint has an explicit error from
the unique endpoint of the single limiting quadratic. -/
theorem actual_endpoint_error {p : ℕ} (hp : 17 ≤ p) {c k₀ r r₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    |r-r₀| ≤ 5000000*scale p := by
  have herr := actual_terminal_limit_error hp hc hk₀ hroot F hr
  rw [he] at herr
  have hrfull : r ∈ Icc (1/16 : ℝ) (1/8) := ⟨hr.1,by linarith [hr.2]⟩
  have hr₀full : r₀ ∈ Icc (1/16 : ℝ) (1/8) := ⟨hr₀.1,by linarith [hr₀.2]⟩
  rcases le_total r r₀ with h | h
  · have hg := model_terminal_growth hk₀ hrfull hr₀full h
    rw [he₀] at hg
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith only [hg,(abs_le.mp herr).1]
  · have hg := model_terminal_growth hk₀ hr₀full hrfull h
    rw [he₀] at hg
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    linarith only [hg,(abs_le.mp herr).2]

/-- The actual endpoint equation is a complex identity, with imaginary
part fixed by the selected crossing family. -/
theorem terminal_complex_equality {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (F : Family p c) (hr : r ∈ Icc (1/16 : ℝ) (1/8))
    (he : terminal F r = -1) :
    ((normalizedReturn c p)^[3]) (point F r) = (-1 : ℂ) := by
  apply Complex.ext
  · simpa only [terminal,Complex.neg_re,Complex.one_re] using he
  · simpa only [point,radiusProjection_eq hr,Complex.neg_im,Complex.one_im,neg_zero]
      using F.third_real (by omega) ⟨r,hr⟩

/-- The actual terminal point itself lies quantitatively near the
limiting endpoint point, rather than merely near its own-radius model. -/
theorem actual_endpoint_point_error {p : ℕ} (hp : 17 ≤ p) {c k₀ r r₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    ‖point F r-radialPoint k₀ r₀‖ ≤ 150000000*scale p := by
  have hrfull : r ∈ Radius := ⟨hr.1,by linarith [hr.2]⟩
  have hr₀full : r₀ ∈ Radius := ⟨hr₀.1,by linarith [hr₀.2]⟩
  have hrad := actual_endpoint_error hp hc hk₀ hroot F hr he hr₀ he₀
  have hpoint := F.point_error hp hc hk₀ hroot ⟨r₀,hr₀full⟩
  have hdist : ‖F.point ⟨r,hrfull⟩-F.point ⟨r₀,hr₀full⟩‖ ≤ 26*|r-r₀| := by
    have h := F.point_lipschitz.dist_le_mul ⟨r,hrfull⟩ ⟨r₀,hr₀full⟩
    rw [dist_eq_norm,NNReal.coe_ofNat,Subtype.dist_eq,Real.dist_eq] at h
    exact h
  have htri : ‖F.point ⟨r,hrfull⟩-radialPoint k₀ r₀‖ ≤
      ‖F.point ⟨r,hrfull⟩-F.point ⟨r₀,hr₀full⟩‖+
        ‖F.point ⟨r₀,hr₀full⟩-radialPoint k₀ r₀‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (F.point ⟨r,hrfull⟩) (F.point ⟨r₀,hr₀full⟩) (radialPoint k₀ r₀)
  rw [point,radiusProjection_eq hrfull]
  linarith only [htri,hdist,hpoint,hrad,scale_pos p]

/-- The complete model crossing branch stays in a smaller common disk. -/
theorem model_point_norm_le {k s : ℝ} (hk : k ∈ parameterInterval)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) :
    ‖radialPoint k s‖ ≤ (79/100 : ℝ) := by
  have hk0 : 0 < k := by linarith [hk.1]
  have hrec : 8/k ≤ (9/2 : ℝ) := by
    apply (div_le_iff₀ hk0).mpr
    linarith [hk.1]
  have hs2 : s^2 ≤ (1/8 : ℝ)^2 :=
    pow_le_pow_left₀ (by linarith [hs.1]) hs.2 2
  have hD : radialDiscriminant k s ≤ 19/8 := by
    unfold radialDiscriminant
    nlinarith only [hrec,hs2]
  have hD0 : 0 ≤ radialDiscriminant k s := by
    have hr : (4 : ℝ) ≤ 8/k := (le_div_iff₀ hk0).mpr (by linarith [hk.2])
    unfold radialDiscriminant
    nlinarith only [hr,sq_nonneg s]
  have hsqrt := Real.sq_sqrt hD0
  have hroot := Real.sqrt_nonneg (radialDiscriminant k s)
  have hrootU : Real.sqrt (radialDiscriminant k s) ≤ (8/5 : ℝ) := by
    nlinarith only [hD,hsqrt,hroot]
  have hxL : -(31/40 : ℝ) ≤ radialAbscissa k s := by
    unfold radialAbscissa
    linarith only [hrootU]
  have hxU := (radical_bounds hk hs).2.2
  have hx2 : (radialAbscissa k s)^2 ≤ (31/40 : ℝ)^2 :=
    sq_le_sq' hxL (by linarith only [hxU])
  have hcircle := radial_circle_identity hk hs
  have hv : radialOrdinateSq k s ≤ s^2 := by
    nlinarith only [hcircle,sq_nonneg (radialAbscissa k s+3/4)]
  have hy := Real.sq_sqrt (radial_ordinate_pos hk hs).le
  have hre : (radialPoint k s).re = radialAbscissa k s := by simp [radialPoint]
  have him : (radialPoint k s).im = Real.sqrt (radialOrdinateSq k s) := by simp [radialPoint]
  have hn : ‖radialPoint k s‖^2 = (radialAbscissa k s)^2+radialOrdinateSq k s := by
    rw [Complex.sq_norm,Complex.normSq_apply,hre,him]
    nlinarith only [hy]
  nlinarith only [hn,hx2,hv,hs2,norm_nonneg (radialPoint k s)]

/-- Exact real polynomial equations for the model endpoint.  In these
coordinates the crossing, two subsequent returns and radius are all retained. -/
theorem model_endpoint_system {k r : ℝ} (hk : k ∈ parameterInterval)
    (hr : r ∈ Icc (1/16 : ℝ) (1/8)) (he : crestTerminal k r = -1) :
    0 < (radialPoint k r).im ∧ 0 < radialHeight k r ∧
      1-k*(1+k*(radialHeight k r)^2)^2 = -1 ∧
      1-k*((-(radialPoint k r).re)^2-(radialPoint k r).im^2) = 0 ∧
      2*k*(-(radialPoint k r).re)*(radialPoint k r).im = radialHeight k r ∧
      (-(radialPoint k r).re-3/4)^2+(radialPoint k r).im^2 = r^2 := by
  have hmodel := radial_model_realization hk hr
  have hpos : 0 < (radialPoint k r).im := by
    simpa only [radialPoint,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
      using Real.sqrt_pos.mpr (radial_ordinate_pos hk hr)
  have hthree := hmodel.2.2.2
  change complexMap k (complexMap k (complexMap k (radialPoint k r))) =
    (crestTerminal k r : ℂ) at hthree
  rw [hmodel.2.2.1,complexMap_imaginary,complexMap_real,he] at hthree
  have hlast := congrArg Complex.re hthree
  simp only [Complex.ofReal_re,LimitingCrest.realMap] at hlast
  have hre := congrArg Complex.re hmodel.2.2.1
  have him := congrArg Complex.im hmodel.2.2.1
  simp [complexMap,pow_two,Complex.mul_re,Complex.mul_im] at hre him
  have hcircle := congrArg (fun x : ℝ => x^2) hmodel.1
  rw [Complex.sq_norm,Complex.normSq_apply] at hcircle
  norm_num [Complex.add_re,Complex.add_im] at hcircle
  refine ⟨hpos,hmodel.2.1,hlast,?_,?_,?_⟩
  · nlinarith only [hre]
  · nlinarith only [him]
  · nlinarith only [hcircle]

/-- The first actual endpoint image converges quantitatively to the
positive imaginary model endpoint image. -/
theorem actual_endpoint_first_error {p : ℕ} (hp : 17 ≤ p) {c k₀ r r₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    ‖normalizedReturn c p (point F r)-(radialHeight k₀ r₀ : ℂ)*Complex.I‖ ≤
      1000000000*scale p := by
  have hr₀full : r₀ ∈ Icc (1/16 : ℝ) (1/8) := ⟨hr₀.1,by linarith [hr₀.2]⟩
  have hz : ‖point F r‖ ≤ 3/2 :=
    (F.point_disk (radiusProjection r)).trans (by norm_num)
  have hw : ‖radialPoint k₀ r₀‖ ≤ 3/2 :=
    (model_point_norm_le hk₀ hr₀full).trans (by norm_num)
  have hpoint := actual_endpoint_point_error hp hc hk₀ hroot F hr he hr₀ he₀
  have hstep := actual_model_step hp hc hk₀ hroot hz hw
  rw [(radial_model_realization hk₀ hr₀full).2.2.1] at hstep
  linarith only [hstep,hpoint,scale_pos p]

/-- The second actual endpoint image converges to the positive real
model endpoint image, with the same chosen endpoint and return. -/
theorem actual_endpoint_second_error {p : ℕ} (hp : 17 ≤ p) {c k₀ r r₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    ‖((normalizedReturn c p)^[2]) (point F r)-
      ((1+k₀*(radialHeight k₀ r₀)^2 : ℝ) : ℂ)‖ ≤ 7000000000*scale p := by
  have hr₀full : r₀ ∈ Icc (1/16 : ℝ) (1/8) := ⟨hr₀.1,by linarith [hr₀.2]⟩
  have hmodel := radial_model_realization hk₀ hr₀full
  have hparent : ‖point F r+(3/4 : ℂ)‖ ≤ 1/8 := by
    unfold point
    rw [F.point_radius]
    exact (radiusProjection r).property.2
  have hz : ‖normalizedReturn c p (point F r)‖ ≤ 3/2 :=
    (first_image_small hp hc hparent).le.trans (by norm_num)
  have hwmem : radialPoint k₀ r₀ ∈ initialDisk := by
    change ‖radialPoint k₀ r₀+(3/4 : ℂ)‖ ≤ 133/2000
    rw [hmodel.1]
    exact hr₀.2
  have hw : ‖complexMap k₀ (radialPoint k₀ r₀)‖ ≤ 3/2 :=
    ((whole_support_bounds hk₀ hwmem).1 1 (by omega)).le.trans (by norm_num)
  have hfirst := actual_endpoint_first_error hp hc hk₀ hroot F hr he hr₀ he₀
  have hstep := actual_model_step hp hc hk₀ hroot hz hw
  rw [hmodel.2.2.1,complexMap_imaginary] at hstep
  change ‖normalizedReturn c p (normalizedReturn c p (point F r))-
    ((1+k₀*(radialHeight k₀ r₀)^2 : ℝ) : ℂ)‖ ≤ _
  linarith only [hstep,hfirst,scale_pos p]

end
end CrestEndpointQuantitative
