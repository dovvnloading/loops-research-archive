import ActualCrestQuarticRelation
import CrestEndpointQuantitative
import CrestModelCoordinateBounds
import CrestResponseArithmetic

/-!
# The positive displacement of the actual maximal crest endpoint

The scalar certificate is applied here to the selected crossing of the
literal normalized polynomial return.  Its three images and its physical
circle radius supply every equation of the certificate.
-/

namespace ActualCrestEndpointResponse

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter GlobalCrestCrossing GlobalCrestOrder
open ActualCrestQuartic ActualCrestQuarticScale ActualCrestQuarticRelation
open CrestEndpointQuantitative CrestResponseConstants CrestResponseArithmetic

noncomputable section

def actualCoordinates {p : ℕ} {c : ℝ} (F : Family p c) (r : ℝ) : Coordinates where
  k := kappa p c
  t := (((normalizedReturn c p)^[2]) (point F r)).re
  y := (normalizedReturn c p (point F r)).im
  x := -(point F r).re
  v := (point F r).im
  r := r

def modelCoordinates (k r : ℝ) : Coordinates where
  k := k
  t := 1+k*(radialHeight k r)^2
  y := radialHeight k r
  x := -(radialPoint k r).re
  v := (radialPoint k r).im
  r := r

/-- A numerical scale bound used only to absorb the certified quadratic
error terms. -/
theorem scale_small_sixty {p : ℕ} (hp : 100 ≤ p) :
    scale p ≤ 1/(10 : ℝ)^60 := by
  have h : scale p ≤ scale 100 :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1) hp
  exact h.trans (by norm_num [scale])

private theorem quartic_real_part (k b : ℝ) (z : ℂ) :
    (complexMap k z+(b : ℂ)*z^4).re =
      1-k*(z.re^2-z.im^2)+b*(z.re^4-6*z.re^2*z.im^2+z.im^4) := by
  simp only [complexMap,pow_succ,pow_zero,mul_one,Complex.add_re,Complex.sub_re,
    Complex.one_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

private theorem quartic_imaginary_part (k b : ℝ) (z : ℂ) :
    (complexMap k z+(b : ℂ)*z^4).im =
      -2*k*z.re*z.im+4*b*z.re*z.im*(z.re^2-z.im^2) := by
  simp only [complexMap,pow_succ,pow_zero,mul_one,Complex.add_im,Complex.sub_im,
    Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

/-- The actual crossing and its next two returns satisfy the five
polynomial equations with the proved quartic remainder. -/
theorem actual_endpoint_equations {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1) :
    ActualEquations (scale p) (normalizedQuartic c p) (actualCoordinates F r) := by
  have hrfull : r ∈ Radius := ⟨hr.1,by linarith [hr.2]⟩
  let s : Radius := ⟨r,hrfull⟩
  let z := point F r
  let H := normalizedReturn c p
  let k := kappa p c
  let b := normalizedQuartic c p
  let y := (H z).im
  let t := ((H^[2]) z).re
  have hz : z = F.point s := by
    dsimp [z,s]
    rw [point,radiusProjection_eq hrfull]
  have hfirst : (H z).re = 0 := by rw [hz]; exact F.crossing s
  have hsecond : ((H^[2]) z).im = 0 := by
    rw [hz]
    exact F.second_real (by omega) s
  have hsecondEq : (H^[2]) z = (t : ℂ) := by
    apply Complex.ext
    · simp [t]
    · simpa only [Complex.ofReal_im] using hsecond
  have hthird : (H^[3]) z = (-1 : ℂ) := terminal_complex_equality hp F hrfull he
  have hlast : H (t : ℂ) = (-1 : ℂ) := by
    rw [← hsecondEq]
    exact hthird
  have hzDisk : ‖z‖ ≤ 3/2 := by
    rw [hz]
    exact (F.point_disk s).trans (by norm_num)
  have hyDisk : ‖H z‖ ≤ 3/2 := by
    apply (first_image_small hp hc (z := z) ?_).le.trans (by norm_num)
    rw [hz,F.point_radius]
    exact hrfull.2
  have htDisk : ‖(t : ℂ)‖ ≤ 3/2 := by
    rw [← hsecondEq,hz]
    exact (second_image_bounds hp hc F s).2.2.le.trans (by norm_num)
  have hQz := normalized_quartic_error hp hc hzDisk
  have hQy := normalized_quartic_error hp hc hyDisk
  have hQt := normalized_quartic_error hp hc htDisk
  have hzRe := (Complex.abs_re_le_norm
    (H z-(complexMap k z+(b : ℂ)*z^4))).trans hQz
  have hzIm := (Complex.abs_im_le_norm
    (H z-(complexMap k z+(b : ℂ)*z^4))).trans hQz
  have hyRe := (Complex.abs_re_le_norm
    (H (H z)-(complexMap k (H z)+(b : ℂ)*(H z)^4))).trans hQy
  have htRe := (Complex.abs_re_le_norm
    (H (t : ℂ)-(complexMap k (t : ℂ)+(b : ℂ)*(t : ℂ)^4))).trans hQt
  rw [Complex.sub_re,quartic_real_part,hlast] at htRe
  simp only [Complex.neg_re,Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 4 ≠ 0),mul_zero,
    sub_zero,add_zero] at htRe
  have htEquation : |2-k*t^2+b*t^4| ≤ 400*(scale p)^2 := by
    have hid : -1-(1-k*t^2+b*t^4) = -(2-k*t^2+b*t^4) := by ring
    rw [hid,abs_neg] at htRe
    exact htRe
  rw [Complex.sub_re,quartic_real_part,hfirst] at hyRe
  have hsecondRe : (H (H z)).re = t := rfl
  rw [hsecondRe] at hyRe
  simp only [zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 4 ≠ 0),
    zero_mul,mul_zero,sub_zero,zero_sub,zero_add,add_zero] at hyRe
  have hyEquation : |1+k*y^2+b*y^4-t| ≤ 400*(scale p)^2 := by
    change |t-(1-k*(-y^2)+b*y^4)| ≤ _ at hyRe
    have hid : t-(1-k*(-y^2)+b*y^4) = -(1+k*y^2+b*y^4-t) := by ring
    rw [hid,abs_neg] at hyRe
    exact hyRe
  rw [Complex.sub_re,quartic_real_part,hfirst,zero_sub,abs_neg] at hzRe
  rw [Complex.sub_im,quartic_imaginary_part] at hzIm
  have hcircle : (-(z.re)-3/4)^2+z.im^2-r^2 = 0 := by
    have hrad : ‖z+(3/4 : ℂ)‖ = r := by rw [hz,F.point_radius]
    have hsquare := congrArg (fun a : ℝ => a^2) hrad
    rw [Complex.sq_norm,Complex.normSq_apply] at hsquare
    norm_num [Complex.add_re,Complex.add_im] at hsquare
    nlinarith only [hsquare]
  change |2-k*t^2+b*t^4| ≤ _ ∧ |1+k*y^2+b*y^4-t| ≤ _ ∧
    |1-k*((-z.re)^2-z.im^2)+b*((-z.re)^4-6*(-z.re)^2*z.im^2+z.im^4)| ≤ _ ∧
    |2*k*(-z.re)*z.im-4*b*(-z.re)*z.im*((-z.re)^2-z.im^2)-y| ≤ _ ∧ _
  refine ⟨htEquation,hyEquation,?_,?_,hcircle⟩
  · have hfour : (-z.re)^4 = z.re^4 := by ring
    simpa only [neg_sq,hfour] using hzRe
  · have hid : (H z).im-(-2*k*z.re*z.im+4*b*z.re*z.im*(z.re^2-z.im^2)) =
        -(2*k*(-z.re)*z.im-4*b*(-z.re)*z.im*((-z.re)^2-z.im^2)-y) := by
      dsimp [y]
      ring
    rw [hid,abs_neg] at hzIm
    exact hzIm

/-- The limiting polynomial equations are satisfied by the same radical
endpoint already identified with the selected circular branch. -/
theorem model_endpoint_equations {k r : ℝ} (hk : k ∈ parameterInterval)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : crestTerminal k r = -1) :
    ModelEquations (modelCoordinates k r) := by
  have hrfull : r ∈ Icc (1/16 : ℝ) (1/8) := ⟨hr.1,by linarith [hr.2]⟩
  obtain ⟨_,_,hT,hx,hY,hradius⟩ := model_endpoint_system hk hrfull he
  dsimp [ModelEquations,modelCoordinates]
  refine ⟨?_,by ring,hx,?_,?_⟩
  · nlinarith only [hT]
  · linarith only [hY]
  · linarith only [hradius]

/-- Tight arithmetic enclosures are proved for the canonical limiting
coordinates, without assuming their numerical values. -/
theorem model_coordinate_centers {k r : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : crestTerminal k r = -1) :
    |k-kRef| ≤ 1/10^22 ∧
      |(modelCoordinates k r).t-tRef| ≤ 1/10^22 ∧
      |(modelCoordinates k r).y-yRef| ≤ 1/10^22 ∧
      |(modelCoordinates k r).x-xRef| ≤ 1/10^22 ∧
      |(modelCoordinates k r).v-vRef| ≤ 1/10^22 ∧ |r-rRef| ≤ 1/10^22 := by
  have hrfull : r ∈ Icc (1/16 : ℝ) (1/8) := ⟨hr.1,by linarith [hr.2]⟩
  obtain ⟨hv0,hY0,hT,hx,hY,hradius⟩ := model_endpoint_system hk hrfull he
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hx0 : 0 ≤ -(radialPoint k r).re := by
    have hre : (radialPoint k r).re = radialAbscissa k r := by simp [radialPoint]
    rw [hre]
    unfold radialAbscissa
    linarith only [Real.sqrt_nonneg (radialDiscriminant k r)]
  apply CrestModelCoordinateBounds.model_system_center_bounds hk hroot
    (by positivity) hY0.le hx0 hv0.le (by linarith [hr.1])
    (by nlinarith only [hT]) rfl (by nlinarith only [hx]) hY hradius

private theorem transfer_center {a o c q : ℝ}
    (ho : |o-c| ≤ 1/10^22) (hd : |a-o| ≤ 10^10*q)
    (hq : q ≤ 1/10^60) : |a-c| ≤ 1/10^20 := by
  have htri := abs_sub_le a o c
  linarith only [htri,ho,hd,hq]

/-- Positive first-order motion of the literal maximal crest radius.
All coordinates are extracted from the actual selected crossing and its
polynomial images; no alternate endpoint or auxiliary width is substituted. -/
theorem actual_endpoint_quartic_response {p : ℕ} (hp : 100 ≤ p) {c k₀ r r₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    normalizedQuartic c p/50 < r-r₀ ∧ r-r₀ < 3*normalizedQuartic c p/100 := by
  have hp17 : 17 ≤ p := by omega
  let a := actualCoordinates F r
  let o := modelCoordinates k₀ r₀
  have hq0 : 0 ≤ scale p := (scale_pos p).le
  have hqsmall := scale_small_sixty hp
  have hb := normalized_quartic_scale_bounds hp17 hc
  have hcorrelation := actual_quartic_parameter_correlation hp hc hk₀ hroot
  have hdpoint := actual_endpoint_point_error hp17 hc hk₀ hroot F hr he hr₀ he₀
  have hdfirst := actual_endpoint_first_error hp17 hc hk₀ hroot F hr he hr₀ he₀
  have hdsecond := actual_endpoint_second_error hp17 hc hk₀ hroot F hr he hr₀ he₀
  have hdradius := actual_endpoint_error hp17 hc hk₀ hroot F hr he hr₀ he₀
  have hdk : |a.k-o.k| ≤ 10^10*scale p := by
    have hb0 : 0 < normalizedQuartic c p := by linarith only [hb.1,scale_pos p]
    have hdelta0 : 0 < kappa p c-k₀ := by nlinarith only [hcorrelation.1,hb0]
    change |kappa p c-k₀| ≤ _
    rw [abs_of_pos hdelta0]
    nlinarith only [hcorrelation.2,hb.2,scale_pos p]
  have hdt : |a.t-o.t| ≤ 10^10*scale p := by
    have h := (Complex.abs_re_le_norm
      (((normalizedReturn c p)^[2]) (point F r)-
        ((1+k₀*(radialHeight k₀ r₀)^2 : ℝ) : ℂ))).trans hdsecond
    simp only [Complex.sub_re,Complex.ofReal_re] at h
    change |(((normalizedReturn c p)^[2]) (point F r)).re-
      (1+k₀*(radialHeight k₀ r₀)^2)| ≤ _
    nlinarith only [h,scale_pos p]
  have hdy : |a.y-o.y| ≤ 10^10*scale p := by
    have h := (Complex.abs_im_le_norm
      (normalizedReturn c p (point F r)-(radialHeight k₀ r₀ : ℂ)*Complex.I)).trans hdfirst
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero] at h
    change |(normalizedReturn c p (point F r)).im-radialHeight k₀ r₀| ≤ _
    nlinarith only [h,scale_pos p]
  have hdx : |a.x-o.x| ≤ 10^10*scale p := by
    have h := (Complex.abs_re_le_norm (point F r-radialPoint k₀ r₀)).trans hdpoint
    simp only [Complex.sub_re] at h
    change |-(point F r).re- -(radialPoint k₀ r₀).re| ≤ _
    rw [neg_sub_neg,abs_sub_comm]
    nlinarith only [h,scale_pos p]
  have hdv : |a.v-o.v| ≤ 10^10*scale p := by
    have h := (Complex.abs_im_le_norm (point F r-radialPoint k₀ r₀)).trans hdpoint
    simp only [Complex.sub_im] at h
    change |(point F r).im-(radialPoint k₀ r₀).im| ≤ _
    nlinarith only [h,scale_pos p]
  have hdr : |a.r-o.r| ≤ 10^10*scale p := by
    change |r-r₀| ≤ _
    nlinarith only [hdradius,scale_pos p]
  have hd : DifferenceBounds (scale p) a o := ⟨hdk,hdt,hdy,hdx,hdv,hdr⟩
  obtain ⟨hok,hot,hoy,hox,hov,hor⟩ := model_coordinate_centers hk₀ hroot hr₀ he₀
  have ho : Centered o := by
    refine ⟨hok.trans ?_,hot.trans ?_,hoy.trans ?_,hox.trans ?_,hov.trans ?_,hor.trans ?_⟩
    all_goals norm_num
  have ha : Centered a :=
    ⟨transfer_center hok hdk hqsmall,transfer_center hot hdt hqsmall,
      transfer_center hoy hdy hqsmall,transfer_center hox hdx hqsmall,
      transfer_center hov hdv hqsmall,transfer_center hor hdr hqsmall⟩
  exact endpoint_response_certificate hq0 hqsmall hb hcorrelation ha ho hd
    (model_endpoint_equations hk₀ hr₀ he₀) (actual_endpoint_equations hp17 hc F hr he)

end
end ActualCrestEndpointResponse
