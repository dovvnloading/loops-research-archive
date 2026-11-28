import SlitCubicCalibration
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Injectivity of the actual cubic primitive

The logarithmic coordinate of the two outer branch points turns the upper
half-plane into a convex strip. The derivative of the cubic primitive in
that coordinate has positive real part. This gives injectivity by a real
mean-value argument.
-/

namespace SlitCubicUnivalence

open Set Filter Function MeasureTheory SlitCubicCalibration
open scoped Topology
noncomputable section

def rootRatio (a b c : ℝ) (z : ℂ) : ℂ := upperRoot a z * upperRoot c z / upperRoot b z

private theorem upper_ne_real {z : ℂ} (hz : z ∈ upper) (t : ℝ) : z ≠ (t:ℂ) := by
  intro heq
  have him := congrArg Complex.im heq
  have hz' : 0 < z.im := hz
  simp only [Complex.ofReal_im] at him
  linarith

theorem rootRatio_sq {a b c : ℝ} {z : ℂ} (hz : z ∈ closedUpper) :
    rootRatio a b c z ^2 = (z-(a:ℂ))*(z-(c:ℂ))/(z-(b:ℂ)) := by
  simp only [rootRatio, div_pow, mul_pow, upperRoot_sq hz]

private theorem rootRatio_sq_im_pos {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {z : ℂ} (hz : z ∈ upper) : 0 < (rootRatio a b c z ^2).im := by
  have hne : z-(b:ℂ) ≠ 0 := sub_ne_zero.mpr (upper_ne_real hz b)
  have hid : (z-(a:ℂ))*(z-(c:ℂ))/(z-(b:ℂ)) =
      z+((b-a-c:ℝ):ℂ)-(((b-a)*(c-b):ℝ):ℂ)/(z-(b:ℂ)) := by
    push_cast
    field_simp
    ring
  rw [rootRatio_sq (by simpa [closedUpper] using (show 0 < z.im from hz).le), hid]
  have hn : 0 < Complex.normSq (z-(b:ℂ)) := Complex.normSq_pos.mpr hne
  have hk : 0 < (b-a)*(c-b) := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hbc)
  have hy : 0 < z.im := hz
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero,
    Complex.div_im, Complex.ofReal_re, zero_mul, sub_zero, zero_div, zero_sub]
  have hd : 0 < (b-a)*(c-b)*z.im/Complex.normSq (z-(b:ℂ)) := div_pos (mul_pos hk hy) hn
  linarith

private theorem rootRatio_re_ne_zero {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {z : ℂ} (hz : z ∈ upper) : (rootRatio a b c z).re ≠ 0 := by
  intro heq
  have h := rootRatio_sq_im_pos hab hbc hz
  simp only [pow_two, Complex.mul_im, heq, zero_mul, mul_zero, add_zero] at h
  exact (lt_irrefl 0) h

theorem rootRatio_continuousAt {a b c : ℝ} {z : ℂ} (hz : z ∈ closedUpper)
    (hzb : z ≠ (b:ℂ)) : ContinuousAt (rootRatio a b c) z := by
  exact ((upperRoot_continuous a).continuousAt.mul (upperRoot_continuous c).continuousAt).div
    (upperRoot_continuous b).continuousAt (upperRoot_ne_zero hz hzb)

private theorem rootRatio_real_right_pos {a b c x : ℝ} (hax : a < x)
    (hbx : b < x) (hcx : c < x) : 0 < (rootRatio a b c (x:ℂ)).re := by
  simp only [rootRatio, upperRoot_real_right hax.le, upperRoot_real_right hbx.le,
    upperRoot_real_right hcx.le, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re]
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hax))
    (Real.sqrt_pos.mpr (sub_pos.mpr hcx))) (Real.sqrt_pos.mpr (sub_pos.mpr hbx))

/-- The branch selected by the upper-side square roots has positive real
part after the logarithmic change of variable. -/
theorem rootRatio_re_pos {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {z : ℂ} (hz : z ∈ upper) : 0 < (rootRatio a b c z).re := by
  have hc : ContinuousOn (fun u => (rootRatio a b c u).re) upper := by
    intro u hu
    exact (Complex.continuous_re.continuousAt.comp
      (rootRatio_continuousAt (a := a) (c := c) (by simpa [closedUpper] using (show 0 < u.im from hu).le)
        (upper_ne_real hu b))).continuousWithinAt
  let r : ℝ := c+1
  have hrpos : 0 < (rootRatio a b c (r:ℂ)).re :=
    rootRatio_real_right_pos (by dsimp [r]; linarith) (by dsimp [r]; linarith)
      (by dsimp [r]; linarith)
  have hrb : (r:ℂ) ≠ (b:ℂ) := by
    exact_mod_cast (show r ≠ b by dsimp [r]; linarith)
  have hrc : ContinuousAt (fun u => (rootRatio a b c u).re) (r:ℂ) :=
    Complex.continuous_re.continuousAt.comp
      (rootRatio_continuousAt (a := a) (c := c) (by simp [closedUpper]) hrb)
  have hnh : {u : ℂ | 0 < (rootRatio a b c u).re} ∈ 𝓝 (r:ℂ) :=
    hrc.preimage_mem_nhds (Ioi_mem_nhds hrpos)
  have hrcl : (r:ℂ) ∈ closure upper := by
    rw [upper, Complex.closure_setOf_lt_im]
    simp
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.1 hnh
  obtain ⟨w,hw,hwd⟩ := Metric.mem_closure_iff.1 hrcl δ hδ
  have hwp : 0 < (rootRatio a b c w).re := hδsub (by simpa [Metric.mem_ball, dist_comm] using hwd)
  by_contra hnot
  have hnonpos := le_of_not_gt hnot
  have hzero : (0:ℝ) ∈ (fun u => (rootRatio a b c u).re) '' upper :=
    upper_convex.isPreconnected.intermediate_value hz hw hc ⟨hnonpos,hwp.le⟩
  obtain ⟨u,hu,hu0⟩ := hzero
  exact rootRatio_re_ne_zero hab hbc hu hu0


/-- A positive real derivative on a convex complex domain prevents two
points from having the same image. -/
theorem injOn_of_derivative_re_pos {D : Set ℂ} (hD : Convex ℝ D)
    {F F' : ℂ → ℂ} (hF : ∀ z ∈ D, HasDerivAt F (F' z) z)
    (hpos : ∀ z ∈ D, 0 < (F' z).re) : InjOn F D := by
  intro z hz w hw heq
  by_contra hne
  have hv : w-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let γ : ℂ → ℂ := fun t => z+t*(w-z)
  have hseg (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : γ (s:ℂ) ∈ D := by
    have hc := hD hz hw (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s = 1)
    convert hc using 1
    simp only [γ, Complex.real_smul]
    push_cast
    ring
  let G : ℂ → ℂ := fun t => (F (γ t)-F z)/(w-z)
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt G (F' (γ (s:ℂ))) (s:ℂ) := by
    have hγ : HasDerivAt γ (w-z) (s:ℂ) := by
      convert ((hasDerivAt_id (s:ℂ)).mul_const (w-z)).const_add z using 1 <;> first | rfl | simp
    have h := (((hF _ (hseg s hs)).comp (s:ℂ) hγ).sub_const (F z)).div_const (w-z)
    convert h using 1 <;> first | rfl | simp [hv]
  have hm : StrictMonoOn (fun s : ℝ => (G (s:ℂ)).re) (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · intro s hs
      exact (hd s hs).real_of_complex.continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0:ℝ) 1 := interior_subset hs
      rw [(hd s hs').real_of_complex.deriv]
      exact hpos _ (hseg s hs')
  have hlt := hm (left_mem_Icc.mpr (by norm_num)) (right_mem_Icc.mpr (by norm_num))
    (show (0:ℝ) < 1 by norm_num)
  simp [G,γ,heq] at hlt


def logStrip : Set ℂ := {w | -Real.pi < w.im ∧ w.im < 0}

theorem logStrip_convex : Convex ℝ logStrip :=
  (convex_halfSpace_im_gt (-Real.pi)).inter (convex_halfSpace_im_lt 0)

def stripToUpper (a c : ℝ) (w : ℂ) : ℂ :=
  (c:ℂ)+((c-a:ℝ):ℂ)/(Complex.exp w-1)

def upperToStrip (a c : ℝ) (z : ℂ) : ℂ :=
  Complex.log ((z-(a:ℂ))/(z-(c:ℂ)))

private theorem exp_sub_one_im_neg {w : ℂ} (hw : w ∈ logStrip) :
    (Complex.exp w-1).im < 0 := by
  simpa only [Complex.sub_im, Complex.one_im, sub_zero, Complex.exp_im] using
    mul_neg_of_pos_of_neg (Real.exp_pos w.re) (Real.sin_neg_of_neg_of_neg_pi_lt hw.2 hw.1)

private theorem exp_sub_one_ne_zero {w : ℂ} (hw : w ∈ logStrip) : Complex.exp w-1 ≠ 0 := by
  intro heq
  have h := exp_sub_one_im_neg hw
  rw [heq] at h
  simp at h

theorem stripToUpper_mem_upper {a c : ℝ} (hac : a < c) {w : ℂ} (hw : w ∈ logStrip) :
    stripToUpper a c w ∈ upper := by
  have hn := Complex.normSq_pos.mpr (exp_sub_one_ne_zero hw)
  have hm : 0 < -(c-a)*(Complex.exp w-1).im :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos (sub_pos.mpr hac)) (exp_sub_one_im_neg hw)
  change 0 < (stripToUpper a c w).im
  simpa only [stripToUpper, Complex.add_im, Complex.ofReal_im, Complex.div_im,
    Complex.ofReal_re, zero_mul, zero_div, zero_sub, zero_add, neg_mul, neg_div] using div_pos hm hn

private theorem stripToUpper_hasDerivAt {a c : ℝ} (hac : a < c)
    {w : ℂ} (hw : w ∈ logStrip) :
    HasDerivAt (stripToUpper a c)
      (-(stripToUpper a c w-(a:ℂ))*(stripToUpper a c w-(c:ℂ))/((c-a:ℝ):ℂ)) w := by
  have hden := exp_sub_one_ne_zero hw
  have hca : (c:ℂ)-(a:ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hac).ne'
  have hd := ((hasDerivAt_const w ((c-a:ℝ):ℂ)).div
    ((Complex.hasDerivAt_exp w).sub_const 1) hden).const_add (c:ℂ)
  convert hd using 1 <;> first | rfl | (simp only [stripToUpper]; push_cast; field_simp [hca, hden]; ring)

private theorem differential_mul_outer {a b c : ℝ} {z : ℂ} (hz : z ∈ upper) :
    differential a b c z * (z-(a:ℂ)) * (z-(c:ℂ)) = rootRatio a b c z := by
  have ha := upperRoot_ne_zero (show 0 ≤ z.im from (show 0 < z.im from hz).le) (upper_ne_real hz a)
  have hb := upperRoot_ne_zero (show 0 ≤ z.im from (show 0 < z.im from hz).le) (upper_ne_real hz b)
  have hc := upperRoot_ne_zero (show 0 ≤ z.im from (show 0 < z.im from hz).le) (upper_ne_real hz c)
  rw [← upperRoot_sq (t := a) (show 0 ≤ z.im from (show 0 < z.im from hz).le),
    ← upperRoot_sq (t := c) (show 0 ≤ z.im from (show 0 < z.im from hz).le)]
  unfold differential rootRatio
  field_simp

def stripPotential (a b c : ℝ) (w : ℂ) : ℂ := tail a b c (stripToUpper a c w)

theorem stripPotential_hasDerivAt {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ logStrip) :
    HasDerivAt (stripPotential a b c)
      (rootRatio a b c (stripToUpper a c w)/((c-a:ℝ):ℂ)) w := by
  have hupper := stripToUpper_mem_upper (hab.trans hbc) hw
  have hd := (tail_hasDerivAt (realDensity_integrable hab hbc) hupper).comp w
    (stripToUpper_hasDerivAt (hab.trans hbc) hw)
  convert hd using 1 <;> first | rfl | skip
  rw [← differential_mul_outer hupper]
  ring

theorem stripPotential_injOn {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    InjOn (stripPotential a b c) logStrip := by
  apply injOn_of_derivative_re_pos logStrip_convex
    (fun w hw => stripPotential_hasDerivAt hab hbc hw)
  intro w hw
  rw [Complex.div_ofReal_re]
  exact div_pos (rootRatio_re_pos hab hbc (stripToUpper_mem_upper (hab.trans hbc) hw))
    (sub_pos.mpr (hab.trans hbc))


private theorem outerRatio_im_neg {a c : ℝ} (hac : a < c) {z : ℂ} (hz : z ∈ upper) :
    ((z-(a:ℂ))/(z-(c:ℂ))).im < 0 := by
  have hne : z-(c:ℂ) ≠ 0 := sub_ne_zero.mpr (upper_ne_real hz c)
  have he : (z-(a:ℂ))/(z-(c:ℂ)) = 1+((c-a:ℝ):ℂ)/(z-(c:ℂ)) := by
    push_cast
    field_simp
    ring
  rw [he]
  have hn := Complex.normSq_pos.mpr hne
  have hy : 0 < z.im := hz
  have hp : 0 < (c-a)*z.im/Complex.normSq (z-(c:ℂ)) :=
    div_pos (mul_pos (sub_pos.mpr hac) hy) hn
  simpa only [Complex.add_im, Complex.one_im, Complex.div_im, Complex.ofReal_im,
    Complex.ofReal_re, Complex.sub_im, sub_zero, zero_mul, zero_div, zero_sub, zero_add] using neg_neg_of_pos hp

theorem upperToStrip_mem_logStrip {a c : ℝ} (hac : a < c) {z : ℂ} (hz : z ∈ upper) :
    upperToStrip a c z ∈ logStrip := by
  exact ⟨Complex.neg_pi_lt_log_im _,
    by simpa only [upperToStrip, Complex.log_im] using
      Complex.arg_neg_iff.mpr (outerRatio_im_neg hac hz)⟩

theorem stripToUpper_upperToStrip {a c : ℝ} (hac : a < c) {z : ℂ} (hz : z ∈ upper) :
    stripToUpper a c (upperToStrip a c z) = z := by
  have hza : z-(a:ℂ) ≠ 0 := sub_ne_zero.mpr (upper_ne_real hz a)
  have hzc : z-(c:ℂ) ≠ 0 := sub_ne_zero.mpr (upper_ne_real hz c)
  have hca : (c:ℂ)-(a:ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hac).ne'
  unfold stripToUpper upperToStrip
  rw [Complex.exp_log (div_ne_zero hza hzc)]
  push_cast
  field_simp [hza, hzc, hca]
  field_simp [hca]
  ring

/-- The horizontal cubic tail is injective on the actual upper half-plane.
No rectangle chart or injectivity hypothesis is supplied. -/
theorem tail_injOn_upper {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    InjOn (tail a b c) upper := by
  intro z hz w hw heq
  have heq' : stripPotential a b c (upperToStrip a c z) =
      stripPotential a b c (upperToStrip a c w) := by
    simpa only [stripPotential, stripToUpper_upperToStrip (hab.trans hbc) hz,
      stripToUpper_upperToStrip (hab.trans hbc) hw] using heq
  have heq'' := stripPotential_injOn hab hbc (upperToStrip_mem_logStrip (hab.trans hbc) hz)
    (upperToStrip_mem_logStrip (hab.trans hbc) hw) heq'
  have h := congrArg (stripToUpper a c) heq''
  simpa only [stripToUpper_upperToStrip (hab.trans hbc) hz,
    stripToUpper_upperToStrip (hab.trans hbc) hw] using h

end
end SlitCubicUnivalence
