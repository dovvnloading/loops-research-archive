import ActualPairableSource
import ActualPairableSourceTopology
import SlitDiskCutChart
import Mathlib.Analysis.Complex.OpenMapping

/-!
# A regular coordinate across the physical source ports

The square root in the cut-target chart has different boundary values on
the two banks.  Factoring the complete even return before taking its square
root gives one holomorphic physical coordinate on the entire actual source,
including the real ports and the critical point.
-/

namespace ActualPairableCoordinate

open Set Filter Function Metric
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open QuadraticCrestDividedDifference ActualPairableSource ActualPairableSourceBounds
open scoped Topology

noncomputable section

def secant (c : ℝ) (p : ℕ) (z : ℂ) : ℂ := evenSecant c (p-1) z 0

def root (c : ℝ) (p : ℕ) (z : ℂ) : ℂ := z * Complex.sqrt (-secant c p z)

def factorArgument (c : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  (radius p : ℂ)^2 - (criticalValue c p : ℂ) * returnMap c p z

def coordinate (c : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  2 * (Real.sqrt (radius p) : ℂ) * root c p z * Complex.sqrt (factorArgument c p z) /
    (((radius p - criticalValue c p : ℝ) : ℂ) * ((radius p : ℂ) - returnMap c p z))

private theorem evenSecant_differentiable_left (c : ℝ) (n : ℕ) (w : ℂ) :
    Differentiable ℂ (fun z => evenSecant c n z w) := by
  have hf : Differentiable ℂ (quadraticMap c) := by
    intro z
    exact ((hasDerivAt_id z).pow 2 |>.add_const (c : ℂ)).differentiableAt
  induction n with
  | zero => exact differentiable_const _
  | succ n ih => exact ((hf.iterate (n+1)).add_const _).mul ih

theorem secant_differentiable (c : ℝ) (p : ℕ) : Differentiable ℂ (secant c p) :=
  evenSecant_differentiable_left c (p-1) 0

private theorem evenSecant_neg_left (c : ℝ) (n : ℕ) (z w : ℂ) :
    evenSecant c n (-z) w = evenSecant c n z w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evenSecant, ih]
    rw [show ((quadraticMap c)^[n+1]) (-z) = ((quadraticMap c)^[n+1]) z from
      returnMap_neg c (by omega) z]

theorem secant_neg (c : ℝ) (p : ℕ) (z : ℂ) : secant c p (-z) = secant c p z :=
  evenSecant_neg_left c (p-1) z 0

private theorem evenSecant_conj (c : ℝ) (n : ℕ) (z w : ℂ) :
    evenSecant c n (star z) (star w) = star (evenSecant c n z w) := by
  induction n with
  | zero => simp only [evenSecant, star_one]
  | succ n ih =>
    simp only [evenSecant, ih]
    rw [show ((quadraticMap c)^[n+1]) (star z) = star (((quadraticMap c)^[n+1]) z) from
      returnMap_conj c (n+1) z,
      show ((quadraticMap c)^[n+1]) (star w) = star (((quadraticMap c)^[n+1]) w) from
      returnMap_conj c (n+1) w]
    simp

theorem secant_conj (c : ℝ) (p : ℕ) (z : ℂ) :
    secant c p (star z) = star (secant c p z) := by
  simpa only [secant,star_zero] using evenSecant_conj c (p-1) z 0

theorem secant_re_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    {z : ℂ} (hz : z ∈ source c p) : (secant c p z).re < 0 :=
  evenSecant_re_neg hp hc (norm_lt_radius_of_mem_source hp hc hz).le
    (by simp : ‖(0 : ℂ)‖ ≤ (1/2 : ℝ)^p)

theorem returnMap_factor (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    returnMap c p z = (criticalValue c p : ℂ) + z^2 * secant c p z := by
  have h := iterate_difference c (p-1) z 0
  rw [Nat.sub_add_cancel hp] at h
  change returnMap c p z - returnMap c p 0 = _ at h
  simp only [zero_pow (by norm_num : 2 ≠ 0),sub_zero,returnMap_zero] at h
  dsimp [secant]
  linear_combination h

theorem root_sq (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    (root c p z)^2 = (criticalValue c p : ℂ) - returnMap c p z := by
  rw [root,mul_pow,SlitDiskCayley.sqrt_sq,returnMap_factor c hp]
  ring

theorem root_neg (c : ℝ) (p : ℕ) (z : ℂ) : root c p (-z) = -root c p z := by
  simp only [root,secant_neg,neg_mul]

theorem factorArgument_re_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    0 < (factorArgument c p z).re := by
  have hd := criticalValue_lt_radius hp hc
  have hr := radius_pos p
  have hf : (returnMap c p z).re < radius p :=
    (Complex.re_le_norm _).trans_lt (mem_ball_zero_iff.mp (returnMap_mem_ball hp hz))
  have hm := mul_lt_mul_of_pos_left hf hc.2.1
  have hp' := mul_pos hr (sub_pos.mpr hd)
  simp only [factorArgument,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,pow_two,mul_zero,zero_mul,sub_zero] at *
  nlinarith

theorem source_denominator_ne_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (_hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    ((radius p : ℂ) - returnMap c p z) ≠ 0 := by
  intro he
  have hh := mem_ball_zero_iff.mp (returnMap_mem_ball hp hz)
  rw [← sub_eq_zero.mp he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (radius_pos p)] at hh
  exact lt_irrefl _ hh

theorem coordinate_differentiableAt {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    DifferentiableAt ℂ (coordinate c p) z := by
  have hs : -secant c p z ∈ Complex.slitPlane :=
    Or.inl (by simpa only [Complex.neg_re] using neg_pos.mpr (secant_re_neg hp hc hz))
  have ht : factorArgument c p z ∈ Complex.slitPlane :=
    Or.inl (factorArgument_re_pos hp hc hz)
  have hf := (returnMap_hasDerivAt c (by omega : 1 ≤ p) z).differentiableAt
  have hsq : DifferentiableAt ℂ Complex.sqrt (-secant c p z) :=
    Complex.differentiableAt_sqrt hs
  have hscomp : DifferentiableAt ℂ (fun w => Complex.sqrt (-secant c p w)) z := by
    simpa only [Function.comp_def] using! hsq.comp z ((secant_differentiable c p z).neg)
  have hroot : DifferentiableAt ℂ (root c p) z :=
    differentiableAt_id.mul hscomp
  have hfactor : DifferentiableAt ℂ (factorArgument c p) z :=
    (differentiableAt_const ((radius p : ℂ)^2)).sub
      (hf.const_mul (criticalValue c p : ℂ))
  have hsq' : DifferentiableAt ℂ Complex.sqrt (factorArgument c p z) :=
    Complex.differentiableAt_sqrt ht
  exact ((hroot.const_mul (2 * (Real.sqrt (radius p) : ℂ))).mul
    (hsq'.comp z hfactor)).div
    (((differentiableAt_const (radius p : ℂ)).sub hf).const_mul
      ((radius p-criticalValue c p : ℝ) : ℂ))
    (mul_ne_zero (by exact_mod_cast (sub_pos.mpr (criticalValue_lt_radius hp hc)).ne')
      (source_denominator_ne_zero hp hc hz))

theorem coordinate_differentiableOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : DifferentiableOn ℂ (coordinate c p) (source c p) :=
  fun _ hz => (coordinate_differentiableAt hp hc hz).differentiableWithinAt

theorem coordinate_analyticOnNhd {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : AnalyticOnNhd ℂ (coordinate c p) (source c p) :=
  (coordinate_differentiableOn hp hc).analyticOnNhd (source_isOpen hp c)

theorem coordinate_continuousOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ContinuousOn (coordinate c p) (source c p) :=
  (coordinate_differentiableOn hp hc).continuousOn

theorem coordinate_neg (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    coordinate c p (-z) = -coordinate c p z := by
  simp only [coordinate,root_neg,factorArgument,returnMap_neg c hp]
  ring

@[simp] theorem coordinate_zero (c : ℝ) (p : ℕ) : coordinate c p 0 = 0 := by
  simp [coordinate,root]

theorem coordinate_eq_zero_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    coordinate c p z = 0 ↔ z = 0 := by
  have hs : Complex.sqrt (-secant c p z) ≠ 0 := by
    intro he
    have h := SlitDiskCayley.sqrt_sq (-secant c p z)
    rw [he,zero_pow (by norm_num : 2 ≠ 0)] at h
    have hn := secant_re_neg hp hc hz
    have he' : secant c p z = 0 := neg_eq_zero.mp h.symm
    simp [he'] at hn
  have ht : Complex.sqrt (factorArgument c p z) ≠ 0 := by
    intro he
    have h := SlitDiskCayley.sqrt_sq (factorArgument c p z)
    rw [he,zero_pow (by norm_num : 2 ≠ 0)] at h
    have hn := factorArgument_re_pos hp hc hz
    simp [← h] at hn
  have hr : (Real.sqrt (radius p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (radius_pos p)).ne'
  have hd : (((radius p-criticalValue c p : ℝ) : ℂ) *
      ((radius p : ℂ)-returnMap c p z)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (sub_pos.mpr (criticalValue_lt_radius hp hc)).ne')
      (source_denominator_ne_zero hp hc hz)
  simp only [coordinate,root,div_eq_zero_iff,mul_eq_zero,hr,hs,ht,hd,
    OfNat.ofNat_ne_zero,or_false,false_or]

private theorem shift_factor {R d : ℝ} (hd : R-d ≠ 0) {w : ℂ}
    (hw : (R : ℂ)-w ≠ 0) :
    SlitDiskCutChart.shift R d w =
      4*(R : ℂ)*((d : ℂ)-w)*((R : ℂ)^2-(d : ℂ)*w) /
        ((((R-d : ℝ) : ℂ)*((R : ℂ)-w))^2) := by
  have hdC : (R : ℂ)-(d : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [SlitDiskCutChart.shift,SlitDiskCayley.map,SlitDiskCayley.cayley,
    SlitDiskCayley.realMap]
  push_cast
  simp only [sub_neg_eq_add,← sub_eq_add_neg]
  field_simp [hdC,hw]
  ring

theorem coordinate_sq {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    (coordinate c p z)^2 = SlitDiskCutChart.shift (radius p) (criticalValue c p)
      (returnMap c p z) := by
  rw [coordinate,div_pow,mul_pow,mul_pow,mul_pow,
    SlitDiskCayley.sqrt_sq,root_sq c (by omega)]
  have hs : (Real.sqrt (radius p) : ℂ)^2 = (radius p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (radius_pos p).le
  rw [hs,shift_factor (sub_pos.mpr (criticalValue_lt_radius hp hc)).ne'
    (source_denominator_ne_zero hp hc hz)]
  unfold factorArgument
  congr 1
  ring

private theorem sqrt_re_pos {w : ℂ} (hw : 0 < w.re) : 0 < (Complex.sqrt w).re := by
  have hs : -w ∈ SlitDiskCayley.slit := Or.inl (by simpa using neg_neg_of_pos hw)
  simpa only [neg_neg] using SlitDiskCayley.sqrt_neg_re_pos hs

private theorem sqrt_conj_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    Complex.sqrt (star w) = star (Complex.sqrt w) := by
  have he : (Complex.sqrt (star w))^2 = (star (Complex.sqrt w))^2 := by
    rw [SlitDiskCayley.sqrt_sq,← star_pow,SlitDiskCayley.sqrt_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · exact he
  · have h1 := sqrt_re_pos (w := star w) (by simpa only [Complex.star_def,Complex.conj_re] using hw)
    have h2 := sqrt_re_pos hw
    rw [he] at h1
    simp only [Complex.neg_re,Complex.star_def,Complex.conj_re] at h1
    linarith

theorem coordinate_conj {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    coordinate c p (star z) = star (coordinate c p z) := by
  have hs : Complex.sqrt (-secant c p (star z)) = star (Complex.sqrt (-secant c p z)) := by
    rw [secant_conj,← star_neg]
    exact sqrt_conj_of_re_pos (by simpa only [Complex.neg_re] using neg_pos.mpr (secant_re_neg hp hc hz))
  have hf : factorArgument c p (star z) = star (factorArgument c p z) := by
    unfold factorArgument
    rw [returnMap_conj]
    simp
  have ht : Complex.sqrt (factorArgument c p (star z)) =
      star (Complex.sqrt (factorArgument c p z)) := by
    rw [hf]
    exact sqrt_conj_of_re_pos (factorArgument_re_pos hp hc hz)
  rw [coordinate,coordinate,root,root,hs,ht,returnMap_conj]
  simp

theorem coordinate_real_im {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) (him : z.im = 0) :
    (coordinate c p z).im = 0 := by
  have he : star z = z := by apply Complex.ext <;> simp [him]
  have h := congrArg Complex.im (coordinate_conj hp hc hz)
  rw [he] at h
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

private theorem sqrt_of_real_pos {w : ℂ} (hr : 0 < w.re) (hi : w.im = 0) :
    Complex.sqrt w = (Real.sqrt w.re : ℂ) := by
  have he : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have hs : (Real.sqrt w.re : ℂ)^2 = w := by
    rw [he]
    norm_cast
    exact Real.sq_sqrt hr.le
  calc
    Complex.sqrt w = Complex.sqrt ((Real.sqrt w.re : ℂ)^2) := congrArg _ hs.symm
    _ = (Real.sqrt w.re : ℂ) := SlitDiskCayley.sqrt_square_of_re_pos (by
      simpa only [Complex.ofReal_re] using Real.sqrt_pos.mpr hr)

theorem coordinate_real_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {x : ℝ} (hx : (x : ℂ) ∈ source c p) (hneg : x < 0) :
    (coordinate c p (x : ℂ)).re < 0 := by
  have hsreal : (secant c p (x : ℂ)).im = 0 := by
    have h := congrArg Complex.im (secant_conj c p (x : ℂ))
    simp only [Complex.star_def,Complex.conj_ofReal,Complex.conj_im] at h
    linarith
  have hfreal : (returnMap c p (x : ℂ)).im = 0 := returnMap_real_of_real c p (by simp)
  have ht : (factorArgument c p (x : ℂ)).im = 0 := by simp [factorArgument,hfreal,pow_two]
  have hs := sqrt_of_real_pos (w := -secant c p (x : ℂ))
    (by simpa only [Complex.neg_re] using neg_pos.mpr (secant_re_neg hp hc hx))
    (by simpa only [Complex.neg_im,neg_eq_zero] using hsreal)
  have ht' := sqrt_of_real_pos (factorArgument_re_pos hp hc hx) ht
  have hspos : 0 < Real.sqrt (-secant c p (x : ℂ)).re :=
    Real.sqrt_pos.mpr (by simpa only [Complex.neg_re] using neg_pos.mpr (secant_re_neg hp hc hx))
  have hF : returnMap c p (x : ℂ) = ((returnMap c p (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [hfreal]
  have heq : coordinate c p (x : ℂ) =
      ((2 * Real.sqrt (radius p) * (x * Real.sqrt (-secant c p (x : ℂ)).re) *
        Real.sqrt (factorArgument c p (x : ℂ)).re /
        ((radius p-criticalValue c p)*(radius p-(returnMap c p (x : ℂ)).re)) : ℝ) : ℂ) := by
    rw [coordinate,root,hs,ht',hF]
    push_cast
    rfl
  rw [heq]
  simp only [Complex.ofReal_re]
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos
    · exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Real.sqrt_pos.mpr (radius_pos p)))
        (mul_neg_of_neg_of_pos hneg hspos)
    · exact Real.sqrt_pos.mpr (factorArgument_re_pos hp hc hx)
  · exact mul_pos (sub_pos.mpr (criticalValue_lt_radius hp hc))
      (sub_pos.mpr ((Complex.re_le_norm _).trans_lt
        (mem_ball_zero_iff.mp (returnMap_mem_ball hp hx))))

theorem coordinate_injOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : InjOn (coordinate c p) (source c p) := by
  intro z hz w hw he
  have heq := congrArg (fun q : ℂ => q^2) he
  rw [coordinate_sq hp hc hz,coordinate_sq hp hc hw,SlitDiskCutChart.shift,
    SlitDiskCutChart.shift,sub_left_inj] at heq
  have hm := SlitDiskCayley.map_injOn (radius_pos p)
  have hz' : -returnMap c p z ∈ SlitDiskCayley.disk (radius p) := by
    simpa [SlitDiskCayley.disk] using mem_ball_zero_iff.mp (returnMap_mem_ball hp hz)
  have hw' : -returnMap c p w ∈ SlitDiskCayley.disk (radius p) := by
    simpa [SlitDiskCayley.disk] using mem_ball_zero_iff.mp (returnMap_mem_ball hp hw)
  have hF : returnMap c p z = returnMap c p w := neg_injective (hm hz' hw' heq)
  rcases (archived_collision_iff hp hc (norm_lt_radius_of_mem_source hp hc hz).le
    (norm_lt_radius_of_mem_source hp hc hw).le).mp hF with h | h
  · exact h
  · have hn : coordinate c p z = -coordinate c p w := by rw [h,coordinate_neg c (by omega)]
    have hzero : coordinate c p w = 0 := by linear_combination (1/2 : ℂ)*hn-(1/2 : ℂ)*he
    have hw0 := (coordinate_eq_zero_iff hp hc hw).mp hzero
    simpa only [hw0,neg_zero] using h

private theorem exists_imaginary_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ∃ y : ℝ, 0 < y ∧ (y : ℂ)*Complex.I ∈ source c p := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (source_isOpen hp c) 0 (zero_mem_source hp hc)
  refine ⟨ε/2,half_pos hε,hball ?_⟩
  rw [mem_ball_zero_iff,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (half_pos hε)]
  linarith

theorem coordinate_im_pos_of_imaginary {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {y : ℝ} (hy : 0 < y)
    (hz : (y : ℂ)*Complex.I ∈ source c p) :
    0 < (coordinate c p ((y : ℂ)*Complex.I)).im := by
  let z : ℂ := (y : ℂ)*Complex.I
  have hstar : star z = -z := by simp [z]
  have hsreal : (secant c p z).im = 0 := by
    have h := congrArg Complex.im (secant_conj c p z)
    rw [hstar,secant_neg] at h
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
  have hfreal : (returnMap c p z).im = 0 := by
    have h := congrArg Complex.im (returnMap_conj c p z)
    rw [hstar,returnMap_neg c (by omega)] at h
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
  have ht : (factorArgument c p z).im = 0 := by simp [factorArgument,hfreal,pow_two]
  have hs := sqrt_of_real_pos (w := -secant c p z)
    (by simpa only [Complex.neg_re] using neg_pos.mpr (secant_re_neg hp hc hz))
    (by simpa only [Complex.neg_im,neg_eq_zero] using hsreal)
  have ht' := sqrt_of_real_pos (factorArgument_re_pos hp hc hz) ht
  have hspos : 0 < Real.sqrt (-secant c p z).re :=
    Real.sqrt_pos.mpr (by simpa only [Complex.neg_re] using neg_pos.mpr (secant_re_neg hp hc hz))
  have hF : returnMap c p z = ((returnMap c p z).re : ℂ) := by
    apply Complex.ext <;> simp [hfreal]
  have heq : coordinate c p z =
      ((2 * Real.sqrt (radius p) * (y * Real.sqrt (-secant c p z).re) *
        Real.sqrt (factorArgument c p z).re /
        ((radius p-criticalValue c p)*(radius p-(returnMap c p z).re)) : ℝ) : ℂ)*Complex.I := by
    rw [coordinate,root,hs,ht',hF]
    dsimp only [z]
    push_cast
    simp only [Complex.ofReal_re]
    ring
  change 0 < (coordinate c p z).im
  rw [heq]
  simp only [Complex.mul_I_im,Complex.ofReal_re]
  exact div_pos
    (mul_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (radius_pos p)))
      (mul_pos hy hspos)) (Real.sqrt_pos.mpr (factorArgument_re_pos hp hc hz)))
    (mul_pos (sub_pos.mpr (criticalValue_lt_radius hp hc))
      (sub_pos.mpr ((Complex.re_le_norm _).trans_lt
        (mem_ball_zero_iff.mp (returnMap_mem_ball hp hz)))))

private theorem coordinate_im_ne_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ upperSource c p) :
    (coordinate c p z).im ≠ 0 := by
  have hF := returnMap_mapsTo_slitTarget hp hc hz
  have hd : criticalValue c p ∈ Ioo (-(radius p)) (radius p) :=
    ⟨by linarith [hc.2.1,radius_pos p],criticalValue_lt_radius hp hc⟩
  have hsl := (SlitDiskCutChart.shift_mem_slit_iff (radius_pos p) hd
    (show returnMap c p z ∈ SlitDiskCayley.disk (radius p) from
      mem_ball_zero_iff.mp hF.1)).mpr hF.2
  rw [← coordinate_sq hp hc hz.1] at hsl
  intro he
  rcases hsl with hr | hi
  · simp only [pow_two,Complex.mul_re,he,mul_zero,sub_zero] at hr
    nlinarith [sq_nonneg (coordinate c p z).re]
  · apply hi
    simp [pow_two,he]

theorem coordinate_mem_upper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ upperSource c p) :
    coordinate c p z ∈ SlitCubicCalibration.upper := by
  obtain ⟨y,hy,hyV⟩ := exists_imaginary_source hp hc
  have hyU : (y : ℂ)*Complex.I ∈ upperSource c p := ⟨hyV,by simpa using hy⟩
  have hypos := coordinate_im_pos_of_imaginary hp hc hy hyV
  have hcont : ContinuousOn (fun w => (coordinate c p w).im) (upperSource c p) :=
    Complex.continuous_im.comp_continuousOn ((coordinate_continuousOn hp hc).mono inter_subset_left)
  have hne := coordinate_im_ne_zero hp hc hz
  rcases lt_or_gt_of_ne hne with hn | hpos
  · obtain ⟨w,hw,hw0⟩ := (upperSource_isConnected hp hc).isPreconnected.intermediate_value
      hz hyU hcont (show (0 : ℝ) ∈ Icc (coordinate c p z).im
        (coordinate c p ((y : ℂ)*Complex.I)).im from ⟨hn.le,hypos.le⟩)
    exact False.elim (coordinate_im_ne_zero hp hc hw hw0)
  · exact hpos

/-- The regular physical coordinate selects the actual upper branch of
the cut-target chart; no boundary branch is an assumed identification. -/
theorem coordinate_eq_forward {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ upperSource c p) :
    coordinate c p z = SlitDiskCutChart.forward (radius p) (criticalValue c p)
      (returnMap c p z) := by
  have hF := returnMap_mapsTo_slitTarget hp hc hz
  have hd : criticalValue c p ∈ Ioo (-(radius p)) (radius p) :=
    ⟨by linarith [hc.2.1,radius_pos p],criticalValue_lt_radius hp hc⟩
  have hF' : returnMap c p z ∈ SlitDiskCutChart.domain (radius p) (criticalValue c p) :=
    ⟨mem_ball_zero_iff.mp hF.1,hF.2⟩
  have he : (coordinate c p z)^2 =
      (SlitDiskCutChart.forward (radius p) (criticalValue c p) (returnMap c p z))^2 := by
    rw [coordinate_sq hp hc hz.1,SlitDiskCutChart.forward_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · exact he
  · have h1 : 0 < (coordinate c p z).im := coordinate_mem_upper hp hc hz
    have h2 : 0 < (SlitDiskCutChart.forward (radius p) (criticalValue c p)
        (returnMap c p z)).im := SlitDiskCutChart.forward_mem_upper (radius_pos p) hd hF'
    rw [he,Complex.neg_im] at h1
    linarith

theorem coordinate_image_upperSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    coordinate c p '' upperSource c p = SlitCubicCalibration.upper := by
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact coordinate_mem_upper hp hc hz
  · intro w hw
    have hd : criticalValue c p ∈ Ioo (-(radius p)) (radius p) :=
      ⟨by linarith [hc.2.1,radius_pos p],criticalValue_lt_radius hp hc⟩
    let v := SlitDiskCutChart.inverse (radius p) (criticalValue c p) w
    have hv := SlitDiskCutChart.inverse_mem_domain (radius_pos p) hd hw
    have hv' : v ∈ slitTarget c p := ⟨mem_ball_zero_iff.mpr hv.1,hv.2⟩
    obtain ⟨z,hz,he⟩ := returnMap_surjOn_slitTarget hp hc hv'
    refine ⟨z,hz,?_⟩
    rw [coordinate_eq_forward hp hc hz,he]
    exact SlitDiskCutChart.forward_inverse (radius_pos p) hd hw

private def cofactor (c : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  2 * (Real.sqrt (radius p) : ℂ) * Complex.sqrt (-secant c p z) *
    Complex.sqrt (factorArgument c p z) /
    (((radius p-criticalValue c p : ℝ) : ℂ) * ((radius p : ℂ)-returnMap c p z))

private theorem coordinate_eq_mul (c : ℝ) (p : ℕ) (z : ℂ) :
    coordinate c p z = z * cofactor c p z := by
  unfold coordinate root cofactor
  ring

private theorem cofactor_differentiableAt {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    DifferentiableAt ℂ (cofactor c p) z := by
  have hs : -secant c p z ∈ Complex.slitPlane :=
    Or.inl (by simpa only [Complex.neg_re] using neg_pos.mpr (secant_re_neg hp hc hz))
  have ht : factorArgument c p z ∈ Complex.slitPlane := Or.inl (factorArgument_re_pos hp hc hz)
  have hf := (returnMap_hasDerivAt c (by omega : 1 ≤ p) z).differentiableAt
  have hsq : DifferentiableAt ℂ Complex.sqrt (-secant c p z) := Complex.differentiableAt_sqrt hs
  have hscomp : DifferentiableAt ℂ (fun w => Complex.sqrt (-secant c p w)) z := by
    simpa only [Function.comp_def] using! hsq.comp z ((secant_differentiable c p z).neg)
  have hfactor : DifferentiableAt ℂ (factorArgument c p) z :=
    (differentiableAt_const ((radius p : ℂ)^2)).sub (hf.const_mul (criticalValue c p : ℂ))
  have hsq' : DifferentiableAt ℂ Complex.sqrt (factorArgument c p z) :=
    Complex.differentiableAt_sqrt ht
  exact ((hscomp.const_mul (2 * (Real.sqrt (radius p) : ℂ))).mul
    (hsq'.comp z hfactor)).div
    (((differentiableAt_const (radius p : ℂ)).sub hf).const_mul
      ((radius p-criticalValue c p : ℝ) : ℂ))
    (mul_ne_zero (by exact_mod_cast (sub_pos.mpr (criticalValue_lt_radius hp hc)).ne')
      (source_denominator_ne_zero hp hc hz))

private theorem cofactor_ne_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) : cofactor c p z ≠ 0 := by
  have hs : Complex.sqrt (-secant c p z) ≠ 0 := by
    intro he
    have hh := sqrt_re_pos (w := -secant c p z)
      (by simpa only [Complex.neg_re] using neg_pos.mpr (secant_re_neg hp hc hz))
    simp only [he,Complex.zero_re,lt_self_iff_false] at hh
  have ht : Complex.sqrt (factorArgument c p z) ≠ 0 := by
    intro he
    have hh := sqrt_re_pos (factorArgument_re_pos hp hc hz)
    simp only [he,Complex.zero_re,lt_self_iff_false] at hh
  unfold cofactor
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast (Real.sqrt_pos.mpr (radius_pos p)).ne')) hs) ht)
    (mul_ne_zero (by exact_mod_cast (sub_pos.mpr (criticalValue_lt_radius hp hc)).ne')
      (source_denominator_ne_zero hp hc hz))

theorem coordinate_deriv_ne_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    deriv (coordinate c p) z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    have he : coordinate c p = fun w => w * cofactor c p w := funext (coordinate_eq_mul c p)
    have h := (hasDerivAt_id (0 : ℂ)).mul (cofactor_differentiableAt hp hc hz).hasDerivAt
    have hd : HasDerivAt (coordinate c p) (cofactor c p 0) 0 := by
      rw [he]
      simpa only [one_mul,zero_mul,add_zero,id_eq,Pi.mul_apply] using! h
    rw [hd.deriv]
    exact cofactor_ne_zero hp hc hz
  · have hz' : -returnMap c p z ∈ SlitDiskCayley.disk (radius p) := by
      simpa [SlitDiskCayley.disk] using mem_ball_zero_iff.mp (returnMap_mem_ball hp hz)
    have hsq := (coordinate_differentiableAt hp hc hz).hasDerivAt.pow 2
    have htarget := ((SlitDiskCayley.map_hasDerivAt (radius_pos p) hz').comp z
      (returnMap_hasDerivAt c (by omega : 1 ≤ p) z).neg).sub_const
        (SlitDiskCayley.realMap (radius p) (-(criticalValue c p)) : ℂ)
    have heq : (fun w => SlitDiskCutChart.shift (radius p) (criticalValue c p)
        (returnMap c p w)) =ᶠ[𝓝 z] (fun w => (coordinate c p w)^2) := by
      filter_upwards [(source_isOpen hp c).mem_nhds hz] with w hw
      exact (coordinate_sq hp hc hw).symm
    have hder := (hsq.congr_of_eventuallyEq heq).unique htarget
    have hn := mul_ne_zero (SlitDiskCayley.map_derivative_ne_zero (radius_pos p) hz')
      (neg_ne_zero.mpr (archived_derivative_ne_zero hp hc
        (norm_lt_radius_of_mem_source hp hc hz).le hz0))
    intro he
    apply hn
    simpa only [he,mul_zero,ActualPairableSource.derivative] using hder.symm

theorem coordinate_deriv_continuousOn {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ContinuousOn (deriv (coordinate c p)) (source c p) :=
  ((coordinate_differentiableOn hp hc).deriv (source_isOpen hp c)).continuousOn

theorem coordinate_image_isOpen {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {S : Set ℂ} (hS : S ⊆ source c p) (ho : IsOpen S) :
    IsOpen (coordinate c p '' S) := by
  rcases (coordinate_analyticOnNhd hp hc).is_constant_or_isOpen
      (source_isConnected hp hc).isPreconnected with ⟨w,hw⟩ | hopen
  · obtain ⟨y,hy,hyV⟩ := exists_imaginary_source hp hc
    have he := coordinate_injOn hp hc (zero_mem_source hp hc) hyV
      ((hw _ (zero_mem_source hp hc)).trans (hw _ hyV).symm)
    have him := congrArg Complex.im he
    simp only [Complex.zero_im,Complex.mul_I_im,Complex.ofReal_re] at him
    linarith
  · exact hopen S hS ho

private theorem coordinate_restrict_isOpenMap {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsOpenMap ((source c p).restrict (coordinate c p)) := by
  intro S hS
  have hopen : IsOpen (Subtype.val '' S : Set ℂ) :=
    (source_isOpen hp c).isOpenEmbedding_subtypeVal.isOpenMap S hS
  have hsub : (Subtype.val '' S : Set ℂ) ⊆ source c p := by
    rintro z ⟨w,hw,rfl⟩
    exact w.property
  change IsOpen ((fun x : source c p => coordinate c p (x : ℂ)) '' S)
  simpa only [image_image,Function.comp_def] using coordinate_image_isOpen hp hc hsub hopen

/-- The regular coordinate is a genuine conformal chart on the entire
physical source.  In particular its inverse is regular at every real
electrode interior, rather than only at points of the open upper sheet. -/
def conformalChart {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    CrestConformalModulus.ConformalChart where
  homeomorph := OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((coordinate_injOn hp hc).toPartialEquiv (coordinate c p) (source c p))
    (coordinate_continuousOn hp hc) (coordinate_restrict_isOpenMap hp hc) (source_isOpen hp c)
  derivative := deriv (coordinate c p)
  hasDeriv := fun _ hz => (coordinate_differentiableAt hp hc hz).hasDerivAt
  derivative_continuous := coordinate_deriv_continuousOn hp hc
  derivative_ne_zero := fun _ hz => coordinate_deriv_ne_zero hp hc hz

@[simp] theorem conformalChart_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    (conformalChart hp hc).homeomorph.source = source c p := rfl

@[simp] theorem conformalChart_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    (conformalChart hp hc).homeomorph.target = coordinate c p '' source c p := rfl

@[simp] theorem conformalChart_apply {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    (z : ℂ) : (conformalChart hp hc).homeomorph z = coordinate c p z := rfl

@[simp] theorem conformalChart_derivative {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) :
    (conformalChart hp hc).derivative z = deriv (coordinate c p) z := rfl

end
end ActualPairableCoordinate
