import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import CrestConformalModulus
import Mathlib.Tactic

/-!
# Explicit disk-to-slit-plane coordinates

The squared Cayley transform and its principal-square-root inverse give
actual complex analytic coordinates for a finite disk.  This module does
not assert invariance of any curve-family modulus.
-/

namespace SlitDiskCayley

open Set Filter
open scoped Topology

noncomputable section

def disk (R : ℝ) : Set ℂ := {z | ‖z‖ < R}

def slit : Set ℂ := {w | w.re < 0 ∨ w.im ≠ 0}

def cayley (R : ℝ) (z : ℂ) : ℂ := ((R:ℂ)-z) / ((R:ℂ)+z)

def map (R : ℝ) (z : ℂ) : ℂ := -(cayley R z)^2

def inverse (R : ℝ) (w : ℂ) : ℂ :=
  (R:ℂ) * (1-Complex.sqrt (-w)) / (1+Complex.sqrt (-w))

def realMap (R x : ℝ) : ℝ := -((R-x)/(R+x))^2

theorem disk_open (R : ℝ) : IsOpen (disk R) :=
  isOpen_lt continuous_norm continuous_const

theorem slit_open : IsOpen slit :=
  (isOpen_lt Complex.continuous_re continuous_const).union
    (isOpen_ne_fun Complex.continuous_im continuous_const)

private theorem denominator_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ disk R) : (R:ℂ)+z ≠ 0 := by
  intro he
  have he' : z = -(R:ℂ) := by linear_combination he
  change ‖z‖ < R at hz
  simp [he', norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hz

private theorem numerator_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ disk R) : (R:ℂ)-z ≠ 0 := by
  intro he
  have he' : z = (R:ℂ) := (sub_eq_zero.mp he).symm
  change ‖z‖ < R at hz
  simp [he', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hz

theorem cayley_re (R : ℝ) (z : ℂ) :
    (cayley R z).re = (R^2 - ‖z‖^2) / Complex.normSq ((R:ℂ)+z) := by
  rw [cayley, Complex.div_re]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.sub_im,
    Complex.add_im, Complex.ofReal_im, zero_sub, zero_add]
  rw [← add_div]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem cayley_im (R : ℝ) (z : ℂ) :
    (cayley R z).im = -2*R*z.im / Complex.normSq ((R:ℂ)+z) := by
  rw [cayley, Complex.div_im]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.sub_im,
    Complex.add_im, Complex.ofReal_im, zero_sub, zero_add]
  rw [← sub_div]
  congr 1
  ring

theorem cayley_re_pos {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    0 < (cayley R z).re := by
  rw [cayley_re]
  apply div_pos
  · have hnorm : ‖z‖ < R := hz
    nlinarith [norm_nonneg z]
  · exact Complex.normSq_pos.mpr (denominator_ne_zero hR hz)

private theorem neg_square_mem_slit {q : ℂ} (hq : 0 < q.re) : -(q^2) ∈ slit := by
  by_cases hi : q.im = 0
  · left
    simp only [pow_two, Complex.neg_re, Complex.mul_re, hi, mul_zero, sub_zero]
    nlinarith
  · right
    simp only [pow_two, Complex.neg_im, Complex.mul_im]
    intro he
    apply hi
    nlinarith

theorem map_mem_slit {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    map R z ∈ slit := neg_square_mem_slit (cayley_re_pos hR hz)

private theorem sqrt_sq (w : ℂ) : (Complex.sqrt w)^2 = w := by
  rw [Complex.sqrt, ← Complex.cpow_mul_nat]
  norm_num

private theorem sqrt_re_nonneg (w : ℂ) : 0 ≤ (Complex.sqrt w).re := by
  rw [Complex.sqrt_eq_real_add_ite]
  split_ifs <;> simpa using Real.sqrt_nonneg ((‖w‖ + w.re) / 2)

private theorem sqrt_neg_re_pos {w : ℂ} (hw : w ∈ slit) :
    0 < (Complex.sqrt (-w)).re := by
  have hnn := sqrt_re_nonneg (-w)
  by_contra hn
  have hre : (Complex.sqrt (-w)).re = 0 := le_antisymm (le_of_not_gt hn) hnn
  have hs := sqrt_sq (-w)
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, hre, zero_mul, mul_zero, add_zero, zero_sub] at hr hi
  rcases hw with hw | hw
  · nlinarith [sq_nonneg (Complex.sqrt (-w)).im]
  · exact hw (neg_eq_zero.mp hi.symm)

private theorem sqrt_square_of_re_pos {q : ℂ} (hq : 0 < q.re) :
    Complex.sqrt (q^2) = q := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sqrt_sq (q^2)) with h | h
  · exact h
  · have hn := sqrt_re_nonneg (q^2)
    rw [h, Complex.neg_re] at hn
    linarith

private theorem one_add_ne_zero {q : ℂ} (hq : 0 < q.re) : 1+q ≠ 0 := by
  intro he
  have h := congrArg Complex.re he
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h
  linarith

private theorem cayley_inverse_algebra {R : ℝ} (hR : R ≠ 0) {q : ℂ}
    (hq : 1+q ≠ 0) : cayley R ((R:ℂ)*(1-q)/(1+q)) = q := by
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have he : (R:ℂ) + (R:ℂ)*(1-q)/(1+q) = (2*(R:ℂ))/(1+q) := by
    field_simp
    ring
  rw [cayley, he]
  field_simp
  ring

private theorem inverse_cayley_algebra {R : ℝ} (hR : R ≠ 0) {z : ℂ}
    (hz : (R:ℂ)+z ≠ 0) :
    (R:ℂ)*(1-cayley R z)/(1+cayley R z) = z := by
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have he : 1+cayley R z = (2*(R:ℂ))/((R:ℂ)+z) := by
    unfold cayley
    field_simp
    ring
  rw [he, cayley]
  field_simp
  ring

theorem inverse_mem_disk {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit) :
    inverse R w ∈ disk R := by
  let q := Complex.sqrt (-w)
  have hq : 0 < q.re := sqrt_neg_re_pos hw
  have hnorm : ‖1-q‖ < ‖1+q‖ := by
    apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hden : 0 < ‖1+q‖ := norm_pos_iff.mpr (one_add_ne_zero hq)
  change ‖(R:ℂ)*(1-q)/(1+q)‖ < R
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact (div_lt_iff₀ hden).mpr (mul_lt_mul_of_pos_left hnorm hR)

theorem inverse_map {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    inverse R (map R z) = z := by
  unfold inverse map
  rw [neg_neg, sqrt_square_of_re_pos (cayley_re_pos hR hz)]
  exact inverse_cayley_algebra hR.ne' (denominator_ne_zero hR hz)

theorem map_inverse {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit) :
    map R (inverse R w) = w := by
  unfold map inverse
  rw [cayley_inverse_algebra hR.ne' (one_add_ne_zero (sqrt_neg_re_pos hw)), sqrt_sq,
    neg_neg]

theorem map_injOn {R : ℝ} (hR : 0 < R) : InjOn (map R) (disk R) := by
  intro z hz w hw he
  rw [← inverse_map hR hz, ← inverse_map hR hw, he]

theorem map_bijOn {R : ℝ} (hR : 0 < R) : BijOn (map R) (disk R) slit := by
  refine ⟨fun z hz => map_mem_slit hR hz, map_injOn hR, ?_⟩
  intro w hw
  exact ⟨inverse R w, inverse_mem_disk hR hw, map_inverse hR hw⟩

theorem cayley_hasDerivAt {R : ℝ} {z : ℂ} (hz : (R:ℂ)+z ≠ 0) :
    HasDerivAt (cayley R) (-2*(R:ℂ)/((R:ℂ)+z)^2) z := by
  have h := ((hasDerivAt_const z (R:ℂ)).sub (hasDerivAt_id z)).div
    ((hasDerivAt_const z (R:ℂ)).add (hasDerivAt_id z)) hz
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.sub_apply, id_eq]
  field_simp
  ring

theorem map_hasDerivAt {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    HasDerivAt (map R) (4*(R:ℂ)*((R:ℂ)-z)/((R:ℂ)+z)^3) z := by
  have h := ((cayley_hasDerivAt (denominator_ne_zero hR hz)).pow 2).neg
  apply h.congr_deriv
  have hden := denominator_ne_zero hR hz
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  unfold cayley
  field_simp [hden]
  ring

theorem map_derivative_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    4*(R:ℂ)*((R:ℂ)-z)/((R:ℂ)+z)^3 ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hR.ne'))
      (numerator_ne_zero hR hz))
    (pow_ne_zero _ (denominator_ne_zero hR hz))

theorem map_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (map R) (disk R) :=
  fun _ hz => (map_hasDerivAt hR hz).differentiableAt.differentiableWithinAt

theorem inverse_differentiableOn (R : ℝ) : DifferentiableOn ℂ (inverse R) slit := by
  intro w hw
  have hsl : -w ∈ Complex.slitPlane := by
    simpa only [slit, Complex.slitPlane, mem_setOf_eq, Complex.neg_re, Complex.neg_im,
      neg_pos, neg_ne_zero] using hw
  have hs : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (-z)) w :=
    (Complex.differentiableAt_sqrt hsl).comp w differentiableAt_id.neg
  exact (((differentiableAt_const (R:ℂ)).mul ((differentiableAt_const 1).sub hs)).div
    ((differentiableAt_const 1).add hs) (one_add_ne_zero (sqrt_neg_re_pos hw))).differentiableWithinAt

/-- The explicit analytic map and inverse packaged as a homeomorphism. -/
def homeomorph {R : ℝ} (hR : 0 < R) : disk R ≃ₜ slit where
  toFun z := ⟨map R z, map_mem_slit hR z.property⟩
  invFun w := ⟨inverse R w, inverse_mem_disk hR w.property⟩
  left_inv z := Subtype.ext (inverse_map hR z.property)
  right_inv w := Subtype.ext (map_inverse hR w.property)
  continuous_toFun := (map_differentiableOn hR).continuousOn.restrict.subtype_mk _
  continuous_invFun := (inverse_differentiableOn R).continuousOn.restrict.subtype_mk _

theorem map_conj (R : ℝ) (z : ℂ) : map R (starRingEnd ℂ z) = starRingEnd ℂ (map R z) := by
  simp [map, cayley]

theorem map_im_pos {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R)
    (him : 0 < z.im) : 0 < (map R z).im := by
  have hre := cayley_re_pos hR hz
  have hneg : (cayley R z).im < 0 := by
    rw [cayley_im]
    apply div_neg_of_neg_of_pos
    · nlinarith
    · exact Complex.normSq_pos.mpr (denominator_ne_zero hR hz)
  simp only [map, pow_two, Complex.neg_im, Complex.mul_im]
  nlinarith

theorem map_ofReal (R x : ℝ) : map R (x:ℂ) = (realMap R x : ℂ) := by
  simp [map, cayley, realMap]

theorem ofReal_mem_disk {R x : ℝ} (hx : x ∈ Ioo (-R) R) : (x:ℂ) ∈ disk R := by
  simpa only [disk, mem_setOf_eq, mem_Ioo, Complex.norm_real, Real.norm_eq_abs, abs_lt] using hx

theorem realMap_neg {R x : ℝ} (hx : x ∈ Ioo (-R) R) : realMap R x < 0 := by
  have hnum : 0 < R-x := sub_pos.mpr hx.2
  have hden : 0 < R+x := by linarith [hx.1]
  have hq : 0 < (R-x)/(R+x) := div_pos hnum hden
  unfold realMap
  nlinarith

theorem realMap_strictMonoOn {R : ℝ} (hR : 0 < R) :
    StrictMonoOn (realMap R) (Ioo (-R) R) := by
  intro x hx y hy hxy
  have hxden : 0 < R+x := by linarith [hx.1]
  have hyden : 0 < R+y := by linarith [hy.1]
  have hqx : 0 < (R-x)/(R+x) := div_pos (sub_pos.mpr hx.2) hxden
  have hqy : 0 < (R-y)/(R+y) := div_pos (sub_pos.mpr hy.2) hyden
  have hq : (R-y)/(R+y) < (R-x)/(R+x) := by
    apply (div_lt_div_iff₀ hyden hxden).mpr
    nlinarith
  have hsq := (sq_lt_sq₀ hqy.le hqx.le).mpr hq
  change -((R-x)/(R+x))^2 < -((R-y)/(R+y))^2
  linarith

theorem map_continuousAt {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    ContinuousAt (map R) z := (map_hasDerivAt hR hz).continuousAt

theorem map_derivative_continuousAt {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    ContinuousAt (fun z : ℂ => 4*(R:ℂ)*((R:ℂ)-z)/((R:ℂ)+z)^3) z := by
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact pow_ne_zero _ (denominator_ne_zero hR hz)

theorem derivative_conj (R : ℝ) (z : ℂ) :
    4*(R:ℂ)*((R:ℂ)-starRingEnd ℂ z)/((R:ℂ)+starRingEnd ℂ z)^3 =
      starRingEnd ℂ (4*(R:ℂ)*((R:ℂ)-z)/((R:ℂ)+z)^3) := by
  have h4 : starRingEnd ℂ (4:ℂ) = (4:ℂ) := map_ofNat (starRingEnd ℂ) 4
  simp only [map_div₀, map_mul, map_sub, map_add, map_pow, Complex.conj_ofReal, h4]

theorem map_im (R : ℝ) (z : ℂ) :
    (map R z).im =
      (4*R*(cayley R z).re / Complex.normSq ((R:ℂ)+z)) * z.im := by
  simp only [map, pow_two, Complex.neg_im, Complex.mul_im]
  rw [cayley_im]
  ring

private theorem im_factor_pos {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    0 < 4*R*(cayley R z).re / Complex.normSq ((R:ℂ)+z) :=
  div_pos (mul_pos (mul_pos (by norm_num) hR) (cayley_re_pos hR hz))
    (Complex.normSq_pos.mpr (denominator_ne_zero hR hz))

theorem map_im_pos_iff {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    0 < (map R z).im ↔ 0 < z.im := by
  rw [map_im]
  exact mul_pos_iff_of_pos_left (im_factor_pos hR hz)

theorem map_im_neg_iff {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    (map R z).im < 0 ↔ z.im < 0 := by
  rw [map_im]
  have hp := im_factor_pos hR hz
  rw [mul_neg_iff]
  simp only [hp, not_lt.mpr hp.le, true_and, false_and, or_false]

theorem map_im_eq_zero_iff {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R) :
    (map R z).im = 0 ↔ z.im = 0 := by
  rw [map_im, mul_eq_zero]
  simp only [(im_factor_pos hR hz).ne', false_or]

theorem map_im_nonneg {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ disk R)
    (him : 0 ≤ z.im) : 0 ≤ (map R z).im := by
  rw [map_im]
  exact mul_nonneg (im_factor_pos hR hz).le him

@[simp] theorem conj_mem_disk_iff (R : ℝ) (z : ℂ) :
    starRingEnd ℂ z ∈ disk R ↔ z ∈ disk R := by simp [disk]

@[simp] theorem conj_mem_slit_iff (w : ℂ) :
    starRingEnd ℂ w ∈ slit ↔ w ∈ slit := by simp [slit]

theorem inverse_conj {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit) :
    inverse R (starRingEnd ℂ w) = starRingEnd ℂ (inverse R w) := by
  apply map_injOn hR (inverse_mem_disk hR ((conj_mem_slit_iff w).mpr hw))
    ((conj_mem_disk_iff R _).mpr (inverse_mem_disk hR hw))
  rw [map_inverse hR ((conj_mem_slit_iff w).mpr hw), map_conj, map_inverse hR hw]

theorem inverse_im_pos {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit)
    (him : 0 < w.im) : 0 < (inverse R w).im := by
  apply (map_im_pos_iff hR (inverse_mem_disk hR hw)).mp
  simpa only [map_inverse hR hw] using him

theorem inverse_im_neg {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit)
    (him : w.im < 0) : (inverse R w).im < 0 := by
  apply (map_im_neg_iff hR (inverse_mem_disk hR hw)).mp
  simpa only [map_inverse hR hw] using him

theorem inverse_real {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit)
    (him : w.im = 0) : (inverse R w).im = 0 := by
  apply (map_im_eq_zero_iff hR (inverse_mem_disk hR hw)).mp
  simpa only [map_inverse hR hw] using him

theorem inverse_eq_ofReal {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit)
    (him : w.im = 0) : inverse R w = ((inverse R w).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [inverse_real hR hw him]

theorem inverse_re_mem_Ioo {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit)
    (him : w.im = 0) : (inverse R w).re ∈ Ioo (-R) R := by
  have hz := inverse_mem_disk hR hw
  rw [inverse_eq_ofReal hR hw him] at hz
  simpa only [disk, mem_setOf_eq, mem_Ioo, Complex.norm_real, Real.norm_eq_abs, abs_lt] using hz

theorem inverse_realMap {R x : ℝ} (hR : 0 < R) (hx : x ∈ Ioo (-R) R) :
    inverse R (realMap R x : ℂ) = (x:ℂ) := by
  rw [← map_ofReal]
  exact inverse_map hR (ofReal_mem_disk hx)

private theorem realMap_inverse_re {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit)
    (him : w.im = 0) : realMap R (inverse R w).re = w.re := by
  have h := congrArg Complex.re (map_inverse hR hw)
  rw [inverse_eq_ofReal hR hw him, map_ofReal, Complex.ofReal_re] at h
  exact h

theorem inverse_re_lt_iff {R x : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit)
    (him : w.im = 0) (hx : x ∈ Ioo (-R) R) :
    (inverse R w).re < x ↔ w.re < realMap R x := by
  have h := (realMap_strictMonoOn hR).lt_iff_lt (inverse_re_mem_Ioo hR hw him) hx
  rw [realMap_inverse_re hR hw him] at h
  exact h.symm

theorem lt_inverse_re_iff {R x : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit)
    (him : w.im = 0) (hx : x ∈ Ioo (-R) R) :
    x < (inverse R w).re ↔ realMap R x < w.re := by
  have h := (realMap_strictMonoOn hR).lt_iff_lt hx (inverse_re_mem_Ioo hR hw him)
  rw [realMap_inverse_re hR hw him] at h
  exact h.symm

/-- The actual disk/slit analytic chart, with its rational derivative. -/
def conformalChart {R : ℝ} (hR : 0 < R) : CrestConformalModulus.ConformalChart where
  homeomorph := {
    toFun := map R
    invFun := inverse R
    source := disk R
    target := slit
    map_source' := fun _ hz => map_mem_slit hR hz
    map_target' := fun _ hw => inverse_mem_disk hR hw
    left_inv' := fun _ hz => inverse_map hR hz
    right_inv' := fun _ hw => map_inverse hR hw
    open_source := disk_open R
    open_target := slit_open
    continuousOn_toFun := (map_differentiableOn hR).continuousOn
    continuousOn_invFun := (inverse_differentiableOn R).continuousOn }
  derivative := fun z => 4*(R:ℂ)*((R:ℂ)-z)/((R:ℂ)+z)^3
  hasDeriv := fun _ hz => map_hasDerivAt hR hz
  derivative_continuous := fun _ hz => (map_derivative_continuousAt hR hz).continuousWithinAt
  derivative_ne_zero := fun _ hz => map_derivative_ne_zero hR hz

@[simp] theorem conformalChart_source {R : ℝ} (hR : 0 < R) :
    (conformalChart hR).homeomorph.source = disk R := rfl

@[simp] theorem conformalChart_target {R : ℝ} (hR : 0 < R) :
    (conformalChart hR).homeomorph.target = slit := rfl

@[simp] theorem conformalChart_apply {R : ℝ} (hR : 0 < R) (z : ℂ) :
    (conformalChart hR).homeomorph z = map R z := rfl

@[simp] theorem conformalChart_symm_apply {R : ℝ} (hR : 0 < R) (w : ℂ) :
    (conformalChart hR).homeomorph.symm w = inverse R w := rfl

@[simp] theorem conformalChart_derivative {R : ℝ} (hR : 0 < R) (z : ℂ) :
    (conformalChart hR).derivative z = 4*(R:ℂ)*((R:ℂ)-z)/((R:ℂ)+z)^3 := rfl

def inverseDerivative (R : ℝ) (w : ℂ) : ℂ :=
  (4*(R:ℂ)*((R:ℂ)-inverse R w)/((R:ℂ)+inverse R w)^3)⁻¹

theorem inverse_hasDerivAt {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit) :
    HasDerivAt (inverse R) (inverseDerivative R w) w :=
  (conformalChart hR).homeomorph.hasDerivAt_symm hw
    (map_derivative_ne_zero hR (inverse_mem_disk hR hw))
    (map_hasDerivAt hR (inverse_mem_disk hR hw))

theorem inverseDerivative_ne_zero {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ slit) :
    inverseDerivative R w ≠ 0 :=
  inv_ne_zero (map_derivative_ne_zero hR (inverse_mem_disk hR hw))

theorem inverseDerivative_continuousAt {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw : w ∈ slit) : ContinuousAt (inverseDerivative R) w := by
  have hc : ContinuousAt (inverse R) w :=
    (inverse_differentiableOn R).continuousOn.continuousAt (slit_open.mem_nhds hw)
  exact ((map_derivative_continuousAt hR (inverse_mem_disk hR hw)).comp hc).inv₀
    (map_derivative_ne_zero hR (inverse_mem_disk hR hw))

end
end SlitDiskCayley
