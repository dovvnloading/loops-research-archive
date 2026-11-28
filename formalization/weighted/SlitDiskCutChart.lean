import SlitDiskCayley
import SlitCubicCalibration

/-!
# An explicit upper-half-plane coordinate for a disk with an interior cut

The target is the original disk slit from its left boundary to the real
critical value. Both directions are explicit compositions of the squared
Cayley map and a square root, with all domains proved.
-/

namespace SlitDiskCutChart

open Set Filter
open scoped Topology
noncomputable section

def domain (R d : ℝ) : Set ℂ :=
  SlitDiskCayley.disk R ∩ {z | d < z.re ∨ z.im ≠ 0}

def shift (R d : ℝ) (z : ℂ) : ℂ :=
  SlitDiskCayley.map R (-z)-(SlitDiskCayley.realMap R (-d) : ℂ)

def forward (R d : ℝ) (z : ℂ) : ℂ := Complex.I*Complex.sqrt (-shift R d z)

def inverseArgument (R d : ℝ) (w : ℂ) : ℂ :=
  w^2+(SlitDiskCayley.realMap R (-d) : ℂ)

def inverse (R d : ℝ) (w : ℂ) : ℂ :=
  -SlitDiskCayley.inverse R (inverseArgument R d w)

def inverseDerivative (R d : ℝ) (w : ℂ) : ℂ :=
  -(SlitDiskCayley.inverseDerivative R (inverseArgument R d w)*(2*w))

theorem domain_open (R d : ℝ) : IsOpen (domain R d) :=
  (SlitDiskCayley.disk_open R).inter
    ((isOpen_lt continuous_const Complex.continuous_re).union
      (isOpen_ne_fun Complex.continuous_im continuous_const))

private theorem neg_mem_disk {R : ℝ} {z : ℂ} (hz : z ∈ SlitDiskCayley.disk R) :
    -z ∈ SlitDiskCayley.disk R := by simpa [SlitDiskCayley.disk] using hz

private theorem neg_mem_Ioo {R x : ℝ} (hx : x ∈ Ioo (-R) R) : -x ∈ Ioo (-R) R := by
  constructor <;> linarith [hx.1,hx.2]

private theorem re_mem_Ioo {R : ℝ} {z : ℂ} (hz : z ∈ SlitDiskCayley.disk R) :
    z.re ∈ Ioo (-R) R := abs_lt.mp ((Complex.abs_re_le_norm z).trans_lt hz)

theorem shift_mem_slit_iff {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {z : ℂ} (hz : z ∈ SlitDiskCayley.disk R) :
    shift R d z ∈ SlitDiskCayley.slit ↔ d < z.re ∨ z.im ≠ 0 := by
  by_cases him : z.im = 0
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    have hs : shift R d z =
        ((SlitDiskCayley.realMap R (-z.re)-SlitDiskCayley.realMap R (-d) : ℝ) : ℂ) := by
      rw [shift,he]
      simp only [← Complex.ofReal_neg,SlitDiskCayley.map_ofReal,Complex.ofReal_re,
        Complex.ofReal_sub]
    rw [hs]
    simp only [SlitDiskCayley.slit,mem_setOf_eq,Complex.ofReal_re,Complex.ofReal_im,
      ne_eq,not_true_eq_false,or_false,him]
    rw [sub_neg]
    have hm := (SlitDiskCayley.realMap_strictMonoOn hR).lt_iff_lt
      (neg_mem_Ioo (re_mem_Ioo hz)) (neg_mem_Ioo hd)
    exact hm.trans neg_lt_neg_iff
  · have hne : (shift R d z).im ≠ 0 := by
      simp only [shift,Complex.sub_im,Complex.ofReal_im,sub_zero,ne_eq,
        SlitDiskCayley.map_im_eq_zero_iff hR (neg_mem_disk hz),Complex.neg_im,neg_eq_zero]
      exact him
    exact iff_of_true (Or.inr hne) (Or.inr him)

theorem forward_mem_upper {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {z : ℂ} (hz : z ∈ domain R d) : forward R d z ∈ SlitCubicCalibration.upper := by
  have hs := (shift_mem_slit_iff hR hd hz.1).mpr hz.2
  simpa only [forward,SlitCubicCalibration.upper,mem_setOf_eq,Complex.mul_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] using
      SlitDiskCayley.sqrt_neg_re_pos hs

private theorem square_add_mem_slit {w : ℂ} (hw : w ∈ SlitCubicCalibration.upper)
    {u : ℝ} (hu : u ≤ 0) : w^2+(u : ℂ) ∈ SlitDiskCayley.slit := by
  have hi : 0 < w.im := hw
  by_cases hr : w.re = 0
  · left
    simp only [Complex.add_re,Complex.ofReal_re,pow_two,Complex.mul_re,hr,
      zero_mul,zero_sub]
    nlinarith
  · right
    simp only [Complex.add_im,Complex.ofReal_im,add_zero,pow_two,Complex.mul_im]
    intro he
    apply hr
    nlinarith

theorem inverseArgument_mem_slit {R d : ℝ} (hd : d ∈ Ioo (-R) R)
    {w : ℂ} (hw : w ∈ SlitCubicCalibration.upper) :
    inverseArgument R d w ∈ SlitDiskCayley.slit :=
  square_add_mem_slit hw (SlitDiskCayley.realMap_neg (neg_mem_Ioo hd)).le

theorem shift_inverse {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {w : ℂ} (hw : w ∈ SlitCubicCalibration.upper) : shift R d (inverse R d w) = w^2 := by
  unfold shift inverse
  rw [neg_neg,SlitDiskCayley.map_inverse hR (inverseArgument_mem_slit hd hw)]
  simp only [inverseArgument,add_sub_cancel_right]

theorem inverse_mem_domain {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {w : ℂ} (hw : w ∈ SlitCubicCalibration.upper) : inverse R d w ∈ domain R d := by
  have hz : inverse R d w ∈ SlitDiskCayley.disk R :=
    neg_mem_disk (SlitDiskCayley.inverse_mem_disk hR (inverseArgument_mem_slit hd hw))
  refine ⟨hz,(shift_mem_slit_iff hR hd hz).mp ?_⟩
  rw [shift_inverse hR hd hw]
  simpa only [Complex.ofReal_zero,add_zero] using square_add_mem_slit hw (le_refl (0 : ℝ))

theorem forward_sq (R d : ℝ) (z : ℂ) : (forward R d z)^2 = shift R d z := by
  rw [forward,mul_pow,Complex.I_sq,SlitDiskCayley.sqrt_sq]
  ring

theorem inverse_forward {R d : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ domain R d) :
    inverse R d (forward R d z) = z := by
  unfold inverse inverseArgument
  rw [forward_sq]
  simp only [shift,sub_add_cancel]
  rw [SlitDiskCayley.inverse_map hR (neg_mem_disk hz.1),neg_neg]

theorem forward_inverse {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {w : ℂ} (hw : w ∈ SlitCubicCalibration.upper) : forward R d (inverse R d w) = w := by
  rw [forward,shift_inverse hR hd hw]
  have he : -(w^2) = (-Complex.I*w)^2 := by rw [mul_pow,neg_sq,Complex.I_sq]; ring
  rw [he,SlitDiskCayley.sqrt_square_of_re_pos (q := -Complex.I*w) (by
    simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
      Complex.I_im,neg_zero,zero_mul,neg_mul,one_mul,zero_sub,neg_neg] using
        (show 0 < w.im from hw))]
  rw [← mul_assoc]
  simp

theorem forward_differentiableOn {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R) :
    DifferentiableOn ℂ (forward R d) (domain R d) := by
  intro z hz
  have hsl : -shift R d z ∈ Complex.slitPlane := by
    have hs := (shift_mem_slit_iff hR hd hz.1).mpr hz.2
    simpa only [SlitDiskCayley.slit,Complex.slitPlane,mem_setOf_eq,Complex.neg_re,
      Complex.neg_im,neg_pos,neg_ne_zero] using hs
  have hs : DifferentiableAt ℂ (fun z => -shift R d z) z :=
    ((((SlitDiskCayley.map_hasDerivAt hR (neg_mem_disk hz.1)).differentiableAt.comp z
      differentiableAt_id.neg).sub_const (SlitDiskCayley.realMap R (-d) : ℂ)).neg)
  exact ((differentiableAt_const Complex.I).mul
    ((Complex.differentiableAt_sqrt hsl).comp z hs)).differentiableWithinAt

theorem inverse_hasDerivAt {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {w : ℂ} (hw : w ∈ SlitCubicCalibration.upper) :
    HasDerivAt (inverse R d) (inverseDerivative R d w) w := by
  have hi := (SlitDiskCayley.inverse_hasDerivAt hR (inverseArgument_mem_slit hd hw)).comp w
    (((hasDerivAt_id w).pow 2).add_const (SlitDiskCayley.realMap R (-d) : ℂ))
  simpa only [inverse,inverseDerivative,inverseArgument,Function.comp_def,pow_one,
    Nat.cast_ofNat,mul_one,Pi.neg_apply,Nat.reduceSub,id_eq] using! hi.neg

theorem inverseDerivative_ne_zero {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {w : ℂ} (hw : w ∈ SlitCubicCalibration.upper) : inverseDerivative R d w ≠ 0 := by
  have hw0 : w ≠ 0 := by intro he; have hi : 0 < w.im := hw; simpa [he] using hi
  exact neg_ne_zero.mpr (mul_ne_zero
    (SlitDiskCayley.inverseDerivative_ne_zero hR (inverseArgument_mem_slit hd hw))
    (mul_ne_zero (by norm_num) hw0))

theorem inverseDerivative_continuousAt {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {w : ℂ} (hw : w ∈ SlitCubicCalibration.upper) : ContinuousAt (inverseDerivative R d) w := by
  have ha : Continuous (inverseArgument R d) := by unfold inverseArgument; fun_prop
  exact (((SlitDiskCayley.inverseDerivative_continuousAt hR (inverseArgument_mem_slit hd hw)).comp
    ha.continuousAt).mul (continuous_const.mul continuous_id).continuousAt).neg

/-- The actual inverse coordinate maps the whole upper half-plane onto
the original cut disk. -/
def inverseConformal {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R) :
    CrestConformalModulus.ConformalChart where
  homeomorph := {
    toFun := inverse R d
    invFun := forward R d
    source := SlitCubicCalibration.upper
    target := domain R d
    map_source' := fun _ hw => inverse_mem_domain hR hd hw
    map_target' := fun _ hz => forward_mem_upper hR hd hz
    left_inv' := fun _ hw => forward_inverse hR hd hw
    right_inv' := fun _ hz => inverse_forward hR hz
    open_source := SlitCubicCalibration.upper_open
    open_target := domain_open R d
    continuousOn_toFun := fun _ hw => (inverse_hasDerivAt hR hd hw).continuousAt.continuousWithinAt
    continuousOn_invFun := (forward_differentiableOn hR hd).continuousOn }
  derivative := inverseDerivative R d
  hasDeriv := fun _ hw => inverse_hasDerivAt hR hd hw
  derivative_continuous := fun _ hw => (inverseDerivative_continuousAt hR hd hw).continuousWithinAt
  derivative_ne_zero := fun _ hw => inverseDerivative_ne_zero hR hd hw

@[simp] theorem inverseConformal_source {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) :
    (inverseConformal hR hd).homeomorph.source = SlitCubicCalibration.upper := rfl

@[simp] theorem inverseConformal_target {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) :
    (inverseConformal hR hd).homeomorph.target = domain R d := rfl

@[simp] theorem inverseConformal_apply {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) (w : ℂ) :
    (inverseConformal hR hd).homeomorph w = inverse R d w := rfl

@[simp] theorem inverseConformal_symm_apply {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) (z : ℂ) :
    (inverseConformal hR hd).homeomorph.symm z = forward R d z := rfl

def forwardDerivative (R d : ℝ) (z : ℂ) : ℂ :=
  (inverseDerivative R d (forward R d z))⁻¹

theorem forward_hasDerivAt {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {z : ℂ} (hz : z ∈ domain R d) :
    HasDerivAt (forward R d) (forwardDerivative R d z) z :=
  (inverseConformal hR hd).homeomorph.hasDerivAt_symm hz
    (inverseDerivative_ne_zero hR hd (forward_mem_upper hR hd hz))
    (inverse_hasDerivAt hR hd (forward_mem_upper hR hd hz))

theorem forwardDerivative_ne_zero {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R)
    {z : ℂ} (hz : z ∈ domain R d) : forwardDerivative R d z ≠ 0 :=
  inv_ne_zero (inverseDerivative_ne_zero hR hd (forward_mem_upper hR hd hz))

theorem forwardDerivative_continuousAt {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) {z : ℂ} (hz : z ∈ domain R d) :
    ContinuousAt (forwardDerivative R d) z :=
  ((inverseDerivative_continuousAt hR hd (forward_mem_upper hR hd hz)).comp
    (forward_hasDerivAt hR hd hz).continuousAt).inv₀
      (inverseDerivative_ne_zero hR hd (forward_mem_upper hR hd hz))

/-- The cut disk is conformally equivalent to the whole upper half-plane. -/
def conformalChart {R d : ℝ} (hR : 0 < R) (hd : d ∈ Ioo (-R) R) :
    CrestConformalModulus.ConformalChart where
  homeomorph := (inverseConformal hR hd).homeomorph.symm
  derivative := forwardDerivative R d
  hasDeriv := fun _ hz => forward_hasDerivAt hR hd hz
  derivative_continuous := fun _ hz =>
    (forwardDerivative_continuousAt hR hd hz).continuousWithinAt
  derivative_ne_zero := fun _ hz => forwardDerivative_ne_zero hR hd hz

@[simp] theorem conformalChart_source {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) : (conformalChart hR hd).homeomorph.source = domain R d := rfl

@[simp] theorem conformalChart_target {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) :
    (conformalChart hR hd).homeomorph.target = SlitCubicCalibration.upper := rfl

@[simp] theorem conformalChart_apply {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) (z : ℂ) :
    (conformalChart hR hd).homeomorph z = forward R d z := rfl

@[simp] theorem conformalChart_symm_apply {R d : ℝ} (hR : 0 < R)
    (hd : d ∈ Ioo (-R) R) (w : ℂ) :
    (conformalChart hR hd).homeomorph.symm w = inverse R d w := rfl

end
end SlitDiskCutChart
