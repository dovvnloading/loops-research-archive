import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Omega

/-!
# Physical cylinder estimates from quadratic secants

An even full-branch interval map need not expand Euclidean distance near its
critical point.  Two-sided bounds for its *quadratic* secants instead give an
expansion in the explicit cosine coordinate.  Both endpoints are included,
and the resulting cylinder estimate applies at every depth.

The hypotheses below are ordinary inequalities for the actual function.
No conjugacy to a model map, invariant metric, or cylinder-shrinking premise
is assumed.  The application to literal polynomial returns is separate.
-/

namespace AngularCylinderExpansion

open Set Function
open scoped Topology

noncomputable section

/-- Bounds for a normalized even interval map, with its actual endpoint
values and its quadratic secants on the positive branch. -/
structure EvenQuadraticBounds (f : ℝ → ℝ) (a b : ℝ) : Prop where
  a_pos : 0 < a
  b_pos : 0 < b
  continuous : Continuous f
  differentiable : Differentiable ℝ f
  even : ∀ x : ℝ, f (-x) = f x
  zero : f 0 = 1
  one : f 1 = -1
  secant : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x ≤ y →
    a * (y^2-x^2) ≤ f x-f y ∧ f x-f y ≤ b * (y^2-x^2)

def angleDistance (x y : ℝ) : ℝ := |Real.arccos x-Real.arccos y|

def SameBranch (x y : ℝ) : Prop :=
  (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0)

/-- The full sign itinerary is shared up to, but not including, time `n`.
Critical and endpoint encounters are allowed. -/
def SameItinerary (f : ℝ → ℝ) (n : ℕ) (x y : ℝ) : Prop :=
  ∀ j : ℕ, j < n → SameBranch ((f^[j]) x) ((f^[j]) y)

theorem angleDistance_nonneg (x y : ℝ) : 0 ≤ angleDistance x y := abs_nonneg _

theorem angleDistance_comm (x y : ℝ) : angleDistance x y = angleDistance y x :=
  abs_sub_comm _ _

theorem angleDistance_neg_neg (x y : ℝ) :
    angleDistance (-x) (-y) = angleDistance x y := by
  unfold angleDistance
  rw [Real.arccos_neg, Real.arccos_neg]
  have he : Real.pi-Real.arccos x-(Real.pi-Real.arccos y) =
      -(Real.arccos x-Real.arccos y) := by ring
  rw [he, abs_neg]

theorem angleDistance_le_pi (x y : ℝ) : angleDistance x y ≤ Real.pi := by
  rw [angleDistance, abs_le]
  constructor <;> linarith [Real.arccos_nonneg x, Real.arccos_le_pi x,
    Real.arccos_nonneg y, Real.arccos_le_pi y]

theorem abs_sub_le_angleDistance {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |x-y| ≤ angleDistance x y := by
  have h := Real.abs_cos_sub_cos_le (Real.arccos x) (Real.arccos y)
  rw [Real.cos_arccos hx.1 hx.2, Real.cos_arccos hy.1 hy.2] at h
  exact h

namespace EvenQuadraticBounds

variable {f : ℝ → ℝ} {a b : ℝ} (h : EvenQuadraticBounds f a b)

theorem ratio_nonneg : 0 ≤ b/(2*a) :=
  div_nonneg h.b_pos.le (mul_nonneg (by norm_num) h.a_pos.le)

theorem endpoint_bounds {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (a*x^2 ≤ 1-f x ∧ 1-f x ≤ b*x^2) ∧
      (a*(1-x^2) ≤ 1+f x ∧ 1+f x ≤ b*(1-x^2)) := by
  have hleft := h.secant 0 (by norm_num) x hx hx.1
  have hright := h.secant x hx 1 (by norm_num) hx.2
  rw [h.zero] at hleft
  rw [h.one] at hright
  norm_num at hleft hright
  exact ⟨by simpa using hleft, by simpa only [sub_neg_eq_add, add_comm] using hright⟩

theorem positive_branch_mapsTo {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f x ∈ Icc (-1 : ℝ) 1 := by
  have he := h.endpoint_bounds hx
  have hx2 : 0 ≤ 1-x^2 := by
    have hm := mul_nonneg (by linarith [hx.1] : 0 ≤ 1+x) (sub_nonneg.mpr hx.2)
    nlinarith only [hm]
  have hleft := mul_nonneg h.a_pos.le (sq_nonneg x)
  have hright := mul_nonneg h.a_pos.le hx2
  constructor <;> linarith [he.1.1, he.2.1]

theorem mapsTo : MapsTo f (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
  intro x hx
  by_cases hx0 : 0 ≤ x
  · exact h.positive_branch_mapsTo ⟨hx0,hx.2⟩
  · have hn : -x ∈ Icc (0 : ℝ) 1 := ⟨by linarith,by linarith [hx.1]⟩
    simpa only [h.even] using h.positive_branch_mapsTo hn

theorem positive_branch_interior {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    f x ∈ Ioo (-1 : ℝ) 1 := by
  have he := h.endpoint_bounds ⟨hx.1.le,hx.2.le⟩
  have hx2 : 0 < 1-x^2 := by
    have hm := mul_pos (by linarith [hx.1] : 0 < 1+x) (sub_pos.mpr hx.2)
    nlinarith only [hm]
  have hleft := mul_pos h.a_pos (sq_pos_of_pos hx.1)
  have hright := mul_pos h.a_pos hx2
  constructor <;> linarith [he.1.1,he.2.1]

/-- The lower derivative estimate is a consequence of the actual secant
inequality. It is not an additional expansion hypothesis. -/
theorem neg_deriv_lower {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    2*a*x ≤ -deriv f x := by
  have hm : AntitoneOn (fun z : ℝ => f z+a*z^2) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    have hs := (h.secant u hu v hv huv).1
    nlinarith only [hs]
  have hd := (h.differentiable x).hasDerivAt.add
    (((hasDerivAt_id x).pow 2).const_mul a)
  have hn := hm.derivWithin_nonpos (x := x)
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), hd.deriv] at hn
  norm_num at hn
  linarith only [hn]

private theorem square_root_bound {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt (1-(f x)^2) ≤ b*x*Real.sqrt (1-x^2) := by
  have he := h.endpoint_bounds ⟨hx.1.le,hx.2.le⟩
  have hf := h.positive_branch_interior hx
  have hx2 : 0 ≤ 1-x^2 := by
    have hm := mul_nonneg (by linarith [hx.1] : 0 ≤ 1+x) (sub_nonneg.mpr hx.2.le)
    nlinarith only [hm]
  have hf2 : 0 ≤ 1-(f x)^2 := by
    have hm := mul_nonneg (by linarith [hf.1] : 0 ≤ 1+f x) (sub_nonneg.mpr hf.2.le)
    nlinarith only [hm]
  have hp := mul_le_mul he.1.2 he.2.2
    (by linarith [hf.1] : 0 ≤ 1+f x) (mul_nonneg h.b_pos.le (sq_nonneg x))
  have hs : (Real.sqrt (1-(f x)^2))^2 ≤ (b*x*Real.sqrt (1-x^2))^2 := by
    rw [Real.sq_sqrt hf2, mul_pow, mul_pow, Real.sq_sqrt hx2]
    nlinarith only [hp]
  have hn : 0 ≤ b*x*Real.sqrt (1-x^2) :=
    mul_nonneg (mul_nonneg h.b_pos.le hx.1.le) (Real.sqrt_nonneg _)
  have hd := Real.sqrt_nonneg (1-(f x)^2)
  exact (sq_le_sq₀ hd hn).mp hs

private def compensation (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  Real.arccos (f x)+(2*a/b)*Real.arccos x

private theorem compensation_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (compensation f a b)
      (-(1/Real.sqrt (1-(f x)^2))*deriv f x +
        (2*a/b)*(-(1/Real.sqrt (1-x^2)))) x := by
  have hf := h.positive_branch_interior hx
  exact ((Real.hasDerivAt_arccos (by linarith [hf.1]) (by linarith [hf.2])).comp x
    (h.differentiable x).hasDerivAt).add
      ((Real.hasDerivAt_arccos (by linarith [hx.1]) (by linarith [hx.2])).const_mul
        (2*a/b))

private theorem compensation_deriv_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ -(1/Real.sqrt (1-(f x)^2))*deriv f x +
      (2*a/b)*(-(1/Real.sqrt (1-x^2))) := by
  have hf := h.positive_branch_interior hx
  have hxprod := mul_pos (by linarith [hx.1] : 0 < 1+x) (sub_pos.mpr hx.2)
  have hfprod := mul_pos (by linarith [hf.1] : 0 < 1+f x) (sub_pos.mpr hf.2)
  have hS : 0 < Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by nlinarith only [hxprod])
  have hD : 0 < Real.sqrt (1-(f x)^2) :=
    Real.sqrt_pos.mpr (by nlinarith only [hfprod])
  have hratio : 0 ≤ 2*a/b :=
    div_nonneg (mul_nonneg (by norm_num) h.a_pos.le) h.b_pos.le
  have hp : (2*a/b)*Real.sqrt (1-(f x)^2) ≤
      (-deriv f x)*Real.sqrt (1-x^2) := by
    calc
      _ ≤ (2*a/b)*(b*x*Real.sqrt (1-x^2)) :=
        mul_le_mul_of_nonneg_left (h.square_root_bound hx) hratio
      _ = (2*a*x)*Real.sqrt (1-x^2) := by field_simp [h.b_pos.ne']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (h.neg_deriv_lower hx) hS.le
  have hd : (2*a/b)/Real.sqrt (1-x^2) ≤
      (-deriv f x)/Real.sqrt (1-(f x)^2) :=
    (div_le_div_iff₀ hS hD).mpr hp
  have he : -(1/Real.sqrt (1-(f x)^2))*deriv f x +
      (2*a/b)*(-(1/Real.sqrt (1-x^2))) =
      (-deriv f x)/Real.sqrt (1-(f x)^2) - (2*a/b)/Real.sqrt (1-x^2) := by ring
  rw [he]
  exact sub_nonneg.mpr hd

private theorem compensation_monotone :
    MonotoneOn (compensation f a b) (Icc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · exact (h.continuous.arccos.add
      (continuous_const.mul Real.continuous_arccos)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (h.compensation_hasDerivAt hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(h.compensation_hasDerivAt hx).deriv]
    exact h.compensation_deriv_nonneg hx

private theorem ordered_positive_branch_bound {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    angleDistance x y ≤ (b/(2*a))*angleDistance (f x) (f y) := by
  have hm := h.compensation_monotone hx hy hxy
  have hs := (h.secant x hx y hy hxy).1
  have hsq : 0 ≤ y^2-x^2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hxy) (by linarith [hx.1,hy.1] : 0 ≤ y+x)
    nlinarith only [hm]
  have ham := mul_nonneg h.a_pos.le hsq
  have hf : f y ≤ f x := by linarith only [hs,ham]
  have hc : Real.arccos y ≤ Real.arccos x := Real.arccos_le_arccos hxy
  have hfc : Real.arccos (f x) ≤ Real.arccos (f y) := Real.arccos_le_arccos hf
  rw [angleDistance,angleDistance,abs_of_nonneg (sub_nonneg.mpr hc),
    abs_of_nonpos (sub_nonpos.mpr hfc)]
  have hmul := mul_le_mul_of_nonneg_left hm h.ratio_nonneg
  have hid : (b/(2*a))*(2*a/b) = 1 := by
    field_simp [h.a_pos.ne',h.b_pos.ne'] <;> ring
  dsimp [compensation] at hmul
  simp only [mul_add, ← mul_assoc, hid, one_mul] at hmul
  linarith only [hmul]

/-- One positive branch expands the concrete cosine-coordinate distance.
The endpoint cases follow from continuity, so no endpoint is deleted. -/
theorem positive_branch_bound {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    angleDistance x y ≤ (b/(2*a))*angleDistance (f x) (f y) := by
  rcases le_total x y with hxy | hyx
  · exact h.ordered_positive_branch_bound hx hy hxy
  · simpa only [angleDistance_comm y x,angleDistance_comm (f y) (f x)] using
      h.ordered_positive_branch_bound hy hx hyx

/-- Every pair on one of the two closed branches obeys the same expansion
estimate, including pairs containing the critical point or an endpoint. -/
theorem branch_bound {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hs : SameBranch x y) :
    angleDistance x y ≤ (b/(2*a))*angleDistance (f x) (f y) := by
  rcases hs with ⟨hx0,hy0⟩ | ⟨hx0,hy0⟩
  · exact h.positive_branch_bound ⟨hx0,hx.2⟩ ⟨hy0,hy.2⟩
  · have hn := h.positive_branch_bound
      (show -x ∈ Icc (0 : ℝ) 1 from ⟨by linarith,by linarith [hx.1]⟩)
      (show -y ∈ Icc (0 : ℝ) 1 from ⟨by linarith,by linarith [hy.1]⟩)
    simpa only [angleDistance_neg_neg,h.even] using hn

theorem iterate_mem {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    (f^[n]) x ∈ Icc (-1 : ℝ) 1 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact h.mapsTo ih

/-- The inverse contraction is iterated along an arbitrary full branch
word; no periodicity or avoidance of boundary points is required. -/
theorem itinerary_angle_bound (n : ℕ) {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hi : SameItinerary f n x y) :
    angleDistance x y ≤ (b/(2*a))^n * angleDistance ((f^[n]) x) ((f^[n]) y) := by
  induction n generalizing x y with
  | zero => simp only [pow_zero,Function.iterate_zero,id_eq,one_mul,le_refl]
  | succ n ih =>
    have hs : SameBranch x y := by simpa using hi 0 (by omega)
    have ht : SameItinerary f n (f x) (f y) := by
      intro j hj
      simpa only [Function.iterate_succ_apply] using hi (j+1) (by omega)
    have hb := ih (h.mapsTo hx) (h.mapsTo hy) ht
    calc
      angleDistance x y ≤ (b/(2*a))*angleDistance (f x) (f y) := h.branch_bound hx hy hs
      _ ≤ (b/(2*a))*((b/(2*a))^n * angleDistance ((f^[n]) (f x)) ((f^[n]) (f y))) :=
        mul_le_mul_of_nonneg_left hb h.ratio_nonneg
      _ = (b/(2*a))^(n+1) * angleDistance ((f^[n+1]) x) ((f^[n+1]) y) := by
        rw [pow_succ,Function.iterate_succ_apply,Function.iterate_succ_apply]
        ring

/-- Every real cylinder has a uniform explicit physical diameter bound.
In the application `a=15*t` and `b=19*t`, the factor is `19/30`. -/
theorem cylinder_diameter_le (n : ℕ) {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hi : SameItinerary f n x y) :
    |x-y| ≤ Real.pi*(b/(2*a))^n := by
  calc
    |x-y| ≤ angleDistance x y := abs_sub_le_angleDistance hx hy
    _ ≤ (b/(2*a))^n * angleDistance ((f^[n]) x) ((f^[n]) y) :=
      h.itinerary_angle_bound n hx hy hi
    _ ≤ (b/(2*a))^n * Real.pi := mul_le_mul_of_nonneg_left
      (angleDistance_le_pi _ _) (pow_nonneg h.ratio_nonneg n)
    _ = _ := mul_comm _ _

end EvenQuadraticBounds
end
end AngularCylinderExpansion
