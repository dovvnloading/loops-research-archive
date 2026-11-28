import ActualThreeReturnExpansion
import ThreeReturnRealization
import AngularCylinderExpansion

/-!
# The canonical central real return in physical coordinates

The radius and the interval map below are obtained from the actual
critical orbit.  No conjugacy or metric estimate is supplied as input.
-/

namespace ActualThreeReturnNormalization

open Set Function
open LimitingCrestQuadraticReturn NearTwoTip GlobalCrestSourceGates
open ActualThreeReturnExpansion ThreeReturnDomain ThreeReturnRealization
open AngularCylinderExpansion

noncomputable section

/-- Radius of the actual central invariant interval, in p-return units. -/
def centralRadius (c : ℝ) (p : ℕ) : ℝ := -actualOrbit c p 0 3

/-- The literal three-return in its own signed unit-interval coordinate. -/
def centralMap (c : ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  -actualOrbit c p (centralRadius c p * x) 3 / centralRadius c p

/-- The map back to the original quadratic dynamical plane. -/
def physicalPoint (c : ℝ) (p : ℕ) (x : ℝ) : ℂ :=
  ((-criticalValue c p * centralRadius c p * x : ℝ) : ℂ)

theorem centralRadius_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : centralRadius c p ∈ Icc (117/1000 : ℝ) (119/1000) := by
  have h := third_critical_bounds hp hc
  dsimp [centralRadius]
  constructor <;> linarith [h.1, h.2]

theorem centralRadius_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : 0 < centralRadius c p := by
  linarith [(centralRadius_bounds hp hc).1]

private theorem real_iterate_cast (c x : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (x : ℂ) =
      (((fun y : ℝ => y^2+c)^[n]) x : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp [quadraticMap]

private theorem actualMap_real_formula (c x : ℝ) (p : ℕ) :
    actualMap c p x =
      ((fun y : ℝ => y^2+c)^[p]) (criticalValue c p*x) / criticalValue c p := by
  unfold actualMap normalizedReturn
  rw [← Complex.ofReal_mul, real_iterate_cast, ← Complex.ofReal_div]
  rfl

theorem actualMap_differentiable (c : ℝ) (p : ℕ) :
    Differentiable ℝ (actualMap c p) := by
  have hq : Differentiable ℝ (fun y : ℝ => y^2+c) :=
    (differentiable_id.pow 2).add_const c
  have he : actualMap c p = fun x : ℝ =>
      ((fun y : ℝ => y^2+c)^[p]) (criticalValue c p*x) / criticalValue c p :=
    funext (fun x => actualMap_real_formula c x p)
  rw [he]
  exact ((hq.iterate p).comp
    (differentiable_const.mul differentiable_id)).div_const _

theorem actualOrbit_differentiable (c : ℝ) (p n : ℕ) :
    Differentiable ℝ (fun x => actualOrbit c p x n) := by
  induction n with
  | zero => exact differentiable_id
  | succ n ih => exact (actualMap_differentiable c p).comp ih

theorem centralMap_differentiable (c : ℝ) (p : ℕ) :
    Differentiable ℝ (centralMap c p) := by
  exact (((actualOrbit_differentiable c p 3).comp
    (differentiable_const.mul differentiable_id)).neg).div_const _

theorem third_even {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x : ℝ) :
    actualOrbit c p (-x) 3 = actualOrbit c p x 3 := by
  apply sub_eq_zero.mp
  rw [third_difference hp hc]
  ring

theorem centralMap_even {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x : ℝ) :
    centralMap c p (-x) = centralMap c p x := by
  simp only [centralMap, mul_neg, third_even hp hc]

theorem centralMap_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : centralMap c p 0 = 1 := by
  have ht := (centralRadius_pos hp hc).ne'
  change -actualOrbit c p (centralRadius c p*0) 3 / centralRadius c p = 1
  rw [mul_zero]
  change centralRadius c p / centralRadius c p = 1
  exact div_self ht

private theorem third_endpoint {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    actualOrbit c p (centralRadius c p) 3 = centralRadius c p := by
  have h := (critical_signed_orbit c p (by omega) hc.2.1.ne'
    hc.2.2.2.2.1).2
  have h0 : (actualOrbit c p 0 3 : ℂ) = threeReturn c p 0 := by
    simpa only [Complex.ofReal_zero] using actualOrbit_cast c 0 p 3
  have ht : (centralRadius c p : ℂ) = -threeReturn c p 0 := by
    simp only [centralRadius, Complex.ofReal_neg, h0]
  have he : (actualOrbit c p (centralRadius c p) 3 : ℂ) =
      (centralRadius c p : ℂ) := by
    rw [actualOrbit_cast, ht]
    exact h
  exact Complex.ofReal_injective he

theorem centralMap_one {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : centralMap c p 1 = -1 := by
  have ht := (centralRadius_pos hp hc).ne'
  simp only [centralMap, mul_one, third_endpoint hp hc, neg_div, div_self ht]

/-- Uniform square-secants are now proved for the actual interval map. -/
theorem centralMap_square_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    EvenQuadraticBounds (centralMap c p)
      (15*centralRadius c p) (19*centralRadius c p) := by
  have ht := centralRadius_pos hp hc
  have htb := (centralRadius_bounds hp hc).2
  refine {
    a_pos := by positivity
    b_pos := by positivity
    continuous := (centralMap_differentiable c p).continuous
    differentiable := centralMap_differentiable c p
    even := centralMap_even hp hc
    zero := centralMap_zero hp hc
    one := centralMap_one hp hc
    secant := ?_
  }
  intro x hx y hy hxy
  have htx : 0 ≤ centralRadius c p*x := mul_nonneg ht.le hx.1
  have hty : centralRadius c p*y ≤ 119/1000 :=
    (mul_le_mul_of_nonneg_left hy.2 ht.le).trans (by simpa using htb)
  have he := third_quadratic_expansion hp hc htx
    (mul_le_mul_of_nonneg_left hxy ht.le) hty
  have hid : centralMap c p x-centralMap c p y =
      (actualOrbit c p (centralRadius c p*y) 3-
        actualOrbit c p (centralRadius c p*x) 3)/centralRadius c p := by
    simp only [centralMap]
    ring
  rw [hid]
  constructor
  · apply (le_div_iff₀ ht).mpr
    nlinarith only [he.1]
  · apply (div_le_iff₀ ht).mpr
    nlinarith only [he.2]

/-- The sign in the physical coordinate is fixed by the critical orbit. -/
theorem physicalPoint_semiconj {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    Semiconj (physicalPoint c p) (centralMap c p) ((quadraticMap c)^[3*p]) := by
  intro x
  have ht := (centralRadius_pos hp hc).ne'
  have h := actualOrbit_physical c (-(centralRadius c p*x)) p 3 hc.2.1
  have hin : ((criticalValue c p : ℂ)*(-(centralRadius c p*x) : ℝ)) =
      physicalPoint c p x := by
    simp only [physicalPoint, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [hin, third_even hp hc] at h
  rw [h]
  apply congrArg (fun r : ℝ => (r : ℂ))
  change -criticalValue c p*centralRadius c p*
    (-actualOrbit c p (centralRadius c p*x) 3/centralRadius c p) =
      criticalValue c p*actualOrbit c p (centralRadius c p*x) 3
  field_simp [ht]
  <;> ring

end
end ActualThreeReturnNormalization
