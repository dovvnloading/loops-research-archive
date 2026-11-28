import GlobalCrestEstimates
import GlobalCrestSourceGates

/-!
# Complete secant expansion of the native three-return interval

The third iterate of the actual normalized return has a positive even
divided difference between fifteen and nineteen throughout the complete
central interval.  The factorization retains all terms of all three
high-degree returns.  No model map or derivative approximation is used
as a dynamical hypothesis.
-/

namespace ActualThreeReturnExpansion

open Set Function
open LimitingCrest LimitingCrestQuadraticReturn
open NearTwoTip NearTwoShooting QuadraticCrestDividedDifference
open GlobalCrestEstimates GlobalCrestSourceGates

noncomputable section

/-- The real even divided difference of the complete normalized return. -/
def realSecant (c : ℝ) (p : ℕ) (x y : ℝ) : ℝ :=
  (normalizedSecant c p (x : ℂ) (y : ℂ)).re

theorem real_difference {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x y : ℝ) :
    actualMap c p x-actualMap c p y = (x^2-y^2)*realSecant c p x y := by
  have h := congrArg Complex.re
    (normalized_difference c p (by omega) hc.2.1.ne' (x : ℂ) (y : ℂ))
  have hs : (x : ℂ)^2-(y : ℂ)^2 = ((x^2-y^2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_pow]
  rw [hs] at h
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, actualMap, realSecant] using h

/-- The sign and quantitative size of every real secant on the larger
normalization disk, including its diagonal values. -/
theorem realSecant_bounds {p : ℕ} (hp : 17 ≤ p) {c x y : ℝ}
    (hc : ActualTip p c) (hx : |x| ≤ 3/2) (hy : |y| ≤ 3/2) :
    -realSecant c p x y ∈ Icc (179/100 : ℝ) (9/5) := by
  have he := (Complex.abs_re_le_norm
    (normalizedSecant c p (x : ℂ) (y : ℂ)+(kappa p c : ℂ))).trans
      (actual_secant_error hp hc
        (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx)
        (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hy))
  simp only [Complex.add_re, Complex.ofReal_re] at he
  have hk := hc.2.2.2.1
  have hq := scale_small hp
  change |realSecant c p x y+kappa p c| ≤ 61*scale p at he
  constructor <;> linarith [(abs_le.mp he).1, (abs_le.mp he).2, hk.1, hk.2]

private theorem real_error {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : ActualTip p c) (hx : |x| ≤ 3/2) :
    |actualMap c p x-(1-kappa p c*x^2)| ≤ 1/100000000 := by
  have he := (Complex.abs_re_le_norm
    (normalizedReturn c p (x : ℂ)-complexMap (kappa p c) (x : ℂ))).trans
      (actual_return_error_small hp hc
        (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx))
  simpa only [complexMap_real, Complex.sub_re, Complex.ofReal_re,
    realMap, actualMap] using he

private theorem step_sq {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hxd : |x| ≤ 3/2)
    (hx : a ≤ x^2 ∧ x^2 ≤ b) (ha : 0 ≤ a)
    (hl : l ≤ 1-(17904/10000)*b-1/100000000)
    (hu : 1-(17903/10000)*a+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  have hk := hc.2.2.2.1
  have hlo := mul_le_mul hk.1 hx.1 ha (by linarith [hk.1])
  have hhi := mul_le_mul hk.2 hx.2 (sq_nonneg x) (by norm_num)
  have he := abs_le.mp (real_error hp hc hxd)
  constructor <;> linarith

private theorem step_pos {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hx : x ∈ Icc a b)
    (ha : 0 ≤ a) (hb : b ≤ 3/2)
    (hl : l ≤ 1-(17904/10000)*b^2-1/100000000)
    (hu : 1-(17903/10000)*a^2+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  apply step_sq hp hc
    (abs_le.mpr ⟨by linarith [hx.1], hx.2.trans hb⟩)
    ⟨pow_le_pow_left₀ ha hx.1 2,
      pow_le_pow_left₀ (ha.trans hx.1) hx.2 2⟩ (sq_nonneg a) hl hu

private theorem step_neg {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hx : x ∈ Icc a b)
    (ha : -(3/2) ≤ a) (hb : b ≤ 0)
    (hl : l ≤ 1-(17904/10000)*a^2-1/100000000)
    (hu : 1-(17903/10000)*b^2+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  have hs : b^2 ≤ x^2 ∧ x^2 ≤ a^2 := by
    constructor
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr hb) (neg_le_neg hx.2) 2
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr (hx.2.trans hb)) (neg_le_neg hx.1) 2
  exact step_sq hp hc
    (abs_le.mpr ⟨ha.trans hx.1, by linarith [hx.2]⟩) hs (sq_nonneg b) hl hu

/-- The actual third critical return locates the native central interval. -/
theorem third_critical_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    actualOrbit c p 0 3 ∈ Icc (-119/1000 : ℝ) (-117/1000) := by
  have c0 : (0 : ℝ) ∈ Icc 0 0 := ⟨le_rfl, le_rfl⟩
  have c1 : actualOrbit c p 0 1 ∈ Icc (99999999/100000000) (100000001/100000000) :=
    step_pos hp hc c0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c2 : actualOrbit c p 0 2 ∈ Icc (-790401/1000000) (-790299/1000000) :=
    step_pos hp hc c1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact step_neg hp hc c2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The first complete image of every point in the central interval
remains in the same positive real strip. -/
theorem first_image_bounds {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : ActualTip p c) (hx : |x| ≤ 119/1000) :
    actualMap c p x ∈ Icc (97/100 : ℝ) (1001/1000) := by
  have hsq : x^2 ≤ (119/1000 : ℝ)^2 :=
    sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
  exact step_sq hp hc (hx.trans (by norm_num))
    ⟨sq_nonneg x, hsq⟩ (by norm_num) (by norm_num) (by norm_num)

/-- The second complete image has a uniformly negative real sign. -/
theorem second_image_bounds {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : ActualTip p c) (hx : |x| ≤ 119/1000) :
    actualMap c p (actualMap c p x) ∈ Icc (-4/5 : ℝ) (-17/25) :=
  step_pos hp hc (first_image_bounds hp hc hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The five real factors in the complete three-return divided difference.
The signs are arranged so that every displayed factor is positive on
the native central interval. -/
def thirdSecant (c : ℝ) (p : ℕ) (x y : ℝ) : ℝ :=
  (-realSecant c p x y) *
    (actualMap c p x+actualMap c p y) *
    (-realSecant c p (actualMap c p x) (actualMap c p y)) *
    (-(actualMap c p (actualMap c p x)+actualMap c p (actualMap c p y))) *
    (-realSecant c p (actualMap c p (actualMap c p x))
      (actualMap c p (actualMap c p y)))

/-- Exact factorization of the difference of the genuine three returns. -/
theorem third_difference {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x y : ℝ) :
    actualOrbit c p x 3-actualOrbit c p y 3 =
      (x^2-y^2)*thirdSecant c p x y := by
  have h0 := real_difference hp hc x y
  have h1 := real_difference hp hc (actualMap c p x) (actualMap c p y)
  have h2 := real_difference hp hc
    (actualMap c p (actualMap c p x)) (actualMap c p (actualMap c p y))
  simp only [actualOrbit]
  rw [h2]
  have hs1 : (actualMap c p (actualMap c p x))^2-
      (actualMap c p (actualMap c p y))^2 =
      (actualMap c p (actualMap c p x)+actualMap c p (actualMap c p y))*
        (actualMap c p (actualMap c p x)-actualMap c p (actualMap c p y)) := by ring
  have hs0 : (actualMap c p x)^2-(actualMap c p y)^2 =
      (actualMap c p x+actualMap c p y)*(actualMap c p x-actualMap c p y) := by ring
  rw [hs1, h1, hs0, h0]
  unfold thirdSecant
  ring

private theorem mul_box {a b x c d y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    x*y ∈ Icc (a*c) (b*d) :=
  ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))⟩

/-- A uniform complete-iterate secant bound on the entire central
interval.  In particular the lower bound holds at every pair of
points and does not lose strength at the critical point. -/
theorem thirdSecant_bounds {p : ℕ} (hp : 17 ≤ p) {c x y : ℝ}
    (hc : ActualTip p c) (hx : |x| ≤ 119/1000) (hy : |y| ≤ 119/1000) :
    thirdSecant c p x y ∈ Icc (15 : ℝ) 19 := by
  have hx1 := first_image_bounds hp hc hx
  have hy1 := first_image_bounds hp hc hy
  have hx2 := second_image_bounds hp hc hx
  have hy2 := second_image_bounds hp hc hy
  have hxd1 : |actualMap c p x| ≤ 3/2 :=
    abs_le.mpr ⟨by linarith [hx1.1], by linarith [hx1.2]⟩
  have hyd1 : |actualMap c p y| ≤ 3/2 :=
    abs_le.mpr ⟨by linarith [hy1.1], by linarith [hy1.2]⟩
  have hxd2 : |actualMap c p (actualMap c p x)| ≤ 3/2 :=
    abs_le.mpr ⟨by linarith [hx2.1], by linarith [hx2.2]⟩
  have hyd2 : |actualMap c p (actualMap c p y)| ≤ 3/2 :=
    abs_le.mpr ⟨by linarith [hy2.1], by linarith [hy2.2]⟩
  have h0 := realSecant_bounds hp hc (hx.trans (by norm_num)) (hy.trans (by norm_num))
  have h1 := realSecant_bounds hp hc hxd1 hyd1
  have h2 := realSecant_bounds hp hc hxd2 hyd2
  have hsum1 : actualMap c p x+actualMap c p y ∈
      Icc (97/50 : ℝ) (1001/500) :=
    ⟨by linarith [hx1.1, hy1.1], by linarith [hx1.2, hy1.2]⟩
  have hsum2 : -(actualMap c p (actualMap c p x)+actualMap c p (actualMap c p y)) ∈
      Icc (34/25 : ℝ) (8/5) :=
    ⟨by linarith [hx2.2, hy2.2], by linarith [hx2.1, hy2.1]⟩
  have ha := mul_box h0 hsum1 (by norm_num) (by norm_num)
  have hb := mul_box ha h1 (by norm_num) (by norm_num)
  have hd := mul_box hb hsum2 (by norm_num) (by norm_num)
  have he := mul_box hd h2 (by norm_num) (by norm_num)
  change _ ≤ thirdSecant c p x y ∧ thirdSecant c p x y ≤ _ at he
  constructor <;> linarith [he.1, he.2]

/-- The full third return has quadratic expansion on each ordered
positive subinterval of the actual central carrier. -/
theorem third_quadratic_expansion {p : ℕ} (hp : 17 ≤ p) {c x y : ℝ}
    (hc : ActualTip p c) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 119/1000) :
    15*(y^2-x^2) ≤ actualOrbit c p y 3-actualOrbit c p x 3 ∧
      actualOrbit c p y 3-actualOrbit c p x 3 ≤ 19*(y^2-x^2) := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have hsec := thirdSecant_bounds hp hc
    (show |y| ≤ 119/1000 by rw [abs_of_nonneg hy0]; exact hy)
    (show |x| ≤ 119/1000 by rw [abs_of_nonneg hx]; exact hxy.trans hy)
  have hs : 0 ≤ y^2-x^2 := sub_nonneg.mpr (pow_le_pow_left₀ hx hxy 2)
  rw [third_difference hp hc y x]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right hsec.1 hs
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right hsec.2 hs

end

end ActualThreeReturnExpansion
