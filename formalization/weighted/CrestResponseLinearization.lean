import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Finite differences with a certified linear part

This elementary algebra keeps the correlation between the parameter and
quartic perturbations in the endpoint equations.  It concerns finite
differences, and does not assume differentiability of a selected root.
-/

namespace CrestResponseLinearization

noncomputable section

/-- A scalar expression at two points, with a common numerical center and
a certified linear approximation to its finite difference. -/
structure Jet (q : ℝ) where
  value : ℝ
  base : ℝ
  center : ℝ
  radius : ℝ
  difference : ℝ
  linear : ℝ
  error : ℝ
  value_bound : |value-center| ≤ radius
  base_bound : |base-center| ≤ radius
  difference_bound : |value-base| ≤ difference*q
  error_bound : |value-base-linear| ≤ error*q

namespace Jet

variable {q : ℝ}

theorem radius_nonneg (a : Jet q) : 0 ≤ a.radius :=
  (abs_nonneg _).trans a.value_bound

theorem value_abs (a : Jet q) : |a.value| ≤ |a.center|+a.radius := by
  calc
    |a.value| = |a.center+(a.value-a.center)| := by congr 1; ring
    _ ≤ |a.center|+|a.value-a.center| := abs_add_le _ _
    _ ≤ |a.center|+a.radius := add_le_add le_rfl a.value_bound

theorem base_abs (a : Jet q) : |a.base| ≤ |a.center|+a.radius := by
  calc
    |a.base| = |a.center+(a.base-a.center)| := by congr 1; ring
    _ ≤ |a.center|+|a.base-a.center| := abs_add_le _ _
    _ ≤ |a.center|+a.radius := add_le_add le_rfl a.base_bound

def const (q c : ℝ) : Jet q where
  value := c
  base := c
  center := c
  radius := 0
  difference := 0
  linear := 0
  error := 0
  value_bound := by simp
  base_bound := by simp
  difference_bound := by simp
  error_bound := by simp

def coordinate (q x x₀ c a d : ℝ)
    (hx : |x-c| ≤ a) (hx₀ : |x₀-c| ≤ a)
    (hd : |x-x₀| ≤ d*q) : Jet q where
  value := x
  base := x₀
  center := c
  radius := a
  difference := d
  linear := x-x₀
  error := 0
  value_bound := hx
  base_bound := hx₀
  difference_bound := hd
  error_bound := by simp

def add (a b : Jet q) : Jet q where
  value := a.value+b.value
  base := a.base+b.base
  center := a.center+b.center
  radius := a.radius+b.radius
  difference := a.difference+b.difference
  linear := a.linear+b.linear
  error := a.error+b.error
  value_bound := by
    calc
      |a.value+b.value-(a.center+b.center)| =
          |(a.value-a.center)+(b.value-b.center)| := by congr 1; ring
      _ ≤ |a.value-a.center|+|b.value-b.center| := abs_add_le _ _
      _ ≤ a.radius+b.radius := add_le_add a.value_bound b.value_bound
  base_bound := by
    calc
      |a.base+b.base-(a.center+b.center)| =
          |(a.base-a.center)+(b.base-b.center)| := by congr 1; ring
      _ ≤ |a.base-a.center|+|b.base-b.center| := abs_add_le _ _
      _ ≤ a.radius+b.radius := add_le_add a.base_bound b.base_bound
  difference_bound := by
    calc
      |a.value+b.value-(a.base+b.base)| =
          |(a.value-a.base)+(b.value-b.base)| := by congr 1; ring
      _ ≤ |a.value-a.base|+|b.value-b.base| := abs_add_le _ _
      _ ≤ a.difference*q+b.difference*q :=
        add_le_add a.difference_bound b.difference_bound
      _ = (a.difference+b.difference)*q := by ring
  error_bound := by
    calc
      |a.value+b.value-(a.base+b.base)-(a.linear+b.linear)| =
          |(a.value-a.base-a.linear)+(b.value-b.base-b.linear)| := by
        congr 1; ring
      _ ≤ |a.value-a.base-a.linear|+|b.value-b.base-b.linear| := abs_add_le _ _
      _ ≤ a.error*q+b.error*q := add_le_add a.error_bound b.error_bound
      _ = (a.error+b.error)*q := by ring

def neg (a : Jet q) : Jet q where
  value := -a.value
  base := -a.base
  center := -a.center
  radius := a.radius
  difference := a.difference
  linear := -a.linear
  error := a.error
  value_bound := by simpa only [neg_sub_neg, abs_sub_comm] using a.value_bound
  base_bound := by simpa only [neg_sub_neg, abs_sub_comm] using a.base_bound
  difference_bound := by
    simpa only [neg_sub_neg, abs_sub_comm] using a.difference_bound
  error_bound := by
    have he : -a.value- -a.base- -a.linear = -(a.value-a.base-a.linear) := by ring
    rw [he, abs_neg]
    exact a.error_bound

def sub (a b : Jet q) : Jet q := a.add b.neg

private theorem product_center_bound {x y c d a b : ℝ}
    (hx : |x-c| ≤ a) (hy : |y-d| ≤ b) :
    |x*y-c*d| ≤ |c| *b+|d| *a+a*b := by
  have ha : 0 ≤ a := (abs_nonneg _).trans hx
  have hb : 0 ≤ b := (abs_nonneg _).trans hy
  calc
    |x*y-c*d| = |(c*(y-d)+d*(x-c))+(x-c)*(y-d)| := by congr 1; ring
    _ ≤ |c*(y-d)+d*(x-c)|+|(x-c)*(y-d)| := abs_add_le _ _
    _ ≤ (|c*(y-d)|+|d*(x-c)|)+|(x-c)*(y-d)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = (|c| *|y-d|+|d| *|x-c|)+|x-c| *|y-d| := by simp only [abs_mul]
    _ ≤ (|c| *b+|d| *a)+a*b := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg c))
          (mul_le_mul_of_nonneg_left hx (abs_nonneg d)))
        (mul_le_mul hx hy (abs_nonneg _) ha)

def mul (a b : Jet q) : Jet q where
  value := a.value*b.value
  base := a.base*b.base
  center := a.center*b.center
  radius := |a.center| *b.radius+|b.center| *a.radius+a.radius*b.radius
  difference := (|a.center|+a.radius)*b.difference+
    (|b.center|+b.radius)*a.difference
  linear := a.center*b.linear+b.center*a.linear
  error := |a.center| *b.error+|b.center| *a.error+
    a.radius*b.difference+b.radius*a.difference
  value_bound := product_center_bound a.value_bound b.value_bound
  base_bound := product_center_bound a.base_bound b.base_bound
  difference_bound := by
    calc
      |a.value*b.value-a.base*b.base| =
          |a.value*(b.value-b.base)+b.base*(a.value-a.base)| := by congr 1; ring
      _ ≤ |a.value*(b.value-b.base)|+|b.base*(a.value-a.base)| := abs_add_le _ _
      _ = |a.value| *|b.value-b.base|+|b.base| *|a.value-a.base| := by
        simp only [abs_mul]
      _ ≤ (|a.center|+a.radius)*(b.difference*q)+
          (|b.center|+b.radius)*(a.difference*q) := by
        exact add_le_add
          (mul_le_mul a.value_abs b.difference_bound (abs_nonneg _)
            (add_nonneg (abs_nonneg _) a.radius_nonneg))
          (mul_le_mul b.base_abs a.difference_bound (abs_nonneg _)
            (add_nonneg (abs_nonneg _) b.radius_nonneg))
      _ = ((|a.center|+a.radius)*b.difference+
          (|b.center|+b.radius)*a.difference)*q := by ring
  error_bound := by
    have hid : a.value*b.value-a.base*b.base-
        (a.center*b.linear+b.center*a.linear) =
        (a.center*(b.value-b.base-b.linear)+
          b.center*(a.value-a.base-a.linear))+
        ((a.value-a.center)*(b.value-b.base)+
          (b.base-b.center)*(a.value-a.base)) := by ring
    rw [hid]
    calc
      |(a.center*(b.value-b.base-b.linear)+
          b.center*(a.value-a.base-a.linear))+
        ((a.value-a.center)*(b.value-b.base)+
          (b.base-b.center)*(a.value-a.base))| ≤
          |a.center*(b.value-b.base-b.linear)+b.center*(a.value-a.base-a.linear)|+
          |(a.value-a.center)*(b.value-b.base)+(b.base-b.center)*(a.value-a.base)| :=
        abs_add_le _ _
      _ ≤ (|a.center*(b.value-b.base-b.linear)|+
          |b.center*(a.value-a.base-a.linear)|)+
          (|(a.value-a.center)*(b.value-b.base)|+
          |(b.base-b.center)*(a.value-a.base)|) :=
        add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ = (|a.center| *|b.value-b.base-b.linear|+
          |b.center| *|a.value-a.base-a.linear|)+
          (|a.value-a.center| *|b.value-b.base|+
          |b.base-b.center| *|a.value-a.base|) := by simp only [abs_mul]
      _ ≤ (|a.center| *(b.error*q)+|b.center| *(a.error*q))+
          (a.radius*(b.difference*q)+b.radius*(a.difference*q)) := by
        exact add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left b.error_bound (abs_nonneg _))
            (mul_le_mul_of_nonneg_left a.error_bound (abs_nonneg _)))
          (add_le_add
            (mul_le_mul a.value_bound b.difference_bound (abs_nonneg _) a.radius_nonneg)
            (mul_le_mul b.base_bound a.difference_bound (abs_nonneg _) b.radius_nonneg))
      _ = (|a.center| *b.error+|b.center| *a.error+
          a.radius*b.difference+b.radius*a.difference)*q := by ring

def sq (a : Jet q) : Jet q := a.mul a

/-- An expression vanishing at the base point and small at the perturbed
point yields an equally explicit bound for its retained linear part. -/
theorem linear_bound (a : Jet q) {E : ℝ}
    (hb : a.base = 0) (hv : |a.value| ≤ E*q) :
    |a.linear| ≤ (E+a.error)*q := by
  calc
    |a.linear| = |a.value-(a.value-a.base-a.linear)| := by rw [hb]; congr 1; ring
    _ ≤ |a.value|+|a.value-a.base-a.linear| := by
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le a.value (-(a.value-a.base-a.linear))
    _ ≤ E*q+a.error*q := add_le_add hv a.error_bound
    _ = (E+a.error)*q := by ring

end Jet
end
end CrestResponseLinearization
