import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive inverse shooting near the quadratic endpoint

Quantitative estimates for the actual positive inverse branch of x ↦ x²+c.
The branch bounds are used to construct parameters for the crest problem;
they carry no ideal-boundary or extremal-width identification.
-/

namespace NearTwoInverse

open Set Function
open scoped BigOperators

noncomputable section

def B (c x : ℝ) : ℝ := Real.sqrt (x-c)

def back (c : ℝ) (n : ℕ) (d : ℝ) : ℝ := (B c)^[n] d

theorem back_zero (c d : ℝ) : back c 0 d = d := rfl

theorem back_succ (c d : ℝ) (n : ℕ) :
    back c (n+1) d = B c (back c n d) := by
  exact Function.iterate_succ_apply' (B c) n d

theorem B_nonneg (c x : ℝ) : 0 ≤ B c x := Real.sqrt_nonneg _

theorem B_sq {c x : ℝ} (hc : c ≤ 0) (hx : 0 ≤ x) :
    (B c x)^2 = x-c := Real.sq_sqrt (by linarith)

theorem B_bounds {c x : ℝ} (hc : c ∈ Icc (-2) (-49/25))
    (hx : x ∈ Icc 0 2) : B c x ∈ Icc (7/5) 2 := by
  have hs := B_sq (show c ≤ 0 by linarith [hc.2]) hx.1
  have hn := B_nonneg c x
  constructor <;> nlinarith [hc.1, hc.2, hx.1, hx.2]

theorem back_bounds {c d : ℝ} (hc : c ∈ Icc (-2) (-49/25))
    (hd : d ∈ Icc 0 2) (n : ℕ) : back c n d ∈ Icc 0 2 := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    rw [back_succ]
    have h := B_bounds hc ih
    exact ⟨by linarith [h.1], h.2⟩

theorem back_lower {c d : ℝ} (hc : c ∈ Icc (-2) (-49/25))
    (hd : d ∈ Icc 0 2) (n : ℕ) : 7/5 ≤ back c (n+1) d := by
  rw [back_succ]
  exact (B_bounds hc (back_bounds hc hd n)).1

theorem continuous_back (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => back p.1 n p.2) := by
  induction n with
  | zero => exact continuous_snd
  | succ n ih =>
    simp only [back_succ, B]
    exact Real.continuous_sqrt.comp (ih.sub continuous_fst)

theorem continuous_back_parameter (n : ℕ) (d : ℝ) :
    Continuous (fun c : ℝ => back c n d) :=
  (continuous_back n).comp (continuous_id.prodMk continuous_const)

theorem back_mono_initial (c : ℝ) (n : ℕ) : Monotone (back c n) := by
  induction n with
  | zero => exact monotone_id
  | succ n ih =>
    intro d e hde
    simp only [back_succ, B]
    exact Real.sqrt_le_sqrt (sub_le_sub_right (ih hde) c)

theorem back_antitone_parameter (n : ℕ) (d : ℝ) :
    Antitone (fun c : ℝ => back c n d) := by
  induction n with
  | zero => intro c c' _; exact le_rfl
  | succ n ih =>
    intro c c' hcc
    simp only [back_succ, B]
    exact Real.sqrt_le_sqrt (sub_le_sub (ih hcc) hcc)

private theorem branch_difference_bound {c c' x y : ℝ}
    (hc : c ∈ Icc (-2) (-49/25)) (hc' : c' ∈ Icc (-2) (-49/25))
    (hx : x ∈ Icc 0 2) (hy : y ∈ Icc 0 2) :
    (14/5 : ℝ) * |B c x - B c' y| ≤ |x-y|+|c-c'| := by
  have hA := B_bounds hc hx
  have hB := B_bounds hc' hy
  have hsA := B_sq (show c ≤ 0 by linarith [hc.2]) hx.1
  have hsB := B_sq (show c' ≤ 0 by linarith [hc'.2]) hy.1
  have hid : (B c x-B c' y)*(B c x+B c' y) = (x-y)-(c-c') := by
    nlinarith [hsA, hsB]
  have habs : |B c x-B c' y| * (B c x+B c' y) = |(x-y)-(c-c')| := by
    rw [← abs_of_nonneg (show 0 ≤ B c x+B c' y by linarith [hA.1,hB.1]),
      ← abs_mul, hid]
  have htri := abs_sub (x-y) (c-c')
  have hmul := mul_le_mul_of_nonneg_left
    (show (14/5 : ℝ) ≤ B c x+B c' y by linarith [hA.1,hB.1])
    (abs_nonneg (B c x-B c' y))
  nlinarith

theorem back_parameter_lipschitz {c c' d : ℝ}
    (hc : c ∈ Icc (-2) (-49/25)) (hc' : c' ∈ Icc (-2) (-49/25))
    (hd : d ∈ Icc 0 2) (n : ℕ) :
    |back c n d-back c' n d| ≤ (5/9 : ℝ)*|c-c'| := by
  induction n with
  | zero => simp only [back_zero, sub_self, abs_zero]; positivity
  | succ n ih =>
    have h := branch_difference_bound hc hc' (back_bounds hc hd n) (back_bounds hc' hd n)
    rw [back_succ, back_succ]
    nlinarith

theorem chebyshev_deficit_barrier (n : ℕ) :
    2-back (-2) n 0 ≤
      (13/5 : ℝ)*(1/4 : ℝ)^n-(3/5 : ℝ)*((1/4 : ℝ)^n)^2 := by
  induction n with
  | zero => norm_num [back_zero]
  | succ n ih =>
    let q : ℝ := (1/4 : ℝ)^n
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq1 : q ≤ 1 := by dsimp [q]; exact pow_le_one₀ (by norm_num) (by norm_num)
    have hq2 : q^2 ≤ q := by nlinarith [mul_le_mul_of_nonneg_left hq1 hq0]
    have hb := back_bounds (c := (-2 : ℝ)) (d := (0 : ℝ))
      (by norm_num) (by norm_num) (n+1)
    have hs := B_sq (c := (-2 : ℝ))
      (x := back (-2) n 0) (by norm_num)
      (back_bounds (c := (-2 : ℝ)) (d := (0 : ℝ))
        (by norm_num) (by norm_num) n).1
    rw [← back_succ] at hs
    let v : ℝ := (13/20)*q-(3/80)*q^2
    have hv0 : 0 ≤ v := by dsimp [v]; nlinarith
    have hv1 : v ≤ 13/20 := by dsimp [v]; nlinarith [sq_nonneg q]
    have hcoef : 0 ≤ 176+312*q-9*q^2 := by nlinarith
    have hbar : (13/5 : ℝ)*q-(3/5 : ℝ)*q^2 ≤ 4*v-v^2 := by
      have hprod := mul_nonneg (sq_nonneg q) hcoef
      dsimp [v]
      nlinarith only [hprod]
    have hold : 2-back (-2) n 0 ≤ (13/5 : ℝ)*q-(3/5 : ℝ)*q^2 := ih
    have hnext : 2-back (-2) (n+1) 0 ≤ v := by
      by_contra h
      have hv : v < 2-back (-2) (n+1) 0 := lt_of_not_ge h
      have hpos := mul_pos (sub_pos.mpr hv)
        (show 0 < 4-(2-back (-2) (n+1) 0)-v by linarith [hb.1])
      nlinarith [hold, hbar, hs]
    have hp : (1/4 : ℝ)^(n+1) = q/4 := by dsimp [q]; rw [pow_succ]; ring
    rw [hp]
    dsimp [v] at hnext
    nlinarith only [hnext]

theorem chebyshev_deficit_upper (n : ℕ) :
    2-back (-2) n 0 ≤ (13/5 : ℝ)*(1/4 : ℝ)^n := by
  have h := chebyshev_deficit_barrier n
  nlinarith [sq_nonneg ((1/4 : ℝ)^n)]

end

end NearTwoInverse
