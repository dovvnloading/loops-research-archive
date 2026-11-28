import GlobalInverseWindow
import NearTwoShooting

/-!
# Quantitative placement of globally localized return windows

An actual positive shooting relation, with its previously derived return
scale, forces the narrower parameter corridor 14 < (c+2)4^p < 16.
The proof keeps the parameter displacement and the terminal displacement
separate in the positive inverse orbit.
-/

namespace GlobalWindowChart

open Set Function
open NearTwoInverse NearTwoShooting

noncomputable section

private theorem band {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000)) :
    c ∈ Icc (-2 : ℝ) (-49/25) :=
  ⟨hc.1, by linarith [hc.2]⟩

private theorem inverse_sq {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hd : d ∈ Icc (0 : ℝ) 2) (n : ℕ) :
    (back c (n+1) d)^2 = back c n d-c := by
  have h := B_sq (c := c) (x := back c n d)
    (by linarith [hc.2]) (back_bounds (band hc) hd n).1
  rw [← back_succ] at h
  exact h

private theorem tail_parameter_step {c c' d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hc' : c' ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hd : d ∈ Icc (0 : ℝ) 2) (n : ℕ) (hn : 2 ≤ n) :
    (39/10 : ℝ)*|back c (n+1) d-back c' (n+1) d| ≤
      |back c n d-back c' n d|+|c-c'| := by
  have hA : 1961/1000 ≤ back c (n+1) d := by
    simpa only [show n-2+3=n+1 by omega] using inverse_tail_lower hc hd (n-2)
  have hB : 1961/1000 ≤ back c' (n+1) d := by
    simpa only [show n-2+3=n+1 by omega] using inverse_tail_lower hc' hd (n-2)
  have hid : (back c (n+1) d-back c' (n+1) d)*
      (back c (n+1) d+back c' (n+1) d) =
      (back c n d-back c' n d)-(c-c') := by
    nlinarith only [inverse_sq hc hd n, inverse_sq hc' hd n]
  have habs : |back c (n+1) d-back c' (n+1) d|*
      (back c (n+1) d+back c' (n+1) d) =
      |(back c n d-back c' n d)-(c-c')| := by
    rw [← abs_of_nonneg (show 0 ≤ back c (n+1) d+back c' (n+1) d by linarith),
      ← abs_mul, hid]
  have htri := abs_sub (back c n d-back c' n d) (c-c')
  have hmul := mul_le_mul_of_nonneg_left
    (show (39/10 : ℝ) ≤ back c (n+1) d+back c' (n+1) d by linarith)
    (abs_nonneg (back c (n+1) d-back c' (n+1) d))
  nlinarith only [habs, htri, hmul]

/-- The inverse tail improves the parameter Lipschitz constant after five
steps.  The terminal point is held fixed throughout this comparison. -/
theorem back_parameter_three_eighths {c c' d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hc' : c' ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hd : d ∈ Icc (0 : ℝ) 2) {n : ℕ} (hn : 5 ≤ n) :
    |back c n d-back c' n d| ≤ (3/8 : ℝ)*|c-c'| := by
  have hnonneg := abs_nonneg (c-c')
  have h3 := back_parameter_lipschitz (band hc) (band hc') hd 3
  have h4step := tail_parameter_step hc hc' hd 3 (by omega)
  have h4 : |back c 4 d-back c' 4 d| ≤ (2/5 : ℝ)*|c-c'| := by
    linarith only [h3, h4step, hnonneg]
  have h5step := tail_parameter_step hc hc' hd 4 (by omega)
  have h5 : |back c 5 d-back c' 5 d| ≤ (3/8 : ℝ)*|c-c'| := by
    linarith only [h4, h5step, hnonneg]
  induction n, hn using Nat.le_induction with
  | base => exact h5
  | succ n hn ih =>
    have hstep := tail_parameter_step hc hc' hd n (by omega)
    linarith only [ih, hstep, hnonneg]

/-- A rational lower barrier for the actual Chebyshev inverse deficit.
The base case certifies three nested square roots; the recurrence then
propagates the estimate to every depth. -/
theorem chebyshev_deficit_lower {n : ℕ} (hn : 3 ≤ n) :
    (49/20 : ℝ)*(1/4 : ℝ)^n ≤ 2-back (-2) n 0 := by
  have hs (k : ℕ) : (back (-2) (k+1) 0)^2 = back (-2) k 0+2 := by
    have h := inverse_sq (c := (-2 : ℝ)) (d := (0 : ℝ))
      (by norm_num) (by norm_num) k
    linarith only [h]
  have h1 := hs 0
  simp only [back_zero] at h1
  have h1up : back (-2) 1 0 ≤ 283/200 := by
    nlinarith only [h1, sq_nonneg (back (-2) 1 0-283/200)]
  have h2up : back (-2) 2 0 ≤ 231/125 := by
    nlinarith only [hs 1, h1up, sq_nonneg (back (-2) 2 0-231/125)]
  have h3up : back (-2) 3 0 ≤ 2511/1280 := by
    nlinarith only [hs 2, h2up, sq_nonneg (back (-2) 3 0-2511/1280)]
  induction n, hn using Nat.le_induction with
  | base => norm_num; linarith only [h3up]
  | succ n hn ih =>
    have hstep : 2-back (-2) n 0 ≤ 4*(2-back (-2) (n+1) 0) := by
      nlinarith only [hs n, sq_nonneg (2-back (-2) (n+1) 0)]
    rw [pow_succ]
    nlinarith only [ih, hstep]

/-- A parameter displacement lowers every nontrivial inverse iterate by
at least one quarter of that displacement. -/
theorem inverse_parameter_decrease {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hd : d ∈ Icc (0 : ℝ) 2) (n : ℕ) :
    (c+2)/4 ≤ back (-2) (n+1) d-back c (n+1) d := by
  have hprev := back_antitone_parameter n d hc.1
  have hnext := back_antitone_parameter (n+1) d hc.1
  have hA := back_bounds (c := (-2 : ℝ)) (by norm_num) hd (n+1)
  have hC := back_bounds (band hc) hd (n+1)
  have hmul := mul_le_mul_of_nonneg_left
    (show back (-2) (n+1) d+back c (n+1) d ≤ 4 by linarith [hA.2,hC.2])
    (show 0 ≤ back (-2) (n+1) d-back c (n+1) d from sub_nonneg.mpr hnext)
  have hsqA := inverse_sq (c := (-2 : ℝ)) (by norm_num) hd n
  have hsqC := inverse_sq hc hd n
  nlinarith only [hprev, hmul, hsqA, hsqC]

private theorem terminal_effect {p : ℕ} (hp : 17 ≤ p) {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    back c (p-2) d-back c (p-2) 0 ≤ scale p/10 := by
  have hq := scale_small hp
  have h := GlobalInverseWindow.inverse_difference_bound hc
    (show d ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith [hd.1,hd.2])
    (show (0 : ℝ) ∈ Icc (-3/2 : ℝ) 2 by norm_num) hd.1 (p-3)
  rw [show p-3+1=p-2 by omega] at h
  simp only [sub_zero] at h
  have hpow : (1/3 : ℝ)^(p-3) ≤ (1/3 : ℝ)^5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hcoeff : (3/4 : ℝ)*(1/3 : ℝ)^(p-3) ≤ 1/140 := by
    norm_num at hpow
    linarith only [hpow]
  have hmul := mul_le_mul_of_nonneg_right hcoeff hd.1
  nlinarith only [h, hmul, hd.2]

private theorem scale_shift {p : ℕ} (hp : 2 ≤ p) :
    (1/4 : ℝ)^(p-2) = 16*scale p := by
  have h := pow_add (1/4 : ℝ) (p-2) 2
  rw [Nat.sub_add_cancel hp] at h
  norm_num at h
  dsimp [scale]
  linarith only [h]

/-- Every actual shooting relation in the globally derived parameter
and return bounds lies strictly inside the narrower 14-to-16 corridor. -/
theorem shooting_parameter_bounds {p : ℕ} (hp : 17 ≤ p) {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (hs : shooting (p-2) d c = 0) :
    14*scale p < c+2 ∧ c+2 < 16*scale p := by
  have hq0 := scale_pos p
  have hq := scale_small hp
  have hsmall : c ∈ Icc (-2 : ℝ) (-2+1/10000) :=
    ⟨hc.1, by linarith [hc.2]⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 2 := by norm_num
  have hdeflow := chebyshev_deficit_lower (n := p-2) (by omega)
  have hdefup := chebyshev_deficit_upper (p-2)
  rw [scale_shift (by omega : 2 ≤ p)] at hdeflow hdefup
  have hdecrease : (c+2)/4 ≤ back (-2) (p-2) 0-back c (p-2) 0 := by
    simpa only [show p-3+1=p-2 by omega] using
      inverse_parameter_decrease hsmall hzero (p-3)
  have hterminal := terminal_effect hp hsmall hd
  have hlip := back_parameter_three_eighths
    (c := (-2 : ℝ)) (c' := c) (by norm_num) hsmall hzero
    (n := p-2) (by omega)
  have he : |(-2 : ℝ)-c| = c+2 := by
    rw [abs_of_nonpos (by linarith [hc.1])]
    ring
  rw [he] at hlip
  have hdiff := (le_abs_self (back (-2) (p-2) 0-back c (p-2) 0)).trans hlip
  have hmono := back_mono_initial c (p-2) hd.1
  have hpar0 : 0 ≤ c+2 := by linarith [hc.1]
  have hpar : c+2 ≤ 20*scale p := by linarith [hc.2]
  have hsq := mul_le_mul hpar hpar hpar0
    (show 0 ≤ 20*scale p by positivity)
  have hqsq := mul_le_mul_of_nonneg_left hq hq0.le
  dsimp [shooting] at hs
  constructor
  · by_contra! h
    nlinarith only [hs, hdeflow, hdecrease, hterminal, h, hq0, sq_nonneg (c+2)]
  · by_contra! h
    nlinarith only [hs, hdefup, hdiff, hmono, hsq, hqsq, h, hq0]

end

end GlobalWindowChart
