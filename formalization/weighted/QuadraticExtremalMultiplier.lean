import QuadraticEscape
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Actual quadratic bounded-orbit and derivative bounds.
No symbolic realization or unproved complex-dynamical input is assumed. -/
namespace QuadraticEscape

noncomputable section

theorem norm_step_lower (c z : ℂ) : ‖z‖ ^ 2 ≤ ‖z^2+c‖ + ‖c‖ := by
  calc
    ‖z‖ ^ 2 = ‖(z^2+c)-c‖ := by rw [add_sub_cancel_right, norm_pow]
    _ ≤ _ := norm_sub_le _ _

/-- Escape outside both the radius two and the parameter radius. -/
theorem escape_pos_of_large (c z : ℂ) (hz : 2 < ‖z‖)
    (hc : ‖c‖ ≤ ‖z‖) : 0 < escape c z := by
  by_contra h
  have hzero : escape c z = 0 :=
    le_antisymm (le_of_not_gt h) (escape_nonneg c z)
  have hgrowth (n : ℕ) :
      ‖z‖ + (n : ℝ) * (‖z‖-2) ≤ ‖orbit c n z‖ := by
    induction n with
    | zero => simp [orbit]
    | succ n ih =>
      have hnn : 0 ≤ (n : ℝ) * (‖z‖-2) :=
        mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hz.le)
      have hr : ‖z‖ ≤ ‖orbit c n z‖ := by linarith only [ih, hnn]
      have hr2 : 2 ≤ ‖orbit c n z‖ := (le_of_lt hz).trans hr
      have hprod : 0 ≤ (‖orbit c n z‖-2)*(‖orbit c n z‖-1) :=
        mul_nonneg (by linarith) (by linarith)
      have hs := norm_step_lower c (orbit c n z)
      simp only [orbit, Nat.cast_succ]
      nlinarith only [ih, hr, hc, hs, hprod]
  obtain ⟨n, hn⟩ := exists_nat_gt ((1+‖c‖)/(‖z‖-2))
  have hgt : 1+‖c‖ < (n : ℝ)*(‖z‖-2) :=
    (div_lt_iff₀ (sub_pos.mpr hz)).mp hn
  have hb := escape_zero_orbit_bound c z hzero n
  linarith only [hgrowth n, hgt, hb, norm_nonneg z]

/-- The true critical bounded-orbit parameter locus lies in the radius-two disk. -/
theorem parameter_norm_le_two (c : ℂ) (hc : parameterEscape c = 0) :
    ‖c‖ ≤ 2 := by
  by_contra h
  have hp := escape_pos_of_large c c (lt_of_not_ge h) le_rfl
  change escape c c = 0 at hc
  linarith

theorem bounded_point_norm_le_two (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) : ‖z‖ ≤ 2 := by
  by_contra h
  have hlt : 2 < ‖z‖ := lt_of_not_ge h
  have hp := escape_pos_of_large c z hlt (hc.trans hlt.le)
  linarith

theorem bounded_orbit_norm_le_two (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) (n : ℕ) : ‖orbit c n z‖ ≤ 2 := by
  apply bounded_point_norm_le_two c _ hc
  rw [escape_iterate, hz, mul_zero]

/-- The parameter-dependent squared radius improves the uniform disk bound. -/
theorem bounded_orbit_norm_sq (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) (n : ℕ) :
    ‖orbit c n z‖ ^ 2 ≤ 2 + ‖c‖ := by
  have h := norm_step_lower c (orbit c n z)
  have hb := bounded_orbit_norm_le_two c z hc hz (n+1)
  rw [orbit] at hb
  linarith only [h,hb]

/-- The derivative of the actual n-fold quadratic iterate, not an abstract product. -/
def multiplier (c z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => 2 * orbit c n z * multiplier c z n

theorem orbit_hasDerivAt (c z : ℂ) (n : ℕ) :
    HasDerivAt (orbit c n) (multiplier c z n) z := by
  induction n with
  | zero =>
    change HasDerivAt (id : ℂ → ℂ) 1 z
    exact hasDerivAt_id z
  | succ n ih =>
    have hh := HasDerivAt.add (HasDerivAt.pow ih 2) (hasDerivAt_const z c)
    have heq : orbit c (n+1) = (orbit c n)^2 + fun _ => c := by
      funext w
      simp [orbit]
    rw [heq]
    simpa only [multiplier, Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero] using hh

theorem multiplier_eq_deriv (c z : ℂ) (n : ℕ) :
    deriv (orbit c n) z = multiplier c z n :=
  (orbit_hasDerivAt c z n).deriv

theorem multiplier_norm_bound (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) (n : ℕ) :
    ‖multiplier c z n‖ ≤ (4 : ℝ)^n := by
  induction n with
  | zero => simp [multiplier]
  | succ n ih =>
    have hb := bounded_orbit_norm_le_two c z hc hz n
    have hf : 2 * ‖orbit c n z‖ ≤ 4 := by linarith
    rw [multiplier, norm_mul, norm_mul, Complex.norm_two, pow_succ]
    calc
      2 * ‖orbit c n z‖ * ‖multiplier c z n‖ ≤ 4 * (4:ℝ)^n :=
        mul_le_mul hf ih (norm_nonneg _) (by norm_num)
      _ = _ := mul_comm _ _

theorem deriv_norm_bound (c z : ℂ) (hc : parameterEscape c = 0)
    (hz : escape c z = 0) (n : ℕ) : ‖deriv (orbit c n) z‖ ≤ (4:ℝ)^n := by
  rw [multiplier_eq_deriv]
  exact multiplier_norm_bound c z (parameter_norm_le_two c hc) hz n

/-- A reverse-triangle equality defect quantified by the parallelogram law.
Only the parameter and the immediate successor must lie in the radius-two disk. -/
theorem successor_defect_sq (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hw : ‖z^2+c‖ ≤ 2) :
    ‖(z^2+c)+c‖^2 ≤ 8*(4-‖z‖^2) := by
  let w := z^2+c
  have hpar : ‖w+c‖^2 + ‖w-c‖^2 = 2*‖w‖^2+2*‖c‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
    ring
  have heq : w-c = z^2 := by dsimp [w]; ring
  rw [heq, norm_pow] at hpar
  have hc2 : ‖c‖^2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg c) hc 2
    norm_num at h
    exact h
  have hw2 : ‖w‖^2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg w) hw 2
    norm_num at h
    exact h
  change ‖w+c‖^2 ≤ _
  nlinarith only [hpar,hc2,hw2,sq_nonneg (4-‖z‖^2)]

/-- The squared radial deficit can increase by at most four in one step. -/
theorem successor_radial_deficit (c z : ℂ) (hc : ‖c‖ ≤ 2) :
    4-‖z^2+c‖^2 ≤ 4*(4-‖z‖^2) := by
  have hs := norm_step_lower c z
  nlinarith only [hs,hc,sq_nonneg (2-‖z^2+c‖)]

/-- Three consecutive bounded points force quantitative parameter rigidity:
a point near the extremal radius two forces c near -2. No periodicity or
repelling assumption is needed. -/
theorem parameter_defect_sq (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hw : ‖z^2+c‖ ≤ 2) (hu : ‖(z^2+c)^2+c‖ ≤ 2) :
    ‖c+2‖^2 ≤ 288*(4-‖z‖^2) := by
  let w := z^2+c
  let u := w^2+c
  have hstep := norm_step_lower c z
  change ‖z‖^2 ≤ ‖w‖+‖c‖ at hstep
  change ‖w‖ ≤ 2 at hw
  change ‖u‖ ≤ 2 at hu
  have ha : ‖w+c‖^2 ≤ 8*(4-‖z‖^2) :=
    successor_defect_sq c z hc hw
  have hb₀ : ‖u+c‖^2 ≤ 8*(4-‖w‖^2) :=
    successor_defect_sq c w hc hu
  have hb₁ : 4-‖w‖^2 ≤ 4*(4-‖z‖^2) := successor_radial_deficit c z hc
  have hb : ‖u+c‖^2 ≤ 32*(4-‖z‖^2) := by linarith only [hb₀,hb₁]
  by_cases hC : 1 ≤ ‖c‖
  · have heq : c*(c+2) = (c+w)*(c-w)+(u+c) := by
      dsimp [u]
      ring
    have hcw : ‖c-w‖ ≤ 4 := (norm_sub_le _ _).trans (by linarith)
    have hp : ‖c‖ * ‖c+2‖ ≤ 4*‖w+c‖+‖u+c‖ := by
      calc
        ‖c‖*‖c+2‖ = ‖c*(c+2)‖ := (norm_mul _ _).symm
        _ = ‖(c+w)*(c-w)+(u+c)‖ := by rw [heq]
        _ ≤ ‖(c+w)*(c-w)‖+‖u+c‖ := norm_add_le _ _
        _ = ‖w+c‖*‖c-w‖+‖u+c‖ := by rw [norm_mul, add_comm c w]
        _ ≤ 4*‖w+c‖+‖u+c‖ := by
          have hh := mul_le_mul_of_nonneg_left hcw (norm_nonneg (w+c))
          linarith only [hh]
    have hl : ‖c+2‖ ≤ ‖c‖*‖c+2‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (norm_nonneg (c+2))
    have hs := pow_le_pow_left₀ (norm_nonneg (c+2)) (hl.trans hp) 2
    nlinarith only [hs,ha,hb,sq_nonneg (2*‖w+c‖-‖u+c‖)]
  · have hC' : ‖c‖ < 1 := lt_of_not_ge hC
    have hnorm : ‖c+2‖ ≤ 3 := by
      calc
        ‖c+2‖ ≤ ‖c‖+‖(2:ℂ)‖ := norm_add_le _ _
        _ ≤ 3 := by rw [Complex.norm_two]; linarith
    have hs : ‖c+2‖^2 ≤ 9 := by
      have h := pow_le_pow_left₀ (norm_nonneg (c+2)) hnorm 2
      norm_num at h
      exact h
    nlinarith only [hs,hstep,hw,hC']

/-- The physical bounded-orbit locus obeys the three-point rigidity estimate. -/
theorem bounded_orbit_parameter_defect (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) (n : ℕ) :
    ‖c+2‖^2 ≤ 288*(4-‖orbit c n z‖^2) := by
  have hw := bounded_orbit_norm_le_two c z hc hz (n+1)
  have hu := bounded_orbit_norm_le_two c z hc hz (n+1+1)
  rw [orbit] at hw
  rw [orbit, orbit] at hu
  exact parameter_defect_sq c (orbit c n z) hc hw hu

/-- Uniform per-iterate gap away from the Chebyshev parameter. The bound
is on the true derivative of every iterate, and is exponential in the
number of iterates, not merely a strict inequality for each fixed period. -/
theorem multiplier_sq_uniform_gap (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : escape c z = 0) (n : ℕ) :
    ‖multiplier c z n‖^2 ≤ (16-‖c+2‖^2/72)^n := by
  have hbase : 0 ≤ 16-‖c+2‖^2/72 := by
    have h := bounded_orbit_parameter_defect c z hc hz 0
    nlinarith only [h,sq_nonneg ‖orbit c 0 z‖]
  induction n with
  | zero => simp [multiplier]
  | succ n ih =>
    have h := bounded_orbit_parameter_defect c z hc hz n
    have hf : 4*‖orbit c n z‖^2 ≤ 16-‖c+2‖^2/72 := by linarith only [h]
    calc
      ‖multiplier c z (n+1)‖^2 =
          (4*‖orbit c n z‖^2)*‖multiplier c z n‖^2 := by
        rw [multiplier, norm_mul, norm_mul, Complex.norm_two]
        ring
      _ ≤ (16-‖c+2‖^2/72)*(16-‖c+2‖^2/72)^n :=
        mul_le_mul hf ih (sq_nonneg _) hbase
      _ = (16-‖c+2‖^2/72)^(n+1) := by
        rw [pow_succ (16-‖c+2‖^2/72) n]
        exact mul_comm _ _

theorem deriv_sq_uniform_gap (c z : ℂ) (hc : parameterEscape c = 0)
    (hz : escape c z = 0) (n : ℕ) :
    ‖deriv (orbit c n) z‖^2 ≤ (16-‖c+2‖^2/72)^n := by
  rw [multiplier_eq_deriv]
  exact multiplier_sq_uniform_gap c z (parameter_norm_le_two c hc) hz n

/-- Equality in the extremal derivative bound at any positive iterate
forces the actual parameter to be -2. -/
theorem extremal_deriv_parameter (c z : ℂ) (hc : parameterEscape c = 0)
    (hz : escape c z = 0) (n : ℕ)
    (he : ‖deriv (orbit c (n+1)) z‖ = (4:ℝ)^(n+1)) :
    c = -2 := by
  have hc2 := parameter_norm_le_two c hc
  rw [multiplier_eq_deriv, multiplier, norm_mul, norm_mul, Complex.norm_two,
    pow_succ] at he
  have hm := multiplier_norm_bound c z hc2 hz n
  have hp : 0 ≤ 2*‖orbit c n z‖ := by positivity
  have hle := mul_le_mul_of_nonneg_left hm hp
  rw [he] at hle
  have hpos : 0 < (4:ℝ)^n := by positivity
  have hf : 4 ≤ 2*‖orbit c n z‖ := by
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      (4:ℝ)^n * 4 ≤ (2*‖orbit c n z‖)*(4:ℝ)^n := hle
      _ = (4:ℝ)^n*(2*‖orbit c n z‖) := mul_comm _ _
  have hr := bounded_orbit_norm_le_two c z hc2 hz n
  have hre : ‖orbit c n z‖ = 2 := by linarith
  have h := bounded_orbit_parameter_defect c z hc2 hz n
  rw [hre] at h
  have hn : ‖c+2‖ = 0 := by
    by_contra hn
    have hpos : 0 < ‖c+2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    nlinarith only [h,mul_pos hpos hpos]
  have hzero : c+2 = 0 := norm_eq_zero.mp hn
  linear_combination hzero

/-- The bound is attained by the actual repelling fixed point at c=-2. -/
theorem chebyshev_fixed_orbit (n : ℕ) : orbit (-2) n 2 = 2 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbit, ih]; norm_num

theorem chebyshev_fixed_escape_zero : escape (-2) 2 = 0 := by
  apply (escape_zero_iff_bounded (-2) 2).mpr
  refine ⟨2, fun n => ?_⟩
  rw [chebyshev_fixed_orbit, Complex.norm_two]

theorem chebyshev_parameter_escape_zero : parameterEscape (-2) = 0 := by
  have h := escape_step (-2) (-2)
  have he : (-2:ℂ)^2+(-2) = 2 := by norm_num
  rw [he, chebyshev_fixed_escape_zero] at h
  change escape (-2) (-2) = 0
  linarith

theorem chebyshev_fixed_multiplier (n : ℕ) :
    multiplier (-2) 2 n = (4:ℂ)^n := by
  induction n with
  | zero => simp [multiplier]
  | succ n ih => rw [multiplier, chebyshev_fixed_orbit, ih, pow_succ]; ring

theorem chebyshev_fixed_deriv_norm (n : ℕ) :
    ‖deriv (orbit (-2) n) 2‖ = (4:ℝ)^n := by
  rw [multiplier_eq_deriv, chebyshev_fixed_multiplier, norm_pow]
  simp


/-- One-step shadowing for two actual quadratic orbits. The nonlinear
error term is retained, rather than replacing the quadratic by a linear model. -/
theorem orbit_difference_step (c d z w : ℂ) (n : ℕ) :
    ‖orbit d (n+1) w - orbit c (n+1) z‖ ≤
      (2 * ‖orbit c n z‖ + ‖orbit d n w - orbit c n z‖) *
        ‖orbit d n w - orbit c n z‖ + ‖d-c‖ := by
  let a := orbit d n w
  let b := orbit c n z
  change ‖(a^2+d)-(b^2+c)‖ ≤ (2*‖b‖+‖a-b‖)*‖a-b‖+‖d-c‖
  have he : (a^2+d)-(b^2+c) = (a-b)*(a-b+2*b)+(d-c) := by ring
  rw [he]
  have h : ‖a-b+2*b‖ ≤ ‖a-b‖+2*‖b‖ := by
    calc
      ‖a-b+2*b‖ ≤ ‖a-b‖+‖(2:ℂ)*b‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, Complex.norm_two]
  calc
    ‖(a-b)*(a-b+2*b)+(d-c)‖ ≤ ‖(a-b)*(a-b+2*b)‖+‖d-c‖ :=
      norm_add_le _ _
    _ = ‖a-b‖*‖a-b+2*b‖+‖d-c‖ := by rw [norm_mul]
    _ ≤ ‖a-b‖*(‖a-b‖+2*‖b‖)+‖d-c‖ :=
      add_le_add_right (mul_le_mul_of_nonneg_left h (norm_nonneg _)) _
    _ = _ := by ring

/-- Finite-scale shadowing with the exact linear growth base A, not A+epsilon.
The forcing error is absorbed into the shadowing variable. The quadratic
correction remains controlled up to the scale A^n * epsilon = 1. -/
theorem orbit_perturbation_bound (c d z w : ℂ) {A ε : ℝ}
    (hA : 3 ≤ A) (hbase : ∀ j : ℕ, 2*‖orbit c j z‖ ≤ A)
    (hε : ‖w-z‖+‖d-c‖ ≤ ε) (n : ℕ) (hn : A^n * ε ≤ 1) :
    ‖orbit d n w - orbit c n z‖+‖d-c‖ ≤ A^n*ε+(A^n*ε)^2 := by
  have hA0 : 0 ≤ A := by linarith
  have he0 : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hε
  induction n with
  | zero =>
    simp only [orbit, pow_zero, one_mul]
    nlinarith only [hε, sq_nonneg ε]
  | succ n ih =>
    let x := A^n*ε
    have hx0 : 0 ≤ x := mul_nonneg (pow_nonneg hA0 _) he0
    have hnext : A^(n+1)*ε = A*x := by
      dsimp [x]
      rw [pow_succ]
      ring
    rw [hnext] at hn ⊢
    have hxle : x ≤ A*x := by
      nlinarith only [mul_nonneg (show 0 ≤ A-1 by linarith) hx0]
    have hx : x ≤ 1 := hxle.trans hn
    let a : ℝ := ‖orbit d n w - orbit c n z‖
    let b : ℝ := ‖d-c‖
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have hi : a+b ≤ x+x^2 := ih hx
    have hs := orbit_difference_step c d z w n
    change ‖orbit d (n+1) w - orbit c (n+1) z‖ ≤
      (2*‖orbit c n z‖+a)*a+b at hs
    have hp := mul_le_mul_of_nonneg_right (add_le_add_right (hbase n) a) ha0
    have hstep : ‖orbit d (n+1) w - orbit c (n+1) z‖+b ≤
        A*(a+b)+(a+b)^2 := by
      nlinarith only [hs, hp, mul_nonneg ha0 hb0, sq_nonneg b,
        mul_nonneg (show 0 ≤ A-2 by linarith) hb0]
    have hsmall : a+b ≤ 2*x := by
      nlinarith only [hi, mul_nonneg hx0 (sub_nonneg.mpr hx)]
    have hsq := pow_le_pow_left₀ (add_nonneg ha0 hb0) hsmall 2
    have hlin := mul_le_mul_of_nonneg_left hi hA0
    have hc : 0 ≤ A^2-A-4 := by
      nlinarith only [hA, sq_nonneg (A-3)]
    have hcoef := mul_nonneg hc (sq_nonneg x)
    change ‖orbit d (n+1) w - orbit c (n+1) z‖+b ≤ A*x+(A*x)^2
    nlinarith only [hstep,hlin,hsq,hcoef]

/-- Explicit physical escape estimate at the full nonlinear shadowing scale.
No Böttcher coordinate or parameter uniformization is assumed. -/
theorem escape_perturbation_scale (c d z w : ℂ) {A ε : ℝ}
    (hA : 3 ≤ A) (hA4 : A ≤ 4) (hbase : ∀ j : ℕ, 2*‖orbit c j z‖ ≤ A)
    (hd : ‖d‖ ≤ 3) (hε : ‖w-z‖+‖d-c‖ ≤ ε)
    (n : ℕ) (hn : A^n*ε ≤ 1) :
    escape d w ≤ weight n * (2*Real.log 4) := by
  have he0 : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hε
  have hx0 : 0 ≤ A^n*ε := mul_nonneg (pow_nonneg (by linarith : 0 ≤ A) _) he0
  have hs := orbit_perturbation_bound c d z w hA hbase hε n hn
  have hdiff : ‖orbit d n w - orbit c n z‖ ≤ 2 := by
    nlinarith only [hs, hn, norm_nonneg (d-c), mul_nonneg hx0 (sub_nonneg.mpr hn)]
  have hb : ‖orbit c n z‖ ≤ 2 := by linarith only [hbase n, hA4]
  have hnorm : ‖orbit d n w‖ ≤ 4 := by
    calc
      ‖orbit d n w‖ = ‖(orbit d n w-orbit c n z)+orbit c n z‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖orbit d n w-orbit c n z‖+‖orbit c n z‖ := norm_add_le _ _
      _ ≤ 4 := by linarith only [hdiff,hb]
  have hl : logSize (orbit d n w) ≤ Real.log 4 := by
    unfold logSize
    apply Real.log_le_log (size_pos _)
    exact max_le (by norm_num) hnorm
  have hm := mul_le_mul_of_nonneg_left hl (weight_pos n).le
  have herr := (abs_le.mp (escape_error d w hd n)).1
  unfold approx at herr
  norm_num at herr
  linarith only [hm,herr]

/-- The strict Chebyshev defect yields a uniform *linear* growth base
less than four for every bounded orbit at a fixed non-Chebyshev parameter. -/
theorem parameter_gap_base (c : ℂ) (hc : parameterEscape c = 0) :
    3 ≤ 4-‖c+2‖^2/576 ∧ 4-‖c+2‖^2/576 ≤ 4 ∧
      ∀ n : ℕ, 2*‖orbit c n c‖ ≤ 4-‖c+2‖^2/576 := by
  have hc2 := parameter_norm_le_two c hc
  have hn : ‖c+2‖ ≤ 4 := by
    calc
      ‖c+2‖ ≤ ‖c‖+‖(2:ℂ)‖ := norm_add_le _ _
      _ ≤ 4 := by rw [Complex.norm_two]; linarith
  have hs := pow_le_pow_left₀ (norm_nonneg (c+2)) hn 2
  have hz : escape c c = 0 := hc
  refine ⟨?_, ?_, fun n => ?_⟩
  · norm_num at hs
    linarith only [hs]
  · nlinarith only [sq_nonneg ‖c+2‖]
  · have h := bounded_orbit_parameter_defect c c hc2 hz n
    nlinarith only [h, sq_nonneg (2-‖orbit c n c‖)]

private theorem one_le_growth_pow {A : ℝ} (hA : 3 ≤ A) (n : ℕ) :
    1 ≤ A^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ A)
    linarith only [h,hA]

/-- Boundary potential at the exact growth base of the reference orbit.
The parameter and its initial critical value both move, hence the factor two. -/
theorem parameter_escape_at_growth_scale (c d : ℂ) (hc : parameterEscape c = 0)
    {A : ℝ} (hA : 3 ≤ A) (hA4 : A ≤ 4)
    (hbase : ∀ j : ℕ, 2*‖orbit c j c‖ ≤ A)
    (n : ℕ) (hn : A^n*(2*‖d-c‖) ≤ 1) :
    parameterEscape d ≤ weight n * (2*Real.log 4) := by
  have hδ := mul_le_mul_of_nonneg_right (one_le_growth_pow hA n)
    (show 0 ≤ 2*‖d-c‖ by positivity)
  have hc2 := parameter_norm_le_two c hc
  have hd : ‖d‖ ≤ 3 := by
    calc
      ‖d‖ = ‖(d-c)+c‖ := by rw [sub_add_cancel]
      _ ≤ ‖d-c‖+‖c‖ := norm_add_le _ _
      _ ≤ 3 := by linarith only [hδ,hn,hc2]
  exact escape_perturbation_scale c d c d hA hA4 hbase hd (by linarith) n hn

/-- Parameter-dependent geometric modulus: at the nth scale the potential
is at most 2 log(4) / 2^n. The radius improves strictly away from c=-2. -/
theorem parameter_escape_improved_scale (c d : ℂ) (hc : parameterEscape c = 0)
    (n : ℕ) (hn : (4-‖c+2‖^2/576)^n*(2*‖d-c‖) ≤ 1) :
    parameterEscape d ≤ weight n * (2*Real.log 4) := by
  obtain ⟨hA,hA4,hbase⟩ := parameter_gap_base c hc
  exact parameter_escape_at_growth_scale c d hc hA hA4 hbase n hn

/-- The universal radius-two bound supplies the endpoint base four. -/
theorem parameter_escape_base_four (c d : ℂ) (hc : parameterEscape c = 0)
    (n : ℕ) (hn : (4:ℝ)^n*(2*‖d-c‖) ≤ 1) :
    parameterEscape d ≤ weight n * (2*Real.log 4) := by
  apply parameter_escape_at_growth_scale c d hc (by norm_num : (3:ℝ) ≤ 4) le_rfl _ n hn
  intro j
  have h := bounded_orbit_norm_le_two c c (parameter_norm_le_two c hc) hc j
  linarith

private theorem weight_sq_four_pow (n : ℕ) : weight n ^ 2 * (4:ℝ)^n = 1 := by
  induction n with
  | zero => norm_num [weight]
  | succ n ih =>
    rw [weight_succ,pow_succ]
    calc
      (weight n / 2)^2*((4:ℝ)^n*4) = weight n^2*(4:ℝ)^n := by ring
      _ = 1 := ih

private theorem four_pow_ge_nat (n : ℕ) : (n:ℝ)+1 ≤ (4:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ,pow_succ]
    linarith only [ih, Nat.cast_nonneg (R := ℝ) n]

private theorem four_scale_crossing {ε : ℝ} (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ n : ℕ, (4:ℝ)^n*ε ≤ 1 ∧ 1 < (4:ℝ)^(n+1)*ε := by
  have hex : ∃ k : ℕ, 1 < (4:ℝ)^k*ε := by
    obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
    refine ⟨k, (div_lt_iff₀ he).mp ?_⟩
    linarith only [hk, four_pow_ge_nat k]
  have hmin := Nat.find_spec hex
  cases h : Nat.find hex with
  | zero =>
    rw [h,pow_zero,one_mul] at hmin
    exact (not_lt_of_ge he1 hmin).elim
  | succ n =>
    refine ⟨n, ?_, ?_⟩
    · by_contra hh
      have hh' := Nat.find_min' hex (lt_of_not_ge hh)
      omega
    · simpa only [h] using hmin

/-- The true critical-value escape potential has a uniform endpoint
one-half Hölder modulus relative to its zero set, expressed without square
roots: G(d)^2 ≤ 32 log(4)^2 |d-c|. No relaxed exponent is used. -/
theorem parameter_escape_half_holder_sq (c d : ℂ) (hc : parameterEscape c = 0)
    (hd : ‖d-c‖ ≤ 1/2) :
    (parameterEscape d)^2 ≤ 32*(Real.log 4)^2*‖d-c‖ := by
  by_cases h : d = c
  · subst d
    simp [hc]
  · have hn : 0 < ‖d-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
    obtain ⟨n,hlo,hhi⟩ := four_scale_crossing
      (show 0 < 2*‖d-c‖ by positivity) (by linarith : 2*‖d-c‖ ≤ 1)
    have hg := parameter_escape_base_four c d hc n hlo
    have hg0 : 0 ≤ parameterEscape d := escape_nonneg d d
    have hsq := pow_le_pow_left₀ hg0 hg 2
    have hw := weight_sq_four_pow n
    have hweight : weight n^2 < 8*‖d-c‖ := by
      have hm := mul_lt_mul_of_pos_left hhi (by positivity : 0 < weight n^2)
      rw [pow_succ] at hm
      calc
        weight n^2 = weight n^2*1 := by ring
        _ < weight n^2*((4:ℝ)^n*4*(2*‖d-c‖)) := hm
        _ = (weight n^2*(4:ℝ)^n)*(8*‖d-c‖) := by ring
        _ = 8*‖d-c‖ := by rw [hw,one_mul]
    calc
      (parameterEscape d)^2 ≤ (weight n*(2*Real.log 4))^2 := hsq
      _ = weight n^2*(4*(Real.log 4)^2) := by ring
      _ ≤ (8*‖d-c‖)*(4*(Real.log 4)^2) :=
        mul_le_mul_of_nonneg_right hweight.le (by positivity)
      _ = 32*(Real.log 4)^2*‖d-c‖ := by ring

end
end QuadraticEscape
