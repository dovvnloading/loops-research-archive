import QuadraticEscape
import Mathlib.Analysis.Calculus.Deriv.Pow

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
  | zero => simpa only [orbit, multiplier] using (hasDerivAt_id z)
  | succ n ih =>
    simpa [orbit, multiplier] using (ih.pow 2).add_const c

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
    simpa using pow_le_pow_left₀ (norm_nonneg c) hc 2
  have hw2 : ‖w‖^2 ≤ 4 := by
    simpa using pow_le_pow_left₀ (norm_nonneg w) hw 2
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
          rw [mul_comm (4:ℝ)]
          exact add_le_add_right (mul_le_mul_of_nonneg_left hcw (norm_nonneg _)) _
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
      simpa using pow_le_pow_left₀ (norm_nonneg (c+2)) hnorm 2
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
      _ = _ := by rw [pow_succ, mul_comm]

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
    apply (mul_le_mul_right₀ hpos).mp
    simpa only [mul_comm (4:ℝ) ((4:ℝ)^n)] using hle
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
  simp [Complex.norm_ofNat]


end
end QuadraticEscape
