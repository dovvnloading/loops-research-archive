import LimitingCrestPersistence

/-!
# The crest corridor for literal quadratic return maps

The complete nonlinear remainder of an actual iterate of z ↦ z²+c is
bounded on a complex disk by an induction on the iterate.  Consequently
the normalized return satisfies the quantitative crest criterion from
raw critical-orbit, return-scale, and quadratic-coefficient inequalities.
No map-approximation or crossing assumption occurs in the final theorem.

The existence, for every period, of the designated near-minus-two
parameter satisfying these real inequalities remains a separate question.
-/

namespace LimitingCrestQuadraticReturn

open Set Function
open LimitingCrest

noncomputable section

def quadraticMap (c : ℝ) (z : ℂ) : ℂ := z^2 + (c : ℂ)

def criticalValue (c : ℝ) (n : ℕ) : ℝ :=
  ((fun t : ℝ => t^2+c)^[n]) 0

/-- The coefficient of z² in the (n+1)-st iterate. -/
def quadraticCoefficient (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => 2 * criticalValue c (n+1) * quadraticCoefficient c n

/-- The complete remainder, including every term of degree at least four. -/
def quadraticRemainder (c : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ) -
    (quadraticCoefficient c n : ℂ) * z^2

/-- Normalization by the actual positive critical return value. -/
def normalizedReturn (c : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  ((quadraticMap c)^[p]) ((criticalValue c p : ℂ)*z) /
    (criticalValue c p : ℂ)

private theorem criticalValue_succ (c : ℝ) (n : ℕ) :
    criticalValue c (n+1) = (criticalValue c n)^2+c := by
  simp only [criticalValue, iterate_succ_apply']

private theorem iterate_real (c t : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (t : ℂ) =
      (((fun x : ℝ => x^2+c)^[n]) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp only [quadraticMap, Complex.ofReal_add, Complex.ofReal_pow]

private theorem coefficient_bound (c : ℝ) (n : ℕ) :
    (∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2) →
      |quadraticCoefficient c n| ≤ (4 : ℝ)^n := by
  induction n with
  | zero => intro h; norm_num [quadraticCoefficient]
  | succ n ih =>
    intro h
    have ha := ih (fun j hj => h j (by omega))
    have hd := h (n+1) (by omega)
    calc
      |quadraticCoefficient c (n+1)| =
          (2*|criticalValue c (n+1)|)*|quadraticCoefficient c n| := by
            norm_num [quadraticCoefficient, abs_mul]
      _ ≤ 4*(4 : ℝ)^n :=
        mul_le_mul (by linarith) ha (abs_nonneg _) (by norm_num)
      _ = (4 : ℝ)^(n+1) := by rw [pow_succ]; ring

private theorem remainder_step (c : ℝ) (n : ℕ) (z : ℂ) :
    quadraticRemainder c (n+1) z =
      2*(criticalValue c (n+1) : ℂ)*quadraticRemainder c n z +
        ((quadraticCoefficient c n : ℂ)*z^2 + quadraticRemainder c n z)^2 := by
  simp only [quadraticRemainder, iterate_succ_apply', quadraticMap,
    criticalValue_succ, quadraticCoefficient]
  push_cast
  ring

/-- An all-point bound for the complete nonlinear remainder.  The sole
dynamical hypothesis bounds the actual critical orbit through the horizon. -/
theorem complete_remainder_bound (c : ℝ) (n : ℕ) :
    ∀ (r : ℝ) (z : ℂ), 0 ≤ r →
      (∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2) →
      (4 : ℝ)^(n+1)*r^2 ≤ 1 → ‖z‖ ≤ r →
      ‖quadraticRemainder c n z‖ ≤ ((4 : ℝ)^(n+1)*r^2)^2/128 := by
  induction n with
  | zero =>
    intro r z hr hcrit hscale hz
    have he : quadraticRemainder c 0 z = 0 := by
      simp [quadraticRemainder, quadraticMap, criticalValue, quadraticCoefficient]
    rw [he, norm_zero]
    positivity
  | succ n ih =>
    intro r z hr hcrit hscale hz
    let t : ℝ := (4 : ℝ)^(n+1)*r^2
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    have hnext : (4 : ℝ)^(n+1+1)*r^2 = 4*t := by
      dsimp [t]
      rw [pow_succ]
      ring
    have ht : t ≤ 1/4 := by rw [hnext] at hscale; linarith
    have hprevious : ∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2 :=
      fun j hj => hcrit j (by omega)
    have he := ih r z hr hprevious (show (4 : ℝ)^(n+1)*r^2 ≤ 1 by
      change t ≤ 1; linarith) hz
    change ‖quadraticRemainder c n z‖ ≤ t^2/128 at he
    have he' : ‖quadraticRemainder c n z‖ ≤ t/512 := by
      have hprod := mul_le_mul_of_nonneg_left ht ht0
      nlinarith only [he, hprod]
    have ha := coefficient_bound c n hprevious
    have hz2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    have hlead : ‖(quadraticCoefficient c n : ℂ)*z^2‖ ≤ t/4 := by
      calc
        ‖(quadraticCoefficient c n : ℂ)*z^2‖ =
            |quadraticCoefficient c n|*‖z‖^2 := by
              rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (4 : ℝ)^n*r^2 :=
          mul_le_mul ha hz2 (sq_nonneg _) (by positivity)
        _ = t/4 := by dsimp [t]; rw [pow_succ]; ring
    have hsum : ‖(quadraticCoefficient c n : ℂ)*z^2+
        quadraticRemainder c n z‖ ≤ (129/512 : ℝ)*t := by
      have htri := norm_add_le ((quadraticCoefficient c n : ℂ)*z^2)
        (quadraticRemainder c n z)
      linarith
    have hsquare := pow_le_pow_left₀ (norm_nonneg _ ) hsum 2
    have hd := hcrit (n+1) (by omega)
    have hlinear : (2*|criticalValue c (n+1)|)*
        ‖quadraticRemainder c n z‖ ≤ t^2/32 := by
      calc
        (2*|criticalValue c (n+1)|)*‖quadraticRemainder c n z‖ ≤
            4*(t^2/128) :=
          mul_le_mul (by linarith) he (norm_nonneg _) (by norm_num)
        _ = t^2/32 := by ring
    rw [hnext, remainder_step]
    calc
      ‖2*(criticalValue c (n+1) : ℂ)*quadraticRemainder c n z +
          ((quadraticCoefficient c n : ℂ)*z^2 + quadraticRemainder c n z)^2‖ ≤
          ‖2*(criticalValue c (n+1) : ℂ)*quadraticRemainder c n z‖ +
            ‖((quadraticCoefficient c n : ℂ)*z^2 + quadraticRemainder c n z)^2‖ :=
        norm_add_le _ _
      _ = (2*|criticalValue c (n+1)|)*‖quadraticRemainder c n z‖ +
          ‖(quadraticCoefficient c n : ℂ)*z^2 + quadraticRemainder c n z‖^2 := by
        rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
          Real.norm_eq_abs, norm_pow]
      _ ≤ t^2/32 + ((129/512 : ℝ)*t)^2 := add_le_add hlinear hsquare
      _ ≤ (4*t)^2/128 := by nlinarith only [sq_nonneg t]

private theorem power_scale_lower {p : ℕ} (hp : 13 ≤ p) :
    (67108864 : ℝ) ≤ (4 : ℝ)^p := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
  norm_num at h
  exact h

/-- The actual normalized return is within 24·4⁻ᵖ of its quadratic
part on the fixed disk.  This is derived from the orbit and scale
inequalities, rather than assumed as a renormalization estimate. -/
theorem normalized_return_error (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p) :
    ∀ z : ℂ, ‖z‖ ≤ 23/20 →
      ‖normalizedReturn c p z -
        complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) z‖ ≤
          24/(4 : ℝ)^p := by
  cases p with
  | zero => omega
  | succ n =>
    intro z hz
    let d := criticalValue c (n+1)
    let S : ℝ := (4 : ℝ)^(n+1)
    let R : ℝ := 23/20
    have hd0 : 0 < d := hd
    have hS0 : 0 < S := by dsimp [S]; positivity
    have hS := power_scale_lower hp
    change 67108864 ≤ S at hS
    have hSd : S*d ≤ 12 := by
      have h := (le_div_iff₀ hS0).mp hsmall
      nlinarith only [h]
    have hSd0 : 0 ≤ S*d := mul_nonneg hS0.le hd0.le
    have hr : 0 ≤ d*R := by dsimp [R]; positivity
    have hdR : S*(d*R)^2 ≤ 1 := by
      have hsquare := pow_le_pow_left₀ hSd0 hSd 2
      have hnorm : S*(S*(d*R)^2) = (S*d)^2*R^2 := by ring
      have hm := mul_le_mul_of_nonneg_right hsquare (sq_nonneg R)
      have hprod := mul_le_mul_of_nonneg_right hS
        (show 0 ≤ S*(d*R)^2 by positivity)
      dsimp [R] at hm hnorm ⊢
      dsimp [R] at hprod
      nlinarith only [hm, hnorm, hprod]
    have hdz : ‖(d : ℂ)*z‖ ≤ d*R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
      exact mul_le_mul_of_nonneg_left hz hd0.le
    have herr := complete_remainder_bound c n (d*R) ((d : ℂ)*z) hr hcrit hdR hdz
    change ‖quadraticRemainder c n ((d : ℂ)*z)‖ ≤ (S*(d*R)^2)^2/128 at herr
    have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hid : normalizedReturn c (n+1) z -
        complexMap (-quadraticCoefficient c n*d) z =
          quadraticRemainder c n ((d : ℂ)*z)/(d : ℂ) := by
      dsimp [normalizedReturn, complexMap, quadraticRemainder]
      change ((quadraticMap c)^[n+1]) ((d : ℂ)*z)/(d : ℂ) -
        (1-((-quadraticCoefficient c n*d : ℝ) : ℂ)*z^2) =
          (((quadraticMap c)^[n+1]) ((d : ℂ)*z) - (d : ℂ) -
            (quadraticCoefficient c n : ℂ)*((d : ℂ)*z)^2)/(d : ℂ)
      push_cast
      field_simp [hdne]
      ring
    have hcubed := pow_le_pow_left₀ hSd0 hSd 3
    have hbound : (S*(d*R)^2)^2/128/d ≤ 24/S := by
      apply (div_le_div_iff₀ hd0 hS0).mpr
      have hm := mul_le_mul_of_nonneg_right hcubed (hd0.le)
      have hr4 : R^4 < (16/9 : ℝ) := by norm_num [R]
      have hform : ((S*(d*R)^2)^2/128)*S =
          (S*d)^3*d*R^4/128 := by ring
      rw [hform]
      have h1 := mul_le_mul_of_nonneg_right hm
        (pow_nonneg (by norm_num [R] : (0 : ℝ) ≤ R) 4)
      have h2 := mul_le_mul_of_nonneg_left hr4.le (show 0 ≤ (1728 : ℝ)*d by positivity)
      nlinarith only [h1, h2]
    change ‖normalizedReturn c (n+1) z -
      complexMap (-quadraticCoefficient c n*d) z‖ ≤ 24/S
    rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    exact (div_le_div_of_nonneg_right herr hd0.le).trans hbound

private theorem normalizedReturn_continuous (c : ℝ) (p : ℕ) :
    Continuous (normalizedReturn c p) := by
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  exact ((hf.iterate p).comp (continuous_const.mul continuous_id)).div_const _

private theorem normalizedReturn_real (c t : ℝ) (p : ℕ) :
    (normalizedReturn c p (t : ℂ)).im = 0 := by
  unfold normalizedReturn
  rw [← Complex.ofReal_mul, iterate_real]
  simp

private theorem normalizedReturn_imaginary (c t : ℝ) (p : ℕ) (hp : 0 < p) :
    (normalizedReturn c p ((t : ℂ)*Complex.I)).im = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let d := criticalValue c (n+1)
  have hfirst : quadraticMap c ((d : ℂ)*((t : ℂ)*Complex.I)) =
      ((c-(d*t)^2 : ℝ) : ℂ) := by
    simp [quadraticMap, mul_pow, Complex.I_sq] <;> ring
  unfold normalizedReturn
  change (((quadraticMap c)^[n+1]) ((d : ℂ)*((t : ℂ)*Complex.I)) / (d : ℂ)).im = 0
  rw [iterate_succ_apply, hfirst, iterate_real]
  simp

private theorem critical_orbit_bound (c : ℝ)
    (hc : c ∈ Icc (-2 : ℝ) 0) (j : ℕ) :
    |criticalValue c j| ≤ 2 := by
  have hinterval : ∀ n : ℕ, criticalValue c n ∈ Icc c (-c) := by
    intro n
    induction n with
    | zero =>
      change c ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ -c
      constructor <;> linarith [hc.2]
    | succ n ih =>
      have hsquare : (criticalValue c n)^2 ≤ (-c)^2 :=
        sq_le_sq' (show -(-c) ≤ criticalValue c n by linarith [ih.1]) ih.2
      have hproduct : c*(c+2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc.2 (by linarith [hc.1])
      rw [criticalValue_succ]
      constructor
      · nlinarith only [sq_nonneg (criticalValue c n)]
      · nlinarith only [hsquare, hproduct]
  have hj := hinterval j
  rw [abs_le]
  constructor <;> linarith [hc.1, hj.1, hj.2]

/-- A literal quadratic return has the whole persistent source corridor
once its real parameter, positive-return scale, and quadratic coefficient
lie in the stated ranges.  The critical-orbit bound and the complete
complex approximation are proved; no finite-orbit gate is a premise. -/
theorem actual_quadratic_return_corridor (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {s : ℝ} (hs : s ∈ Icc (63/1000 : ℝ) (33/500)) :
    ∃ u : ℝ, u ∈ Ioo (-1/100 : ℝ) (1/100) ∧
      ‖circlePoint s u + (3/4 : ℂ)‖ = s ∧
      (normalizedReturn c p (circlePoint s u)).re = 0 ∧
      0 < (normalizedReturn c p (circlePoint s u)).im ∧
      (((normalizedReturn c p)^[2]) (circlePoint s u)).im = 0 ∧
      (((normalizedReturn c p)^[3]) (circlePoint s u)).im = 0 ∧
      (-999/1000 : ℝ) < (((normalizedReturn c p)^[3]) (circlePoint s u)).re ∧
      (((normalizedReturn c p)^[3]) (circlePoint s u)).re < -977/1000 ∧
      (((normalizedReturn c p)^[3]) (circlePoint s u)).re <
        -(((normalizedReturn c p)^[4]) 0).re := by
  apply uniform_perturbed_corridor (normalizedReturn c p)
    (normalizedReturn_continuous c p)
    (fun t => normalizedReturn_real c t p)
    (fun t => normalizedReturn_imaginary c t p (by omega)) hk hs
  intro z hz
  apply (normalized_return_error c p hp
    (fun j _ => critical_orbit_bound c hc j) hd hsmall z hz).trans
  apply (div_le_iff₀ (show (0 : ℝ) < 4^p by positivity)).mpr
  have h := power_scale_lower hp
  linarith

end
end LimitingCrestQuadraticReturn
