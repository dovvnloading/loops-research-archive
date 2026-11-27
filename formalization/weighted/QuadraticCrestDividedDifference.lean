import LimitingCrestQuadraticReturn

/-!
# Complete divided differences of the actual quadratic return

The estimates retain every term of the iterate.  They control two points
at once and therefore detect all collisions in the normalization disk.
-/

namespace QuadraticCrestDividedDifference

open Set Function LimitingCrestQuadraticReturn

noncomputable section

/-- The exact divided difference after the first, even, quadratic step. -/
def evenSecant (c : ℝ) : ℕ → ℂ → ℂ → ℂ
  | 0, _, _ => 1
  | n+1, z, w =>
      (((quadraticMap c)^[n+1]) z + ((quadraticMap c)^[n+1]) w) *
        evenSecant c n z w

theorem iterate_difference (c : ℝ) (n : ℕ) (z w : ℂ) :
    ((quadraticMap c)^[n+1]) z - ((quadraticMap c)^[n+1]) w =
      (z^2-w^2) * evenSecant c n z w := by
  induction n with
  | zero => simp [evenSecant, quadraticMap]
  | succ n ih =>
    calc
      _ = (((quadraticMap c)^[n+1]) z)^2 - (((quadraticMap c)^[n+1]) w)^2 := by
        rw [iterate_succ_apply' (quadraticMap c) (n+1) z,
          iterate_succ_apply' (quadraticMap c) (n+1) w]
        simp [quadraticMap]
      _ = (((quadraticMap c)^[n+1]) z + ((quadraticMap c)^[n+1]) w) *
          (((quadraticMap c)^[n+1]) z - ((quadraticMap c)^[n+1]) w) := by ring
      _ = _ := by rw [ih]; simp only [evenSecant]; ring

private theorem coefficient_bound (c : ℝ) (n : ℕ)
    (h : ∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2) :
    |quadraticCoefficient c n| ≤ (4 : ℝ)^n := by
  induction n with
  | zero => norm_num [quadraticCoefficient]
  | succ n ih =>
    have ha := ih (fun j hj => h j (by omega))
    have hd := h (n+1) (by omega)
    calc
      |quadraticCoefficient c (n+1)| =
          (2 * |criticalValue c (n+1)|) * |quadraticCoefficient c n| := by
            norm_num [quadraticCoefficient, abs_mul]
      _ ≤ 4*(4 : ℝ)^n :=
        mul_le_mul (by linarith) ha (abs_nonneg _) (by norm_num)
      _ = (4 : ℝ)^(n+1) := by rw [pow_succ]; ring

private theorem orbit_displacement (c : ℝ) (n : ℕ) (r : ℝ) (z : ℂ)
    (hr : 0 ≤ r)
    (hcrit : ∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2)
    (hscale : (4 : ℝ)^(n+1)*r^2 ≤ 1) (hz : ‖z‖ ≤ r) :
    ‖((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ)‖ ≤
      (4 : ℝ)^(n+1)*r^2/3 := by
  let T : ℝ := (4 : ℝ)^(n+1)*r^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hT1 : T ≤ 1 := hscale
  have hE := complete_remainder_bound c n r z hr hcrit hscale hz
  have hA := coefficient_bound c n hcrit
  have hz2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hlead : ‖(quadraticCoefficient c n : ℂ)*z^2‖ ≤ T/4 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      |quadraticCoefficient c n| * ‖z‖^2 ≤ (4 : ℝ)^n*r^2 :=
        mul_le_mul hA hz2 (sq_nonneg _) (by positivity)
      _ = T/4 := by dsimp [T]; rw [pow_succ]; ring
  have hident : ((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ) =
      (quadraticCoefficient c n : ℂ)*z^2 + quadraticRemainder c n z := by
    unfold quadraticRemainder
    ring
  rw [hident]
  have htri := norm_add_le ((quadraticCoefficient c n : ℂ)*z^2)
    (quadraticRemainder c n z)
  change ‖quadraticRemainder c n z‖ ≤ T^2/128 at hE
  change _ ≤ T/3
  nlinarith only [htri, hlead, hE, mul_le_mul_of_nonneg_left hT1 hT]

/-- A full two-point error bound relative to the quadratic coefficient.
There is no derivative assumption and no truncated power series. -/
theorem evenSecant_error (c : ℝ) (n : ℕ) :
    ∀ (r : ℝ) (z w : ℂ), 0 ≤ r →
      (∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2) →
      (4 : ℝ)^(n+1)*r^2 ≤ 1 → ‖z‖ ≤ r → ‖w‖ ≤ r →
      ‖evenSecant c n z w - (quadraticCoefficient c n : ℂ)‖ ≤
        (4 : ℝ)^n*((4 : ℝ)^(n+1)*r^2)/16 := by
  induction n with
  | zero =>
    intro r z w hr hc hs hz hw
    simp only [evenSecant, quadraticCoefficient, Complex.ofReal_one,
      sub_self, norm_zero, pow_zero, one_mul]
    positivity
  | succ n ih =>
    intro r z w hr hc hs hz hw
    let T : ℝ := (4 : ℝ)^(n+1)*r^2
    let A : ℝ := (4 : ℝ)^n
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hnext : (4 : ℝ)^(n+1+1)*r^2 = 4*T := by
      dsimp [T]; rw [pow_succ]; ring
    have hsmall : T ≤ 1/4 := by rw [hnext] at hs; linarith
    have hc' : ∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2 :=
      fun j hj => hc j (by omega)
    have hs' : (4 : ℝ)^(n+1)*r^2 ≤ 1 := by change T ≤ 1; linarith
    have hE := ih r z w hr hc' hs' hz hw
    change ‖evenSecant c n z w - (quadraticCoefficient c n : ℂ)‖ ≤ A*T/16 at hE
    have hD : ‖evenSecant c n z w‖ ≤ 65*A/64 := by
      have ht := norm_le_norm_sub_add (evenSecant c n z w)
        (quadraticCoefficient c n : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at ht
      have hb := coefficient_bound c n hc'
      change |quadraticCoefficient c n| ≤ A at hb
      nlinarith only [ht, hb, hE, mul_le_mul_of_nonneg_left hsmall hA]
    have hZ := orbit_displacement c n r z hr hc' hs' hz
    have hW := orbit_displacement c n r w hr hc' hs' hw
    change ‖((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ)‖ ≤ T/3 at hZ
    change ‖((quadraticMap c)^[n+1]) w - (criticalValue c (n+1) : ℂ)‖ ≤ T/3 at hW
    let L : ℂ := ((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ) +
      (((quadraticMap c)^[n+1]) w - (criticalValue c (n+1) : ℂ))
    have hL : ‖L‖ ≤ 2*T/3 := by
      have ht := norm_add_le
        (((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ))
        (((quadraticMap c)^[n+1]) w - (criticalValue c (n+1) : ℂ))
      change ‖L‖ ≤ _ at ht
      linarith
    have hident : evenSecant c (n+1) z w - (quadraticCoefficient c (n+1) : ℂ) =
        (2*(criticalValue c (n+1) : ℂ)) *
          (evenSecant c n z w - (quadraticCoefficient c n : ℂ)) +
        L * evenSecant c n z w := by
      simp only [evenSecant, quadraticCoefficient, Complex.ofReal_mul,
        Complex.ofReal_ofNat]
      dsimp [L]
      ring
    have hcrit := hc (n+1) (by omega)
    have hlinear : ‖2*(criticalValue c (n+1) : ℂ) *
        (evenSecant c n z w - (quadraticCoefficient c n : ℂ))‖ ≤ A*T/4 := by
      rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
      calc
        (2*|criticalValue c (n+1)|) *
            ‖evenSecant c n z w - (quadraticCoefficient c n : ℂ)‖ ≤ 4*(A*T/16) :=
          mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
        _ = A*T/4 := by ring
    have hnonlinear : ‖L * evenSecant c n z w‖ ≤ (2*T/3)*(65*A/64) := by
      rw [norm_mul]
      exact mul_le_mul hL hD (norm_nonneg _) (by positivity)
    rw [hident, hnext, pow_succ]
    change _ ≤ (A*4)*(4*T)/16
    exact (norm_add_le _ _).trans ((add_le_add hlinear hnonlinear).trans
      (by nlinarith only [mul_nonneg hA hT]))

/-- Exact even divided difference after normalization by the return value. -/
def normalizedSecant (c : ℝ) (p : ℕ) (z w : ℂ) : ℂ :=
  (criticalValue c p : ℂ) * evenSecant c (p-1)
    ((criticalValue c p : ℂ)*z) ((criticalValue c p : ℂ)*w)

theorem normalized_difference (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0) (z w : ℂ) :
    normalizedReturn c p z - normalizedReturn c p w =
      (z^2-w^2)*normalizedSecant c p z w := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hdC : (criticalValue c (n+1) : ℂ) ≠ 0 := by exact_mod_cast hd
  unfold normalizedReturn normalizedSecant
  rw [← sub_div, iterate_difference]
  simp only [Nat.succ_sub_one]
  field_simp [hdC]

private theorem power_scale_lower {p : ℕ} (hp : 13 ≤ p) :
    (67108864 : ℝ) ≤ (4 : ℝ)^p := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
  norm_num at h
  exact h

private theorem critical_orbit_bound (c : ℝ) (hc : c ∈ Icc (-2 : ℝ) 0) (j : ℕ) :
    |criticalValue c j| ≤ 2 := by
  have hsucc (n : ℕ) : criticalValue c (n+1) = (criticalValue c n)^2+c := by
    simp only [criticalValue, iterate_succ_apply']
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
      rw [hsucc]
      constructor
      · nlinarith only [sq_nonneg (criticalValue c n)]
      · nlinarith only [hsquare, hproduct]
  have hj := hinterval j
  rw [abs_le]
  constructor <;> linarith [hc.1, hj.1, hj.2]

/-- Uniform control of the actual normalized even divided difference.
This is a two-point estimate on the complete complex disk. -/
theorem normalizedSecant_error (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    ‖normalizedSecant c p z w -
      ((quadraticCoefficient c (p-1)*criticalValue c p : ℝ) : ℂ)‖ ≤
        36/(4 : ℝ)^p := by
  cases p with
  | zero => omega
  | succ n =>
    let d : ℝ := criticalValue c (n+1)
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
    have hscale : S*(d*R)^2 ≤ 1 := by
      have h2 := pow_le_pow_left₀ hSd0 hSd 2
      have hf : S*(S*(d*R)^2) = (S*d)^2*R^2 := by ring
      have hm := mul_le_mul_of_nonneg_right h2 (sq_nonneg R)
      have hb := mul_le_mul_of_nonneg_right hS
        (show 0 ≤ S*(d*R)^2 by positivity)
      dsimp [R] at hf hm hb ⊢
      nlinarith only [hf, hm, hb]
    have hdz : ‖(d : ℂ)*z‖ ≤ d*R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
      exact mul_le_mul_of_nonneg_left hz hd0.le
    have hdw : ‖(d : ℂ)*w‖ ≤ d*R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
      exact mul_le_mul_of_nonneg_left hw hd0.le
    have he := evenSecant_error c n (d*R) ((d : ℂ)*z) ((d : ℂ)*w) hr
      (fun j _ => critical_orbit_bound c hc j) hscale hdz hdw
    change ‖evenSecant c n ((d : ℂ)*z) ((d : ℂ)*w) -
      (quadraticCoefficient c n : ℂ)‖ ≤ (4 : ℝ)^n*(S*(d*R)^2)/16 at he
    have hident : normalizedSecant c (n+1) z w -
        ((quadraticCoefficient c n*d : ℝ) : ℂ) =
      (d : ℂ)*(evenSecant c n ((d : ℂ)*z) ((d : ℂ)*w) -
        (quadraticCoefficient c n : ℂ)) := by
      simp only [normalizedSecant, Nat.add_sub_cancel, Complex.ofReal_mul]
      change (d : ℂ)*_ - (quadraticCoefficient c n : ℂ)*(d : ℂ) = _
      ring
    simp only [Nat.add_sub_cancel]
    change ‖normalizedSecant c (n+1) z w -
      ((quadraticCoefficient c n*d : ℝ) : ℂ)‖ ≤ 36/S
    rw [hident, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    apply (mul_le_mul_of_nonneg_left he hd0.le).trans
    apply (le_div_iff₀ hS0).mpr
    have hpow : (4 : ℝ)^n*4 = S := by dsimp [S]; rw [pow_succ]
    have hf : (d*((4 : ℝ)^n*(S*(d*R)^2)/16))*S = (S*d)^3*R^2/64 := by
      rw [← hpow]
      ring
    rw [hf]
    have h3 := pow_le_pow_left₀ hSd0 hSd 3
    have hm := mul_le_mul_of_nonneg_right h3 (sq_nonneg R)
    dsimp [R] at hm ⊢
    nlinarith only [hm]

/-- A convenient absolute version of the sharp exponentially small error. -/
theorem normalizedSecant_error_small (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    ‖normalizedSecant c p z w -
      ((quadraticCoefficient c (p-1)*criticalValue c p : ℝ) : ℂ)‖ ≤ 1/1000 := by
  apply (normalizedSecant_error c p hp hc hd hsmall hz hw).trans
  apply (div_le_iff₀ (show (0 : ℝ) < 4^p by positivity)).mpr
  linarith [power_scale_lower hp]

/-- The normalized remainder has a small even divided difference,
uniformly for every pair of points of the disk. -/
theorem normalized_remainder_difference (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    ‖(normalizedReturn c p z -
        LimitingCrest.complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) z) -
      (normalizedReturn c p w -
        LimitingCrest.complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) w)‖ ≤
      (1/1000 : ℝ)*‖z^2-w^2‖ := by
  have he := normalizedSecant_error_small c p hp hc hd hsmall hz hw
  have hid := normalized_difference c p (by omega) hd.ne' z w
  have halg : (normalizedReturn c p z -
        LimitingCrest.complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) z) -
      (normalizedReturn c p w -
        LimitingCrest.complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) w) =
      (z^2-w^2)*(normalizedSecant c p z w -
        ((quadraticCoefficient c (p-1)*criticalValue c p : ℝ) : ℂ)) := by
    calc
      _ = (normalizedReturn c p z - normalizedReturn c p w) -
          (LimitingCrest.complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) z -
            LimitingCrest.complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) w) := by
              ring
      _ = _ := by
        rw [hid]
        unfold LimitingCrest.complexMap
        push_cast
        ring
  rw [halg, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right he (norm_nonneg _)

theorem normalizedSecant_norm_bounds (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    1 < ‖normalizedSecant c p z w‖ ∧ ‖normalizedSecant c p z w‖ < 2 := by
  let a : ℝ := quadraticCoefficient c (p-1)*criticalValue c p
  have ha : a < 0 := by dsimp [a]; linarith [hk.1]
  have he := normalizedSecant_error_small c p hp hc hd hsmall hz hw
  change ‖normalizedSecant c p z w - (a : ℂ)‖ ≤ 1/1000 at he
  have hup := norm_le_norm_sub_add (normalizedSecant c p z w) (a : ℂ)
  have hlo := norm_le_norm_sub_add (a : ℂ) (normalizedSecant c p z w)
  rw [norm_sub_rev (a : ℂ) (normalizedSecant c p z w)] at hlo
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha] at hup hlo
  have hak : -a ∈ Icc (17903/10000 : ℝ) (17904/10000) := by
    simpa only [a, neg_mul] using hk
  constructor <;> linarith [hak.1, hak.2]

/-- Every collision in the full disk is exactly the original quadratic
symmetry; iterating has introduced no additional pair of sheets there. -/
theorem normalized_return_collision_iff (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w := by
  have hD := (normalizedSecant_norm_bounds c p hp hc hd hsmall hk hz hw).1
  have hD0 : normalizedSecant c p z w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hD
    norm_num at hD
  have hid := normalized_difference c p (by omega) hd.ne' z w
  constructor
  · intro h
    have hzsq : z^2-w^2 = 0 := by
      have hprod : (z^2-w^2)*normalizedSecant c p z w = 0 := by
        rw [← hid, h, sub_self]
      exact (mul_eq_zero.mp hprod).resolve_right hD0
    have hprod : (z-w)*(z+w) = 0 := by
      calc (z-w)*(z+w) = z^2-w^2 := by ring
           _ = 0 := hzsq
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · intro h
    apply sub_eq_zero.mp
    rw [hid]
    rcases h with h | h
    · rw [h, sub_self, zero_mul]
    · rw [h, neg_sq, sub_self, zero_mul]

/-- Uniform Lipschitz control of the literal normalized return. -/
theorem normalized_return_norm_sub_le (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    ‖normalizedReturn c p z - normalizedReturn c p w‖ ≤ 5*‖z-w‖ := by
  have hD := (normalizedSecant_norm_bounds c p hp hc hd hsmall hk hz hw).2.le
  have hsum : ‖z+w‖ ≤ (23/10 : ℝ) := by
    have ht := norm_add_le z w
    linarith
  rw [normalized_difference c p (by omega) hd.ne',
    show z^2-w^2 = (z-w)*(z+w) by ring, norm_mul, norm_mul]
  have hmul := mul_le_mul hsum hD (norm_nonneg _) (by norm_num)
  have hlast := mul_le_mul_of_nonneg_left hmul (norm_nonneg (z-w))
  nlinarith only [hlast, norm_nonneg (z-w)]

/-- On the negative crest-side half disk, the same map has a uniform
lower distance bound. This proves injectivity with a controlled inverse. -/
theorem normalized_return_coercive (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20)
    (hzr : z.re ≤ -5/8) (hwr : w.re ≤ -5/8) :
    ‖z-w‖ ≤ ‖normalizedReturn c p z - normalizedReturn c p w‖ := by
  have hD := (normalizedSecant_norm_bounds c p hp hc hd hsmall hk hz hw).1.le
  have hre : (z+w).re ≤ -(5/4 : ℝ) := by simp only [Complex.add_re]; linarith
  have hn := Complex.abs_re_le_norm (z+w)
  rw [abs_of_nonpos (by linarith : (z+w).re ≤ 0)] at hn
  have hsum : (1 : ℝ) ≤ ‖z+w‖ := by linarith
  have hm := mul_le_mul hsum hD (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)
  rw [normalized_difference c p (by omega) hd.ne',
    show z^2-w^2 = (z-w)*(z+w) by ring, norm_mul, norm_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hm (norm_nonneg (z-w))]

end
end QuadraticCrestDividedDifference
