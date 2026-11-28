import ThreeReturnDegree

/-!
# Actual normalized-return control beyond the full crest second image

The full parent crest leaves the smaller historical comparison disk.
Complete squaring-remainder and divided-difference estimates on the disk
of radius 3/2 keep all first, second and terminal real comparisons valid.
-/

namespace GlobalCrestEstimates

open Set Function LimitingCrest LimitingCrestQuadraticReturn
open QuadraticCrestDividedDifference NearTwoShooting NearTwoTip
noncomputable section

private theorem power_scale_lower {p : ℕ} (hp : 13 ≤ p) :
    (67108864 : ℝ) ≤ (4 : ℝ)^p := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
  norm_num at h
  exact h

/-- The actual normalized return is within 72·4⁻ᵖ of its quadratic
part on the fixed disk.  This is derived from the orbit and scale
inequalities, rather than assumed as a renormalization estimate. -/
theorem normalized_return_large_error (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p) :
    ∀ z : ℂ, ‖z‖ ≤ 3/2 →
      ‖normalizedReturn c p z -
        complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) z‖ ≤
          72/(4 : ℝ)^p := by
  cases p with
  | zero => omega
  | succ n =>
    intro z hz
    let d := criticalValue c (n+1)
    let S : ℝ := (4 : ℝ)^(n+1)
    let R : ℝ := 3/2
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
    have hbound : (S*(d*R)^2)^2/128/d ≤ 72/S := by
      apply (div_le_div_iff₀ hd0 hS0).mpr
      have hm := mul_le_mul_of_nonneg_right hcubed (hd0.le)
      have hr4 : R^4 < (16/3 : ℝ) := by norm_num [R]
      have hform : ((S*(d*R)^2)^2/128)*S =
          (S*d)^3*d*R^4/128 := by ring
      rw [hform]
      have h1 := mul_le_mul_of_nonneg_right hm
        (pow_nonneg (by norm_num [R] : (0 : ℝ) ≤ R) 4)
      have h2 := mul_le_mul_of_nonneg_left hr4.le (show 0 ≤ (1728 : ℝ)*d by positivity)
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).mpr
      calc
        (S*d)^3*d*R^4 ≤ 12^3*d*R^4 := h1
        _ = 1728*d*R^4 := by norm_num
        _ ≤ 1728*d*(16/3) := h2
        _ = (72*d)*128 := by ring
    change ‖normalizedReturn c (n+1) z -
      complexMap (-quadraticCoefficient c n*d) z‖ ≤ 72/S
    rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    exact (div_le_div_of_nonneg_right herr hd0.le).trans hbound

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
theorem normalizedSecant_large_error (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    {z w : ℂ} (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 3/2) :
    ‖normalizedSecant c p z w -
      ((quadraticCoefficient c (p-1)*criticalValue c p : ℝ) : ℂ)‖ ≤
        61/(4 : ℝ)^p := by
  cases p with
  | zero => omega
  | succ n =>
    let d : ℝ := criticalValue c (n+1)
    let S : ℝ := (4 : ℝ)^(n+1)
    let R : ℝ := 3/2
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
      ((quadraticCoefficient c n*d : ℝ) : ℂ)‖ ≤ 61/S
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


private theorem actual_small {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    criticalValue c p ≤ 12/(4 : ℝ)^p := by
  simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1

private theorem actual_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    c ∈ Icc (-2 : ℝ) 0 := by
  have hb := parameter_band hp hc.1
  exact ⟨hb.1,by linarith [hb.2]⟩

/-- The entire larger disk has an explicit exponentially small map error. -/
theorem actual_return_error {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 3/2) :
    ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ 72*scale p := by
  have h := normalized_return_large_error c p (by omega)
    hc.2.2.2.2.2.2 hc.2.1 (actual_small hc) z hz
  simpa only [kappa,scale,one_div_pow,mul_one_div] using h

/-- All actual secants on the larger disk retain their quadratic factor. -/
theorem actual_secant_error {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ} (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 3/2) :
    ‖normalizedSecant c p z w+(kappa p c : ℂ)‖ ≤ 61*scale p := by
  have h := normalizedSecant_large_error c p (by omega)
    (actual_band hp hc) hc.2.1 (actual_small hc) hz hw
  have hident : normalizedSecant c p z w+(kappa p c : ℂ) =
      normalizedSecant c p z w-
        ((quadraticCoefficient c (p-1)*criticalValue c p : ℝ) : ℂ) := by
    simp only [kappa, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [hident]
  simpa only [scale,one_div_pow,mul_one_div] using h

/-- Fixed numerical slack on the complete larger disk. -/
theorem actual_return_error_small {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 3/2) :
    ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ 1/100000000 := by
  apply (actual_return_error hp hc hz).trans
  have hq := scale_small hp
  linarith

/-- The secant stays uniformly in the negative-real half plane. -/
theorem actual_secant_re_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ} (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 3/2) :
    (normalizedSecant c p z w).re < -1 := by
  have he := (Complex.abs_re_le_norm
    (normalizedSecant c p z w+(kappa p c : ℂ))).trans
      (actual_secant_error hp hc hz hw)
  simp only [Complex.add_re,Complex.ofReal_re] at he
  have hk := hc.2.2.2.1.1
  change 17903/10000 ≤ kappa p c at hk
  have hq := scale_small hp
  linarith [(abs_le.mp he).2]

/-- The original two-sheet collision law holds even beyond the former
comparison disk, so later real phases introduce no hidden extra branch. -/
theorem actual_return_collision_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ} (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 3/2) :
    normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w := by
  have hD := actual_secant_re_neg hp hc hz hw
  have hD0 : normalizedSecant c p z w ≠ 0 := by
    intro h
    rw [h,Complex.zero_re] at hD
    norm_num at hD
  have hid := normalized_difference c p (by omega) hc.2.1.ne' z w
  constructor
  · intro h
    have hzsq : z^2-w^2 = 0 := by
      have hprod : (z^2-w^2)*normalizedSecant c p z w = 0 := by
        rw [← hid,h,sub_self]
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
    · rw [h,sub_self,zero_mul]
    · rw [h,neg_sq,sub_self,zero_mul]

/-- The actual return is strictly decreasing on the whole positive
real interval reached by the full-parent second phase. -/
theorem actual_return_real_strictAnti {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    StrictAntiOn (fun t : ℝ => (normalizedReturn c p (t : ℂ)).re)
      (Icc (0 : ℝ) (3/2)) := by
  intro x hx y hy hxy
  have hxnorm : ‖(x : ℂ)‖ ≤ 3/2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hynorm : ‖(y : ℂ)‖ ≤ 3/2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2
  have hD := actual_secant_re_neg hp hc hynorm hxnorm
  have hid := congrArg Complex.re
    (normalized_difference c p (by omega) hc.2.1.ne' (y : ℂ) (x : ℂ))
  simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    sub_self,zero_mul,sub_zero] at hid
  have hsq : 0 < y^2-x^2 := by
    have hprod := mul_pos (sub_pos.mpr hxy) (show 0 < y+x by linarith [hx.1])
    nlinarith only [hprod]
  have hneg := mul_neg_of_pos_of_neg hsq (show
    (normalizedSecant c p (y : ℂ) (x : ℂ)).re < 0 by linarith)
  linarith only [hid,hneg]

end
end GlobalCrestEstimates
