import LimitingCrestQuadraticReturn
import LimitingCrestParameter

/-!
# Six-return shooting stability in the narrow crest coefficient chart

The signed collision relation is compared with the actual quadratic
iterate, including all nonlinear remainders. The endpoint signs and the
negative third return hold for every period at least seventeen.
-/

namespace CriticalReturnRelationStability

open Set Function
open LimitingCrest LimitingCrestPerturbation LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter

noncomputable section

private theorem errorCoefficient_six_bounds (n : ℕ) (hn : n ≤ 6) :
    0 ≤ errorCoefficient n ∧ errorCoefficient n ≤ 3906 := by
  interval_cases n <;> norm_num [errorCoefficient]

/-- Six complete compositions stay inside the disk on which the actual
map approximation is available. No perturbed orbit bound is assumed. -/
theorem iterate_perturbation_up_to_six
    (H Q : ℂ → ℂ) (z : ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hεmax : ε ≤ 1/100000)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 → ‖H w-Q w‖ ≤ ε)
    (hlip : ∀ v w : ℂ, ‖v‖ ≤ 23/20 → ‖w‖ ≤ 23/20 →
      ‖Q v-Q w‖ ≤ 5*‖v-w‖)
    (hmodel : ∀ n : ℕ, n ≤ 6 → ‖(Q^[n]) z‖ ≤ 1) :
    ∀ n : ℕ, n ≤ 6 →
      ‖(H^[n]) z-(Q^[n]) z‖ ≤ errorCoefficient n*ε ∧
      ‖(H^[n]) z‖ ≤ 23/20 := by
  intro n
  induction n with
  | zero =>
    intro hn
    refine ⟨by simp [errorCoefficient], ?_⟩
    have h := hmodel 0 (by omega)
    simpa only [iterate_zero, id_eq] using h.trans (by norm_num : (1 : ℝ) ≤ 23/20)
  | succ n ih =>
    intro hn
    have hn6 : n ≤ 6 := by omega
    obtain ⟨herr,hHdisk⟩ := ih hn6
    have hQdisk : ‖(Q^[n]) z‖ ≤ 23/20 := (hmodel n hn6).trans (by norm_num)
    have hnext : ‖(H^[n+1]) z-(Q^[n+1]) z‖ ≤ errorCoefficient (n+1)*ε := by
      rw [iterate_succ_apply',iterate_succ_apply']
      calc
        ‖H ((H^[n]) z)-Q ((Q^[n]) z)‖ ≤
            ‖H ((H^[n]) z)-Q ((H^[n]) z)‖+
              ‖Q ((H^[n]) z)-Q ((Q^[n]) z)‖ := by
                simpa only [dist_eq_norm] using
                  dist_triangle (H ((H^[n]) z)) (Q ((H^[n]) z)) (Q ((Q^[n]) z))
        _ ≤ ε+5*(errorCoefficient n*ε) :=
          add_le_add (hclose _ hHdisk)
            ((hlip _ _ hHdisk hQdisk).trans
              (mul_le_mul_of_nonneg_left herr (by norm_num)))
        _ = errorCoefficient (n+1)*ε := by simp only [errorCoefficient]; ring
    refine ⟨hnext,?_⟩
    have hb := errorCoefficient_six_bounds (n+1) hn
    have hemax : errorCoefficient (n+1)*ε ≤ 3906/100000 := by
      calc
        errorCoefficient (n+1)*ε ≤ 3906*ε := mul_le_mul_of_nonneg_right hb.2 hε
        _ ≤ 3906/100000 := by linarith
    have htri : ‖(H^[n+1]) z‖ ≤
        ‖(H^[n+1]) z-(Q^[n+1]) z‖+‖(Q^[n+1]) z‖ := by
      simpa only [dist_eq_norm,sub_zero] using
        dist_triangle ((H^[n+1]) z) ((Q^[n+1]) z) (0 : ℂ)
    linarith [hmodel (n+1) hn]

private theorem model_iterate_real (k : ℝ) (n : ℕ) :
    ((complexMap k)^[n]) 0 = (criticalOrbit k n : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',ih]
    simp only [criticalOrbit,Q,complexMap]
    push_cast
    rfl

private theorem power_seventeen {p : ℕ} (hp : 17 ≤ p) :
    (17179869184 : ℝ) ≤ (4 : ℝ)^p := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
  norm_num at h
  exact h

/-- The exact normalized third-plus-sixth relation differs from the
limiting relation by at most 94488 divided by 4^p. -/
theorem actual_signed_relation_error (c : ℝ) (p : ℕ) (hp : 17 ≤ p)
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000)) :
    |(((normalizedReturn c p)^[6]) 0).re+
      (((normalizedReturn c p)^[3]) 0).re-
        relation (-quadraticCoefficient c (p-1)*criticalValue c p)| ≤
          94488/(4 : ℝ)^p := by
  let k := -quadraticCoefficient c (p-1)*criticalValue c p
  let ε : ℝ := 24/(4 : ℝ)^p
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hεmax : ε ≤ 1/100000 := by
    dsimp [ε]
    apply (div_le_iff₀ (show (0 : ℝ) < 4^p by positivity)).mpr
    linarith [power_seventeen hp]
  have hk0 : 0 ≤ k := by dsimp [k]; linarith [hk.1]
  have hk2 : k ≤ 2 := by dsimp [k]; linarith [hk.2]
  have hclose := normalized_return_error c p (by omega) hcrit hd hsmall
  have hiter := iterate_perturbation_up_to_six (normalizedReturn c p) (complexMap k)
    0 ε hε0 hεmax hclose (quadratic_disk_lipschitz k hk0 hk2)
    (fun n _ => quadratic_critical_orbit_unit k hk0 hk2 n)
  have h6 := (hiter 6 (by omega)).1
  have h3 := (hiter 3 (by omega)).1
  have hr6 := (Complex.abs_re_le_norm
    (((normalizedReturn c p)^[6]) 0-((complexMap k)^[6]) 0)).trans h6
  have hr3 := (Complex.abs_re_le_norm
    (((normalizedReturn c p)^[3]) 0-((complexMap k)^[3]) 0)).trans h3
  rw [model_iterate_real] at hr6 hr3
  simp only [Complex.sub_re,Complex.ofReal_re] at hr6 hr3
  rw [show errorCoefficient 6 = 3906 by norm_num [errorCoefficient]] at hr6
  rw [show errorCoefficient 3 = 31 by norm_num [errorCoefficient]] at hr3
  have ht := abs_add_le
    ((((normalizedReturn c p)^[6]) 0).re-criticalOrbit k 6)
    ((((normalizedReturn c p)^[3]) 0).re-criticalOrbit k 3)
  have heq : (((normalizedReturn c p)^[6]) 0).re+
      (((normalizedReturn c p)^[3]) 0).re-relation k =
        ((((normalizedReturn c p)^[6]) 0).re-criticalOrbit k 6)+
        ((((normalizedReturn c p)^[3]) 0).re-criticalOrbit k 3) := by
    unfold relation
    ring
  change |(((normalizedReturn c p)^[6]) 0).re+
      (((normalizedReturn c p)^[3]) 0).re-relation k| ≤ _
  rw [heq]
  calc
    _ ≤ |(((normalizedReturn c p)^[6]) 0).re-criticalOrbit k 6|+
        |(((normalizedReturn c p)^[3]) 0).re-criticalOrbit k 3| := ht
    _ ≤ 3906*ε+31*ε := add_le_add hr6 hr3
    _ = 94488/(4 : ℝ)^p := by dsimp [ε]; ring

private theorem actual_iterate_real (c t : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (t : ℂ) =
      (((fun x : ℝ => x^2+c)^[n]) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',ih]
    simp only [quadraticMap,Complex.ofReal_add,Complex.ofReal_pow]

/-- Multiplication by the positive critical return carries the signed
normalized relation to the literal polynomial collision relation. -/
theorem actual_signed_relation_scale (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0) :
    criticalValue c (6*p)+criticalValue c (3*p) =
      criticalValue c p * ((((normalizedReturn c p)^[6]) 0).re+
        (((normalizedReturn c p)^[3]) 0).re) := by
  have h6 := normalized_iterate_scale c p hd 6 (0 : ℂ)
  have h3 := normalized_iterate_scale c p hd 3 (0 : ℂ)
  simp only [mul_zero] at h6 h3
  have hcritical6 : ((quadraticMap c)^[6*p]) (0 : ℂ) =
      (criticalValue c (6*p) : ℂ) := actual_iterate_real c 0 (6*p)
  have hcritical3 : ((quadraticMap c)^[3*p]) (0 : ℂ) =
      (criticalValue c (3*p) : ℂ) := actual_iterate_real c 0 (3*p)
  rw [hcritical6] at h6
  rw [hcritical3] at h3
  have hr6 := congrArg Complex.re h6
  have hr3 := congrArg Complex.re h3
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr6 hr3
  change criticalValue c p * (((normalizedReturn c p)^[6]) 0).re =
    criticalValue c (6*p) at hr6
  change criticalValue c p * (((normalizedReturn c p)^[3]) 0).re =
    criticalValue c (3*p) at hr3
  nlinarith

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem narrow_model_endpoint_margins :
    relation (17903/10000) < -1/10000 ∧
      1/10000 < relation (17904/10000) := by
  norm_num [relation,criticalOrbit,Q]

theorem actual_relation_negative (c : ℝ) (p : ℕ) (hp : 17 ≤ p)
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p = 17903/10000) :
    criticalValue c (6*p)+criticalValue c (3*p) < 0 := by
  have he := actual_signed_relation_error c p hp hcrit hd hsmall
    (show -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000) by rw [hk]; constructor <;> norm_num)
  rw [hk] at he
  have herr : 94488/(4 : ℝ)^p < 1/10000 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < 4^p by positivity)).mpr
    linarith [power_seventeen hp]
  have hr := (abs_le.mp he).2
  have hsign : (((normalizedReturn c p)^[6]) 0).re+
      (((normalizedReturn c p)^[3]) 0).re < 0 := by
    linarith [narrow_model_endpoint_margins.1]
  rw [actual_signed_relation_scale c p hd.ne']
  exact mul_neg_of_pos_of_neg hd hsign

theorem actual_relation_positive (c : ℝ) (p : ℕ) (hp : 17 ≤ p)
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p = 17904/10000) :
    0 < criticalValue c (6*p)+criticalValue c (3*p) := by
  have he := actual_signed_relation_error c p hp hcrit hd hsmall
    (show -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000) by rw [hk]; constructor <;> norm_num)
  rw [hk] at he
  have herr : 94488/(4 : ℝ)^p < 1/10000 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < 4^p by positivity)).mpr
    linarith [power_seventeen hp]
  have hr := (abs_le.mp he).1
  have hsign : 0 < (((normalizedReturn c p)^[6]) 0).re+
      (((normalizedReturn c p)^[3]) 0).re := by
    linarith [narrow_model_endpoint_margins.2]
  rw [actual_signed_relation_scale c p hd.ne']
  exact mul_pos hd hsign

/-- The narrow coefficient chart forces the strict negative third
return, excluding the zero-return collision branch. -/
theorem actual_third_return_negative (c : ℝ) (p : ℕ) (hp : 17 ≤ p)
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000)) :
    criticalValue c (3*p) < 0 := by
  let k := -quadraticCoefficient c (p-1)*criticalValue c p
  let ε : ℝ := 24/(4 : ℝ)^p
  have hk0 : 0 ≤ k := by dsimp [k]; linarith [hk.1]
  have hk2 : k ≤ 2 := by dsimp [k]; linarith [hk.2]
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hεmax : ε ≤ 1/100000 := by
    dsimp [ε]
    apply (div_le_iff₀ (show (0 : ℝ) < 4^p by positivity)).mpr
    linarith [power_seventeen hp]
  have hiter := iterate_perturbation_up_to_six (normalizedReturn c p) (complexMap k)
    0 ε hε0 hεmax (normalized_return_error c p (by omega) hcrit hd hsmall)
    (quadratic_disk_lipschitz k hk0 hk2)
    (fun n _ => quadratic_critical_orbit_unit k hk0 hk2 n)
  have h3 := (hiter 3 (by omega)).1
  have hr := (Complex.abs_re_le_norm
    (((normalizedReturn c p)^[3]) 0-((complexMap k)^[3]) 0)).trans h3
  rw [model_iterate_real] at hr
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  rw [show errorCoefficient 3 = 31 by norm_num [errorCoefficient]] at hr
  have hmodel : criticalOrbit k 3 < -(118/1000) := (parameter_orbit_bounds hk).2.1
  have hsign : (((normalizedReturn c p)^[3]) 0).re < 0 := by
    have hle := (abs_le.mp hr).2
    have hmax : ε ≤ 1/100000 := hεmax
    linarith only [hle, hmax, hmodel]
  have hscale := normalized_iterate_scale c p hd.ne' 3 (0 : ℂ)
  simp only [mul_zero] at hscale
  have hcritical : ((quadraticMap c)^[3*p]) (0 : ℂ) =
      (criticalValue c (3*p) : ℂ) := actual_iterate_real c 0 (3*p)
  rw [hcritical] at hscale
  have hrscale := congrArg Complex.re hscale
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hrscale
  change criticalValue c p * (((normalizedReturn c p)^[3]) 0).re =
    criticalValue c (3*p) at hrscale
  rw [← hrscale]
  exact mul_neg_of_pos_of_neg hd hsign

end

end CriticalReturnRelationStability
