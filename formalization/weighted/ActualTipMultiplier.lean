import ThreeReturnRealization

/-!
# Uniform repulsion of the actual signed terminal cycle

The derivative is that of the complete physical polynomial return.
The lower bound follows from the full divided difference and the three
actual phase positions; no derivative of a truncated model is substituted.
-/

namespace ActualTipMultiplier

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter LimitingCrest LimitingCrestPerturbation
open CriticalReturnRelationStability QuadraticCrestDividedDifference
open ThreeReturnDomain ThreeReturnDegree ThreeReturnEstimates ThreeReturnRealization

noncomputable section

private theorem parameter_data {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    c ∈ Icc (-2 : ℝ) 0 ∧ criticalValue c p ≤ 12/(4 : ℝ)^p := by
  have hb := parameter_band hp hc.1
  refine ⟨⟨hb.1,by linarith [hb.2]⟩,?_⟩
  simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1

private theorem model_zero_iterate (k : ℝ) (n : ℕ) :
    ((complexMap k)^[n]) 0 = (criticalOrbit k n : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',ih]
    simp only [criticalOrbit,Q,complexMap]
    push_cast
    rfl

/-- The actual third critical return has a fixed negative margin,
uniformly over the entire signed-tip parameter class. -/
theorem actual_third_coordinate_lt {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : (threeReturn c p 0).re < -(1/10 : ℝ) := by
  let k := kappa p c
  let ε := 24*scale p
  have hk : k ∈ parameterInterval := hc.2.2.2.1
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hk2 : k ≤ 2 := by linarith [hk.2]
  have hε : 0 ≤ ε := mul_nonneg (by norm_num) (scale_pos p).le
  have hεmax : ε ≤ 1/100000 := by
    dsimp [ε]
    linarith [scale_small hp]
  have hclose : ∀ z : ℂ, ‖z‖ ≤ 23/20 →
      ‖normalizedReturn c p z-complexMap k z‖ ≤ ε := by
    intro z hz
    simpa only [ε,k,kappa,scale,one_div_pow,mul_one_div] using
      normalized_return_error c p (by omega) hc.2.2.2.2.2.2 hc.2.1
        (parameter_data hp hc).2 z hz
  have hiter := iterate_perturbation_up_to_six
    (normalizedReturn c p) (complexMap k) 0 ε hε hεmax hclose
    (quadratic_disk_lipschitz k hk0 hk2)
    (fun n _ => quadratic_critical_orbit_unit k hk0 hk2 n)
  have h3 := (hiter 3 (by omega)).1
  have hr := (Complex.abs_re_le_norm
    (((normalizedReturn c p)^[3]) 0-((complexMap k)^[3]) 0)).trans h3
  rw [model_zero_iterate] at hr
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  rw [show errorCoefficient 3 = 31 by norm_num [errorCoefficient]] at hr
  have hmodel := (parameter_orbit_bounds hk).2.1
  have hb := (abs_le.mp hr).2
  change (threeReturn c p 0).re-criticalOrbit k 3 ≤ 31*ε at hb
  linarith

/-- The complete normalized secant has modulus greater than 7/4
throughout the whole disk used by all three phases. -/
theorem actual_secant_lower {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ}
    (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    (7/4 : ℝ) < ‖normalizedSecant c p z w‖ := by
  let a := quadraticCoefficient c (p-1)*criticalValue c p
  have he := normalizedSecant_error_small c p (by omega)
    (parameter_data hp hc).1 hc.2.1 (parameter_data hp hc).2 hz hw
  change ‖normalizedSecant c p z w-(a : ℂ)‖ ≤ 1/1000 at he
  have hk : -a ∈ parameterInterval := by
    simpa only [a,kappa,neg_mul] using hc.2.2.2.1
  have ha : a < 0 := by linarith [hk.1]
  have ht := norm_le_norm_sub_add (a : ℂ) (normalizedSecant c p z w)
  rw [norm_sub_rev (a : ℂ) (normalizedSecant c p z w),
    Complex.norm_real,Real.norm_eq_abs,abs_of_neg ha] at ht
  linarith [hk.1]

/-- The signed fixed point of the normalized three-return is uniformly
repelling, with a multiplier modulus greater than 3/2. -/
theorem actual_normalized_multiplier_gt {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (3/2 : ℝ) < ‖deriv (threeReturn c p) (-threeReturn c p 0)‖ := by
  let F := normalizedReturn c p
  let a := -threeReturn c p 0
  have haR : ‖a‖ ≤ 1/6 := by
    dsimp [a]
    rw [norm_neg]
    exact (actual_critical_value_bound hp hc).le
  have haL : (1/10 : ℝ) < ‖a‖ := by
    have hr := actual_third_coordinate_lt hp hc
    have hn := (abs_le.mp (Complex.abs_re_le_norm (threeReturn c p 0))).1
    dsimp [a]
    rw [norm_neg]
    linarith
  have hphase := actual_phase_bounds hp hc haR
  have hsign := actual_phase_signs hp hc haR
  have hfirst : (9/10 : ℝ) < ‖F a‖ := by
    have ht := norm_le_norm_sub_add (1 : ℂ) (F a)
    rw [norm_sub_rev (1 : ℂ) (F a),norm_one] at ht
    have he : ‖F a-1‖ < 51/1000 := hphase.1
    linarith
  have hsecond : (1/2 : ℝ) < ‖F (F a)‖ := by
    have hr := (abs_le.mp (Complex.abs_re_le_norm
      (F (F a)-((1-kappa p c : ℝ) : ℂ)))).2
    simp only [Complex.sub_re,Complex.ofReal_re] at hr
    have hl := (abs_le.mp (Complex.abs_re_le_norm (F (F a)))).1
    have he : ‖F (F a)-((1-kappa p c : ℝ) : ℂ)‖ < 19/100 := hphase.2.1
    have hk := hc.2.2.2.1.1
    change 17903/10000 ≤ kappa p c at hk
    linarith
  have hsec0 := actual_secant_lower hp hc (haR.trans (by norm_num))
    (haR.trans (by norm_num))
  have hsec1 := actual_secant_lower hp hc hsign.1 hsign.1
  have hsec2 := actual_secant_lower hp hc hsign.2.1 hsign.2.1
  have h0 := normalized_return_hasDerivAt c p (by omega) hc.2.1.ne' a
  have h1 := normalized_return_hasDerivAt c p (by omega) hc.2.1.ne' (F a)
  have h2 := normalized_return_hasDerivAt c p (by omega) hc.2.1.ne' (F (F a))
  have hthree := h2.comp a (h1.comp a h0)
  change HasDerivAt (threeReturn c p)
    ((2*F (F a)*normalizedSecant c p (F (F a)) (F (F a))) *
      ((2*F a*normalizedSecant c p (F a) (F a)) *
        (2*a*normalizedSecant c p a a))) a at hthree
  change (3/2 : ℝ) < ‖deriv (threeReturn c p) a‖
  rw [hthree.deriv]
  simp only [norm_mul,Complex.norm_two]
  have hlo : (2*(1/2 : ℝ)*(7/4)) *
      ((2*(9/10)*(7/4))*(2*(1/10)*(7/4))) ≤
      (2*‖F (F a)‖*‖normalizedSecant c p (F (F a)) (F (F a))‖) *
        ((2*‖F a‖*‖normalizedSecant c p (F a) (F a)‖) *
          (2*‖a‖*‖normalizedSecant c p a a‖)) := by
    gcongr
  linarith

/-- Linear conjugacy preserves the complete three-return multiplier.
The right side is differentiated in the original physical coordinate. -/
theorem physical_multiplier_eq (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0) (z : ℂ) :
    deriv ((quadraticMap c)^[3*p]) ((criticalValue c p : ℂ)*z) =
      deriv (threeReturn c p) z := by
  let d : ℂ := (criticalValue c p : ℂ)
  have hdC : d ≠ 0 := by dsimp [d]; exact_mod_cast hd
  have hlin : HasDerivAt (fun w : ℂ => d*w) d z := by
    simpa using (hasDerivAt_id z).const_mul d
  have hleft := ((physical_return_differentiable c p)
    (d*z)).hasDerivAt.comp z hlin
  have hF : Differentiable ℂ (normalizedReturn c p) :=
    fun w => (normalized_return_hasDerivAt c p hp hd w).differentiableAt
  have hH : Differentiable ℂ (threeReturn c p) := hF.iterate 3
  have hright := ((hH z).hasDerivAt).const_mul d
  have he : (fun w : ℂ => ((quadraticMap c)^[3*p]) (d*w)) =
      (fun w : ℂ => d*threeReturn c p w) := by
    funext w
    exact (normalized_iterate_scale c p hd 3 w).symm
  change HasDerivAt (fun w : ℂ => ((quadraticMap c)^[3*p]) (d*w))
    (deriv ((quadraticMap c)^[3*p]) (d*z)*d) z at hleft
  rw [he] at hleft
  have heq := hleft.unique hright
  rw [mul_comm _ d] at heq
  exact mul_left_cancel₀ hdC heq

/-- The literal physical periodic point has multiplier modulus greater
than 3/2 for every actual signed tip with return index at least seventeen. -/
theorem actual_physical_multiplier_gt {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (3/2 : ℝ) <
      ‖deriv ((quadraticMap c)^[3*p]) (-(criticalValue c (3*p) : ℂ))‖ := by
  have he := normalized_iterate_scale c p hc.2.1.ne' 3 (0 : ℂ)
  simp only [mul_zero,ThreeReturnParent.quadratic_iterate_zero] at he
  change (criticalValue c p : ℂ)*threeReturn c p 0 =
    (criticalValue c (3*p) : ℂ) at he
  have hpoint : (criticalValue c p : ℂ)*(-threeReturn c p 0) =
      -(criticalValue c (3*p) : ℂ) := by rw [mul_neg,he]
  rw [← hpoint,physical_multiplier_eq c p (by omega) hc.2.1.ne']
  exact actual_normalized_multiplier_gt hp hc

end
end ActualTipMultiplier
