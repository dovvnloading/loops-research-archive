import LimitingCrestParameter
import NearTwoShooting
import CriticalReturnRelationStability

/-!
# Actual all-period signed tips and convergence of their normalized coefficients

The positive inverse shooting chart supplies literal quadratic parameters.
The signed collision is then imposed by a second intermediate-value argument.
-/

namespace NearTwoTip

open Set Function
open LoopsLimitingCrestParameter
open NearTwoShooting LimitingCrestQuadraticReturn CriticalReturnRelationStability
noncomputable section

/-- The already certified transverse model relation has an explicit inverse
modulus throughout the whole parameter interval. -/
theorem model_parameter_error_bound {k k₀ ε : ℝ}
    (hk : k ∈ parameterInterval) (hk₀ : k₀ ∈ parameterInterval)
    (hzero : relation k₀ = 0) (herror : |relation k| ≤ ε) :
    |k-k₀| ≤ ε/6 := by
  have hd (t : ℝ) : HasDerivAt (fun s => relation s-6*s)
      (criticalSlope t 6+criticalSlope t 3-6) t := by
    convert (relation_hasDerivAt t).sub ((hasDerivAt_id t).const_mul (6 : ℝ)) using 1
    all_goals first | rfl | simp
  have hcont : Continuous (fun t => relation t-6*t) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hm : StrictMonoOn (fun t => relation t-6*t) parameterInterval := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hcont.continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have h := relation_slope_gt_six (interior_subset ht)
    linarith only [h]
  rcases le_total k k₀ with hle | hle
  · have h := hm.monotoneOn hk hk₀ hle
    rw [hzero] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hb := (abs_le.mp herror).1
    linarith only [h,hb]
  · have h := hm.monotoneOn hk₀ hk hle
    rw [hzero] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    have hb := (abs_le.mp herror).2
    linarith only [h,hb]

def ActualTip (p : ℕ) (c : ℝ) : Prop :=
  c ∈ Icc (-2 : ℝ) (-2+20*scale p) ∧
  0 < criticalValue c p ∧ criticalValue c p ≤ 12*scale p ∧
  kappa p c ∈ parameterInterval ∧
  criticalValue c (6*p)+criticalValue c (3*p) = 0 ∧
  criticalValue c (3*p) < 0 ∧
  (∀ j ≤ p, |criticalValue c j| ≤ 2)

/-- A literal quadratic parameter is constructed for every p at least
seventeen. Its signed six-versus-three return relation, positive return
scale, and sharp normalized coefficient are all proved together. -/
theorem exists_actual_tip (p : ℕ) (hp : 17 ≤ p) : ∃ c : ℝ, ActualTip p c := by
  obtain ⟨a,b,h⟩ := exists_sharp_chart p hp
  let F : ℝ → ℝ := fun c => criticalValue c (6*p)+criticalValue c (3*p)
  have hF : Continuous F := (continuous_criticalValue (6*p)).add (continuous_criticalValue (3*p))
  have ha : a ∈ Icc a b := left_mem_Icc.mpr h.ordered.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr h.ordered.le
  have hs {c : ℝ} (hc : c ∈ Icc a b) : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    have hh := (h.return_range c hc).2
    simpa only [scale,one_div_pow,mul_one_div] using hh
  have hpos : 0 < F a := actual_relation_positive a p hp
    (SharpChart.critical_orbit_bound hp h ha) (h.return_range a ha).1 (hs ha) h.left_coefficient
  have hneg : F b < 0 := actual_relation_negative b p hp
    (SharpChart.critical_orbit_bound hp h hb) (h.return_range b hb).1 (hs hb) h.right_coefficient
  obtain ⟨c,hc,hzero⟩ := intermediate_value_Icc' h.ordered.le hF.continuousOn
    (show (0 : ℝ) ∈ Icc (F b) (F a) from ⟨hneg.le,hpos.le⟩)
  refine ⟨c,h.parameter_range c hc,(h.return_range c hc).1,(h.return_range c hc).2,
    h.coefficient_range hc,hzero,?_,SharpChart.critical_orbit_bound hp h hc⟩
  exact actual_third_return_negative c p hp (SharpChart.critical_orbit_bound hp h hc)
    (h.return_range c hc).1 (hs hc) (h.coefficient_range hc)

/-- The normalized coefficient of every constructed actual signed tip is
within an explicit exponentially small distance of the unique model root. -/
theorem actual_tip_coefficient_error {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0) :
    |kappa p c-k₀| ≤ 15748*scale p := by
  obtain ⟨hpar,hd,hsmall,hk,hzero,hthird,hcrit⟩ := hc
  have hsmall' : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hsmall
  have he := actual_signed_relation_error c p hp hcrit hd hsmall' hk
  have hscale := actual_signed_relation_scale c p hd.ne'
  rw [hzero] at hscale
  have hsum : (((normalizedReturn c p)^[6]) 0).re+
      (((normalizedReturn c p)^[3]) 0).re = 0 := by
    have hm : criticalValue c p * ((((normalizedReturn c p)^[6]) 0).re+
      (((normalizedReturn c p)^[3]) 0).re) = 0 := hscale.symm
    exact (mul_eq_zero.mp hm).resolve_left hd.ne'
  rw [hsum,zero_sub,abs_neg] at he
  have hm := model_parameter_error_bound hk hk₀ hroot he
  change |kappa p c-k₀| ≤ _ at hm
  have harith : (94488/(4 : ℝ)^p)/6 = 15748/(4 : ℝ)^p := by ring
  rw [harith] at hm
  simpa only [scale,one_div_pow,mul_one_div] using hm

/-- The model coefficient and the all-period actual parameters are
constructed in the same theorem, with no assumed return-scale or
quadratic-coefficient inequalities. -/
theorem exists_actual_tips_with_coefficient_limit :
    ∃ k₀ : ℝ, k₀ ∈ parameterInterval ∧ relation k₀ = 0 ∧
      ∀ p : ℕ, 17 ≤ p → ∃ c : ℝ, ActualTip p c ∧
        |kappa p c-k₀| ≤ 15748*scale p := by
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := exists_unique_limiting_parameter
  refine ⟨k₀,hk₀,hroot,?_⟩
  intro p hp
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  exact ⟨c,hc,actual_tip_coefficient_error hp hc hk₀ hroot⟩

/-- The original p-th iterate at the constructed signed tip has a crest
crossing on every radius of the certified interval. This discharges the
real-parameter premises of the archived conditional corridor theorem. -/
theorem exists_actual_tip_corridor (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧
      ∀ s ∈ Icc (63/1000 : ℝ) (33/500), ∃ z : ℂ,
        ‖z+((3*criticalValue c p/4 : ℝ) : ℂ)‖ = criticalValue c p*s ∧
        (((quadraticMap c)^[p]) z).re = 0 ∧
        0 < (((quadraticMap c)^[p]) z).im ∧
        (((quadraticMap c)^[2*p]) z).im = 0 ∧
        (((quadraticMap c)^[3*p]) z).im = 0 ∧
        -criticalValue c p < (((quadraticMap c)^[3*p]) z).re ∧
        (((quadraticMap c)^[3*p]) z).re < -criticalValue c (4*p) := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  refine ⟨c,hc,?_⟩
  intro s hs
  have hband := parameter_band hp hc.1
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1
  exact unscaled_quadratic_corridor c p (by omega)
    ⟨hband.1,by linarith [hband.2]⟩ hc.2.1 hsmall hc.2.2.2.1 hs

end
end NearTwoTip
