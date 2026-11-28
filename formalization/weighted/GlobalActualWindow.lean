import GlobalRestrictiveWindow
import NearTwoTip

/-!
# The archived actual signed tips lie in the global restrictive class

The interval and phase hypotheses are derived for every actual signed tip.
The argument uses the complete quadratic iterates, including every
intermediate phase, and the already proved full normalized remainder.
-/

namespace GlobalActualWindow

open Set Function
open NearTwoInverse NearTwoShooting LimitingCrestQuadraticReturn
open GlobalRestrictiveWindow NearTwoTip

noncomputable section

private theorem scale_identity (p : ℕ) : (4 : ℝ)^p * scale p = 1 := by
  unfold scale
  rw [← mul_pow]
  norm_num

private theorem critical_deficit {c : ℝ} (hc : -2 ≤ c) :
    ∀ j : ℕ, 2 ≤ j →
      2-criticalValue c j ≤ 3*(4 : ℝ)^(j-2)*(c+2) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    rw [criticalValue_two]
    norm_num
    nlinarith [sq_nonneg (c+2)]
  | succ n hn ih =>
    have hpow : (4 : ℝ)^(n+1-2) = 4*(4 : ℝ)^(n-2) := by
      rw [show n+1-2 = (n-2)+1 by omega, pow_succ]
      ring
    have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 4)
    rw [criticalValue_step, hpow]
    nlinarith only [hm, sq_nonneg (criticalValue c n-2), hc]

/-- The near-endpoint parameter bound forces a positive physical margin
at every intermediate critical phase, independently of a supplied chart. -/
theorem actual_critical_phase_lower {p j : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (hj : 2 ≤ j) (hjp : j < p) :
    17/16 ≤ criticalValue c j := by
  have hdef := critical_deficit hc.1.1 j hj
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
    (show j-2 ≤ p-3 by omega)
  have heps : 0 ≤ c+2 := by linarith [hc.1.1]
  have hmul := mul_le_mul_of_nonneg_right hpow heps
  have hupper := mul_le_mul_of_nonneg_left
    (show c+2 ≤ 20*scale p by linarith [hc.1.2])
    (show (0 : ℝ) ≤ (4 : ℝ)^(p-3) by positivity)
  have hid := scale_identity p
  have hpowp : (4 : ℝ)^p = (4 : ℝ)^(p-3)*64 := by
    calc
      (4 : ℝ)^p = (4 : ℝ)^((p-3)+3) := by congr 1; omega
      _ = (4 : ℝ)^(p-3)*64 := by rw [pow_add]; norm_num
  rw [hpowp] at hid
  nlinarith only [hdef, hmul, hupper, hid]

private def orbitError (p : ℕ) (c : ℝ) (j : ℕ) : ℝ :=
  (4 : ℝ)^j * (criticalValue c p)^2 / 4

private theorem error_bound {p j : ℕ} {c : ℝ} (hc : ActualTip p c)
    (hj : j ≤ p) : orbitError p c j ≤ 36*scale p := by
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj
  have hsquare := pow_le_pow_left₀ hc.2.1.le hc.2.2.1 2
  have hm := mul_le_mul hpow hsquare (sq_nonneg (criticalValue c p))
    (show (0 : ℝ) ≤ (4 : ℝ)^p by positivity)
  have hid : (4 : ℝ)^p * (12*scale p)^2 = 144*scale p := by
    calc
      (4 : ℝ)^p * (12*scale p)^2 =
          144*((4 : ℝ)^p*scale p)*scale p := by ring
      _ = 144*scale p := by rw [scale_identity]; ring
  unfold orbitError
  linarith only [hm, hid]

private theorem error_succ (p : ℕ) (c : ℝ) (j : ℕ) :
    orbitError p c (j+1) = 4*orbitError p c j := by
  unfold orbitError
  rw [pow_succ]
  ring

private theorem square_bound {d x : ℝ} (hx : x ∈ Icc (-d) d) : x^2 ≤ d^2 := by
  have hm := mul_nonneg (show 0 ≤ d-x by linarith [hx.2])
    (show 0 ≤ d+x by linarith [hx.1])
  nlinarith only [hm]

private theorem initial_negative {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : ActualTip p c) (hx : x ∈ returnInterval c p) : realMap c x < 0 := by
  have hband := parameter_band hp hc.1
  have hq := scale_small hp
  have hd := hc.2.1
  have hsmall := hc.2.2.1
  have hs := square_bound hx
  have hdone : criticalValue c p ≤ 1/100 := by linarith
  have hdsquare := pow_le_pow_left₀ hd.le hdone 2
  dsimp [realMap]
  nlinarith [hband.2, hdsquare]

private theorem interval_orbit_bound {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : ActualTip p c) (hx : x ∈ returnInterval c p) :
    ∀ j : ℕ, 2 ≤ j → j ≤ p →
      0 ≤ criticalValue c j - (realMap c)^[j] x ∧
      criticalValue c j - (realMap c)^[j] x ≤ orbitError p c j ∧
      (j < p → 0 < (realMap c)^[j] x) := by
  have hq := scale_small hp
  have hs := square_bound hx
  have hfirst := initial_negative hp hc hx
  have hfirstlow : -2 ≤ realMap c x := by
    dsimp [realMap]
    nlinarith [hc.1.1, sq_nonneg x]
  have hband := parameter_band hp hc.1
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro hjp
    have hfac : 0 ≤ -c-realMap c x ∧ -c-realMap c x ≤ 4 := by
      constructor <;> linarith [hband.1, hband.2]
    have hid : criticalValue c 2 - (realMap c)^[2] x =
        (-c-realMap c x)*x^2 := by
      rw [criticalValue_two]
      change c^2+c-((x^2+c)^2+c)=(-c-(x^2+c))*x^2
      ring
    have hlo : 0 ≤ criticalValue c 2 - (realMap c)^[2] x := by
      rw [hid]
      exact mul_nonneg hfac.1 (sq_nonneg x)
    have hup : criticalValue c 2 - (realMap c)^[2] x ≤ orbitError p c 2 := by
      rw [hid]
      have hm := mul_le_mul hfac.2 hs (sq_nonneg x) (by norm_num : (0 : ℝ) ≤ 4)
      norm_num [orbitError] <;> nlinarith only [hm]
    refine ⟨hlo, hup, ?_⟩
    intro hlt
    have he := error_bound hc hjp
    have hlow := actual_critical_phase_lower hp hc le_rfl hlt
    linarith
  | succ n hn ih =>
    intro hnp
    obtain ⟨hlo,hup,hphase⟩ := ih (by omega)
    have hpos := hphase (by omega)
    have hcn := actual_critical_phase_lower hp hc hn (by omega)
    have hcu : criticalValue c n ≤ 2 :=
      (le_abs_self _).trans (hc.2.2.2.2.2.2 n (by omega))
    have hsum : 0 ≤ criticalValue c n + (realMap c)^[n] x ∧
        criticalValue c n + (realMap c)^[n] x ≤ 4 := by
      constructor <;> linarith
    have hid : criticalValue c (n+1) - (realMap c)^[n+1] x =
        (criticalValue c n + (realMap c)^[n] x) *
          (criticalValue c n - (realMap c)^[n] x) := by
      rw [criticalValue_step, Function.iterate_succ_apply']
      dsimp [realMap]
      ring
    have hlo' : 0 ≤ criticalValue c (n+1) - (realMap c)^[n+1] x := by
      rw [hid]
      exact mul_nonneg hsum.1 hlo
    have hup' : criticalValue c (n+1) - (realMap c)^[n+1] x ≤
        orbitError p c (n+1) := by
      rw [hid, error_succ]
      exact mul_le_mul hsum.2 hup hlo (by norm_num : (0 : ℝ) ≤ 4)
    refine ⟨hlo', hup', ?_⟩
    intro hlt
    have he := error_bound hc hnp
    have hlow := actual_critical_phase_lower hp hc (by omega) hlt
    linarith

private theorem complex_iterate_real (c x : ℝ) (n : ℕ) :
    (quadraticMap c)^[n] (x : ℂ) = (((realMap c)^[n] x : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [quadraticMap, realMap, Complex.ofReal_add, Complex.ofReal_pow]

private theorem normalized_real_value (c t : ℝ) (p : ℕ) :
    normalizedReturn c p (t : ℂ) =
      ((((realMap c)^[p] (criticalValue c p*t))/criticalValue c p : ℝ) : ℂ) := by
  unfold normalizedReturn
  rw [← Complex.ofReal_mul, complex_iterate_real, Complex.ofReal_div]

private theorem lower_return {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : ActualTip p c) (hx : x ∈ returnInterval c p) :
    -criticalValue c p < (realMap c)^[p] x := by
  let d := criticalValue c p
  let t := x/d
  have hd : 0 < d := hc.2.1
  have ht : t ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      simpa only [neg_one_mul] using hx.1
    · apply (div_le_iff₀ hd).mpr
      simpa only [one_mul] using hx.2
  have htabs := abs_le.mpr ht
  have htNorm : ‖(t : ℂ)‖ ≤ 23/20 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have he := normalized_return_error c p (by omega) hc.2.2.2.2.2.2 hc.2.1 hsmall t htNorm
  have hinput : criticalValue c p*t = x := by
    dsimp [t,d]
    field_simp [hc.2.1.ne'] <;> ring
  rw [normalized_real_value, hinput] at he
  change ‖((((realMap c)^[p] x/d : ℝ) : ℂ) -
    LimitingCrest.complexMap (kappa p c) (t : ℂ))‖ ≤ 24/(4 : ℝ)^p at he
  have hid : ((((realMap c)^[p] x/d : ℝ) : ℂ) -
      LimitingCrest.complexMap (kappa p c) (t : ℂ)) =
      ((((realMap c)^[p] x/d-(1-kappa p c*t^2) : ℝ)) : ℂ) := by
    simp only [LimitingCrest.complexMap, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hid, Complex.norm_real, Real.norm_eq_abs] at he
  have he' : |(realMap c)^[p] x/d-(1-kappa p c*t^2)| ≤ 24*scale p := by
    simpa only [scale, one_div_pow, mul_one_div] using he
  have htsquare : t^2 ≤ 1 := by
    have hm := mul_nonneg (show 0 ≤ 1-t by linarith [ht.2])
      (show 0 ≤ 1+t by linarith [ht.1])
    nlinarith only [hm]
  have hk := hc.2.2.2.1
  have hkpos : 0 ≤ kappa p c := by linarith [hk.1]
  have hmul := mul_le_mul_of_nonneg_left htsquare hkpos
  have hq := scale_small hp
  have hquot : -1 < (realMap c)^[p] x/d := by
    have herr := (abs_le.mp he').1
    nlinarith [hk.2]
  have hphys := (lt_div_iff₀ hd).mp hquot
  dsimp [d] at hphys
  linarith only [hphys]

/-- Every archived actual signed tip supplies the full literal
restrictive-interval geometry used by the global localization theorem.
No additional itinerary or invariant-interval premise is required. -/
theorem actual_tip_restrictive_return {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : PositiveRestrictiveReturn c p := by
  have hband := parameter_band hp hc.1
  refine {
    parameter_band := ⟨hband.1, by linarith [hband.2]⟩
    return_pos := hc.2.1
    negative_first := fun x hx => initial_negative hp hc hx
    positive_phases := ?_
    invariant := ?_ }
  · intro j hj hjp x hx
    exact (interval_orbit_bound hp hc hx j hj hjp.le).2.2 hjp
  · intro x hx
    have hlo := lower_return hp hc hx
    have hup := (interval_orbit_bound hp hc hx p (by omega) le_rfl).1
    exact ⟨hlo.le, by linarith⟩

end

end GlobalActualWindow
