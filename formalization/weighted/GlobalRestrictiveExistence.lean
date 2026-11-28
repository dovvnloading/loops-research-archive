import GlobalRestrictiveWindow

/-!
# Unconditional physical witnesses for the global restrictive class

For every period at least seventeen, inverse shooting selects an actual
quadratic parameter with critical return exactly 4^(-p).  Whole-interval
estimates then prove every clause of the global restrictive-return class.
This is a nonvacuity theorem; no signed-tip relation is asserted here.
-/

namespace GlobalRestrictiveExistence

open Set Function
open NearTwoInverse NearTwoShooting LimitingCrestQuadraticReturn
open GlobalRestrictiveWindow

noncomputable section

private def orbitError (p j : ℕ) : ℝ := (4 : ℝ)^j * (scale p)^2 / 4

private theorem scale_identity (p : ℕ) : (4 : ℝ)^p * scale p = 1 := by
  unfold scale
  rw [← mul_pow]
  norm_num

private theorem error_bound {p j : ℕ} (hj : j ≤ p) :
    orbitError p j ≤ scale p / 4 := by
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj
  have hm := mul_le_mul_of_nonneg_right hpow (sq_nonneg (scale p))
  have hi := scale_identity p
  have he : (4 : ℝ)^p * (scale p)^2 = scale p := by
    calc
      (4 : ℝ)^p * (scale p)^2 = ((4 : ℝ)^p * scale p) * scale p := by ring
      _ = scale p := by rw [hi, one_mul]
  unfold orbitError
  linarith only [hm, he]

private theorem error_succ (p j : ℕ) :
    orbitError p (j+1) = 4 * orbitError p j := by
  unfold orbitError
  rw [pow_succ]
  ring

private theorem square_bound {q x : ℝ} (hq : 0 ≤ q)
    (hx : x ∈ Icc (-q) q) : x^2 ≤ q^2 := by
  have hm := mul_nonneg (show 0 ≤ q-x by linarith [hx.2])
    (show 0 ≤ q+x by linarith [hx.1])
  nlinarith only [hm]

private theorem initial_negative {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25))
    (hx : x ∈ Icc (-scale p) (scale p)) : realMap c x < 0 := by
  have hq := scale_small hp
  have hq0 := (scale_pos p).le
  have hs := square_bound hq0 hx
  have hq1 : scale p ≤ 1 := by linarith
  have hsq := mul_le_mul_of_nonneg_left hq1 hq0
  dsimp [realMap]
  nlinarith [hc.2]

private theorem interval_orbit_bound {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25))
    (hcrit : ∀ j : ℕ, 2 ≤ j → j ≤ p →
      scale p ≤ criticalValue c j ∧ criticalValue c j ≤ 2)
    (hx : x ∈ Icc (-scale p) (scale p)) :
    ∀ j : ℕ, 2 ≤ j → j ≤ p →
      0 ≤ criticalValue c j - (realMap c)^[j] x ∧
      criticalValue c j - (realMap c)^[j] x ≤ orbitError p j ∧
      0 < (realMap c)^[j] x := by
  have hq0 := scale_pos p
  have hs := square_bound hq0.le hx
  have hfirst := initial_negative hp hc hx
  have hfirstlow : -2 ≤ realMap c x := by
    dsimp [realMap]
    nlinarith [hc.1, sq_nonneg x]
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro hjp
    have hfac : 0 ≤ -c-realMap c x ∧ -c-realMap c x ≤ 4 := by
      constructor <;> linarith [hc.1, hc.2]
    have hid : criticalValue c 2 - (realMap c)^[2] x =
        (-c-realMap c x)*x^2 := by
      rw [criticalValue_two]
      change c^2+c-((x^2+c)^2+c)=(-c-(x^2+c))*x^2
      ring
    have hlo : 0 ≤ criticalValue c 2 - (realMap c)^[2] x := by
      rw [hid]
      exact mul_nonneg hfac.1 (sq_nonneg x)
    have hup : criticalValue c 2 - (realMap c)^[2] x ≤ orbitError p 2 := by
      rw [hid]
      have hm := mul_le_mul hfac.2 hs (sq_nonneg x) (by norm_num : (0 : ℝ) ≤ 4)
      norm_num [orbitError] <;> nlinarith only [hm]
    refine ⟨hlo, hup, ?_⟩
    have he := error_bound (p := p) (j := 2) hjp
    have hlow := (hcrit 2 le_rfl hjp).1
    linarith
  | succ n hn ih =>
    intro hnp
    obtain ⟨hlo,hup,hpos⟩ := ih (by omega)
    have hcn := hcrit n hn (by omega)
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
        orbitError p (n+1) := by
      rw [hid, error_succ]
      exact mul_le_mul hsum.2 hup hlo (by norm_num : (0 : ℝ) ≤ 4)
    refine ⟨hlo', hup', ?_⟩
    have he := error_bound (p := p) (j := n+1) hnp
    have hlow := (hcrit (n+1) (by omega) hnp).1
    linarith

/-- Every period at least seventeen has an actual global restrictive
return, with the exact prescribed physical critical scale 4^(-p).
The parameter, invariant interval and all intermediate phase signs are
constructed, so the hypotheses of the global localization are nonempty. -/
theorem exists_positive_restrictive_return (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, PositiveRestrictiveReturn c p ∧ criticalValue c p = scale p := by
  have hq0 := scale_pos p
  have hq := scale_small hp
  have hd : scale p ∈ Icc (0 : ℝ) (12*scale p) :=
    ⟨hq0.le, by linarith⟩
  obtain ⟨c,⟨hband,hshoot⟩,_⟩ := unique_shooting_parameter hp hd
  have hc := parameter_band hp hband
  have hd2 : scale p ∈ Icc (0 : ℝ) 2 := ⟨hq0.le, by linarith⟩
  have hret := shooting_terminal_value hc hd2 hshoot
  rw [Nat.sub_add_cancel (by omega : 2 ≤ p)] at hret
  have hcrit : ∀ j : ℕ, 2 ≤ j → j ≤ p →
      scale p ≤ criticalValue c j ∧ criticalValue c j ≤ 2 := by
    intro j hj hjp
    rcases eq_or_lt_of_le hjp with rfl | hjp
    · rw [hret]
      exact ⟨le_rfl, hd2.2⟩
    · have he := shooting_critical_itinerary hc hd2 hshoot (j-2) (by omega)
      rw [Nat.sub_add_cancel hj] at he
      have hb := NearTwoInverse.back_bounds hc hd2 ((p-2)-(j-2))
      have hindex : (p-2)-(j-2) = ((p-2)-(j-2)-1)+1 := by omega
      have hl := NearTwoInverse.back_lower hc hd2 ((p-2)-(j-2)-1)
      rw [← hindex] at hl
      rw [he]
      exact ⟨by linarith, hb.2⟩
  have hinterval : returnInterval c p = Icc (-scale p) (scale p) := by
    simp only [returnInterval, hret]
  refine ⟨c, ?_, hret⟩
  refine {
    parameter_band := ⟨hc.1, by linarith [hc.2]⟩
    return_pos := by rw [hret]; exact hq0
    negative_first := ?_
    positive_phases := ?_
    invariant := ?_ }
  · intro x hx
    rw [hinterval] at hx
    exact initial_negative hp hc hx
  · intro j hj hjp x hx
    rw [hinterval] at hx
    exact (interval_orbit_bound hp hc hcrit hx j hj hjp.le).2.2
  · intro x hx
    rw [hinterval] at hx ⊢
    obtain ⟨hlo,hup,hpos⟩ := interval_orbit_bound hp hc hcrit hx p (by omega) le_rfl
    rw [hret] at hlo
    exact ⟨by linarith, by linarith⟩

end

end GlobalRestrictiveExistence
