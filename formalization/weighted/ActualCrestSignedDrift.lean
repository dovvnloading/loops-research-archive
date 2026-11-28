import ActualCrestRemainderScale
import GlobalCrestSourceGates

/-!
# The actual crest parameter approaches its limit from a forced side

The archived absolute error estimate did not determine the sign of the
finite-period displacement.  The actual nonquadratic remainder is
nonnegative and bounded above on the real unit interval by its strictly
positive value at one.  Following that same remainder through the signed
six-versus-three relation forces the model relation to be positive.

The comparison retains the correlations between consecutive orbit
differences: the first positive displacement is amplified, then changes
sign at the fourth phase, and the sixth phase dominates the third.  The
result gives a nonzero lower bound of order `4⁻ᵖ` for the displacement of
every actual signed-tip coefficient from the unique limiting coefficient.
-/

namespace ActualCrestSignedDrift

open Set Function
open LimitingCrest LimitingCrestQuadraticReturn LoopsLimitingCrestParameter
open NearTwoShooting NearTwoTip GlobalCrestSourceGates GlobalCrestEstimates
open ActualCrestRemainderOrder ActualCrestRemainderScale

noncomputable section

private theorem remainder_one_small {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : realRemainder c p 1 ≤ 1/100000000 := by
  have h := actual_return_error_small hp hc
    (show ‖(1 : ℂ)‖ ≤ (3/2 : ℝ) by norm_num)
  have hr := (Complex.re_le_norm
    (normalizedReturn c p 1-complexMap (kappa p c) 1)).trans h
  simpa [realRemainder,complexMap] using hr

private theorem actual_step_sq {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hx : |x| ≤ 1)
    (hsq : a ≤ x^2 ∧ x^2 ≤ b) (ha : 0 ≤ a)
    (hl : l ≤ 1-(17904/10000)*b)
    (hu : 1-(17903/10000)*a+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  have hk := hc.2.2.2.1
  have hlow := mul_le_mul hk.1 hsq.1 ha (by linarith [hk.1])
  have hupp := mul_le_mul hk.2 hsq.2 (sq_nonneg x) (by norm_num)
  have hE := actual_remainder_order hp hc hx
  have hsmall := remainder_one_small hp hc
  dsimp [realRemainder] at hE hsmall
  change l ≤ (normalizedReturn c p (x : ℂ)).re ∧
    (normalizedReturn c p (x : ℂ)).re ≤ u
  constructor <;> linarith [hE.1,hE.2]

private theorem actual_step_pos {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hx : x ∈ Icc a b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hl : l ≤ 1-(17904/10000)*b^2)
    (hu : 1-(17903/10000)*a^2+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hunit : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx.2.trans hb
  exact actual_step_sq hp hc hunit
    ⟨pow_le_pow_left₀ ha hx.1 2,pow_le_pow_left₀ hx0 hx.2 2⟩
    (sq_nonneg a) hl hu

private theorem actual_step_neg {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hx : x ∈ Icc a b) (ha : -1 ≤ a) (hb : b ≤ 0)
    (hl : l ≤ 1-(17904/10000)*a^2)
    (hu : 1-(17903/10000)*b^2+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  have hx0 : x ≤ 0 := hx.2.trans hb
  have hunit : |x| ≤ 1 := by rw [abs_of_nonpos hx0]; linarith [hx.1]
  have hsq : b^2 ≤ x^2 ∧ x^2 ≤ a^2 := by
    constructor
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr hb) (neg_le_neg hx.2) 2
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr hx0) (neg_le_neg hx.1) 2
  exact actual_step_sq hp hc hunit hsq (sq_nonneg b) hl hu

private theorem model_step_pos {κ x a b l u : ℝ}
    (hk : κ ∈ parameterInterval) (hx : x ∈ Icc a b) (ha : 0 ≤ a)
    (hl : l ≤ 1-(17904/10000)*b^2)
    (hu : 1-(17903/10000)*a^2 ≤ u) :
    Q κ x ∈ Icc l u := by
  have hs1 := pow_le_pow_left₀ ha hx.1 2
  have hs2 := pow_le_pow_left₀ (ha.trans hx.1) hx.2 2
  have hlow := mul_le_mul hk.1 hs1 (sq_nonneg a) (by linarith [hk.1])
  have hupp := mul_le_mul hk.2 hs2 (sq_nonneg x) (by norm_num)
  dsimp [Q]
  constructor <;> linarith

private theorem actual_first_orbit {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : actualOrbit c p 0 1 = 1 := by
  have h := realRemainder_zero hp hc
  change (normalizedReturn c p (0 : ℂ)).re - (1-kappa p c*(0 : ℝ)^2) = 0 at h
  change (normalizedReturn c p (0 : ℂ)).re = 1
  nlinarith only [h]

/-- Five complete actual critical returns stay in the real unit
interval, with enough quantitative separation to fix every multiplier
in the signed orbit-difference recurrence. -/
private theorem critical_boxes {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    actualOrbit c p 0 2 ∈ Icc (-790401/1000000) (-790299/1000000) ∧
    actualOrbit c p 0 3 ∈ Icc (-119/1000) (-117/1000) ∧
    actualOrbit c p 0 4 ∈ Icc (9746/10000) (9756/10000) ∧
    actualOrbit c p 0 5 ∈ Icc (-705/1000) (-700/1000) := by
  have y1 : actualOrbit c p 0 1 ∈ Icc (1 : ℝ) 1 := by
    rw [actual_first_orbit hp hc]
    exact ⟨le_rfl,le_rfl⟩
  have y2 : actualOrbit c p 0 2 ∈ Icc (-790401/1000000) (-790299/1000000) :=
    actual_step_pos hp hc y1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have y3 : actualOrbit c p 0 3 ∈ Icc (-119/1000) (-117/1000) :=
    actual_step_neg hp hc y2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have y4 : actualOrbit c p 0 4 ∈ Icc (9746/10000) (9756/10000) :=
    actual_step_neg hp hc y3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have y5 : actualOrbit c p 0 5 ∈ Icc (-705/1000) (-700/1000) :=
    actual_step_pos hp hc y4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨y2,y3,y4,y5⟩

set_option maxHeartbeats 800000 in
/-- The nonlinear correction forces a strict deficit in the actual
six-versus-three relation relative to its quadratic part.  Its size is
bounded below by `39/10` times the actual remainder at one. -/
theorem actual_signed_relation_deficit {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (39/10 : ℝ)*realRemainder c p 1 ≤ relation (kappa p c) -
      (actualOrbit c p 0 6+actualOrbit c p 0 3) := by
  let κ := kappa p c
  let e := realRemainder c p 1
  let y := actualOrbit c p 0
  let u := criticalOrbit κ
  let δ : ℕ → ℝ := fun n => y n-u n
  have hk : κ ∈ parameterInterval := hc.2.2.2.1
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have he : 0 < e := actual_remainder_one_pos hp hc
  obtain ⟨y2,y3,y4,y5⟩ := critical_boxes hp hc
  change y 2 ∈ Icc (-790401/1000000) (-790299/1000000) at y2
  change y 3 ∈ Icc (-119/1000) (-117/1000) at y3
  change y 4 ∈ Icc (9746/10000) (9756/10000) at y4
  change y 5 ∈ Icc (-705/1000) (-700/1000) at y5
  have u2 : u 2 ∈ Icc (-7904/10000) (-7903/10000) := by
    have htwo : u 2 = 1-κ := by norm_num [u,criticalOrbit,Q]
    rw [htwo]
    constructor <;> linarith [hk.1,hk.2]
  have ub := parameter_orbit_bounds hk
  have u3 : u 3 ∈ Icc (-119/1000) (-118/1000) := ⟨ub.1.le,ub.2.1.le⟩
  have u4 : u 4 ∈ Icc (9748/10000) (9751/10000) := ⟨ub.2.2.1.le,ub.2.2.2.le⟩
  have u5 : u 5 ∈ Icc (-703/1000) (-700/1000) :=
    model_step_pos hk u4 (by norm_num) (by norm_num) (by norm_num)
  have hE2 := actual_remainder_order hp hc
    (show |y 2| ≤ 1 by rw [abs_le]; constructor <;> linarith [y2.1,y2.2])
  have hE3 := actual_remainder_order hp hc
    (show |y 3| ≤ 1 by rw [abs_le]; constructor <;> linarith [y3.1,y3.2])
  have hE4 := actual_remainder_order hp hc
    (show |y 4| ≤ 1 by rw [abs_le]; constructor <;> linarith [y4.1,y4.2])
  have hE5 := actual_remainder_order hp hc
    (show |y 5| ≤ 1 by rw [abs_le]; constructor <;> linarith [y5.1,y5.2])
  have hrec (n : ℕ) : δ (n+1) =
      (-κ*(y n+u n))*δ n+realRemainder c p (y n) := by
    change actualMap c p (y n)-(1-κ*(u n)^2) =
      (-κ*(y n+u n))*(y n-u n)+
        ((normalizedReturn c p (y n : ℂ)).re-(1-κ*(y n)^2))
    dsimp [actualMap]
    ring
  have hδ2 : δ 2 = e := by
    change actualMap c p (actualOrbit c p 0 1)-criticalOrbit κ 2 = e
    rw [actual_first_orbit hp hc]
    dsimp [actualMap,criticalOrbit,Q,e,realRemainder,κ]
    ring
  have a2 : (282/100 : ℝ) ≤ -κ*(y 2+u 2) := by
    have hs : (158/100 : ℝ) ≤ -(y 2+u 2) := by linarith [y2.2,u2.2]
    have hm := mul_le_mul hk.1 hs (by norm_num : (0 : ℝ) ≤ 158/100) hk0
    nlinarith only [hm]
  have a3 : (42/100 : ℝ) ≤ -κ*(y 3+u 3) := by
    have hs : (235/1000 : ℝ) ≤ -(y 3+u 3) := by linarith [y3.2,u3.2]
    have hm := mul_le_mul hk.1 hs (by norm_num : (0 : ℝ) ≤ 235/1000) hk0
    nlinarith only [hm]
  have a4 : -κ*(y 4+u 4) ≤ (-348/100 : ℝ) := by
    have hs : (19494/10000 : ℝ) ≤ y 4+u 4 := by linarith [y4.1,u4.1]
    have hm := mul_le_mul hk.1 hs (by norm_num : (0 : ℝ) ≤ 19494/10000) hk0
    nlinarith only [hm]
  have a5 : (25/10 : ℝ) ≤ -κ*(y 5+u 5) := by
    have hs : (14/10 : ℝ) ≤ -(y 5+u 5) := by linarith [y5.2,u5.2]
    have hm := mul_le_mul hk.1 hs (by norm_num : (0 : ℝ) ≤ 14/10) hk0
    nlinarith only [hm]
  have hδ3 : (282/100 : ℝ)*e ≤ δ 3 := by
    have hm := mul_le_mul_of_nonneg_right a2 he.le
    have hr := hrec 2
    rw [hδ2] at hr
    linarith [hE2.1]
  have hδ30 : 0 ≤ δ 3 := by linarith
  have hδ4 : (42/100 : ℝ)*δ 3 ≤ δ 4 := by
    have hm := mul_le_mul_of_nonneg_right a3 hδ30
    have hr := hrec 3
    linarith [hE3.1]
  have hδ40 : 0 ≤ δ 4 := by linarith
  have hδ5 : δ 5 ≤ (-348/100 : ℝ)*δ 4+e := by
    have hm := mul_le_mul_of_nonneg_right a4 hδ40
    have hr := hrec 4
    have hupper : realRemainder c p (y 4) ≤ e := hE4.2
    linarith [hupper]
  have hδ50 : δ 5 ≤ 0 := by linarith
  have hδ6 : δ 6 ≤ (25/10 : ℝ)*δ 5+e := by
    have hm := mul_le_mul_of_nonpos_right a5 hδ50
    have hr := hrec 5
    have hupper : realRemainder c p (y 5) ≤ e := hE5.2
    linarith [hupper]
  have hsum : δ 6+δ 3 ≤ -(39/10 : ℝ)*e := by linarith
  change (39/10 : ℝ)*e ≤ (u 6+u 3)-(y 6+y 3)
  dsimp only [δ] at hsum
  linarith only [hsum]

private theorem actual_relation_zero {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    actualOrbit c p 0 6+actualOrbit c p 0 3 = 0 := by
  have hs := CriticalReturnRelationStability.actual_signed_relation_scale c p hc.2.1.ne'
  rw [← actualOrbit_cast c 0 p 6,← actualOrbit_cast c 0 p 3] at hs
  simp only [Complex.ofReal_re] at hs
  rw [hc.2.2.2.2.1] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left hc.2.1.ne'

/-- The exact actual signed-tip relation lies strictly above zero when
evaluated in its quadratic part, by a fixed multiple of `4⁻ᵖ`. -/
theorem actual_model_relation_lower {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (39/10 : ℝ)*scale p ≤ relation (kappa p c) := by
  have hd := actual_signed_relation_deficit hp hc
  rw [actual_relation_zero hc,sub_zero] at hd
  have he := actual_remainder_one_lower_scale hp hc
  linarith

/-- Every admissible actual coefficient approaches the unique model
coefficient from above.  The sign is forced by the actual nonlinear
remainder, rather than selected as an additional shooting hypothesis. -/
theorem actual_coefficient_gt_limit {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0) :
    k₀ < kappa p c := by
  have hpos : 0 < relation (kappa p c) := by
    have hl := actual_model_relation_lower hp hc
    have hq := scale_pos p
    linarith
  by_contra h
  have hm := relation_strictMonoOn.monotoneOn hc.2.2.2.1 hk₀ (le_of_not_gt h)
  rw [hroot] at hm
  linarith

private theorem relation_upper_secant {k k₀ : ℝ}
    (hk : k ∈ parameterInterval) (hk₀ : k₀ ∈ parameterInterval)
    (hzero : relation k₀ = 0) (hkk₀ : k₀ < k) :
    relation k < 7*(k-k₀) := by
  have hd (t : ℝ) : HasDerivAt (fun s => 7*s-relation s)
      (7-(criticalSlope t 6+criticalSlope t 3)) t := by
    convert ((hasDerivAt_id t).const_mul (7 : ℝ)).sub (relation_hasDerivAt t) using 1
    all_goals first | rfl | simp
  have hcont : Continuous (fun t => 7*t-relation t) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hm : StrictMonoOn (fun t => 7*t-relation t) parameterInterval := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hcont.continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have h := relation_slope_lt_seven (interior_subset ht)
    linarith only [h]
  have h := hm hk₀ hk hkk₀
  rw [hzero] at h
  linarith only [h]

/-- A nonzero, intrinsically signed finite-period correction: every
actual signed tip has coefficient displacement between positive
multiples of `4⁻ᵖ`.  In particular the archived upper error order cannot
be improved to `o(4⁻ᵖ)` for these actual coefficients. -/
theorem actual_tip_signed_drift {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0) :
    scale p/2 < kappa p c-k₀ ∧ kappa p c-k₀ ≤ 15748*scale p := by
  have hgt := actual_coefficient_gt_limit hp hc hk₀ hroot
  have hl := actual_model_relation_lower hp hc
  have hu := relation_upper_secant hc.2.2.2.1 hk₀ hroot hgt
  have hq := scale_pos p
  constructor
  · linarith
  · have h := actual_tip_coefficient_error hp hc hk₀ hroot
    simpa only [abs_of_pos (sub_pos.mpr hgt)] using h

end
end ActualCrestSignedDrift
