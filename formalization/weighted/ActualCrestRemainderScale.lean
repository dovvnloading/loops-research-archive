import ActualCrestRemainderOrder

/-!
# A scale-sharp lower bound for the complete nonlinear crest remainder

The nonlinear remainder of an actual return cannot vanish faster than
the dynamical scale `4⁻ᵖ`.  The last quadratic step already contributes
the square of the preceding orbit displacement.  Positivity of the
earlier remainder keeps this contribution, and the actual normalized
coefficient forces that displacement to be a fixed fraction of the
positive return value.

All bounds concern the complete actual iterate, rather than a truncated
quartic expansion or an assumed perturbation model.
-/

namespace ActualCrestRemainderScale

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter ActualCrestRemainderOrder

noncomputable section

/- This is the unchanged elementary coefficient bound from
LimitingCrestQuadraticReturn.lean, where it is private. Keeping this
small proof local avoids changing the interface of that widely imported
module solely to expose a supporting estimate. -/
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
          (2 * |criticalValue c (n+1)|) * |quadraticCoefficient c n| := by
            norm_num [quadraticCoefficient, abs_mul]
      _ ≤ 4*(4 : ℝ)^n :=
        mul_le_mul (by linarith) ha (abs_nonneg _) (by norm_num)
      _ = (4 : ℝ)^(n+1) := by rw [pow_succ]; ring

/-- The normalized coefficient forces the positive critical return to
have at least its natural exponential scale. -/
theorem actual_return_scale_lower {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    4*kappa p c*scale p ≤ criticalValue c p := by
  have hd : 0 < criticalValue c p := hc.2.1
  have hA : |quadraticCoefficient c (p-1)| ≤ (4 : ℝ)^(p-1) :=
    coefficient_bound c (p-1) (fun j hj =>
      hc.2.2.2.2.2.2 j (by omega))
  have hk : kappa p c ≤ (4 : ℝ)^(p-1)*criticalValue c p := by
    unfold kappa
    calc
      -quadraticCoefficient c (p-1)*criticalValue c p ≤
          |quadraticCoefficient c (p-1)|*criticalValue c p :=
        mul_le_mul_of_nonneg_right (neg_le_abs _) hd.le
      _ ≤ (4 : ℝ)^(p-1)*criticalValue c p :=
        mul_le_mul_of_nonneg_right hA hd.le
  have hpow : (4 : ℝ)^(p-1)*scale (p-1) = 1 := by
    simp only [scale, ← mul_pow]
    norm_num
  have hscale : scale (p-1) = 4*scale p := by
    have h := scale_succ (p-1)
    rw [show p-1+1 = p by omega] at h
    linarith
  rw [hscale] at hpow
  calc
    4*kappa p c*scale p = (4*scale p)*kappa p c := by ring
    _ ≤ (4*scale p)*((4 : ℝ)^(p-1)*criticalValue c p) :=
      mul_le_mul_of_nonneg_left hk (mul_nonneg (by norm_num) (scale_pos p).le)
    _ = ((4 : ℝ)^(p-1)*(4*scale p))*criticalValue c p := by ring
    _ = criticalValue c p := by rw [hpow, one_mul]

/-- The archived complete complex remainder estimate also controls the
literal real remainder at the normalized point one. -/
theorem actual_remainder_one_abs_le {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    |realRemainder c p 1| ≤ 24*scale p := by
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have hnorm := normalized_return_error c p (by omega)
    hc.2.2.2.2.2.2 hc.2.1 hsmall (1 : ℂ) (by norm_num)
  change ‖normalizedReturn c p 1-complexMap (kappa p c) 1‖ ≤ _ at hnorm
  have hre := (Complex.abs_re_le_norm
    (normalizedReturn c p 1-complexMap (kappa p c) 1)).trans hnorm
  have he : (normalizedReturn c p 1-complexMap (kappa p c) 1).re =
      realRemainder c p 1 := by
    simp [realRemainder, LimitingCrest.complexMap]
  rw [he] at hre
  simpa only [scale, one_div_pow, mul_one_div] using hre

/-- The final squaring step forces a positive lower bound proportional
to the actual critical return value.  Every preceding nonlinear term is
retained through the proved nonnegativity of the physical remainder. -/
theorem actual_remainder_one_lower_return {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (25/144 : ℝ)*criticalValue c p ≤ realRemainder c p 1 := by
  let d := criticalValue c p
  let X := criticalValue c (p-1)
  let Y := realIterate c (p-1) d
  let E := realRemainder c p 1
  let R := physicalRemainder c (p-2) d
  have hd : 0 < d := hc.2.1
  have ht : d ∈ Icc (0 : ℝ) (criticalValue c p) := ⟨hd.le, le_rfl⟩
  have hprefix := physical_prefix_bounds hp hc ht
    (show 2 ≤ p-1 by omega) (show p-1 ≤ p-1 from le_rfl)
  have hXY : 0 ≤ X-Y := hprefix.1.1
  have hY : 1 ≤ Y := hprefix.2
  have hX : 0 ≤ X := by linarith
  have hXupper : X ≤ 2 :=
    (abs_le.mp (hc.2.2.2.2.2.2 (p-1) (by omega))).2
  have hsum : X+Y ≤ 4 := by linarith
  have hcrit : d = X^2+c := by
    simpa only [show p-1+1 = p by omega, realIterate_at_zero] using
      realIterate_succ c (p-1) 0
  have hstep : realIterate c p d = Y^2+c := by
    simpa only [show p-1+1 = p by omega] using
      realIterate_succ c (p-1) d
  have hnorm : E = realIterate c p d/d-(1-kappa p c) := by
    simp only [E, realRemainder, normalizedReturn_real_eq, one_pow, mul_one]
  have hnorm' : d*E = realIterate c p d-d*(1-kappa p c) := by
    rw [hnorm]
    field_simp [hd.ne']
    <;> ring
  have hid : (X-Y)*(X+Y) = d*(kappa p c-E) := by
    nlinarith only [hcrit, hstep, hnorm']
  have hEupper : E ≤ (1/100 : ℝ) := by
    have h := (abs_le.mp (actual_remainder_one_abs_le hp hc)).2
    have hq := scale_small hp
    change E ≤ 24*scale p at h
    linarith
  have hk : (7/4 : ℝ) ≤ kappa p c := by
    have h := hc.2.2.2.1.1
    change (17903/10000 : ℝ) ≤ kappa p c at h
    linarith
  have hkgap : (5/3 : ℝ) ≤ kappa p c-E := by linarith
  have hdisplacement : (5/12 : ℝ)*d ≤ X-Y := by
    have h1 := mul_le_mul_of_nonneg_left hkgap hd.le
    have h2 := mul_le_mul_of_nonneg_left hsum hXY
    rw [hid] at h2
    nlinarith only [h1, h2]
  have hR : 0 ≤ R := physical_remainder_nonneg hp hc ht
    (show p-2+1 ≤ p by omega)
  have hterm : quadraticCoefficient c (p-2)*d^2+R = Y-X := by
    dsimp only [R, physicalRemainder, Y, X]
    rw [show p-2+1 = p-1 by omega]
    ring
  have hRstep : physicalRemainder c (p-1) d = 2*X*R+(Y-X)^2 := by
    have h := physicalRemainder_step c (p-2) d
    rw [show p-2+1 = p-1 by omega] at h
    change physicalRemainder c (p-1) d =
      2*X*R+(quadraticCoefficient c (p-2)*d^2+R)^2 at h
    rwa [hterm] at h
  have hphysical : E = physicalRemainder c (p-1) d/d := by
    simpa only [mul_one] using realRemainder_eq_physical hp hc (1 : ℝ)
  have hRd : physicalRemainder c (p-1) d = d*E := by
    rw [hphysical]
    field_simp [hd.ne']
    <;> ring
  have hsquare : (X-Y)^2 ≤ d*E := by
    rw [← hRd, hRstep]
    have hnonneg : 0 ≤ 2*X*R := by positivity
    nlinarith only [hnonneg]
  have hdisplacement_sq := pow_le_pow_left₀
    (show 0 ≤ (5/12 : ℝ)*d by positivity) hdisplacement 2
  change (25/144 : ℝ)*d ≤ E
  apply (mul_le_mul_left hd).mp
  nlinarith only [hdisplacement_sq, hsquare]

/-- The complete nonlinear actual remainder has the same exponential
order as the established upper bound.  In particular it cannot be
discarded at the first dynamical scale. -/
theorem actual_remainder_one_lower_scale {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    scale p ≤ realRemainder c p 1 := by
  have hd := actual_return_scale_lower hp hc
  have hE := actual_remainder_one_lower_return hp hc
  have hk : (7/4 : ℝ) ≤ kappa p c := by
    have h := hc.2.2.2.1.1
    change (17903/10000 : ℝ) ≤ kappa p c at h
    linarith
  have hq := (scale_pos p).le
  have hprod := mul_le_mul_of_nonneg_right hk hq
  nlinarith only [hd, hE, hq, hprod]

/-- A two-sided certificate for the complete nonlinear displacement at
one, uniform over every actual tip and every return index at least seventeen. -/
theorem actual_remainder_one_scale_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    scale p ≤ realRemainder c p 1 ∧ realRemainder c p 1 ≤ 24*scale p :=
  ⟨actual_remainder_one_lower_scale hp hc,
    (abs_le.mp (actual_remainder_one_abs_le hp hc)).2⟩

end
end ActualCrestRemainderScale
