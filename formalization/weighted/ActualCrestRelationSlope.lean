import LimitingCrestParameter

/-!
# An upper derivative bound for the signed crest relation

The archived parameter certificate supplies the third and fourth orbit
boxes. Coarse rational multiplication, together with the explicit third
derivative and the exact derivative recurrence, gives the complementary
upper bound seven. This is supporting quantitative calculus for the
actual nonlinear drift theorem; no claim of new model dynamics is made.
-/

namespace ActualCrestRelationSlope

open Set LoopsLimitingCrestParameter

noncomputable section

/-- A direct upper slope bound using the existing public model-orbit
certificate and exact rational bounds for three derivative steps. -/
theorem relation_slope_lt_seven {k : ℝ} (hk : k ∈ parameterInterval) :
    criticalSlope k 6 + criticalSlope k 3 < 7 := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hk2l := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 17903/10000) hk.1 2
  have hk2u := pow_le_pow_left₀ hk0 hk.2 2
  have hd3form : criticalSlope k 3 = -1+4*k-3*k^2 := by
    norm_num [criticalSlope, criticalOrbit, Q]
    ring
  have hd3 : criticalSlope k 3 ∈ Icc (-346/100 : ℝ) (-345/100) := by
    rw [hd3form]
    constructor <;> nlinarith only [hk.1, hk.2, hk2l, hk2u]
  obtain ⟨hx3l,hx3u,hx4l,hx4u⟩ := parameter_orbit_bounds hk
  have hx3neg : 0 ≤ -criticalOrbit k 3 := by linarith
  have hx3bound : -criticalOrbit k 3 ≤ (119/1000 : ℝ) := by linarith
  have hd3neg : 0 ≤ -criticalSlope k 3 := by linarith [hd3.2]
  have hd3bound : -criticalSlope k 3 ≤ (346/100 : ℝ) := by linarith [hd3.1]
  have hx3sq : (criticalOrbit k 3)^2 ≤ (119/1000 : ℝ)^2 := by
    simpa only [neg_sq] using pow_le_pow_left₀ hx3neg hx3bound 2
  have hprod3a : k*(-criticalOrbit k 3) ≤
      (17904/10000 : ℝ)*(119/1000) :=
    mul_le_mul hk.2 hx3bound hx3neg (by norm_num)
  have hprod3b : (k*(-criticalOrbit k 3))*(-criticalSlope k 3) ≤
      ((17904/10000 : ℝ)*(119/1000))*(346/100) :=
    mul_le_mul hprod3a hd3bound hd3neg (by norm_num)
  have hd4 : (-149/100 : ℝ) ≤ criticalSlope k 4 := by
    rw [criticalSlope]
    nlinarith only [hx3sq, hprod3b]
  have hx4pos : 0 ≤ criticalOrbit k 4 := by linarith
  have hx4sqL : (9748/10000 : ℝ)^2 ≤ (criticalOrbit k 4)^2 :=
    pow_le_pow_left₀ (by norm_num) hx4l.le 2
  have hx4sqU : (criticalOrbit k 4)^2 ≤ (9751/10000 : ℝ)^2 :=
    pow_le_pow_left₀ hx4pos hx4u.le 2
  have hprod4 : k*criticalOrbit k 4 ≤
      (17904/10000 : ℝ)*(9751/10000) :=
    mul_le_mul hk.2 hx4u.le hx4pos (by norm_num)
  have hmul4 : (2*k*criticalOrbit k 4)*(-criticalSlope k 4) ≤
      (2*k*criticalOrbit k 4)*(149/100) :=
    mul_le_mul_of_nonneg_left (by linarith only [hd4])
      (mul_nonneg (mul_nonneg (by norm_num) hk0) hx4pos)
  have hmul4' := mul_le_mul_of_nonneg_right hprod4
    (by norm_num : (0 : ℝ) ≤ 2*(149/100))
  have hd5 : criticalSlope k 5 ≤ (426/100 : ℝ) := by
    rw [criticalSlope]
    nlinarith only [hx4sqL, hmul4, hmul4']
  have hx5prodL : (17903/10000 : ℝ)*(9748/10000)^2 ≤
      k*(criticalOrbit k 4)^2 :=
    mul_le_mul hk.1 hx4sqL (by norm_num) hk0
  have hx5prodU : k*(criticalOrbit k 4)^2 ≤
      (17904/10000 : ℝ)*(9751/10000)^2 :=
    mul_le_mul hk.2 hx4sqU (sq_nonneg _) (by norm_num)
  have hx5 : criticalOrbit k 5 ∈ Icc (-703/1000 : ℝ) (-700/1000) := by
    change (-703/1000 : ℝ) ≤ 1-k*(criticalOrbit k 4)^2 ∧
      1-k*(criticalOrbit k 4)^2 ≤ (-700/1000 : ℝ)
    constructor <;> nlinarith only [hx5prodL, hx5prodU]
  have hx5neg : 0 ≤ -criticalOrbit k 5 := by linarith [hx5.2]
  have hx5bound : -criticalOrbit k 5 ≤ (703/1000 : ℝ) := by linarith [hx5.1]
  have hx5sq : (700/1000 : ℝ)^2 ≤ (criticalOrbit k 5)^2 := by
    have h : (700/1000 : ℝ) ≤ -criticalOrbit k 5 := by linarith [hx5.2]
    simpa only [neg_sq] using pow_le_pow_left₀ (by norm_num) h 2
  have hprod5 : k*(-criticalOrbit k 5) ≤
      (17904/10000 : ℝ)*(703/1000) :=
    mul_le_mul hk.2 hx5bound hx5neg (by norm_num)
  have hmul5 : (2*k*(-criticalOrbit k 5))*criticalSlope k 5 ≤
      (2*k*(-criticalOrbit k 5))*(426/100) :=
    mul_le_mul_of_nonneg_left hd5
      (mul_nonneg (mul_nonneg (by norm_num) hk0) hx5neg)
  have hmul5' := mul_le_mul_of_nonneg_right hprod5
    (by norm_num : (0 : ℝ) ≤ 2*(426/100))
  have hd6 : criticalSlope k 6 ≤ (1024/100 : ℝ) := by
    rw [criticalSlope]
    nlinarith only [hx5sq, hmul5, hmul5']
  linarith only [hd6, hd3.2]

end
end ActualCrestRelationSlope
