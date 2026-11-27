import LimitingCrestEndpoint

/-!
# Complete angular uniqueness and the fourth-image terminal gate

The angular uniqueness is on the whole upper semicircle, not just the
small interval used for the fixed positive collar.
-/

namespace LimitingCrest

open Set Function
noncomputable section

/-- The full upper semicircle has a quantitatively ordered crossing
function throughout the limiting parent radius interval. -/
theorem crossing_global_growth {κ s u v : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8))
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) (huv : u ≤ v) :
    (v - u) / 10 ≤ crossing κ s v - crossing κ s u := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hsum : v + u ≤ (2 : ℝ) := by linarith [hu.2, hv.2]
  have hprod := mul_le_mul_of_nonneg_left hsum hs0
  have hfactor : (1 : ℝ) ≤ 3 / 2 - 2 * s * (v + u) := by
    nlinarith [hs.2]
  have hks0 := mul_le_mul hk.1 hs.1 (by norm_num) hk0
  have hks : (1 / 10 : ℝ) ≤ κ * s := by nlinarith only [hks0]
  have hboth := mul_le_mul hks hfactor (by norm_num) (by linarith : 0 ≤ κ * s)
  have hlast := mul_le_mul_of_nonneg_right hboth (sub_nonneg.mpr huv)
  have hid : crossing κ s v - crossing κ s u =
      (κ * s * (3 / 2 - 2 * s * (v + u))) * (v - u) := by
    unfold crossing
    ring
  nlinarith only [hlast, hid]

theorem crossing_global_strictMono {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) :
    StrictMonoOn (crossing κ s) (Icc (-1 : ℝ) 1) := by
  intro u hu v hv huv
  have hg := crossing_global_growth hk hs hu hv huv.le
  linarith

/-- No second crossing can be hidden outside the certified small branch. -/
theorem crossing_global_unique {κ s u v : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8))
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
    (huz : crossing κ s u = 0) (hvz : crossing κ s v = 0) : u = v :=
  (crossing_global_strictMono hk hs).injOn hu hv (huz.trans hvz.symm)

/-- The radical endpoint parametrization and the circle-angle
parametrization agree whenever their real coordinates agree. Positivity
selects the same upper semicircle, with no independent square-root choice. -/
theorem radialPoint_eq_circlePoint {κ s u : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8))
    (hu : u ∈ Icc (-1 : ℝ) 1)
    (hcoord : -3 / 4 + s * u = radialAbscissa κ s) :
    radialPoint κ s = circlePoint s u := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hu2 := sq_le_sq' hu.1 hu.2
  have hyr := Real.sq_sqrt (show 0 ≤ 1 - u ^ 2 by nlinarith)
  have hv := radial_ordinate_pos hk hs
  have hyv := Real.sq_sqrt hv.le
  have hc := radial_circle_identity hk hs
  rw [← hcoord] at hc
  have hysq : (s * Real.sqrt (1 - u ^ 2)) ^ 2 = radialOrdinateSq κ s := by
    rw [mul_pow, hyr]
    nlinarith only [hc]
  have hyeq : s * Real.sqrt (1 - u ^ 2) = Real.sqrt (radialOrdinateSq κ s) := by
    nlinarith only [hysq, hyv, Real.sqrt_nonneg (radialOrdinateSq κ s),
      mul_nonneg hs0 (Real.sqrt_nonneg (1 - u ^ 2))]
  unfold radialPoint circlePoint
  rw [hcoord, hyeq]

theorem realMap_negative_strictMono {κ : ℝ} (hk : 0 < κ) :
    StrictMonoOn (realMap κ) (Iic 0) := by
  intro x hx y hy hxy
  change y ≤ 0 at hy
  have hp := pow_lt_pow_left₀ (neg_lt_neg hxy)
    (show 0 ≤ -y by linarith) (by decide : (2 : ℕ) ≠ 0)
  have hm := mul_lt_mul_of_pos_left hp hk
  unfold realMap
  nlinarith only [hm]

theorem fourth_critical_pos {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000)) :
    0 < (realMap κ)^[4] 0 := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hkl : (179 / 100 : ℝ) ≤ κ := by linarith [hk.1]
  have hku : κ ≤ (9 / 5 : ℝ) := by linarith [hk.2]
  have hal : (79 / 100 : ℝ) ≤ κ - 1 := by linarith [hk.1]
  have hau : κ - 1 ≤ (4 / 5 : ℝ) := by linarith [hk.2]
  have hal2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 79 / 100) hal 2
  have hau2 := pow_le_pow_left₀ (by linarith : 0 ≤ κ - 1) hau 2
  have hpl := mul_le_mul hkl hal2 (by norm_num) hk0
  have hpu := mul_le_mul hku hau2 (sq_nonneg (κ - 1)) (by norm_num)
  have hbl : -(4 / 25 : ℝ) ≤ 1 - κ * (1 - κ) ^ 2 := by nlinarith only [hpu]
  have hbu : 1 - κ * (1 - κ) ^ 2 ≤ (4 / 25 : ℝ) := by nlinarith only [hpl]
  have hb2 := sq_le_sq' hbl hbu
  have hq := mul_le_mul hku hb2 (sq_nonneg _) (by norm_num)
  change 0 < 1 - κ * (1 - κ * (1 - κ * (1 - κ * 0 ^ 2) ^ 2) ^ 2) ^ 2
  norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero,
    one_pow, mul_one]
  nlinarith only [hq]

/-- The third-image gate implies the actual fourth image lies strictly
between the second and fifth critical-orbit cuts. -/
theorem fourth_image_target_gate {κ t : ℝ} {z : ℂ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hthird : (complexMap κ)^[3] z = (t : ℂ))
    (ht : t ∈ Ioo (-1 : ℝ) (-(realMap κ)^[4] 0)) :
    ((complexMap κ)^[4] z).im = 0 ∧
      ((complexMap κ)^[4] z).re ∈
        Ioo ((realMap κ)^[2] 0) ((realMap κ)^[5] 0) := by
  have hk0 : 0 < κ := by linarith [hk.1]
  have hq4 := fourth_critical_pos hk
  have ht0 : t ≤ 0 := by linarith [ht.2]
  have hmono := realMap_negative_strictMono hk0
  have hlo := hmono (show (-1 : ℝ) ∈ Iic 0 by norm_num) ht0 ht.1
  have hhi := hmono ht0 (show -(realMap κ)^[4] 0 ∈ Iic 0 by
    change -(realMap κ)^[4] 0 ≤ 0
    linarith) ht.2
  have htwo : realMap κ (-1) = (realMap κ)^[2] 0 := by
    change realMap κ (-1) = realMap κ (realMap κ 0)
    simp [realMap]
  have hfive : realMap κ (-(realMap κ)^[4] 0) = (realMap κ)^[5] 0 := by
    change 1 - κ * (-(realMap κ)^[4] 0) ^ 2 =
      1 - κ * ((realMap κ)^[4] 0) ^ 2
    rw [neg_sq]
  have hfour : (complexMap κ)^[4] z = (realMap κ t : ℂ) := by
    change complexMap κ ((complexMap κ)^[3] z) = _
    rw [hthird, complexMap_real]
  rw [htwo] at hlo
  rw [hfive] at hhi
  rw [hfour]
  exact ⟨by simp, by simpa using (show realMap κ t ∈
    Ioo ((realMap κ)^[2] 0) ((realMap κ)^[5] 0) from ⟨hlo, hhi⟩)⟩

end
end LimitingCrest
