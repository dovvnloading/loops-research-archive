import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A sharp rescaling inequality for an annular Fourier mode

The attenuation of the mode of frequency `n` in a round collar of logarithmic
length `L` is `e = exp (-n * L)`. After normalizing the trace coefficient by
the square root of its frequency, its complete two-ended Dirichlet energy
is `mode e u v`. No condition is imposed on the relation between different
Fourier coefficients of the load attached to the second end.

The main inequality rescales an arbitrary competing exit trace. Consequently
it can be summed and minimized before imposing any quadratic or linear
structure on the attached load. The formulas for individual Fourier modes
are classical; their role here is the common rescaling valid for every mode.
-/

namespace AnnularModeContraction

noncomputable section

/-- Complete normalized Dirichlet energy of one real Fourier mode. -/
def mode (e u v : ℝ) : ℝ :=
  ((u - e * v) ^ 2 + (v - e * u) ^ 2) / (1 - e ^ 2)

/-- Denominator of the exact common rescaling factor. -/
def radiusDenominator (r a : ℝ) : ℝ := (a + 1) - r ^ 2 * (a - 1)

/-- Numerator of the exact common rescaling factor. -/
def radiusNumerator (r a : ℝ) : ℝ := (a + 1) + r ^ 2 * (a - 1)

/-- A multiplicative comparison radius after crossing one complete collar. -/
def radiusStep (r a : ℝ) : ℝ := radiusNumerator r a / radiusDenominator r a

theorem one_sub_sq_pos {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) :
    0 < 1 - e ^ 2 := by
  have h := mul_pos (sub_pos.mpr he1) (show 0 < 1 + e by linarith)
  nlinarith

theorem sq_le_sq_of_nonneg {e r : ℝ} (he : 0 ≤ e) (her : e ≤ r) :
    e ^ 2 ≤ r ^ 2 := by
  have h := mul_nonneg (sub_nonneg.mpr her) (show 0 ≤ r + e by linarith)
  nlinarith

theorem radiusDenominator_pos {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) : 0 < radiusDenominator r a := by
  have h := mul_nonneg (one_sub_sq_pos hr hr1).le (sub_nonneg.mpr ha)
  dsimp [radiusDenominator]
  nlinarith

theorem radiusNumerator_pos {r a : ℝ} (ha : 1 ≤ a) :
    0 < radiusNumerator r a := by
  have h := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr ha)
  dsimp [radiusNumerator]
  linarith

theorem radiusStep_pos {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) : 0 < radiusStep r a :=
  div_pos (radiusNumerator_pos ha) (radiusDenominator_pos hr hr1 ha)

theorem radiusStep_one_le {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) : 1 ≤ radiusStep r a := by
  unfold radiusStep
  apply (le_div_iff₀ (radiusDenominator_pos hr hr1 ha)).2
  have h := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr ha)
  dsimp [radiusNumerator, radiusDenominator]
  nlinarith

theorem radiusStep_le {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) : radiusStep r a ≤ a := by
  unfold radiusStep
  apply (div_le_iff₀ (radiusDenominator_pos hr hr1 ha)).2
  have ha2 : 0 ≤ a ^ 2 - 1 := by nlinarith
  have h := mul_nonneg (one_sub_sq_pos hr hr1).le ha2
  dsimp [radiusNumerator, radiusDenominator]
  nlinarith

/-- The bounded comparison coordinate multiplies by the squared attenuation. -/
theorem radiusStep_crossRatio {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) :
    (radiusStep r a - 1) / (radiusStep r a + 1) =
      r ^ 2 * ((a - 1) / (a + 1)) := by
  have hd : radiusDenominator r a ≠ 0 := (radiusDenominator_pos hr hr1 ha).ne'
  have ha1 : a + 1 ≠ 0 := by linarith
  have hn : radiusNumerator r a + radiusDenominator r a ≠ 0 := by
    have h := add_pos (radiusNumerator_pos (r := r) ha)
      (radiusDenominator_pos hr hr1 ha)
    exact h.ne'
  unfold radiusStep
  field_simp [hd, ha1, hn]
  unfold radiusNumerator radiusDenominator
  ring

theorem mode_nonneg {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (u v : ℝ) :
    0 ≤ mode e u v :=
  div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (one_sub_sq_pos he he1).le

/-- Simultaneous amplitude scaling of both ends is exact. -/
theorem mode_smul (e s u v : ℝ) :
    mode e (s * u) (s * v) = s ^ 2 * mode e u v := by
  unfold mode
  ring

theorem mode_at_zero (e u : ℝ) :
    mode e u 0 = ((1 + e ^ 2) / (1 - e ^ 2)) * u ^ 2 := by
  unfold mode
  ring

/-- Completion of the square, including the entire trace at the second end. -/
theorem mode_completion {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (u v : ℝ) :
    mode e u v - ((1 - e ^ 2) / (1 + e ^ 2)) * u ^ 2 =
      ((1 + e ^ 2) * v - 2 * e * u) ^ 2 /
        ((1 - e ^ 2) * (1 + e ^ 2)) := by
  have hm : 1 - e ^ 2 ≠ 0 := (one_sub_sq_pos he he1).ne'
  have hp : 1 + e ^ 2 ≠ 0 := by positivity
  unfold mode
  field_simp [hm, hp]
  <;> ring

theorem mode_lower {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (u v : ℝ) :
    ((1 - e ^ 2) / (1 + e ^ 2)) * u ^ 2 ≤ mode e u v := by
  have h := div_nonneg (sq_nonneg ((1 + e ^ 2) * v - 2 * e * u))
    (mul_nonneg (one_sub_sq_pos he he1).le (by positivity : 0 ≤ 1 + e ^ 2))
  rw [← mode_completion he he1 u v] at h
  linarith

/-- A lower bound uniform over all frequencies attenuated by at most `r`. -/
theorem mode_coercive {e r : ℝ} (he : 0 ≤ e) (her : e ≤ r) (hr1 : r < 1)
    (u v : ℝ) :
    ((1 - r ^ 2) / (1 + r ^ 2)) * u ^ 2 ≤ mode e u v := by
  have he1 : e < 1 := her.trans_lt hr1
  have hratio : (1 - r ^ 2) / (1 + r ^ 2) ≤ (1 - e ^ 2) / (1 + e ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)
      (by positivity : 0 < 1 + e ^ 2)).2
    nlinarith [sq_le_sq_of_nonneg he her]
  exact (mul_le_mul_of_nonneg_right hratio (sq_nonneg u)).trans (mode_lower he he1 u v)

/-- The zero exit trace is a competitor with a uniform finite energy. -/
theorem mode_at_zero_le {e r : ℝ} (he : 0 ≤ e) (her : e ≤ r) (hr1 : r < 1)
    (u : ℝ) :
    mode e u 0 ≤ ((1 + r ^ 2) / (1 - r ^ 2)) * u ^ 2 := by
  have hr : 0 ≤ r := he.trans her
  have he1 : e < 1 := her.trans_lt hr1
  rw [mode_at_zero]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg u)
  apply (div_le_div_iff₀ (one_sub_sq_pos he he1) (one_sub_sq_pos hr hr1)).2
  nlinarith [sq_le_sq_of_nonneg he her]

private theorem comparison_quadratic_nonneg {e r : ℝ}
    (he : 0 ≤ e) (her : e ≤ r) (hr1 : r < 1) (x y : ℝ) :
    0 ≤ 4 * r ^ 2 * (1 + e ^ 2) * x ^ 2 + (1 + e ^ 2) * y ^ 2 -
      4 * e * (1 + r ^ 2) * x * y := by
  have hr : 0 ≤ r := he.trans her
  by_cases hr0 : r = 0
  · have he0 : e = 0 := by linarith
    simp only [hr0, he0]
    nlinarith [sq_nonneg y]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have he1 : e < 1 := her.trans_lt hr1
  have herprod : e * r ≤ 1 := by
    nlinarith [mul_nonneg he (sub_nonneg.mpr hr1.le)]
  have hleft : 0 ≤ ((r + e) * (1 + r * e) / 2) * (2 * r * x - y) ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    positivity
  have hright : 0 ≤ ((r - e) * (1 - r * e) / 2) * (2 * r * x + y) ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    apply div_nonneg
    · apply mul_nonneg (sub_nonneg.mpr her)
      nlinarith
    · norm_num
  have hid :
      r * (4 * r ^ 2 * (1 + e ^ 2) * x ^ 2 + (1 + e ^ 2) * y ^ 2 -
        4 * e * (1 + r ^ 2) * x * y) =
      ((r + e) * (1 + r * e) / 2) * (2 * r * x - y) ^ 2 +
      ((r - e) * (1 - r * e) / 2) * (2 * r * x + y) ^ 2 := by ring
  have h : 0 ≤ r *
      (4 * r ^ 2 * (1 + e ^ 2) * x ^ 2 + (1 + e ^ 2) * y ^ 2 -
        4 * e * (1 + r ^ 2) * x * y) := by
    rw [hid]
    exact add_nonneg hleft hright
  by_contra hn
  have hneg := mul_neg_of_pos_of_neg hrp (lt_of_not_ge hn)
  exact (not_lt_of_ge h) hneg

/-- One exit-trace rescaling works simultaneously at every Fourier frequency. -/
theorem mode_rescale {e r a : ℝ} (he : 0 ≤ e) (her : e ≤ r) (hr1 : r < 1)
    (ha : 1 ≤ a) (u v : ℝ) :
    mode e u ((radiusStep r a / a) * v) ≤
      (radiusStep r a) ^ 2 * mode e u v := by
  have hr : 0 ≤ r := he.trans her
  have he1 : e < 1 := her.trans_lt hr1
  have ha0 : 0 < a := by linarith
  have ha2 : 0 ≤ a ^ 2 - 1 := by nlinarith
  have hd := radiusDenominator_pos hr hr1 ha
  have hepos := one_sub_sq_pos he he1
  have hquad := comparison_quadratic_nonneg he her hr1
    (a * u) (radiusNumerator r a * v)
  have hprod := mul_nonneg ha2 hquad
  have hden : 0 < a ^ 2 * (radiusDenominator r a) ^ 2 * (1 - e ^ 2) := by
    positivity
  have hid :
      (radiusStep r a) ^ 2 * mode e u v -
        mode e u ((radiusStep r a / a) * v) =
      (a ^ 2 - 1) *
        (4 * r ^ 2 * (1 + e ^ 2) * (a * u) ^ 2 +
          (1 + e ^ 2) * (radiusNumerator r a * v) ^ 2 -
          4 * e * (1 + r ^ 2) * (a * u) * (radiusNumerator r a * v)) /
        (a ^ 2 * (radiusDenominator r a) ^ 2 * (1 - e ^ 2)) := by
    have ha_ne : a ≠ 0 := ha0.ne'
    have hd_ne : radiusDenominator r a ≠ 0 := hd.ne'
    have he_ne : 1 - e ^ 2 ≠ 0 := hepos.ne'
    unfold radiusStep mode
    field_simp [ha_ne, hd_ne, he_ne]
    unfold radiusNumerator radiusDenominator
    ring
  have hnonneg : 0 ≤ (radiusStep r a) ^ 2 * mode e u v -
      mode e u ((radiusStep r a / a) * v) := by
    rw [hid]
    exact div_nonneg hprod hden.le
  linarith

end
end AnnularModeContraction
