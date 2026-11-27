import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A positive circular corridor in the limiting quadratic crest model

The statements concern the actual complex polynomial `1 - κ*z^2`.
They quantify over a parameter interval and a nondegenerate radius interval.
No identification with a physical KKL marking is assumed or asserted.
-/

namespace LimitingCrest

open Set Function
noncomputable section

def realMap (κ t : ℝ) : ℝ := 1 - κ * t ^ 2

def complexMap (κ : ℝ) (z : ℂ) : ℂ := 1 - (κ : ℂ) * z ^ 2

def crossing (κ s u : ℝ) : ℝ :=
  1 - κ * (9 / 16 - (3 / 2) * s * u + s ^ 2 * (2 * u ^ 2 - 1))

def circlePoint (s u : ℝ) : ℂ :=
  ((-3 / 4 + s * u : ℝ) : ℂ) +
    ((s * Real.sqrt (1 - u ^ 2) : ℝ) : ℂ) * Complex.I

def height (κ s u : ℝ) : ℝ :=
  -2 * κ * (-3 / 4 + s * u) * (s * Real.sqrt (1 - u ^ 2))

private theorem radius_sq_bounds {s : ℝ}
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500)) :
    (63 / 1000 : ℝ) ^ 2 ≤ s ^ 2 ∧ s ^ 2 ≤ (33 / 500 : ℝ) ^ 2 :=
  ⟨pow_le_pow_left₀ (by norm_num) hs.1 2,
    pow_le_pow_left₀ (by linarith [hs.1]) hs.2 2⟩

/-- The crossing equation has a uniform signed margin on both angular walls. -/
theorem crossing_endpoint_margins {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500)) :
    crossing κ s (-1 / 100) < -1 / 2000 ∧
      1 / 2000 < crossing κ s (1 / 100) := by
  obtain ⟨hsl, hsu⟩ := radius_sq_bounds hs
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  let a := 9 / 16 - (3 / 2) * s * (-1 / 100) + s ^ 2 * (2 * (-1 / 100 : ℝ) ^ 2 - 1)
  let b := 9 / 16 - (3 / 2) * s * (1 / 100) + s ^ 2 * (2 * (1 / 100 : ℝ) ^ 2 - 1)
  have ha : (559 / 1000 : ℝ) ≤ a := by dsimp [a]; nlinarith [hs.1]
  have hb : b ≤ (558 / 1000 : ℝ) := by dsimp [b]; nlinarith [hs.1]
  have hb0 : 0 ≤ b := by dsimp [b]; nlinarith [hs.2]
  have hpa := mul_le_mul hk.1 ha (by norm_num) hk0
  have hpb := mul_le_mul hk.2 hb hb0 (by norm_num)
  change 1 - κ * a < -1 / 2000 ∧ 1 / 2000 < 1 - κ * b
  constructor <;> nlinarith only [hpa, hpb]

/-- A quantitative angular slope survives throughout the complete rectangle. -/
theorem crossing_growth {κ s u v : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hu : u ∈ Icc (-1 / 100 : ℝ) (1 / 100))
    (hv : v ∈ Icc (-1 / 100 : ℝ) (1 / 100)) (huv : u ≤ v) :
    (v - u) / 10 ≤ crossing κ s v - crossing κ s u := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hsum : v + u ≤ (1 / 50 : ℝ) := by linarith [hu.2, hv.2]
  have hprod := mul_le_mul_of_nonneg_left hsum hs0
  have hrad := mul_le_mul_of_nonneg_right hs.2 (by norm_num : (0 : ℝ) ≤ 1 / 50)
  have hfactor : (1 : ℝ) ≤ 3 / 2 - 2 * s * (v + u) := by nlinarith only [hprod, hrad]
  have hks0 := mul_le_mul hk.1 hs.1 (by norm_num) hk0
  have hks : (1 / 10 : ℝ) ≤ κ * s := by nlinarith only [hks0]
  have hboth := mul_le_mul hks hfactor (by norm_num) (by linarith : 0 ≤ κ * s)
  have hlast := mul_le_mul_of_nonneg_right hboth (sub_nonneg.mpr huv)
  have hid : crossing κ s v - crossing κ s u =
      (κ * s * (3 / 2 - 2 * s * (v + u))) * (v - u) := by
    unfold crossing
    ring
  nlinarith only [hlast, hid]

theorem crossing_strictMono {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500)) :
    StrictMonoOn (crossing κ s) (Icc (-1 / 100 : ℝ) (1 / 100)) := by
  intro u hu v hv huv
  have hg := crossing_growth hk hs hu hv huv.le
  linarith

/-- Every circle in the radius interval has exactly one crossing on the
declared small angular branch; the crossing is strictly inside its walls. -/
theorem crossing_root_unique {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500)) :
    ∃! u : ℝ, u ∈ Ioo (-1 / 100 : ℝ) (1 / 100) ∧ crossing κ s u = 0 := by
  have hc : Continuous (crossing κ s) := by unfold crossing; fun_prop
  obtain ⟨hl, hr⟩ := crossing_endpoint_margins hk hs
  obtain ⟨u, hu, hz⟩ := intermediate_value_Icc
    (by norm_num : (-1 / 100 : ℝ) ≤ 1 / 100) hc.continuousOn
    (show (0 : ℝ) ∈ Icc (crossing κ s (-1 / 100)) (crossing κ s (1 / 100)) by
      constructor <;> linarith)
  have hui : u ∈ Ioo (-1 / 100 : ℝ) (1 / 100) := by
    constructor
    · by_contra h
      have he : u = -1 / 100 := by linarith [hu.1]
      rw [he] at hz
      linarith
    · by_contra h
      have he : u = 1 / 100 := by linarith [hu.2]
      rw [he] at hz
      linarith
  refine ⟨u, ⟨hui, hz⟩, ?_⟩
  intro v hv
  exact (crossing_strictMono hk hs).injOn ⟨hv.1.1.le, hv.1.2.le⟩ hu
    (hv.2.trans hz.symm)

private theorem sqrt_square {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    (Real.sqrt (1 - u ^ 2)) ^ 2 = 1 - u ^ 2 := by
  have hu2 := sq_le_sq' hu.1 hu.2
  exact Real.sq_sqrt (by nlinarith)

/-- The algebraic crossing equation is exactly the real part of the
complex polynomial on the specified circle. -/
theorem circle_image (κ s : ℝ) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    complexMap κ (circlePoint s u) =
      (crossing κ s u : ℂ) + (height κ s u : ℂ) * Complex.I := by
  have hsqrt := sqrt_square hu
  apply Complex.ext
  · simp [complexMap, circlePoint, crossing, height, Complex.mul_re,
      Complex.mul_im, pow_two]
    nlinarith [congrArg (fun t : ℝ => κ * s ^ 2 * t) hsqrt]
  · simp [complexMap, circlePoint, crossing, height, Complex.mul_re,
      Complex.mul_im, pow_two]
    ring

/-- The chosen point is on the actual circle of radius s about -3/4. -/
theorem circle_radius {s u : ℝ} (hs : 0 ≤ s) (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖circlePoint s u + (3 / 4 : ℂ)‖ = s := by
  have hsqrt := sqrt_square hu
  have hn : ‖circlePoint s u + (3 / 4 : ℂ)‖ ^ 2 = s ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [circlePoint, Complex.mul_re, Complex.mul_im]
    nlinarith [congrArg (fun t : ℝ => s ^ 2 * t) hsqrt]
  nlinarith only [hn, hs, norm_nonneg (circlePoint s u + (3 / 4 : ℂ))]

private theorem ordinate_sq_bounds {s u : ℝ}
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hu : u ∈ Icc (-1 / 100 : ℝ) (1 / 100)) :
    (3968 / 1000000 : ℝ) ≤ (s * Real.sqrt (1 - u ^ 2)) ^ 2 ∧
      (s * Real.sqrt (1 - u ^ 2)) ^ 2 ≤ 1089 / 250000 := by
  have hu2 := sq_le_sq' hu.1 hu.2
  have hsqrt := sqrt_square (show u ∈ Icc (-1 : ℝ) 1 by
    constructor <;> linarith [hu.1, hu.2])
  obtain ⟨hsl, hsu⟩ := radius_sq_bounds hs
  have hl := mul_le_mul hsl (show (9999 / 10000 : ℝ) ≤ 1 - u ^ 2 by nlinarith)
    (by norm_num) (sq_nonneg s)
  have hh := mul_le_mul_of_nonneg_left
    (show 1 - u ^ 2 ≤ (1 : ℝ) by nlinarith [sq_nonneg u]) (sq_nonneg s)
  rw [mul_pow, hsqrt]
  constructor <;> nlinarith only [hl, hh, hsu]

theorem crossing_height_pos {κ s u : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hu : u ∈ Icc (-1 / 100 : ℝ) (1 / 100)) : 0 < height κ s u := by
  have hk0 : 0 < κ := by linarith [hk.1]
  have hs0 : 0 < s := by linarith [hs.1]
  have hu2 := sq_le_sq' hu.1 hu.2
  have hr : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hu.2 hs0.le
  have hx : 0 < -(-3 / 4 + s * u) := by nlinarith [hs.2]
  have hp := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hk0) hx)
    (mul_pos hs0 hr)
  unfold height
  nlinarith only [hp]

/-- The imaginary-axis height has a strict uniform enclosure, obtained
from the crossing identity rather than sampled angles. -/
theorem crossing_height_sq_bounds {κ s u : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hu : u ∈ Icc (-1 / 100 : ℝ) (1 / 100)) (hz : crossing κ s u = 0) :
    (286 / 10000 : ℝ) < (height κ s u) ^ 2 ∧
      (height κ s u) ^ 2 < 315 / 10000 := by
  let x := -3 / 4 + s * u
  let y := s * Real.sqrt (1 - u ^ 2)
  have hsqrt := sqrt_square (show u ∈ Icc (-1 : ℝ) 1 by
    constructor <;> linarith [hu.1, hu.2])
  have hid : κ * (x ^ 2 - y ^ 2) = 1 - crossing κ s u := by
    dsimp [x, y]
    rw [mul_pow, hsqrt]
    unfold crossing
    ring
  have he : κ * (x ^ 2 - y ^ 2) = 1 := by simpa [hz] using hid
  have he' := congrArg (fun a : ℝ => 4 * κ * y ^ 2 * a) he
  have hh : (height κ s u) ^ 2 = 4 * (κ * y ^ 2) + 4 * (κ * y ^ 2) ^ 2 := by
    change (-2 * κ * x * y) ^ 2 = _
    nlinarith only [he']
  obtain ⟨hyl, hyu⟩ := ordinate_sq_bounds hs hu
  change (3968 / 1000000 : ℝ) ≤ y ^ 2 at hyl
  change y ^ 2 ≤ (1089 / 250000 : ℝ) at hyu
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hl := mul_le_mul hk.1 hyl (by norm_num) hk0
  have hh' := mul_le_mul hk.2 hyu (sq_nonneg y) (by norm_num)
  have ha : (71 / 10000 : ℝ) ≤ κ * y ^ 2 := by nlinarith only [hl]
  have hb : κ * y ^ 2 ≤ (78 / 10000 : ℝ) := by nlinarith only [hh']
  have ha2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 71 / 10000) ha 2
  have hb2 := pow_le_pow_left₀ (by linarith : 0 ≤ κ * y ^ 2) hb 2
  constructor <;> nlinarith only [hh, ha, hb, ha2, hb2]

/-- Uniform terminal margins for the third image, across the entire
parameter and circle-radius rectangle. -/
theorem terminal_bounds {κ s u : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hu : u ∈ Icc (-1 / 100 : ℝ) (1 / 100)) (hz : crossing κ s u = 0) :
    (-999 / 1000 : ℝ) < realMap κ (1 + κ * (height κ s u) ^ 2) ∧
      realMap κ (1 + κ * (height κ s u) ^ 2) < -977 / 1000 := by
  obtain ⟨hyl, hyu⟩ := crossing_height_sq_bounds hk hs hu hz
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hl := mul_le_mul hk.1 hyl.le (by norm_num) hk0
  have hh := mul_le_mul hk.2 hyu.le (sq_nonneg _) (by norm_num)
  let b := 1 + κ * (height κ s u) ^ 2
  have hbl : (1051 / 1000 : ℝ) ≤ b := by dsimp [b]; nlinarith only [hl]
  have hbu : b ≤ (5282 / 5000 : ℝ) := by dsimp [b]; nlinarith only [hh]
  have hbl2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1051 / 1000) hbl 2
  have hbu2 := pow_le_pow_left₀ (by linarith : 0 ≤ b) hbu 2
  have hpl := mul_le_mul hk.1 hbl2 (by norm_num) hk0
  have hpu := mul_le_mul hk.2 hbu2 (sq_nonneg b) (by norm_num)
  change -999 / 1000 < 1 - κ * b ^ 2 ∧ 1 - κ * b ^ 2 < -977 / 1000
  constructor <;> nlinarith only [hpl, hpu]

/-- The upper terminal cut is separated from the corridor by more than
one thousandth in the normalized real coordinate. -/
theorem fourth_critical_upper {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000)) :
    (realMap κ)^[4] 0 < (976 / 1000 : ℝ) := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hkc : (179 / 100 : ℝ) ≤ κ := by linarith [hk.1]
  have ha : (79 / 100 : ℝ) ≤ κ - 1 := by linarith [hk.1]
  have ha2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 79 / 100) ha 2
  have hp := mul_le_mul hkc ha2 (by norm_num) hk0
  have hb : (117 / 1000 : ℝ) ≤ -(1 - κ * (1 - κ) ^ 2) := by nlinarith only [hp]
  have hb2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 117 / 1000) hb 2
  have hq := mul_le_mul hkc hb2 (by norm_num) hk0
  change 1 - κ * (1 - κ * (1 - κ * (1 - κ * 0 ^ 2) ^ 2) ^ 2) ^ 2 < 976 / 1000
  norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero,
    one_pow, mul_one]
  nlinarith only [hq]

theorem complexMap_real (κ t : ℝ) :
    complexMap κ (t : ℂ) = (realMap κ t : ℂ) := by
  simp [complexMap, realMap]

theorem complexMap_imaginary (κ t : ℝ) :
    complexMap κ ((t : ℂ) * Complex.I) = ((1 + κ * t ^ 2 : ℝ) : ℂ) := by
  simp [complexMap, mul_pow, Complex.I_sq]

/-- All three images are literal complex polynomial images, and the
last one is the real terminal coordinate estimated above. -/
theorem third_image {κ s u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1)
    (hz : crossing κ s u = 0) :
    (complexMap κ)^[3] (circlePoint s u) =
      (realMap κ (1 + κ * (height κ s u) ^ 2) : ℂ) := by
  change complexMap κ (complexMap κ (complexMap κ (circlePoint s u))) = _
  rw [circle_image κ s hu, hz]
  simp only [Complex.ofReal_zero, zero_add]
  rw [complexMap_imaginary, complexMap_real]

/-- A nonempty common family of actual circles with positive imaginary
crossings and strict third-image terminal gates. -/
theorem uniform_model_corridor {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500)) :
    ∃ u : ℝ, u ∈ Ioo (-1 / 100 : ℝ) (1 / 100) ∧
      ‖circlePoint s u + (3 / 4 : ℂ)‖ = s ∧
      0 < height κ s u ∧
      complexMap κ (circlePoint s u) = (height κ s u : ℂ) * Complex.I ∧
      (-999 / 1000 : ℝ) < ((complexMap κ)^[3] (circlePoint s u)).re ∧
      ((complexMap κ)^[3] (circlePoint s u)).re < -977 / 1000 ∧
      ((complexMap κ)^[3] (circlePoint s u)).re < -(realMap κ)^[4] 0 := by
  obtain ⟨u, ⟨hu, hz⟩, _⟩ := crossing_root_unique hk hs
  have hu' : u ∈ Icc (-1 / 100 : ℝ) (1 / 100) := ⟨hu.1.le, hu.2.le⟩
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]
  have him := circle_image κ s hu1
  rw [hz] at him
  simp only [Complex.ofReal_zero, zero_add] at him
  have hi := third_image hu1 hz
  have hre : ((complexMap κ)^[3] (circlePoint s u)).re =
      realMap κ (1 + κ * (height κ s u) ^ 2) := by rw [hi]; rfl
  obtain ⟨htl, htu⟩ := terminal_bounds hk hs hu' hz
  have hcut := fourth_critical_upper hk
  refine ⟨u, hu, circle_radius (by linarith [hs.1]) hu1,
    crossing_height_pos hk hs hu', him, ?_, ?_, ?_⟩
  · rw [hre]; exact htl
  · rw [hre]; exact htu
  · rw [hre]; linarith

end
end LimitingCrest
