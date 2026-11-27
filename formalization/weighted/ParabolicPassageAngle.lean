import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

/-!
# Discrete angular passage through a quadratic bottleneck

The scale `s` is positive.  The angle `arctan (x / s)` converts a step
comparable to `s^2 + x^2` into a step comparable to `s`.  Both endpoints
are required to remain in the stated central window.
-/

namespace ParabolicPassageAngle

open Set

/-- The derivative of the rescaled passage angle. -/
theorem hasDerivAt_angle {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (fun z : ℝ => Real.arctan (z / s))
      (s / (s ^ 2 + x ^ 2)) x := by
  have hden : s ^ 2 + x ^ 2 ≠ 0 := by positivity
  convert ((hasDerivAt_id x).div_const s).arctan using 1
  · funext z
    simp only [id_eq, div_eq_mul_inv]
  · simp only [id_eq]
    field_simp [ne_of_gt hs, hden]

/-- An exact intermediate-point formula for one positive passage step. -/
theorem angle_step_eq {s x y : ℝ} (hs : 0 < s) (hxy : x < y) :
    ∃ z ∈ Ioo x y,
      Real.arctan (y / s) - Real.arctan (x / s) =
        (y - x) * s / (s ^ 2 + z ^ 2) := by
  obtain ⟨z, hz, heq⟩ := exists_hasDerivAt_eq_slope
    (fun u : ℝ => Real.arctan (u / s))
    (fun u : ℝ => s / (s ^ 2 + u ^ 2)) hxy
    (by fun_prop) (fun u _ => hasDerivAt_angle hs u)
  refine ⟨z, hz, ?_⟩
  have hmul := (eq_div_iff (sub_ne_zero.mpr hxy.ne')).mp heq
  calc
    Real.arctan (y / s) - Real.arctan (x / s) =
        s / (s ^ 2 + z ^ 2) * (y - x) := hmul.symm
    _ = (y - x) * s / (s ^ 2 + z ^ 2) := by ring

/-- The quadratic denominator varies by a relative amount at most `2 * δ * b`
along a step of size at most `b * (s^2 + x^2)` inside `[-δ, δ]`. -/
theorem quadratic_denominator_variation {s δ b x y z : ℝ}
    (hδ : 0 ≤ δ) (hxy : x ≤ y)
    (hx : |x| ≤ δ) (hy : |y| ≤ δ) (hz : z ∈ Icc x y)
    (hstep : y - x ≤ b * (s ^ 2 + x ^ 2)) :
    |(s ^ 2 + z ^ 2) - (s ^ 2 + x ^ 2)| ≤
      (2 * δ * b) * (s ^ 2 + x ^ 2) := by
  have hzabs : |z| ≤ δ := abs_le.mpr
    ⟨le_trans (abs_le.mp hx).1 hz.1, le_trans hz.2 (abs_le.mp hy).2⟩
  have hminus : |z - x| ≤ y - x := by
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1)]
    exact sub_le_sub_right hz.2 x
  have hplus : |z + x| ≤ 2 * δ := by
    calc
      |z + x| ≤ |z| + |x| := abs_add_le z x
      _ ≤ δ + δ := add_le_add hzabs hx
      _ = 2 * δ := by ring
  calc
    |(s ^ 2 + z ^ 2) - (s ^ 2 + x ^ 2)| = |(z - x) * (z + x)| := by
      congr 1
      ring
    _ = |z - x| * |z + x| := abs_mul _ _
    _ ≤ (y - x) * (2 * δ) :=
      mul_le_mul hminus hplus (abs_nonneg _) (sub_nonneg.mpr hxy)
    _ ≤ (b * (s ^ 2 + x ^ 2)) * (2 * δ) :=
      mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = (2 * δ * b) * (s ^ 2 + x ^ 2) := by ring

/-- Uniform two-sided angular bounds for a discrete quadratic passage step.

For an increment approximately `B * (s^2 + x^2)`, take `a = B*(1-ε)`
and `b = B*(1+ε)`.  The denominator loss tends to zero with the window
radius `δ`, independently of the much smaller bottleneck scale `s`.
-/
theorem angle_step_bounds {s δ a b x y : ℝ}
    (hs : 0 < s) (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxy : x < y) (hx : |x| ≤ δ) (hy : |y| ≤ δ)
    (hlower : a * (s ^ 2 + x ^ 2) ≤ y - x)
    (hupper : y - x ≤ b * (s ^ 2 + x ^ 2))
    (hsmall : 2 * δ * b < 1) :
    a * s / (1 + 2 * δ * b) ≤
        Real.arctan (y / s) - Real.arctan (x / s) ∧
      Real.arctan (y / s) - Real.arctan (x / s) ≤
        b * s / (1 - 2 * δ * b) := by
  obtain ⟨z, hz, hangle⟩ := angle_step_eq hs hxy
  have hvariation := quadratic_denominator_variation hδ hxy.le hx hy
    (mem_Icc_of_Ioo hz) hupper
  have hden : 0 < s ^ 2 + z ^ 2 := by positivity
  have he : 0 ≤ 2 * δ * b := by positivity
  have hplus : 0 < 1 + 2 * δ * b := by positivity
  have hminus : 0 < 1 - 2 * δ * b := by linarith
  have hlo : (1 - 2 * δ * b) * (s ^ 2 + x ^ 2) ≤ s ^ 2 + z ^ 2 := by
    have := (abs_le.mp hvariation).1
    nlinarith
  have hhi : s ^ 2 + z ^ 2 ≤ (1 + 2 * δ * b) * (s ^ 2 + x ^ 2) := by
    have := (abs_le.mp hvariation).2
    nlinarith
  constructor
  · rw [hangle]
    apply (div_le_div_iff₀ hplus hden).2
    calc
      (a * s) * (s ^ 2 + z ^ 2) ≤
          (a * s) * ((1 + 2 * δ * b) * (s ^ 2 + x ^ 2)) :=
        mul_le_mul_of_nonneg_left hhi (mul_nonneg ha hs.le)
      _ = (a * (s ^ 2 + x ^ 2)) * (s * (1 + 2 * δ * b)) := by ring
      _ ≤ (y - x) * (s * (1 + 2 * δ * b)) :=
        mul_le_mul_of_nonneg_right hlower (by positivity)
      _ = ((y - x) * s) * (1 + 2 * δ * b) := by ring
  · rw [hangle]
    apply (div_le_div_iff₀ hden hminus).2
    calc
      ((y - x) * s) * (1 - 2 * δ * b) =
          (y - x) * (s * (1 - 2 * δ * b)) := by ring
      _ ≤ (b * (s ^ 2 + x ^ 2)) * (s * (1 - 2 * δ * b)) :=
        mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = (b * s) * ((1 - 2 * δ * b) * (s ^ 2 + x ^ 2)) := by ring
      _ ≤ (b * s) * (s ^ 2 + z ^ 2) :=
        mul_le_mul_of_nonneg_left hlo (mul_nonneg hb hs.le)

/-- A convenient error form of the two-sided bounds.  The local drift error
`η` and the angular denominator variation are both charged to `ε`. -/
theorem angle_step_error {s δ B ε η x y : ℝ}
    (hs : 0 < s) (hδ : 0 ≤ δ) (hB : 0 < B)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hη : 0 ≤ η) (hηε : η ≤ ε)
    (hxy : x < y) (hx : |x| ≤ δ) (hy : |y| ≤ δ)
    (hlower : (B * (1 - η)) * (s ^ 2 + x ^ 2) ≤ y - x)
    (hupper : y - x ≤ (B * (1 + η)) * (s ^ 2 + x ^ 2))
    (hscale : 2 * δ * (B * (1 + η)) ≤ ε) :
    |(Real.arctan (y / s) - Real.arctan (x / s)) - B * s| ≤
      4 * ε * (B * s) := by
  let e : ℝ := 2 * δ * (B * (1 + η))
  have he : 0 ≤ e := by dsimp [e]; positivity
  have heε : e ≤ ε := hscale
  have hehalf : e ≤ 1 / 2 := le_trans heε hεhalf
  have hplus : 0 < 1 + e := by positivity
  have hminus : 0 < 1 - e := by linarith
  have ha : 0 ≤ B * (1 - η) := mul_nonneg hB.le (by linarith)
  have hb : 0 ≤ B * (1 + η) := by positivity
  have hsmall : 2 * δ * (B * (1 + η)) < 1 := by
    linarith
  have hbounds := angle_step_bounds hs hδ ha hb hxy hx hy hlower hupper hsmall
  change (B * (1 - η)) * s / (1 + e) ≤
      Real.arctan (y / s) - Real.arctan (x / s) ∧
    Real.arctan (y / s) - Real.arctan (x / s) ≤
      (B * (1 + η)) * s / (1 - e) at hbounds
  have hratioLower : 1 - 4 * ε ≤ (1 - η) / (1 + e) := by
    apply (le_div_iff₀ hplus).2
    nlinarith [mul_nonneg hε he]
  have hratioUpper : (1 + η) / (1 - e) ≤ 1 + 4 * ε := by
    apply (div_le_iff₀ hminus).2
    nlinarith [mul_nonneg hε (show 0 ≤ 1 / 2 - e by linarith)]
  have hq : 0 ≤ B * s := mul_nonneg hB.le hs.le
  have hl : (B * s) * (1 - 4 * ε) ≤
      Real.arctan (y / s) - Real.arctan (x / s) := by
    calc
      (B * s) * (1 - 4 * ε) ≤ (B * s) * ((1 - η) / (1 + e)) :=
        mul_le_mul_of_nonneg_left hratioLower hq
      _ = (B * (1 - η)) * s / (1 + e) := by ring
      _ ≤ Real.arctan (y / s) - Real.arctan (x / s) := hbounds.1
  have hu : Real.arctan (y / s) - Real.arctan (x / s) ≤
      (B * s) * (1 + 4 * ε) := by
    calc
      Real.arctan (y / s) - Real.arctan (x / s) ≤
          (B * (1 + η)) * s / (1 - e) := hbounds.2
      _ = (B * s) * ((1 + η) / (1 - e)) := by ring
      _ ≤ (B * s) * (1 + 4 * ε) :=
        mul_le_mul_of_nonneg_left hratioUpper hq
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end ParabolicPassageAngle
