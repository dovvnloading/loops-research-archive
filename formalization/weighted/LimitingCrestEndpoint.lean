import LimitingCrestGeometry
import Mathlib.Tactic.FieldSimp

/-!
# The terminal endpoint of the limiting circular crest

An explicit radical follows the negative-real, positive-imaginary crossing
branch on the full proposed parent radius interval. Its third image is
strictly decreasing and has one terminal collision, uniformly bracketed.
-/

namespace LimitingCrest

open Set Function
noncomputable section

def radialDiscriminant (κ s : ℝ) : ℝ := 8 / κ + 8 * s ^ 2 - 9 / 4

def radialAbscissa (κ s : ℝ) : ℝ := -3 / 8 - Real.sqrt (radialDiscriminant κ s) / 4

def radialOrdinateSq (κ s : ℝ) : ℝ := (radialAbscissa κ s) ^ 2 - 1 / κ

def radialTerminal (κ v : ℝ) : ℝ :=
  1 - κ * (1 + κ * (4 * (κ * v) + 4 * (κ * v) ^ 2)) ^ 2

def crestTerminal (κ s : ℝ) : ℝ := radialTerminal κ (radialOrdinateSq κ s)

private theorem reciprocal_bounds {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000)) :
    (223 / 50 : ℝ) ≤ 8 / κ ∧ 8 / κ ≤ 447 / 100 ∧ 1 / κ ≤ 14 / 25 := by
  have hk0 : 0 < κ := by linarith [hk.1]
  constructor
  · apply (le_div_iff₀ hk0).2
    nlinarith [hk.2]
  constructor
  · apply (div_le_iff₀ hk0).2
    nlinarith [hk.1]
  · apply (div_le_iff₀ hk0).2
    nlinarith [hk.1]

private theorem discriminant_lower {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) :
    (56 / 25 : ℝ) ≤ radialDiscriminant κ s := by
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 16) hs.1 2
  have hr := (reciprocal_bounds hk).1
  unfold radialDiscriminant
  nlinarith only [hsq, hr]

private theorem abscissa_negative {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) :
    radialAbscissa κ s ≤ (-749 / 1000 : ℝ) := by
  have hd := discriminant_lower hk hs
  have hr := Real.sq_sqrt (show 0 ≤ radialDiscriminant κ s by linarith)
  have hn := Real.sqrt_nonneg (radialDiscriminant κ s)
  have hsqrt : (1496 / 1000 : ℝ) ≤ Real.sqrt (radialDiscriminant κ s) := by
    nlinarith only [hd, hr, hn]
  unfold radialAbscissa
  linarith

/-- The formula has a genuinely positive imaginary coordinate throughout
the full parent interval, including its inner boundary. -/
theorem radial_ordinate_pos {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) : 0 < radialOrdinateSq κ s := by
  have hx := abscissa_negative hk hs
  have hx2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 749 / 1000)
    (show (749 / 1000 : ℝ) ≤ -radialAbscissa κ s by linarith) 2
  have hi := (reciprocal_bounds hk).2.2
  unfold radialOrdinateSq
  nlinarith only [hx2, hi]

/-- This is the exact circle equation, not a numerical parametrization. -/
theorem radial_circle_identity {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) :
    (radialAbscissa κ s + 3 / 4) ^ 2 + radialOrdinateSq κ s = s ^ 2 := by
  have hd := discriminant_lower hk hs
  have hr := Real.sq_sqrt (show 0 ≤ radialDiscriminant κ s by linarith)
  unfold radialOrdinateSq radialAbscissa radialDiscriminant at *
  nlinarith only [hr]

private theorem radial_ordinate_upper {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) : radialOrdinateSq κ s ≤ s ^ 2 := by
  have h := radial_circle_identity hk hs
  nlinarith only [h, sq_nonneg (radialAbscissa κ s + 3 / 4)]

private theorem radial_ordinate_lower_near_endpoint {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (133 / 2000)) :
    s ^ 2 - 1 / 1000000 ≤ radialOrdinateSq κ s := by
  have hs' : s ∈ Icc (1 / 16 : ℝ) (1 / 8) := ⟨hs.1, by linarith [hs.2]⟩
  have hd := discriminant_lower hk hs'
  have hi := (reciprocal_bounds hk).2.1
  have hsq := pow_le_pow_left₀ (by linarith [hs.1] : 0 ≤ s) hs.2 2
  have hdu : radialDiscriminant κ s ≤ (2256 / 1000 : ℝ) := by
    unfold radialDiscriminant
    nlinarith only [hi, hsq]
  have hr := Real.sq_sqrt (show 0 ≤ radialDiscriminant κ s by linarith)
  have hn := Real.sqrt_nonneg (radialDiscriminant κ s)
  have hrl : (1496 / 1000 : ℝ) ≤ Real.sqrt (radialDiscriminant κ s) := by
    nlinarith only [hd, hr, hn]
  have hru : Real.sqrt (radialDiscriminant κ s) ≤ (1504 / 1000 : ℝ) := by
    nlinarith only [hdu, hr, hn]
  have hxlo : (-1 / 1000 : ℝ) ≤ radialAbscissa κ s + 3 / 4 := by
    unfold radialAbscissa
    linarith
  have hxhi : radialAbscissa κ s + 3 / 4 ≤ (1 / 1000 : ℝ) := by
    unfold radialAbscissa
    linarith
  have hxsq := sq_le_sq' (show -(1 / 1000 : ℝ) ≤ radialAbscissa κ s + 3 / 4 by
    linarith only [hxlo]) hxhi
  have hc := radial_circle_identity hk hs'
  nlinarith only [hxsq, hc]

private theorem radialTerminal_antitone {κ λ v w : ℝ}
    (hk : 0 ≤ κ) (hkl : κ ≤ λ) (hv : 0 ≤ v) (hvw : v ≤ w) :
    radialTerminal λ w ≤ radialTerminal κ v := by
  have hl : 0 ≤ λ := hk.trans hkl
  have hw : 0 ≤ w := hv.trans hvw
  have hav : 0 ≤ κ * v := mul_nonneg hk hv
  have haw : 0 ≤ λ * w := mul_nonneg hl hw
  have ha := mul_le_mul hkl hvw hv hl
  have ha2 := pow_le_pow_left₀ hav ha 2
  have hy : 4 * (κ * v) + 4 * (κ * v) ^ 2 ≤
      4 * (λ * w) + 4 * (λ * w) ^ 2 := by linarith
  have hy0 : 0 ≤ 4 * (κ * v) + 4 * (κ * v) ^ 2 := by positivity
  have hb := mul_le_mul hkl hy hy0 hl
  have hb0 : 0 ≤ 1 + κ * (4 * (κ * v) + 4 * (κ * v) ^ 2) := by positivity
  have hb2 := pow_le_pow_left₀ hb0 (show
      1 + κ * (4 * (κ * v) + 4 * (κ * v) ^ 2) ≤
      1 + λ * (4 * (λ * w) + 4 * (λ * w) ^ 2) by linarith) 2
  have hf := mul_le_mul hkl hb2 (sq_nonneg _) hl
  unfold radialTerminal
  linarith

private theorem radialTerminal_strictAnti {κ : ℝ} (hk : 0 < κ) :
    StrictAntiOn (radialTerminal κ) (Ici 0) := by
  intro v hv w hw hvw
  have hav : 0 ≤ κ * v := mul_nonneg hk.le hv
  have haw : 0 ≤ κ * w := mul_nonneg hk.le hw
  have ha := mul_lt_mul_of_pos_left hvw hk
  have ha2 := pow_le_pow_left₀ hav ha.le 2
  have hy : 4 * (κ * v) + 4 * (κ * v) ^ 2 <
      4 * (κ * w) + 4 * (κ * w) ^ 2 := by linarith
  have hy0 : 0 ≤ 4 * (κ * v) + 4 * (κ * v) ^ 2 := by positivity
  have hb := mul_lt_mul_of_pos_left hy hk
  have hb0 : 0 < 1 + κ * (4 * (κ * v) + 4 * (κ * v) ^ 2) := by positivity
  have hbsq : (1 + κ * (4 * (κ * v) + 4 * (κ * v) ^ 2)) ^ 2 <
      (1 + κ * (4 * (κ * w) + 4 * (κ * w) ^ 2)) ^ 2 :=
    pow_lt_pow_left₀ (by linarith only [hb]) hb0.le (by decide)
  have hf := mul_lt_mul_of_pos_left hbsq hk
  unfold radialTerminal
  linarith

/-- Strict radial ordering of the actual third-image terminal coordinate. -/
theorem crestTerminal_strictAnti {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000)) :
    StrictAntiOn (crestTerminal κ) (Icc (1 / 16 : ℝ) (1 / 8)) := by
  intro s hs t ht hst
  have hspos : 0 < s := by linarith [hs.1]
  have htpos : 0 < t := by linarith [ht.1]
  have hdst : radialDiscriminant κ s < radialDiscriminant κ t := by
    unfold radialDiscriminant
    nlinarith only [hspos, htpos, hst]
  have hds := discriminant_lower hk hs
  have hdt := discriminant_lower hk ht
  have hsqrt := Real.sq_sqrt (show 0 ≤ radialDiscriminant κ s by linarith)
  have htqrt := Real.sq_sqrt (show 0 ≤ radialDiscriminant κ t by linarith)
  have hroot : Real.sqrt (radialDiscriminant κ s) < Real.sqrt (radialDiscriminant κ t) := by
    nlinarith [Real.sqrt_nonneg (radialDiscriminant κ s),
      Real.sqrt_nonneg (radialDiscriminant κ t)]
  have hx : radialAbscissa κ t < radialAbscissa κ s := by
    unfold radialAbscissa
    linarith
  have hxs := abscissa_negative hk hs
  have hxt := abscissa_negative hk ht
  have hx2 := pow_lt_pow_left₀ (neg_lt_neg hx)
    (show 0 ≤ -radialAbscissa κ s by linarith) (by decide : (2 : ℕ) ≠ 0)
  have hv : radialOrdinateSq κ s < radialOrdinateSq κ t := by
    unfold radialOrdinateSq
    nlinarith only [hx2]
  exact radialTerminal_strictAnti (by linarith [hk.1])
    (radial_ordinate_pos hk hs).le (radial_ordinate_pos hk ht).le hv

/-- The previously numerical model endpoint lies strictly between
663/10000 and 133/2000 for every parameter in the certified interval. -/
theorem crestTerminal_endpoint_signs {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000)) :
    -1 < crestTerminal κ (663 / 10000) ∧ crestTerminal κ (133 / 2000) < -1 := by
  have hsi : (663 / 10000 : ℝ) ∈ Icc (1 / 16 : ℝ) (1 / 8) := by
    constructor <;> norm_num
  have hso : (133 / 2000 : ℝ) ∈ Icc (1 / 16 : ℝ) (1 / 8) := by
    constructor <;> norm_num
  have hu := radial_ordinate_upper hk hsi
  have hl := radial_ordinate_lower_near_endpoint hk
    (show (133 / 2000 : ℝ) ∈ Icc (1 / 16 : ℝ) (133 / 2000) by constructor <;> norm_num)
  have hinner := radialTerminal_antitone (by linarith [hk.1]) hk.2
    (radial_ordinate_pos hk hsi).le hu
  have houter := radialTerminal_antitone (by norm_num : (0 : ℝ) ≤ 17903 / 10000) hk.1
    (by norm_num : (0 : ℝ) ≤ (133 / 2000 : ℝ) ^ 2 - 1 / 1000000) hl
  have hri : (-1 : ℝ) < radialTerminal (17904 / 10000) ((663 / 10000) ^ 2) := by
    norm_num [radialTerminal]
  have hro : radialTerminal (17903 / 10000) ((133 / 2000) ^ 2 - 1 / 1000000) < (-1 : ℝ) := by
    norm_num [radialTerminal]
  exact ⟨hri.trans_le hinner, houter.trans_lt hro⟩

theorem crestTerminal_continuous (κ : ℝ) : Continuous (crestTerminal κ) := by
  unfold crestTerminal radialTerminal radialOrdinateSq radialAbscissa radialDiscriminant
  fun_prop

def radialPoint (κ s : ℝ) : ℂ :=
  (radialAbscissa κ s : ℂ) + (Real.sqrt (radialOrdinateSq κ s) : ℂ) * Complex.I

def radialHeight (κ s : ℝ) : ℝ :=
  -2 * κ * radialAbscissa κ s * Real.sqrt (radialOrdinateSq κ s)

/-- The radical parametrization is on the actual circle, its first image
is on the positive imaginary axis, and its third image is exactly the
terminal function used in the endpoint theorem. -/
theorem radial_model_realization {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) :
    ‖radialPoint κ s + (3 / 4 : ℂ)‖ = s ∧
      0 < radialHeight κ s ∧
      complexMap κ (radialPoint κ s) = (radialHeight κ s : ℂ) * Complex.I ∧
      (complexMap κ)^[3] (radialPoint κ s) = (crestTerminal κ s : ℂ) := by
  have hk0 : 0 < κ := by linarith [hk.1]
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hv := radial_ordinate_pos hk hs
  have hy := Real.sq_sqrt hv.le
  have hypos := Real.sqrt_pos.mpr hv
  have hx := abscissa_negative hk hs
  have hc := radial_circle_identity hk hs
  have hnorm : ‖radialPoint κ s + (3 / 4 : ℂ)‖ = s := by
    have hn : ‖radialPoint κ s + (3 / 4 : ℂ)‖ ^ 2 = s ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [radialPoint, Complex.mul_re, Complex.mul_im]
      nlinarith only [hy, hc]
    nlinarith only [hn, hs0, norm_nonneg (radialPoint κ s + (3 / 4 : ℂ))]
  have hp := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hk0)
    (show 0 < -radialAbscissa κ s by linarith)) hypos
  have hhpos : 0 < radialHeight κ s := by
    unfold radialHeight
    nlinarith only [hp]
  have hdiff : κ * ((radialAbscissa κ s) ^ 2 - radialOrdinateSq κ s) = 1 := by
    unfold radialOrdinateSq
    field_simp [hk0.ne'] <;> ring
  have him : complexMap κ (radialPoint κ s) = (radialHeight κ s : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [complexMap, radialPoint, radialHeight, Complex.mul_re,
        Complex.mul_im, pow_two]
      nlinarith [congrArg (fun t : ℝ => κ * t) hy]
    · simp [complexMap, radialPoint, radialHeight, Complex.mul_re,
        Complex.mul_im, pow_two]
      ring
  have hh : (radialHeight κ s) ^ 2 =
      4 * (κ * radialOrdinateSq κ s) + 4 * (κ * radialOrdinateSq κ s) ^ 2 := by
    have hmul := congrArg (fun t : ℝ => 4 * κ * radialOrdinateSq κ s * t) hdiff
    have hmul' := congrArg (fun t : ℝ => 4 * κ ^ 2 * (radialAbscissa κ s) ^ 2 * t) hy
    unfold radialHeight
    nlinarith only [hmul, hmul']
  have hthree : (complexMap κ)^[3] (radialPoint κ s) =
      (realMap κ (1 + κ * (radialHeight κ s) ^ 2) : ℂ) := by
    change complexMap κ (complexMap κ (complexMap κ (radialPoint κ s))) = _
    rw [him, complexMap_imaginary, complexMap_real]
  have hterm : realMap κ (1 + κ * (radialHeight κ s) ^ 2) = crestTerminal κ s := by
    rw [hh]
    rfl
  exact ⟨hnorm, hhpos, him, hthree.trans (congrArg (fun t : ℝ => (t : ℂ)) hterm)⟩

private theorem fourth_critical_sharp {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000)) :
    (realMap κ)^[4] 0 < (9751 / 10000 : ℝ) := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have ha : (7903 / 10000 : ℝ) ≤ κ - 1 := by linarith [hk.1]
  have ha2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7903 / 10000) ha 2
  have hp := mul_le_mul hk.1 ha2 (by norm_num) hk0
  have hb : (1181 / 10000 : ℝ) ≤ -(1 - κ * (1 - κ) ^ 2) := by nlinarith only [hp]
  have hb2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1181 / 10000) hb 2
  have hq := mul_le_mul hk.1 hb2 (by norm_num) hk0
  change 1 - κ * (1 - κ * (1 - κ * (1 - κ * 0 ^ 2) ^ 2) ^ 2) ^ 2 < 9751 / 10000
  norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero,
    one_pow, mul_one]
  nlinarith only [hq]

/-- The opposite terminal cut never obstructs this entire radial branch. -/
theorem crestTerminal_upper_gate {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (1 / 16 : ℝ) (1 / 8)) :
    crestTerminal κ s < -(realMap κ)^[4] 0 := by
  have hfirst : (1 / 16 : ℝ) ∈ Icc (1 / 16 : ℝ) (1 / 8) := by
    constructor <;> norm_num
  have hl := radial_ordinate_lower_near_endpoint hk
    (show (1 / 16 : ℝ) ∈ Icc (1 / 16 : ℝ) (133 / 2000) by constructor <;> norm_num)
  have hm := radialTerminal_antitone (by norm_num : (0 : ℝ) ≤ 17903 / 10000) hk.1
    (by norm_num : (0 : ℝ) ≤ (1 / 16 : ℝ) ^ 2 - 1 / 1000000) hl
  have hr : radialTerminal (17903 / 10000) ((1 / 16) ^ 2 - 1 / 1000000) <
      (-9753 / 10000 : ℝ) := by norm_num [radialTerminal]
  have hbase : crestTerminal κ (1 / 16) < (-9753 / 10000 : ℝ) := hm.trans_lt hr
  have hdown := (crestTerminal_strictAnti hk).antitoneOn hfirst hs hs.1
  have hcut := fourth_critical_sharp hk
  linarith

/-- There is exactly one terminal collision in the full parent interval,
and every smaller radius is on the same strict side of its terminal gate. -/
theorem unique_model_endpoint {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000)) :
    ∃ r ∈ Ioo (663 / 10000 : ℝ) (133 / 2000),
      crestTerminal κ r = -1 ∧
      (∀ s ∈ Icc (1 / 16 : ℝ) (1 / 8), crestTerminal κ s = -1 ↔ s = r) ∧
      (∀ s ∈ Icc (1 / 16 : ℝ) (1 / 8), -1 < crestTerminal κ s ↔ s < r) := by
  obtain ⟨hi, ho⟩ := crestTerminal_endpoint_signs hk
  have hc : Continuous (fun s => -crestTerminal κ s) := (crestTerminal_continuous κ).neg
  obtain ⟨r, hr, hz⟩ := intermediate_value_Icc
    (by norm_num : (663 / 10000 : ℝ) ≤ 133 / 2000) hc.continuousOn
    (show (1 : ℝ) ∈ Icc (-crestTerminal κ (663 / 10000))
      (-crestTerminal κ (133 / 2000)) by constructor <;> linarith)
  have he : crestTerminal κ r = -1 := by linarith
  have hri : r ∈ Ioo (663 / 10000 : ℝ) (133 / 2000) := by
    constructor
    · by_contra h
      have eq : r = 663 / 10000 := by linarith [hr.1]
      rw [eq] at he
      linarith
    · by_contra h
      have eq : r = 133 / 2000 := by linarith [hr.2]
      rw [eq] at he
      linarith
  have hparent : r ∈ Icc (1 / 16 : ℝ) (1 / 8) := by
    constructor <;> linarith [hr.1, hr.2]
  have hmono := crestTerminal_strictAnti hk
  refine ⟨r, hri, he, ?_, ?_⟩
  · intro s hs
    constructor
    · intro hz'
      exact hmono.injOn hs hparent (hz'.trans he.symm)
    · intro eq
      simpa [eq] using he
  · intro s hs
    constructor
    · intro hg
      by_contra h
      have hm := hmono.antitoneOn hparent hs (le_of_not_gt h)
      linarith
    · intro hsr
      have hm := hmono hs hparent hsr
      linarith

end
end LimitingCrest
