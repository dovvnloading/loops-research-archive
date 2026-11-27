import LimitingCrestGeometry
import LimitingCrestPerturbation

/-!
# A quantitative open neighborhood of the limiting crest corridor

A continuous complex map within two millionths of the limiting quadratic
on the disk of radius 23/20 has an imaginary-axis crossing on every circle
in the fixed radial interval.  Exact real- and imaginary-axis preservation
makes its second and third images real.  Explicit interval estimates place
the third image strictly between the moving source cuts.  The assertions
are about literal complex iterates; no marked-path realization is inferred.
-/

namespace LimitingCrest

open Set Function
noncomputable section

private theorem circle_in_approximation_disk {s u : ℝ}
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hu : u ∈ Icc (-1 / 100 : ℝ) (1 / 100)) :
    ‖circlePoint s u‖ ≤ 23/20 := by
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have hr := circle_radius (show 0 ≤ s by linarith [hs.1]) hu1
  calc
    ‖circlePoint s u‖ =
        ‖(circlePoint s u + (3/4 : ℂ)) - (3/4 : ℂ)‖ := by congr 1; ring
    _ ≤ ‖circlePoint s u + (3/4 : ℂ)‖ + ‖(3/4 : ℂ)‖ := norm_sub_le _ _
    _ = s + 3/4 := by rw [hr]; norm_num
    _ ≤ 23/20 := by linarith [hs.2]

private theorem height_rectangle_bounds {κ s u : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hu : u ∈ Icc (-1 / 100 : ℝ) (1 / 100)) :
    (169/1000 : ℝ) ≤ height κ s u ∧
      height κ s u ≤ 17741/100000 := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hu2 : u^2 ≤ (1/100 : ℝ)^2 :=
    sq_le_sq' (show -(1/100 : ℝ) ≤ u by linarith [hu.1]) hu.2
  have hr0 : 0 ≤ 1-u^2 := by nlinarith
  have hrsq := Real.sq_sqrt hr0
  have hrpos := Real.sqrt_nonneg (1-u^2)
  have hrl : (9999/10000 : ℝ) ≤ Real.sqrt (1-u^2) := by
    by_contra h
    have hp : 0 < (9999/10000-Real.sqrt (1-u^2)) *
        (9999/10000+Real.sqrt (1-u^2)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith only [hrsq, hp, hu2]
  have hru : Real.sqrt (1-u^2) ≤ (1 : ℝ) := by
    by_contra h
    have hp : 0 < (Real.sqrt (1-u^2)-1) * (Real.sqrt (1-u^2)+1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith only [hrsq, hp, sq_nonneg u]
  have hsu := mul_le_mul_of_nonneg_left hu.2 hs0
  have hsl := mul_le_mul_of_nonneg_left hu.1 hs0
  have hal : (37467/50000 : ℝ) ≤ 3/4-s*u := by
    nlinarith only [hsu, hs.2]
  have hau : 3/4-s*u ≤ (37533/50000 : ℝ) := by
    nlinarith only [hsl, hs.2]
  have ha0 : 0 ≤ 3/4-s*u := by linarith
  have hyl := mul_le_mul hs.1 hrl (by norm_num) hs0
  have hyu := mul_le_mul hs.2 hru hrpos (by norm_num)
  have hy0 : 0 ≤ s * Real.sqrt (1-u^2) := mul_nonneg hs0 hrpos
  have hkl := mul_le_mul hk.1 hal (by norm_num) hk0
  have hku := mul_le_mul hk.2 hau ha0 (by norm_num)
  have hlow := mul_le_mul hkl hyl (by norm_num) (mul_nonneg hk0 ha0)
  have hupp := mul_le_mul hku hyu hy0 (by norm_num)
  unfold height
  constructor <;> nlinarith only [hlow, hupp]

private theorem real_part_error (H : ℂ → ℂ) (κ : ℝ)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 →
      ‖H w-complexMap κ w‖ ≤ 1/500000)
    (w : ℂ) (hw : ‖w‖ ≤ 23/20) :
    |(H w).re-(complexMap κ w).re| ≤ (1/500000 : ℝ) := by
  simpa only [Complex.sub_re] using
    (Complex.abs_re_le_norm (H w-complexMap κ w)).trans (hclose w hw)

private theorem imaginary_part_error (H : ℂ → ℂ) (κ : ℝ)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 →
      ‖H w-complexMap κ w‖ ≤ 1/500000)
    (w : ℂ) (hw : ‖w‖ ≤ 23/20) :
    |(H w).im-(complexMap κ w).im| ≤ (1/500000 : ℝ) := by
  simpa only [Complex.sub_im] using
    (Complex.abs_im_le_norm (H w-complexMap κ w)).trans (hclose w hw)

/-- Uniform map error preserves an actual angular crossing on every
circle.  Continuity is sufficient; no derivative or uniqueness premise
is used.  The root is strictly inside the two fixed angular walls. -/
theorem perturbed_crossing_exists (H : ℂ → ℂ) (hH : Continuous H)
    {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 →
      ‖H w-complexMap κ w‖ ≤ 1/500000) :
    ∃ u : ℝ, u ∈ Ioo (-1/100 : ℝ) (1/100) ∧
      (H (circlePoint s u)).re = 0 := by
  have hcirc : Continuous (circlePoint s) := by unfold circlePoint; fun_prop
  have hc : Continuous (fun u : ℝ => (H (circlePoint s u)).re) :=
    Complex.continuous_re.comp (hH.comp hcirc)
  have hqre (u : ℝ) (hu : u ∈ Icc (-1/100 : ℝ) (1/100)) :
      (complexMap κ (circlePoint s u)).re = crossing κ s u := by
    rw [circle_image κ s (show u ∈ Icc (-1 : ℝ) 1 by
      constructor <;> linarith [hu.1, hu.2])]
    simp
  have hlE := real_part_error H κ hclose (circlePoint s (-1/100))
    (circle_in_approximation_disk hs (by constructor <;> norm_num))
  have hrE := real_part_error H κ hclose (circlePoint s (1/100))
    (circle_in_approximation_disk hs (by constructor <;> norm_num))
  rw [hqre _ (by constructor <;> norm_num)] at hlE
  rw [hqre _ (by constructor <;> norm_num)] at hrE
  obtain ⟨hl, hr⟩ := crossing_endpoint_margins hk hs
  have hleft : (H (circlePoint s (-1/100))).re < 0 := by
    have he := (abs_le.mp hlE).2
    linarith
  have hright : 0 < (H (circlePoint s (1/100))).re := by
    have he := (abs_le.mp hrE).1
    linarith
  obtain ⟨u, hu, hz⟩ := intermediate_value_Icc
    (by norm_num : (-1/100 : ℝ) ≤ 1/100) hc.continuousOn
    (show (0 : ℝ) ∈ Icc ((H (circlePoint s (-1/100))).re)
      ((H (circlePoint s (1/100))).re) from ⟨hleft.le, hright.le⟩)
  refine ⟨u, ?_, hz⟩
  constructor
  · by_contra h
    have he : u = -1/100 := by linarith [hu.1]
    rw [he] at hz
    linarith
  · by_contra h
    have he : u = 1/100 := by linarith [hu.2]
    rw [he] at hz
    linarith

private theorem complex_eq_real_of_im_zero (w : ℂ) (hw : w.im = 0) :
    w = (w.re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using hw

private theorem complex_eq_imaginary_of_re_zero (w : ℂ) (hw : w.re = 0) :
    w = (w.im : ℂ) * Complex.I := by
  apply Complex.ext
  · simpa using hw
  · simp

private theorem model_critical_cast (κ : ℝ) (n : ℕ) :
    (complexMap κ)^[n] (0 : ℂ) = ((realMap κ)^[n] (0 : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih, complexMap_real]

private theorem perturbed_fourth_cut_upper (H : ℂ → ℂ) {κ : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 →
      ‖H w-complexMap κ w‖ ≤ 1/500000) :
    ((H^[4]) 0).re < (2441/2500 : ℝ) := by
  have herr := LimitingCrestPerturbation.quadratic_fourth_cut_error κ
    (by linarith [hk.1]) (by linarith [hk.2]) H (1/500000)
    (by norm_num) le_rfl (by simpa only [complexMap] using hclose)
  have hcut := fourth_critical_upper hk
  have hcut' : ((complexMap κ)^[4] (0 : ℂ)).re ≤ 122/125 := by
    rw [model_critical_cast]
    simp only [Complex.ofReal_re]
    linarith
  apply LimitingCrestPerturbation.fourth_cut_real_upper H (complexMap κ)
    (1/500000) le_rfl _ hcut'
  simpa only [complexMap] using herr.1

/-- Every crossing in the fixed angular rectangle has real second and
third images, with strict terminal bounds and a moving-cut margin.
All evaluations needed for the uniform approximation remain in its disk. -/
theorem perturbed_terminal_bounds (H : ℂ → ℂ)
    (hreal : ∀ t : ℝ, (H (t : ℂ)).im = 0)
    (himag : ∀ t : ℝ, (H ((t : ℂ) * Complex.I)).im = 0)
    {κ s u : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100))
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 →
      ‖H w-complexMap κ w‖ ≤ 1/500000)
    (hroot : (H (circlePoint s u)).re = 0) :
    (H (circlePoint s u)).im ∈ Icc (168998/1000000 : ℝ) (177412/1000000) ∧
      ((H^[2]) (circlePoint s u)).im = 0 ∧
      ((H^[3]) (circlePoint s u)).im = 0 ∧
      (-999/1000 : ℝ) < ((H^[3]) (circlePoint s u)).re ∧
      ((H^[3]) (circlePoint s u)).re < -977/1000 ∧
      ((H^[3]) (circlePoint s u)).re < -((H^[4]) 0).re := by
  let z := circlePoint s u
  let Y := (H z).im
  let b := (H ((Y : ℂ) * Complex.I)).re
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have hqim : (complexMap κ z).im = height κ s u := by
    dsimp [z]
    rw [circle_image κ s hu1]
    simp
  have hyerror := imaginary_part_error H κ hclose z
    (circle_in_approximation_disk hs hu)
  rw [hqim] at hyerror
  have hyerr := abs_le.mp hyerror
  obtain ⟨hyl, hyu⟩ := height_rectangle_bounds hk hs hu
  have hybox : Y ∈ Icc (168998/1000000 : ℝ) (177412/1000000) := by
    dsimp [Y]
    constructor <;> linarith [hyerr.1, hyerr.2]
  have hy0 : 0 ≤ Y := by linarith [hybox.1]
  have hYdisk : ‖(Y : ℂ) * Complex.I‖ ≤ 23/20 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hy0]
    linarith [hybox.2]
  have hbErr := real_part_error H κ hclose ((Y : ℂ) * Complex.I) hYdisk
  rw [complexMap_imaginary] at hbErr
  simp only [Complex.ofReal_re] at hbErr
  have hbe := abs_le.mp hbErr
  have hy2l := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 168998/1000000) hybox.1 2
  have hy2u := pow_le_pow_left₀ hy0 hybox.2 2
  have hbpl := mul_le_mul hk.1 hy2l (by norm_num) hk0
  have hbpu := mul_le_mul hk.2 hy2u (sq_nonneg Y) (by norm_num)
  have hbbox : b ∈ Icc (10511/10000 : ℝ) (10564/10000) := by
    dsimp [b]
    constructor <;> nlinarith only [hbe.1, hbe.2, hbpl, hbpu]
  have hb0 : 0 ≤ b := by linarith [hbbox.1]
  have hbdisk : ‖(b : ℂ)‖ ≤ 23/20 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
    linarith [hbbox.2]
  have htErr := real_part_error H κ hclose (b : ℂ) hbdisk
  rw [complexMap_real] at htErr
  simp only [Complex.ofReal_re, realMap] at htErr
  have hte := abs_le.mp htErr
  have hb2l := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 10511/10000) hbbox.1 2
  have hb2u := pow_le_pow_left₀ hb0 hbbox.2 2
  have htpl := mul_le_mul hk.1 hb2l (by norm_num) hk0
  have htpu := mul_le_mul hk.2 hb2u (sq_nonneg b) (by norm_num)
  have htbox : (-999/1000 : ℝ) < (H (b : ℂ)).re ∧
      (H (b : ℂ)).re < -977/1000 := by
    constructor <;> nlinarith only [hte.1, hte.2, htpl, htpu]
  have hHz : H z = (Y : ℂ) * Complex.I :=
    complex_eq_imaginary_of_re_zero (H z) hroot
  have hHb : H ((Y : ℂ) * Complex.I) = (b : ℂ) :=
    complex_eq_real_of_im_zero _ (himag Y)
  have htwo : (H^[2]) z = (b : ℂ) := by
    change H (H z) = _
    rw [hHz, hHb]
  have hthree : (H^[3]) z = H (b : ℂ) := by
    change H (H (H z)) = _
    rw [hHz, hHb]
  have hcut := perturbed_fourth_cut_upper H hk hclose
  change Y ∈ Icc _ _ ∧ ((H^[2]) z).im = 0 ∧
    ((H^[3]) z).im = 0 ∧ -999/1000 < ((H^[3]) z).re ∧
    ((H^[3]) z).re < -977/1000 ∧ ((H^[3]) z).re < -((H^[4]) 0).re
  refine ⟨hybox, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htwo]; simp
  · rw [hthree]; exact hreal b
  · rw [hthree]; exact htbox.1
  · rw [hthree]; exact htbox.2
  · rw [hthree]; linarith [htbox.2]

/-- A whole nondegenerate radial interval persists throughout an explicit
uniform neighborhood of the quadratic model.  The second and third
images are literal iterates of H, and the upper source cut is H's own
fourth critical image.  No crossing, finite-orbit gate, or perturbed
orbit-disk hypothesis is assumed. -/
theorem uniform_perturbed_corridor (H : ℂ → ℂ) (hH : Continuous H)
    (hreal : ∀ t : ℝ, (H (t : ℂ)).im = 0)
    (himag : ∀ t : ℝ, (H ((t : ℂ) * Complex.I)).im = 0)
    {κ s : ℝ}
    (hk : κ ∈ Icc (17903 / 10000 : ℝ) (17904 / 10000))
    (hs : s ∈ Icc (63 / 1000 : ℝ) (33 / 500))
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 →
      ‖H w-complexMap κ w‖ ≤ 1/500000) :
    ∃ u : ℝ, u ∈ Ioo (-1/100 : ℝ) (1/100) ∧
      ‖circlePoint s u + (3/4 : ℂ)‖ = s ∧
      (H (circlePoint s u)).re = 0 ∧
      0 < (H (circlePoint s u)).im ∧
      ((H^[2]) (circlePoint s u)).im = 0 ∧
      ((H^[3]) (circlePoint s u)).im = 0 ∧
      (-999/1000 : ℝ) < ((H^[3]) (circlePoint s u)).re ∧
      ((H^[3]) (circlePoint s u)).re < -977/1000 ∧
      ((H^[3]) (circlePoint s u)).re < -((H^[4]) 0).re := by
  obtain ⟨u, hu, hz⟩ := perturbed_crossing_exists H hH hk hs hclose
  have hu' : u ∈ Icc (-1/100 : ℝ) (1/100) := ⟨hu.1.le, hu.2.le⟩
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  obtain ⟨hy, htwo, hthree, htl, htu, hcut⟩ :=
    perturbed_terminal_bounds H hreal himag hk hs hu' hclose hz
  exact ⟨u, hu, circle_radius (by linarith [hs.1]) hu1, hz,
    by linarith [hy.1], htwo, hthree, htl, htu, hcut⟩

end
end LimitingCrest
