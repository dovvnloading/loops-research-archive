import Mathlib
import ChebyshevFibers

/-!
# The exact exterior coordinate of a real slit

The positive continuous amplitude below is the modulus of the unique
exterior Joukowski inverse. Its holomorphic coordinate is used only off
the slit. No boundary choice of complex phase is asserted.
-/

namespace SlitJoukowski

open Set Function Filter Topology
open LoopsParabolic LoopsChebyshev
open scoped Classical

noncomputable section

def ellipseParameter (z : ℂ) : ℝ :=
  (‖z - 2‖ + ‖z + 2‖) / 2

def amplitude (z : ℂ) : ℝ :=
  (ellipseParameter z + Real.sqrt ((ellipseParameter z)^2 - 4)) / 2

def exteriorAddress (z : ℂ) : ℂ :=
  if hz : z ∉ realSegment 2 then
    Classical.choose ((exterior_image_iff z).mp hz)
  else 1

theorem exteriorAddress_spec {z : ℂ} (hz : z ∉ realSegment 2) :
    1 < ‖exteriorAddress z‖ ∧ J (exteriorAddress z) = z := by
  classical
  simp only [exteriorAddress, dif_pos hz]
  exact Classical.choose_spec ((exterior_image_iff z).mp hz)

theorem exteriorAddress_of_J {w : ℂ} (hw : 1 < ‖w‖) :
    exteriorAddress (J w) = w := by
  have hz : J w ∉ realSegment 2 :=
    (exterior_image_iff _).mpr ⟨w, hw, rfl⟩
  exact exterior_joukowski_injective (exteriorAddress_spec hz).1 hw
    (exteriorAddress_spec hz).2

theorem exteriorAddress_differentiableAt {z : ℂ}
    (hz : z ∉ realSegment 2) : DifferentiableAt ℂ exteriorAddress z := by
  let w := exteriorAddress z
  have hw : 1 < ‖w‖ := (exteriorAddress_spec hz).1
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    norm_num at hw
  have hj : J w = z := (exteriorAddress_spec hz).2
  have hd : HasStrictDerivAt J (1 - (w^2)⁻¹) w := by
    rw [sub_eq_add_neg]
    change HasStrictDerivAt (fun u : ℂ => u + u⁻¹) (1 + -(w^2)⁻¹) w
    have h₁ : HasStrictDerivAt (fun u : ℂ => u) 1 w := hasStrictDerivAt_id w
    have h₂ : HasStrictDerivAt (fun u : ℂ => u⁻¹) (-(w^2)⁻¹) w :=
      hasStrictDerivAt_inv hw0
    exact h₁.fun_add h₂
  have hl : ∀ᶠ u in 𝓝 w, exteriorAddress (J u) = u := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with u hu
    exact exteriorAddress_of_J hu
  have hi := hd.to_local_left_inverse (exterior_derivative_ne_zero hw) hl
  rw [hj] at hi
  exact hi.hasDerivAt.differentiableAt

private theorem ellipseParameter_J {w : ℂ} (hw : w ≠ 0) :
    ellipseParameter (J w) * ‖w‖ = ‖w‖^2 + 1 := by
  have hm : (J w - 2) * w = (w - 1)^2 := by
    unfold J
    field_simp [hw] <;> ring
  have hp : (J w + 2) * w = (w + 1)^2 := by
    unfold J
    field_simp [hw] <;> ring
  have hmn := congrArg (fun v : ℂ => ‖v‖) hm
  have hpn := congrArg (fun v : ℂ => ‖v‖) hp
  simp only [norm_mul, norm_pow] at hmn hpn
  have hpar : ‖w - 1‖^2 + ‖w + 1‖^2 = 2 * (‖w‖^2 + 1) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    ring
  unfold ellipseParameter
  nlinarith [hmn, hpn, hpar]

theorem amplitude_J {w : ℂ} (hw : 1 ≤ ‖w‖) :
    amplitude (J w) = ‖w‖ := by
  let s : ℝ := ‖w‖
  have hs : 1 ≤ s := hw
  have hspos : 0 < s := by linarith
  have hs0 : s ≠ 0 := hspos.ne'
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp hs0
  have hq : ellipseParameter (J w) = s + s⁻¹ := by
    apply mul_right_cancel₀ hs0
    calc
      ellipseParameter (J w) * s = s^2 + 1 := ellipseParameter_J hw0
      _ = (s + s⁻¹) * s := by field_simp [hs0] <;> ring
  have hdisc : (s + s⁻¹)^2 - 4 = (s - s⁻¹)^2 := by
    field_simp [hs0] <;> ring
  have hi : s⁻¹ ≤ s := by
    have h : 1 / s ≤ s := (div_le_iff₀ hspos).mpr (by nlinarith)
    simpa only [one_div] using h
  unfold amplitude
  rw [hq, hdisc, Real.sqrt_sq (sub_nonneg.mpr hi)]
  dsimp [s]
  ring

theorem amplitude_eq_one_of_mem {z : ℂ} (hz : z ∈ realSegment 2) :
    amplitude z = 1 := by
  obtain ⟨x, hx, rfl⟩ := hz
  have hm : ‖(x : ℂ) - 2‖ = 2 - x := by
    rw [show (x : ℂ) - 2 = ((x - 2 : ℝ) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.2])]
    ring
  have hp : ‖(x : ℂ) + 2‖ = x + 2 := by
    rw [show (x : ℂ) + 2 = ((x + 2 : ℝ) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
  have hq : ellipseParameter (x : ℂ) = 2 := by
    unfold ellipseParameter
    rw [hm, hp]
    ring
  rw [amplitude, hq]
  norm_num

theorem norm_exteriorAddress (z : ℂ) :
    ‖exteriorAddress z‖ = amplitude z := by
  classical
  by_cases hz : z ∈ realSegment 2
  · simp only [exteriorAddress, dif_neg (not_not.mpr hz), norm_one,
      amplitude_eq_one_of_mem hz]
  · have hs := exteriorAddress_spec hz
    calc
      ‖exteriorAddress z‖ = amplitude (J (exteriorAddress z)) :=
        (amplitude_J hs.1.le).symm
      _ = amplitude z := by rw [hs.2]

theorem amplitude_ge_one (z : ℂ) : 1 ≤ amplitude z := by
  by_cases hz : z ∈ realSegment 2
  · rw [amplitude_eq_one_of_mem hz]
  · rw [← norm_exteriorAddress]
    exact (exteriorAddress_spec hz).1.le

theorem amplitude_eq_one_iff (z : ℂ) :
    amplitude z = 1 ↔ z ∈ realSegment 2 := by
  constructor
  · intro h
    by_contra hz
    have hs := (exteriorAddress_spec hz).1
    rw [norm_exteriorAddress, h] at hs
    exact lt_irrefl _ hs
  · exact amplitude_eq_one_of_mem

theorem exteriorAddress_ne_zero (z : ℂ) : exteriorAddress z ≠ 0 := by
  intro h
  have hs := amplitude_ge_one z
  rw [← norm_exteriorAddress, h, norm_zero] at hs
  norm_num at hs

theorem amplitude_continuous : Continuous amplitude := by
  unfold amplitude ellipseParameter
  fun_prop

theorem norm_le_amplitude_add_inv (z : ℂ) :
    ‖z‖ ≤ amplitude z + (amplitude z)⁻¹ := by
  by_cases hz : z ∈ realSegment 2
  · rw [amplitude_eq_one_of_mem hz]
    obtain ⟨x, hx, rfl⟩ := hz
    simpa only [Complex.norm_real, Real.norm_eq_abs, inv_one, one_add_one_eq_two]
      using (abs_le.mpr hx)
  · have hs := exteriorAddress_spec hz
    calc
      ‖z‖ = ‖J (exteriorAddress z)‖ := by rw [hs.2]
      _ ≤ ‖exteriorAddress z‖ + ‖(exteriorAddress z)⁻¹‖ :=
        norm_add_le _ _
      _ = amplitude z + (amplitude z)⁻¹ := by
        rw [norm_inv, norm_exteriorAddress]

theorem amplitude_sub_inv_le_norm (z : ℂ) :
    amplitude z - (amplitude z)⁻¹ ≤ ‖z‖ := by
  by_cases hz : z ∈ realSegment 2
  · rw [amplitude_eq_one_of_mem hz]
    simpa using norm_nonneg z
  · have hs := exteriorAddress_spec hz
    have h := norm_sub_norm_le (exteriorAddress z) (-(exteriorAddress z)⁻¹)
    have hj : exteriorAddress z + (exteriorAddress z)⁻¹ = z := hs.2
    simpa only [norm_neg, norm_inv, sub_neg_eq_add, hj,
      norm_exteriorAddress] using h

def normalize (t : ℝ) (z : ℂ) : ℂ :=
  ((2 / t : ℝ) : ℂ) * z

def slitAddress (t : ℝ) (z : ℂ) : ℂ :=
  exteriorAddress (normalize t z)

def slitAmplitude (t : ℝ) (z : ℂ) : ℝ :=
  amplitude (normalize t z)

theorem normalize_mem_realSegment {t : ℝ} (ht : 0 < t) (z : ℂ) :
    normalize t z ∈ realSegment 2 ↔ z ∈ realSegment t := by
  have hk : 0 < 2 / t := div_pos (by norm_num) ht
  have hkt : (2 / t) * t = 2 := div_mul_cancel₀ _ ht.ne'
  rw [mem_realSegment_iff, mem_realSegment_iff]
  simp only [normalize, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero, mem_Icc]
  constructor
  · rintro ⟨hi, hl, hu⟩
    refine ⟨(mul_eq_zero.mp hi).resolve_left hk.ne', ?_, ?_⟩
    · by_contra h
      have hm := mul_lt_mul_of_pos_left (lt_of_not_ge h) hk
      nlinarith only [hl, hkt, hm]
    · by_contra h
      have hm := mul_lt_mul_of_pos_left (lt_of_not_ge h) hk
      nlinarith only [hu, hkt, hm]
  · rintro ⟨hi, hl, hu⟩
    refine ⟨by rw [hi, mul_zero], ?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_left hl hk.le
      nlinarith only [h, hkt]
    · have h := mul_le_mul_of_nonneg_left hu hk.le
      nlinarith only [h, hkt]

theorem norm_normalize {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖normalize t z‖ = 2 * ‖z‖ / t := by
  simp only [normalize, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) ht)]
  ring

theorem norm_slitAddress (t : ℝ) (z : ℂ) :
    ‖slitAddress t z‖ = slitAmplitude t z :=
  norm_exteriorAddress _

theorem slitAddress_ne_zero (t : ℝ) (z : ℂ) : slitAddress t z ≠ 0 :=
  exteriorAddress_ne_zero _

theorem slitAmplitude_ge_one (t : ℝ) (z : ℂ) : 1 ≤ slitAmplitude t z :=
  amplitude_ge_one _

theorem slitAmplitude_eq_one_iff {t : ℝ} (ht : 0 < t) (z : ℂ) :
    slitAmplitude t z = 1 ↔ z ∈ realSegment t := by
  exact (amplitude_eq_one_iff _).trans (normalize_mem_realSegment ht z)

theorem slitAmplitude_continuous (t : ℝ) : Continuous (slitAmplitude t) := by
  exact amplitude_continuous.comp (by unfold normalize; fun_prop)

theorem slitAddress_differentiableAt {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ realSegment t) : DifferentiableAt ℂ (slitAddress t) z := by
  have hn : normalize t z ∉ realSegment 2 :=
    fun h => hz ((normalize_mem_realSegment ht z).mp h)
  exact (exteriorAddress_differentiableAt hn).comp z
    (by unfold normalize; fun_prop)

/-- A fixed outer-coordinate bound on the complete central normalization disk. -/
theorem slitAmplitude_upper {t : ℝ} (ht : 117/1000 ≤ t) {z : ℂ}
    (hz : ‖z‖ ≤ 1/6) : slitAmplitude t z ≤ 16/5 := by
  have htpos : 0 < t := by linarith
  let s := slitAmplitude t z
  have hs : 1 ≤ s := slitAmplitude_ge_one t z
  have hspos : 0 < s := by linarith
  have hb : ‖normalize t z‖ ≤ 1000/351 := by
    rw [norm_normalize htpos]
    apply (div_le_iff₀ htpos).mpr
    nlinarith only [ht, hz]
  have hi : s - s⁻¹ ≤ 1000/351 :=
    (amplitude_sub_inv_le_norm _).trans hb
  have hm := mul_le_mul_of_nonneg_right hi hspos.le
  have hcancel : s⁻¹ * s = 1 := inv_mul_cancel₀ hspos.ne'
  have hp : s^2 - 1 ≤ (1000/351) * s := by
    nlinarith only [hm, hcancel]
  by_contra h
  have hgt : 16/5 < s := lt_of_not_ge h
  nlinarith [sq_nonneg (s - 16/5)]

/-- A fixed lower exterior coordinate on the enlarged return boundary. -/
theorem slitAmplitude_lower {t : ℝ} (htpos : 0 < t) (ht : t ≤ 119/1000)
    {z : ℂ} (hz : 1/4 ≤ ‖z‖) : 39/10 ≤ slitAmplitude t z := by
  let s := slitAmplitude t z
  have hs : 1 ≤ s := slitAmplitude_ge_one t z
  have hspos : 0 < s := by linarith
  have hb : 500/119 ≤ ‖normalize t z‖ := by
    rw [norm_normalize htpos]
    apply (le_div_iff₀ htpos).mpr
    nlinarith only [ht, hz]
  have hi : 500/119 ≤ s + s⁻¹ :=
    hb.trans (norm_le_amplitude_add_inv _)
  have hm := mul_le_mul_of_nonneg_right hi hspos.le
  have hcancel : s⁻¹ * s = 1 := inv_mul_cancel₀ hspos.ne'
  have hp : (500/119) * s ≤ s^2 + 1 := by
    nlinarith only [hm, hcancel]
  by_contra h
  have hlt : s < 39/10 := lt_of_not_ge h
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hlt.le)]

end
end SlitJoukowski
