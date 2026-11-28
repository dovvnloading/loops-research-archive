import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.NormNum

/-!
# Modulus of simple geometric leaves and quantitative transport

For simple leaves, Hausdorff one-measure on the trace is arclength.  Using
the geometric trace includes leaves of infinite length and avoids making
finite total variation part of the definition of a marked Wave.

The infimum below ranges over every measurable nonnegative density.  The
area measure is ordinary planar Lebesgue measure.  The transport estimate
is proved from the Hausdorff measure inequalities, not postulated as a
property of an abstract width function.
-/

namespace SlitWaveModulus

open Set MeasureTheory Measure
open scoped ENNReal NNReal

noncomputable section

def lineLength (ρ : ℂ → ℝ≥0∞) (S : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z in S, ρ z ∂μH[1]

def area (ρ : ℂ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ z, (ρ z)^2

def Admissible (Γ : Set (Set ℂ)) (ρ : ℂ → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ S ∈ Γ, 1 ≤ lineLength ρ S

def modulus (Γ : Set (Set ℂ)) : ℝ≥0∞ :=
  ⨅ (ρ : ℂ → ℝ≥0∞) (_ : Admissible Γ ρ), area ρ

theorem modulus_le_area {Γ : Set (Set ℂ)} {ρ : ℂ → ℝ≥0∞}
    (hρ : Admissible Γ ρ) : modulus Γ ≤ area ρ :=
  iInf₂_le _ hρ

theorem modulus_mono {Γ Δ : Set (Set ℂ)} (h : Γ ⊆ Δ) :
    modulus Γ ≤ modulus Δ := by
  apply le_iInf₂
  intro ρ hρ
  exact modulus_le_area ⟨hρ.1, fun S hS => hρ.2 S (h hS)⟩

theorem lineLength_mono {ρ σ : ℂ → ℝ≥0∞} (h : ∀ z, ρ z ≤ σ z)
    (S : Set ℂ) : lineLength ρ S ≤ lineLength σ S :=
  lintegral_mono h

theorem lineLength_const_mul (a : ℝ≥0∞) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) (S : Set ℂ) :
    lineLength (fun z => a * ρ z) S = a * lineLength ρ S :=
  lintegral_const_mul a hρ

theorem modulus_union_le (Γ Δ : Set (Set ℂ)) :
    modulus (Γ ∪ Δ) ≤ modulus Γ + modulus Δ := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro ρ hρ σ hσ
  have hm : Measurable (fun z => max (ρ z) (σ z)) := hρ.1.max hσ.1
  have ha : Admissible (Γ ∪ Δ) (fun z => max (ρ z) (σ z)) := by
    refine ⟨hm, ?_⟩
    intro S hS
    rcases hS with hS | hS
    · exact (hρ.2 S hS).trans (lineLength_mono (fun z => le_max_left _ _) S)
    · exact (hσ.2 S hS).trans (lineLength_mono (fun z => le_max_right _ _) S)
  refine (modulus_le_area ha).trans ?_
  calc
    area (fun z => max (ρ z) (σ z)) ≤ ∫⁻ z, (ρ z)^2 + (σ z)^2 := by
      apply lintegral_mono
      intro z
      change (max (ρ z) (σ z))^2 ≤ (ρ z)^2 + (σ z)^2
      rcases le_total (ρ z) (σ z) with h | h
      · rw [max_eq_right h]
        exact le_add_left le_rfl
      · rw [max_eq_left h]
        exact le_add_right le_rfl
    _ = area ρ + area σ := lintegral_add_left (hρ.1.pow_const 2) _

private theorem image_preimage_inter (H : ℂ ≃ₜ ℂ) (S T : Set ℂ) :
    H '' (H ⁻¹' T ∩ S) = T ∩ H '' S := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
    exact ⟨hx, ⟨x, hs, rfl⟩⟩
  · rintro ⟨hz, x, hx, rfl⟩
    exact ⟨x, ⟨hz, hx⟩, rfl⟩

/-- The weighted length of every geometric trace obeys the Lipschitz
bound, even when its one-dimensional measure is infinite. -/
theorem lineLength_image_le (H : ℂ ≃ₜ ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L H) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    (S : Set ℂ) :
    lineLength ρ (H '' S) ≤ (L : ℝ≥0∞) * lineLength (fun z => ρ (H z)) S := by
  have hm : (μH[1] : Measure ℂ).restrict (H '' S) ≤
      (L : ℝ≥0∞) • Measure.map H ((μH[1] : Measure ℂ).restrict S) := by
    apply Measure.le_iff.mpr
    intro T hT
    rw [Measure.restrict_apply hT, Measure.smul_apply,
      Measure.map_apply H.continuous.measurable hT,
      Measure.restrict_apply (H.continuous.measurable hT)]
    have h := hL.hausdorffMeasure_image_le (d := 1) (by norm_num)
      (H ⁻¹' T ∩ S)
    rw [image_preimage_inter] at h
    simpa only [ENNReal.rpow_one, smul_eq_mul] using h
  calc
    lineLength ρ (H '' S) ≤
        ∫⁻ z, ρ z ∂((L : ℝ≥0∞) • Measure.map H ((μH[1] : Measure ℂ).restrict S)) :=
      lintegral_mono' hm le_rfl
    _ = (L : ℝ≥0∞) * lineLength (fun z => ρ (H z)) S := by
      rw [lintegral_smul_measure, lintegral_map hρ H.continuous.measurable]
      rfl

/-- Planar Lebesgue area distortion, derived from Hausdorff measure.
The normalization factor cancels; no numerical value for it is assumed. -/
theorem volume_image_le (H : ℂ ≃ₜ ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L H) (S : Set ℂ) :
    volume (H '' S) ≤ (L : ℝ≥0∞)^2 * volume S := by
  have hv : (μHE[2] : Measure ℂ) = volume := by
    simpa only [Complex.finrank_real_complex] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℂ))
  rw [← hv, euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply]
  have h := hL.hausdorffMeasure_image_le (d := 2) (by norm_num) S
  have hh := mul_le_mul_left' h
    (addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (μH[(2 : ℕ)] : Measure (EuclideanSpace ℝ (Fin 2))) : ℝ≥0∞)
  simpa only [ENNReal.rpow_two, ENNReal.smul_def, smul_eq_mul,
    Nat.cast_ofNat, mul_left_comm, mul_assoc] using hh

/-- Pulling a density through the inverse changes its area by at most
the square of the forward Lipschitz constant. -/
theorem area_comp_symm_le (H : ℂ ≃ₜ ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L H) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    area (fun z => ρ (H.symm z)) ≤ (L : ℝ≥0∞)^2 * area ρ := by
  have hm : Measure.map H.symm (volume : Measure ℂ) ≤ (L : ℝ≥0∞)^2 • volume := by
    apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.map_apply H.symm.continuous.measurable hS, Measure.smul_apply]
    have he : H.symm ⁻¹' S = H '' S := by
      ext z
      constructor
      · intro hz
        exact ⟨H.symm z, hz, H.apply_symm_apply z⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [he]
    exact volume_image_le H hL S
  calc
    area (fun z => ρ (H.symm z)) = ∫⁻ z, (ρ z)^2 ∂Measure.map H.symm volume := by
      rw [lintegral_map (hρ.pow_const 2) H.symm.continuous.measurable]
      rfl
    _ ≤ ∫⁻ z, (ρ z)^2 ∂((L : ℝ≥0∞)^2 • volume) := lintegral_mono' hm le_rfl
    _ = (L : ℝ≥0∞)^2 * area ρ := lintegral_smul_measure _ _

def transportFamily (H : ℂ ≃ₜ ℂ) (Γ : Set (Set ℂ)) : Set (Set ℂ) :=
  (fun S => H '' S) '' Γ

theorem transportFamily_symm (H : ℂ ≃ₜ ℂ) (Γ : Set (Set ℂ)) :
    transportFamily H.symm (transportFamily H Γ) = Γ := by
  ext S
  constructor
  · rintro ⟨T, ⟨U, hU, rfl⟩, rfl⟩
    have he : H.symm '' (H '' U) = U := by
      rw [← image_comp]
      simp
    simpa only [he] using hU
  · intro hS
    refine ⟨H '' S, ⟨S, hS, rfl⟩, ?_⟩
    change H.symm '' (H '' S) = S
    rw [← image_comp]
    simp

/-- A concrete admissible density for the entire transported family. -/
theorem admissible_transport (H : ℂ ≃ₜ ℂ) {M : ℝ≥0}
    (hM : LipschitzWith M H.symm) {Γ : Set (Set ℂ)} {ρ : ℂ → ℝ≥0∞}
    (hρ : Admissible Γ ρ) :
    Admissible (transportFamily H Γ) (fun z => (M : ℝ≥0∞) * ρ (H.symm z)) := by
  refine ⟨measurable_const.mul (hρ.1.comp H.symm.continuous.measurable), ?_⟩
  rintro _ ⟨S, hS, rfl⟩
  have hcomp : Measurable (fun z => ρ (H.symm z)) :=
    hρ.1.comp H.symm.continuous.measurable
  change 1 ≤ lineLength (fun z => (M : ℝ≥0∞) * ρ (H.symm z)) (H '' S)
  rw [lineLength_const_mul _ hcomp]
  have h := lineLength_image_le H.symm hM hρ.1 (H '' S)
  have he : H.symm '' (H '' S) = S := by
    rw [← image_comp]
    simp
  rw [he] at h
  exact (hρ.2 S hS).trans h

theorem area_transport_le (H : ℂ ≃ₜ ℂ) {L M : ℝ≥0}
    (hL : LipschitzWith L H) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    area (fun z => (M : ℝ≥0∞) * ρ (H.symm z)) ≤
      ((M : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2) * area ρ := by
  unfold area
  simp_rw [mul_pow]
  have hcomp : Measurable (fun z => ρ (H.symm z)^2) :=
    (hρ.comp H.symm.continuous.measurable).pow_const 2
  rw [lintegral_const_mul _ hcomp]
  exact (mul_le_mul_left' (area_comp_symm_le H hL hρ) _).trans_eq (mul_assoc _ _ _).symm

/-- The whole family modulus, with no chosen foliation or optimizer,
obeys a distortion factor tending to one when both Lipschitz constants do. -/
theorem modulus_transport_le (H : ℂ ≃ₜ ℂ) {L M : ℝ≥0}
    (hL : LipschitzWith L H) (hM : LipschitzWith M H.symm)
    (hL0 : L ≠ 0) (hM0 : M ≠ 0) (Γ : Set (Set ℂ)) :
    modulus (transportFamily H Γ) ≤
      ((M : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2) * modulus Γ := by
  have h0 : (M : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2 ≠ 0 := by simp [hL0, hM0]
  have ht : (M : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2 ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  unfold modulus
  rw [ENNReal.mul_iInf_of_ne h0 ht]
  apply le_iInf
  intro ρ
  rw [ENNReal.mul_iInf_of_ne h0 ht]
  apply le_iInf
  intro hρ
  exact (modulus_le_area (admissible_transport H hM hρ)).trans (area_transport_le H hL hρ.1)

theorem modulus_le_mul_transport (H : ℂ ≃ₜ ℂ) {L M : ℝ≥0}
    (hL : LipschitzWith L H) (hM : LipschitzWith M H.symm)
    (hL0 : L ≠ 0) (hM0 : M ≠ 0) (Γ : Set (Set ℂ)) :
    modulus Γ ≤ ((M : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2) *
      modulus (transportFamily H Γ) := by
  have h := modulus_transport_le H.symm hM hL hM0 hL0 (transportFamily H Γ)
  rw [transportFamily_symm] at h
  simpa only [mul_comm] using h

end
end SlitWaveModulus
