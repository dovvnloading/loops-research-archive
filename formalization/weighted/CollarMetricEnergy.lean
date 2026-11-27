import CollarCapacityLower
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Planar metric energy from horizontal crossing lengths

The density is arbitrary measurable extended nonnegative data.  Neither
finiteness of its values nor finiteness of its area integral is assumed.
-/

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CollarMetricEnergy

open CollarCapacityLower

noncomputable section

/-- Cauchy--Schwarz gives a uniform quadratic-energy lower bound on
any finite positive measure space, including unbounded densities. -/
theorem reciprocal_mass_le_square_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hmass : μ univ ≠ 0) (hfinite : μ univ ≠ ⊤)
    (hlength : 1 ≤ ∫⁻ x, f x ∂μ) :
    (μ univ)⁻¹ ≤ ∫⁻ x, (f x)^(2 : ℕ) ∂μ := by
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := f) (g := fun _ => 1) hf aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.rpow_two,
    one_pow, lintegral_const, one_mul] at hHolder
  have hsquare := pow_le_pow_left' (hlength.trans hHolder) 2
  have hhalf (a : ℝ≥0∞) : (a ^ ((2 : ℝ)⁻¹))^(2 : ℕ) = a := by
    rw [← ENNReal.rpow_natCast]
    exact ENNReal.rpow_inv_rpow (by norm_num : (2 : ℝ) ≠ 0) a
  simp only [one_pow, mul_pow, one_div, hhalf] at hsquare
  rw [← one_div]
  exact (ENNReal.div_le_iff hmass hfinite).mpr hsquare

/-- A horizontal segment of length `R` whose density integral is at
least one contributes at least `1/R` to its one-dimensional energy. -/
theorem horizontal_square_integral_lower {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) {R : ℝ} (hR : 0 < R) (y : ℝ)
    (hlength : 1 ≤ ∫⁻ x in Icc 0 R, ρ (horizontal y x)) :
    ENNReal.ofReal (1/R) ≤ ∫⁻ x in Icc 0 R, (ρ (horizontal y x))^(2 : ℕ) := by
  have hmass : (volume.restrict (Icc (0 : ℝ) R)) univ = ENNReal.ofReal R := by
    simp
  have h := reciprocal_mass_le_square_integral
    (μ := volume.restrict (Icc (0 : ℝ) R))
    ((hρ.comp (horizontal_lipschitz y).continuous.measurable).aemeasurable)
    (by rw [hmass]; exact (ENNReal.ofReal_pos.mpr hR).ne')
    (by rw [hmass]; exact ENNReal.ofReal_ne_top) hlength
  rw [one_div, ENNReal.ofReal_inv_of_pos hR]
  simpa only [hmass, Function.comp_apply] using h

/-- A positive-width strip of horizontal crossings forces positive
planar quadratic metric energy.  The premise need only hold on almost
every slice, and the result uses the literal complex Lebesgue measure. -/
theorem planar_square_integral_lower_ae {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) {r R : ℝ} (_hr : 0 < r) (hR : 0 < R)
    (hslices : ∀ᵐ y ∂volume.restrict (Ioc (-r/2) (r/2)),
      1 ≤ ∫⁻ x in Icc 0 R, ρ (horizontal y x)) :
    ENNReal.ofReal (r/R) ≤ ∫⁻ z : ℂ, (ρ z)^(2 : ℕ) := by
  let J : Set ℝ := Ioc (-r/2) (r/2)
  have hslice : ∀ᵐ y ∂volume.restrict J,
      ENNReal.ofReal (1/R) ≤ ∫⁻ x in Icc 0 R, (ρ (horizontal y x))^(2 : ℕ) := by
    filter_upwards [hslices] with y hy
    exact horizontal_square_integral_lower hρ hR y hy
  have hconst : (∫⁻ _y in J, ENNReal.ofReal (1/R)) =
      ENNReal.ofReal (r/R) := by
    rw [lintegral_const, Measure.restrict_apply_univ]
    change ENNReal.ofReal (1/R) * volume (Ioc (-r/2) (r/2)) = _
    rw [Real.volume_Ioc]
    have heq : r/2 - -r/2 = r := by ring
    rw [heq, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/R)]
    congr 1
    ring
  have hmeas : Measurable (fun z : ℂ => (ρ z)^(2 : ℕ)) := hρ.pow_const 2
  calc
    ENNReal.ofReal (r/R) = ∫⁻ _y in J, ENNReal.ofReal (1/R) := hconst.symm
    _ ≤ ∫⁻ y in J, ∫⁻ x in Icc 0 R, (ρ (horizontal y x))^(2 : ℕ) := lintegral_mono_ae hslice
    _ ≤ ∫⁻ y in J, ∫⁻ x : ℝ, (ρ (horizontal y x))^(2 : ℕ) :=
      lintegral_mono (fun _ => setLIntegral_le_lintegral _ _)
    _ ≤ ∫⁻ y : ℝ, ∫⁻ x : ℝ, (ρ (horizontal y x))^(2 : ℕ) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p : ℝ × ℝ, (ρ (horizontal p.1 p.2))^(2 : ℕ)
        ∂((volume : Measure ℝ).prod volume) :=
      (lintegral_prod _ (hmeas.comp horizontal_measurePreserving.measurable).aemeasurable).symm
    _ = ∫⁻ z : ℂ, (ρ z)^(2 : ℕ) := horizontal_measurePreserving.lintegral_comp hmeas

/-- Pointwise slice admissibility is a convenient sufficient form of
the almost-everywhere crossing hypothesis. -/
theorem planar_square_integral_lower {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hslices : ∀ y ∈ Ioc (-r/2) (r/2),
      1 ≤ ∫⁻ x in Icc 0 R, ρ (horizontal y x)) :
    ENNReal.ofReal (r/R) ≤ ∫⁻ z : ℂ, (ρ z)^(2 : ℕ) := by
  apply planar_square_integral_lower_ae hρ hr hR
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  exact hslices y hy

end
end CollarMetricEnergy
