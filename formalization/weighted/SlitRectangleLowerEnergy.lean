import SlitCubicLowerEnergy

/-!
# Reflected rectangle energy for arbitrary actual conformal charts

The chart may map the rectangle onto any open subset of the upper
half-plane.  The area lower bound follows from its actual Jacobian and
the two reflected slice integrals; surjectivity onto the whole half-plane
is unnecessary.
-/

namespace SlitRectangleLowerEnergy

open Set MeasureTheory SlitCubicCalibration SlitCubicRectangle SlitCubicLowerEnergy
open scoped ENNReal

noncomputable section

def sliceLength (C : CrestConformalModulus.ConformalChart) (B : ℝ)
    (ρ : ℂ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo 0 B,
    (ρ (C.homeomorph (point x y)) + ρ ((starRingEnd ℂ) (C.homeomorph (point x y)))) *
      ENNReal.ofReal ‖C.derivative (point x y)‖

/-- Each pair of reflected inverse horizontal segments has length at
least one, so every measurable extended density has the stated area. -/
theorem area_lower_of_chart_slices (C : CrestConformalModulus.ConformalChart)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hsource : C.homeomorph.source = openRectangle B A)
    (htarget : C.homeomorph.target ⊆ upper)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    (hlen : ∀ y ∈ Ioo (-A) 0, 1 ≤ sliceLength C B ρ y) :
    ENNReal.ofReal (A/(2*B)) ≤ SlitWaveModulus.area ρ := by
  let ρr : ℂ → ℝ≥0∞ := fun z => ρ ((starRingEnd ℂ) z)
  have hr : Measurable ρr := hρ.comp Complex.continuous_conj.measurable
  have hf := C.pullDensity_measurable hρ
  have hg := C.pullDensity_measurable hr
  have hs : ∀ y ∈ Ioo (-A) 0,
      1 ≤ ∫⁻ x in Ioo 0 B, C.pullDensity ρ (point x y) + C.pullDensity ρr (point x y) := by
    intro y hy
    have he : (∫⁻ x in Ioo 0 B,
        C.pullDensity ρ (point x y) + C.pullDensity ρr (point x y)) =
        sliceLength C B ρ y := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro x hx
      have hw : point x y ∈ C.homeomorph.source := by
        rw [hsource]
        simpa [point, openRectangle] using And.intro hx.1 (And.intro hx.2 hy)
      dsimp only
      rw [CrestConformalModulus.ConformalChart.pullDensity,
        CrestConformalModulus.ConformalChart.pullDensity,
        indicator_of_mem hw, indicator_of_mem hw]
      exact (add_mul _ _ _).symm
    rw [he]
    exact hlen y hy
  have hh := two_rectangle_energy hf hg hA hB hs
  have ha0 : SlitWaveModulus.area (C.pullDensity ρ) ≤ ∫⁻ z in upper, (ρ z)^2 :=
    (C.area_pull ρ).trans_le (lintegral_mono_set htarget)
  have ha1 : SlitWaveModulus.area (C.pullDensity ρr) ≤
      ∫⁻ z in upper, (ρ ((starRingEnd ℂ) z))^2 :=
    (C.area_pull ρr).trans_le (lintegral_mono_set htarget)
  exact hh.trans ((add_le_add ha0 ha1).trans (two_halfplane_energy_le ρ))

end
end SlitRectangleLowerEnergy
