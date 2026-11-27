import ThreeReturnAnnulus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# A lower bound for the actual planar condenser capacity

Horizontal line integration gives a positive lower bound whenever the
inner plate contains a disk.  The energy is the planar derivative and
Lebesgue integral used by `ThreeReturnAnnulus`.
-/

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CollarCapacityLower

noncomputable section

def horizontal (y x : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

theorem horizontal_lipschitz (y : ℝ) : LipschitzWith 1 (horizontal y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp [horizontal, dist_eq_norm, ← Complex.ofReal_sub]

theorem horizontal_hasDerivAt (y x : ℝ) :
    HasDerivAt (horizontal y) (1 : ℂ) x := by
  exact (Complex.ofRealCLM.hasDerivAt (x := x)).add_const
    ((y : ℂ) * Complex.I)

theorem horizontal_energy_integrable {u : ℂ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) (y R : ℝ) :
    IntervalIntegrable (fun x => ‖fderiv ℝ u (horizontal y x)‖ ^ 2) volume 0 R := by
  apply IntervalIntegrable.mono_fun (f := fun _ => (L : ℝ)^2)
    intervalIntegrable_const
  · exact ((measurable_fderiv ℝ u).comp
      (horizontal_lipschitz y).continuous.measurable).norm.pow_const 2 |>.aestronglyMeasurable
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg (‖fderiv ℝ u (horizontal y x)‖)),
      abs_of_nonneg (sq_nonneg (L : ℝ))]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hu) 2

theorem horizontal_energy_lower {u : ℂ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {R : ℝ} (hR : 0 < R) (y : ℝ)
    (hzero : u (horizontal y 0) = 0) (hone : u (horizontal y R) = 1)
    (hdiff : ∀ᵐ x : ℝ, DifferentiableAt ℝ u (horizontal y x)) :
    ENNReal.ofReal (1 / R) ≤
      ∫⁻ x in Ioc 0 R, ENNReal.ofReal (‖fderiv ℝ u (horizontal y x)‖ ^ 2) := by
  let v : ℝ → ℝ := u ∘ horizontal y
  have hv : LipschitzWith L v := by
    simpa [v] using hu.comp (horizontal_lipschitz y)
  have hac := hv.lipschitzOnWith.absolutelyContinuousOnInterval (a := 0) (b := R)
  have hFTC : (∫ x in (0 : ℝ)..R, deriv v x) = 1 := by
    rw [hac.integral_deriv_eq_sub]
    simp [v, Function.comp_def, hzero, hone]
  have he := horizontal_energy_integrable hu y R
  have hineq : ∀ᵐ x : ℝ,
      (2 / R) * deriv v x - 1 / R^2 ≤ ‖fderiv ℝ u (horizontal y x)‖^2 := by
    filter_upwards [hdiff] with x hx
    have hderiv : deriv v x = fderiv ℝ u (horizontal y x) 1 :=
      (hx.hasFDerivAt.comp_hasDerivAt x (horizontal_hasDerivAt y x)).deriv
    have hnorm : |deriv v x| ≤ ‖fderiv ℝ u (horizontal y x)‖ := by
      rw [hderiv, ← Real.norm_eq_abs]
      simpa using (fderiv ℝ u (horizontal y x)).le_opNorm (1 : ℂ)
    have hs : (deriv v x)^2 ≤ ‖fderiv ℝ u (horizontal y x)‖^2 := by
      nlinarith [sq_abs (deriv v x), abs_nonneg (deriv v x), norm_nonneg (fderiv ℝ u (horizontal y x))]
    have hsq : 0 ≤ (deriv v x)^2 - (2/R) * deriv v x + 1/R^2 := by
      have heq : (deriv v x)^2 - (2/R) * deriv v x + 1/R^2 =
          (deriv v x - 1/R)^2 := by ring
      rw [heq]
      exact sq_nonneg _
    nlinarith
  have hint := intervalIntegral.integral_mono_ae hR.le
    ((hac.intervalIntegrable_deriv.const_mul (2/R)).sub intervalIntegrable_const) he hineq
  rw [intervalIntegral.integral_sub
    (hac.intervalIntegrable_deriv.const_mul (2/R)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hFTC, intervalIntegral.integral_const] at hint
  have hbound : 1 / R ≤ ∫ x in (0 : ℝ)..R,
      ‖fderiv ℝ u (horizontal y x)‖^2 := by
    have heq : (2/R)*1 - (R-0) * (1/R^2) = 1/R := by field_simp; ring
    simpa only [smul_eq_mul, heq] using hint
  rw [intervalIntegral.integral_of_le hR.le] at hbound
  rw [← ofReal_integral_eq_lintegral_ofReal he.1 (ae_of_all _ (fun x => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hbound

/-- The real product coordinates have their literal planar Lebesgue
measure; the first coordinate here labels the horizontal slice. -/
theorem horizontal_measurePreserving :
    MeasurePreserving (fun p : ℝ × ℝ => horizontal p.1 p.2)
      ((volume : Measure ℝ).prod volume) (volume : Measure ℂ) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).comp
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  have heq : (fun p : ℝ × ℝ => horizontal p.1 p.2) =
      Complex.measurableEquivRealProd.symm ∘ Prod.swap := by
    funext p
    apply Complex.ext <;> simp [horizontal]
  rw [heq]
  exact h

theorem horizontal_ae_differentiable {u : ℂ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) :
    ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, DifferentiableAt ℝ u (horizontal y x) :=
  Measure.ae_ae_of_ae_prod (horizontal_measurePreserving.quasiMeasurePreserving.ae
    hu.ae_differentiableAt)

theorem energy_measurable (u : ℂ → ℝ) :
    Measurable (fun z => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2)) :=
  ((measurable_fderiv ℝ u).norm.pow_const 2).ennreal_ofReal

/-- Outside the closed outer disk the plate condition makes the
potential locally constant, so its actual derivative vanishes. -/
theorem fderiv_zero_outside_disk {u : ℂ → ℝ} {R : ℝ}
    (hone : ∀ z ∉ Metric.ball (0 : ℂ) R, u z = 1)
    {z : ℂ} (hz : R < ‖z‖) : fderiv ℝ u z = 0 := by
  have heq : u =ᶠ[𝓝 z] (fun _ : ℂ => (1 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).eventually_mem hz] with w hw
    exact hone w (by simpa using (not_lt_of_ge hw.le : ¬ ‖w‖ < R))
  simpa using heq.fderiv_eq

/-- The circle has zero area. Thus integrating over the full plane or
over the actual outer disk gives the same energy for plate potentials. -/
theorem full_energy_eq_disk {u : ℂ → ℝ} {R : ℝ}
    (hone : ∀ z ∉ Metric.ball (0 : ℂ) R, u z = 1) :
    (∫⁻ z : ℂ, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2)) =
      ThreeReturnAnnulus.dirichletEnergy (Metric.ball 0 R) u := by
  have hsphere : ∀ᵐ z : ℂ, z ∉ Metric.sphere (0 : ℂ) R := by
    rw [ae_iff]
    simpa [Metric.sphere] using Measure.addHaar_sphere (volume : Measure ℂ) (0 : ℂ) R
  have heq : (fun z : ℂ => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2)) =ᵐ[volume]
      (Metric.ball (0 : ℂ) R).indicator
        (fun z : ℂ => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2)) := by
    filter_upwards [hsphere] with z hz
    by_cases hin : z ∈ Metric.ball (0 : ℂ) R
    · simp [hin]
    · have hle : R ≤ ‖z‖ := by simpa using hin
      have hne : ‖z‖ ≠ R := by simpa using hz
      have hgt : R < ‖z‖ := lt_of_le_of_ne hle hne.symm
      simp [hin, fderiv_zero_outside_disk hone hgt]
  rw [lintegral_congr_ae heq, lintegral_indicator Metric.isOpen_ball.measurableSet]
  rfl

/-- A quantitative lower bound for every admissible Lipschitz potential.
The inner disk is an actual subset of the zero plate; no gradient,
Sobolev, or boundary-trace hypothesis is added to admissibility. -/
theorem admissible_energy_lower {K : Set ℂ} {u : ℂ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hK : Metric.ball (0 : ℂ) r ⊆ K)
    (hu : ThreeReturnAnnulus.admissible K (Metric.ball 0 R) u) :
    ENNReal.ofReal (r / R) ≤
      ThreeReturnAnnulus.dirichletEnergy (Metric.ball 0 R) u := by
  obtain ⟨L, hL⟩ := hu.1
  let e : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2)
  let J : Set ℝ := Ioc (-r/2) (r/2)
  have hslice : ∀ᵐ y ∂volume.restrict J,
      ENNReal.ofReal (1 / R) ≤ ∫⁻ x in Ioc 0 R, e (horizontal y x) := by
    filter_upwards [(horizontal_ae_differentiable hL).filter_mono
      (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioc] with y hdy hy
    apply horizontal_energy_lower hL hR y
    · apply hu.2.1 _
      apply hK
      have hy' : |y| ≤ r/2 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
      have hn : ‖horizontal y 0‖ < r := by
        simp only [horizontal, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
        linarith
      simpa using hn
    · apply hu.2.2 _
      intro hz
      have hz' : ‖horizontal y R‖ < R := by simpa using hz
      have hn := Complex.abs_re_le_norm (horizontal y R)
      have hre : (horizontal y R).re = R := by simp [horizontal]
      rw [hre, abs_of_pos hR] at hn
      linarith
    · exact hdy
  have hconst : (∫⁻ _y in J, ENNReal.ofReal (1 / R)) =
      ENNReal.ofReal (r/R) := by
    rw [lintegral_const, Measure.restrict_apply_univ]
    change ENNReal.ofReal (1/R) * volume (Ioc (-r/2) (r/2)) = _
    rw [Real.volume_Ioc]
    have heq : r/2 - -r/2 = r := by ring
    rw [heq, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/R)]
    congr 1
    ring
  calc
    ENNReal.ofReal (r/R) = ∫⁻ _y in J, ENNReal.ofReal (1/R) := hconst.symm
    _ ≤ ∫⁻ y in J, ∫⁻ x in Ioc 0 R, e (horizontal y x) := lintegral_mono_ae hslice
    _ ≤ ∫⁻ y in J, ∫⁻ x : ℝ, e (horizontal y x) :=
      lintegral_mono (fun _ => setLIntegral_le_lintegral _ _)
    _ ≤ ∫⁻ y : ℝ, ∫⁻ x : ℝ, e (horizontal y x) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p : ℝ × ℝ, e (horizontal p.1 p.2) ∂((volume : Measure ℝ).prod volume) :=
      (lintegral_prod _ ((energy_measurable u).comp
        horizontal_measurePreserving.measurable).aemeasurable).symm
    _ = ∫⁻ z : ℂ, e z := horizontal_measurePreserving.lintegral_comp (energy_measurable u)
    _ = ThreeReturnAnnulus.dirichletEnergy (Metric.ball 0 R) u := full_energy_eq_disk hu.2.2

/-- Taking the infimum preserves the positive bound uniformly over all
competitors and all shapes of the inner plate containing the given disk. -/
theorem capacity_lower {K : Set ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hK : Metric.ball (0 : ℂ) r ⊆ K) :
    ENNReal.ofReal (r / R) ≤ ThreeReturnAnnulus.capacity K (Metric.ball 0 R) := by
  apply le_sInf
  rintro _ ⟨u, hu, rfl⟩
  exact admissible_energy_lower hr hR hK hu

theorem capacity_pos {K : Set ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hK : Metric.ball (0 : ℂ) r ⊆ K) :
    0 < ThreeReturnAnnulus.capacity K (Metric.ball 0 R) :=
  (ENNReal.ofReal_pos.mpr (div_pos hr hR)).trans_le (capacity_lower hr hR hK)

theorem variationalModulus_lt_top {K : Set ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hK : Metric.ball (0 : ℂ) r ⊆ K) :
    ThreeReturnAnnulus.variationalModulus K (Metric.ball 0 R) < ⊤ := by
  exact lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (capacity_pos hr hR hK).ne')

/-- The quantitative bound also controls the reciprocal from above. -/
theorem variationalModulus_le {K : Set ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hK : Metric.ball (0 : ℂ) r ⊆ K) :
    ThreeReturnAnnulus.variationalModulus K (Metric.ball 0 R) ≤
      ENNReal.ofReal (R/r) := by
  change (ThreeReturnAnnulus.capacity K (Metric.ball 0 R))⁻¹ ≤ _
  calc
    (ThreeReturnAnnulus.capacity K (Metric.ball 0 R))⁻¹ ≤
        (ENNReal.ofReal (r/R))⁻¹ := ENNReal.inv_le_inv.mpr (capacity_lower hr hR hK)
    _ = ENNReal.ofReal ((r/R)⁻¹) := (ENNReal.ofReal_inv_of_pos (div_pos hr hR)).symm
    _ = ENNReal.ofReal (R/r) := by rw [inv_div]

end
end CollarCapacityLower
