import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# A physical Dirichlet-energy certificate for the three-return collar

The quantities here use the actual planar derivative and Lebesgue integral.
For the condenser with inner plate `K` and outer domain `U`, competitors are
globally Lipschitz real potentials, zero on `K` and one outside `U`. The
capacity is the infimum of their Dirichlet energies and its reciprocal is an
extended nonnegative variational modulus. A zero capacity has infinite
reciprocal, so it causes no division convention problem.

The explicit cutoff works for every physical scale, without invoking a
change-of-variables or conformal-invariance theorem. This file does not
identify the variational definition with an annulus uniformization modulus.
-/

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ThreeReturnAnnulus

/-- Planar Dirichlet energy, with the Euclidean operator norm of the real
derivative of the scalar potential. -/
noncomputable def dirichletEnergy (U : Set ℂ) (u : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2)

/-- Literal plate boundary values and a global Lipschitz condition. -/
def admissible (K U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  (∃ L : ℝ≥0, LipschitzWith L u) ∧
  (∀ z ∈ K, u z = 0) ∧ (∀ z ∉ U, u z = 1)

/-- The variational capacity uses every admissible Lipschitz potential. -/
noncomputable def capacity (K U : Set ℂ) : ℝ≥0∞ :=
  sInf (dirichletEnergy U '' {u | admissible K U u})

/-- The reciprocal convention is meaningful also at zero capacity. -/
noncomputable def variationalModulus (K U : Set ℂ) : ℝ≥0∞ :=
  (capacity K U)⁻¹

/-- Every competitor is differentiable almost everywhere by Rademacher. -/
theorem admissible_ae_differentiable {K U : Set ℂ} {u : ℂ → ℝ}
    (hu : admissible K U u) :
    ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ u z := by
  obtain ⟨L, hL⟩ := hu.1
  exact hL.ae_differentiableAt

theorem capacity_le_energy {K U : Set ℂ} {u : ℂ → ℝ}
    (hu : admissible K U u) : capacity K U ≤ dirichletEnergy U u :=
  sInf_le ⟨u, hu, rfl⟩

/-- A potential with a transition over the physical gap `d/60`. -/
noncomputable def collarPotential (d : ℝ) (z : ℂ) : ℝ :=
  min (max ((60 / d) * ‖z‖ - 9) 0) 1

theorem collarPotential_lipschitz {d : ℝ} (hd : 0 < d) :
    LipschitzWith ⟨60 / d, by positivity⟩ (collarPotential d) := by
  have h : LipschitzWith ⟨60 / d, by positivity⟩
      (fun z : ℂ => (60 / d) * ‖z‖ - 9) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [Real.dist_eq, sub_sub_sub_cancel_right]
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 60 / d)]
    exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using abs_norm_sub_norm_le z w)
      (by positivity)
  exact (h.max_const 0).min_const 1

theorem collarPotential_zero {d : ℝ} (hd : 0 < d) {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 (3 * d / 20)) : collarPotential d z = 0 := by
  have hz' : ‖z‖ ≤ 3 * d / 20 := by simpa using hz
  have h : (60 / d) * ‖z‖ - 9 ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hz' (by positivity : (0 : ℝ) ≤ 60 / d)
    have heq : (60 / d) * (3 * d / 20) = 9 := by field_simp; ring
    rw [heq] at hmul
    linarith
  simp [collarPotential, max_eq_right h]

theorem collarPotential_one {d : ℝ} (hd : 0 < d) {z : ℂ}
    (hz : z ∉ Metric.ball 0 (d / 6)) : collarPotential d z = 1 := by
  have hz' : d / 6 ≤ ‖z‖ := by simpa using hz
  have h : 1 ≤ (60 / d) * ‖z‖ - 9 := by
    have hmul := mul_le_mul_of_nonneg_left hz' (by positivity : (0 : ℝ) ≤ 60 / d)
    have heq : (60 / d) * (d / 6) = 10 := by field_simp; ring
    rw [heq] at hmul
    linarith
  exact min_eq_right (h.trans (le_max_left _ _))

theorem collarPotential_admissible {d : ℝ} (hd : 0 < d) {K : Set ℂ}
    (hK : K ⊆ Metric.closedBall 0 (3 * d / 20)) :
    admissible K (Metric.ball 0 (d / 6)) (collarPotential d) := by
  exact ⟨⟨_, collarPotential_lipschitz hd⟩,
    fun z hz => collarPotential_zero hd (hK hz),
    fun z hz => collarPotential_one hd hz⟩

theorem collarPotential_fderiv_zero_inner {d : ℝ} (hd : 0 < d) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (3 * d / 20)) :
    fderiv ℝ (collarPotential d) z = 0 := by
  have h : collarPotential d =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℝ)) := by
    filter_upwards [Metric.isOpen_ball.eventually_mem hz] with w hw
    exact collarPotential_zero hd (Metric.ball_subset_closedBall hw)
  simpa using h.fderiv_eq

theorem collarPotential_energy_le {d : ℝ} (hd : 0 < d) :
    dirichletEnergy (Metric.ball 0 (d / 6)) (collarPotential d) ≤
      ENNReal.ofReal (19 * Real.pi) := by
  have hderiv (z : ℂ) : ‖fderiv ℝ (collarPotential d) z‖ ≤ 60 / d :=
    norm_fderiv_le_of_lipschitz ℝ (collarPotential_lipschitz hd)
  have hsq (z : ℂ) : ‖fderiv ℝ (collarPotential d) z‖ ^ 2 ≤ (60 / d) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hderiv z) 2
  have hradius : 3 * d / 20 ≤ d / 6 := by linarith
  have hvolume : volume (Metric.ball (0 : ℂ) (d / 6) \
      Metric.ball 0 (3 * d / 20)) =
      ENNReal.ofReal (((d / 6) ^ 2 - (3 * d / 20) ^ 2) * Real.pi) := by
    rw [measure_sdiff (Metric.ball_subset_ball hradius)
      Metric.isOpen_ball.measurableSet.nullMeasurableSet measure_ball_lt_top.ne]
    simp only [Complex.volume_ball]
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ d / 6),
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 3 * d / 20),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d / 6) ^ 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 * d / 20) ^ 2),
      ← ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ (3 * d / 20) ^ 2 * Real.pi)]
    congr 1
    ring
  calc
    dirichletEnergy (Metric.ball 0 (d / 6)) (collarPotential d) ≤
        ∫⁻ z in Metric.ball (0 : ℂ) (d / 6),
          (Metric.ball (0 : ℂ) (3 * d / 20))ᶜ.indicator
            (fun _ => ENNReal.ofReal ((60 / d) ^ 2)) z := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ Metric.ball (0 : ℂ) (3 * d / 20)
      · simp [hz, collarPotential_fderiv_zero_inner hd hz]
      · simpa [hz] using ENNReal.ofReal_le_ofReal (hsq z)
    _ = ENNReal.ofReal ((60 / d) ^ 2) *
        volume (Metric.ball (0 : ℂ) (d / 6) \ Metric.ball 0 (3 * d / 20)) := by
      rw [lintegral_indicator Metric.isOpen_ball.measurableSet.compl, lintegral_const,
        Measure.restrict_apply_univ,
        Measure.restrict_apply Metric.isOpen_ball.measurableSet.compl]
      apply congrArg (fun s : Set ℂ => ENNReal.ofReal ((60 / d) ^ 2) * volume s)
      ext z
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    _ = ENNReal.ofReal (19 * Real.pi) := by
      rw [hvolume]
      rw [← ENNReal.ofReal_mul (sq_nonneg (60 / d))]
      congr 1
      field_simp
      ring

theorem physical_capacity_lt_sixty {d : ℝ} (hd : 0 < d) {K : Set ℂ}
    (hK : K ⊆ Metric.closedBall 0 (3 * d / 20)) :
    capacity K (Metric.ball 0 (d / 6)) < 60 := by
  have hbound := (capacity_le_energy (collarPotential_admissible hd hK)).trans
    (collarPotential_energy_le hd)
  apply hbound.trans_lt
  have hpi : 19 * Real.pi < (60 : ℝ) := by nlinarith [Real.pi_lt_d4]
  simpa using ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 60) |>.2 hpi

theorem physical_variationalModulus_gt {d : ℝ} (hd : 0 < d) {K : Set ℂ}
    (hK : K ⊆ Metric.closedBall 0 (3 * d / 20)) :
    (60 : ℝ≥0∞)⁻¹ < variationalModulus K (Metric.ball 0 (d / 6)) := by
  exact ENNReal.inv_lt_inv.mpr (physical_capacity_lt_sixty hd hK)

end ThreeReturnAnnulus
