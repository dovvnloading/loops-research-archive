import AnnularModeContraction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The actual Dirichlet minimum for one annular Fourier mode

The scalar mode form used by `AnnularModeContraction` is identified here with
an interval variational problem.  For a positive frequency `n`, the integrand
is literally `f' ^ 2 + n ^ 2 * f ^ 2`.  The minimizing profile is given by
decaying exponentials.  An exact energy decomposition proves minimality
against every continuously differentiable competitor on the closed interval.

This file concerns positive modes.  The constant mode has a different
variational form and is not included in this identification.
-/

open Set MeasureTheory

namespace AnnularFourierTrace

noncomputable section

/-- Propagation factor of a positive Fourier frequency through a cylinder. -/
def attenuation (n L : ℝ) : ℝ := Real.exp (-(n * L))

/-- Literal one-dimensional Dirichlet energy of a radial Fourier profile. -/
def energy (n L : ℝ) (f f' : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L, (f' t) ^ 2 + n ^ 2 * (f t) ^ 2

/-- Harmonic interpolation with endpoint amplitudes `a` and `b`. -/
def profile (n L a b t : ℝ) : ℝ :=
  ((a - attenuation n L * b) * Real.exp (-(n * t)) +
    (b - attenuation n L * a) * Real.exp (-(n * (L - t)))) /
      (1 - attenuation n L ^ 2)

/-- The explicit derivative of the harmonic interpolation. -/
def profileDeriv (n L a b t : ℝ) : ℝ :=
  n * (-((a - attenuation n L * b) * Real.exp (-(n * t))) +
    (b - attenuation n L * a) * Real.exp (-(n * (L - t)))) /
      (1 - attenuation n L ^ 2)

theorem attenuation_pos (n L : ℝ) : 0 < attenuation n L :=
  Real.exp_pos _

theorem attenuation_lt_one {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    attenuation n L < 1 := by
  rw [attenuation, Real.exp_lt_one_iff]
  exact neg_neg_of_pos (mul_pos hn hL)

theorem attenuation_den_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    0 < 1 - attenuation n L ^ 2 := by
  have h0 := attenuation_pos n L
  have h1 := attenuation_lt_one hn hL
  have hprod : 0 < (1 - attenuation n L) * (1 + attenuation n L) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem hasDerivAt_profile (n L a b t : ℝ) :
    HasDerivAt (profile n L a b) (profileDeriv n L a b t) t := by
  have hleft := (((hasDerivAt_id t).const_mul n).neg.exp).const_mul
    (a - attenuation n L * b)
  have hright := ((((hasDerivAt_id t).const_sub L).const_mul n).neg.exp).const_mul
    (b - attenuation n L * a)
  convert (hleft.add hright).div_const (1 - attenuation n L ^ 2) using 1 <;>
    (try dsimp [profile, profileDeriv]) <;> ring

theorem hasDerivAt_profileDeriv (n L a b t : ℝ) :
    HasDerivAt (profileDeriv n L a b) (n ^ 2 * profile n L a b t) t := by
  have hleft := (((hasDerivAt_id t).const_mul n).neg.exp).const_mul
    (a - attenuation n L * b)
  have hright := ((((hasDerivAt_id t).const_sub L).const_mul n).neg.exp).const_mul
    (b - attenuation n L * a)
  convert ((hleft.neg.add hright).const_mul n).div_const
    (1 - attenuation n L ^ 2) using 1 <;>
    (try dsimp [profile, profileDeriv]) <;> ring

theorem continuous_profile (n L a b : ℝ) : Continuous (profile n L a b) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_profile n L a b t).continuousAt

theorem continuous_profileDeriv (n L a b : ℝ) :
    Continuous (profileDeriv n L a b) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_profileDeriv n L a b t).continuousAt

theorem profile_zero {n L : ℝ} (hn : 0 < n) (hL : 0 < L) (a b : ℝ) :
    profile n L a b 0 = a := by
  simp only [profile, mul_zero, neg_zero, Real.exp_zero, sub_zero, mul_one]
  change ((a - attenuation n L * b) +
    (b - attenuation n L * a) * attenuation n L) / (1 - attenuation n L ^ 2) = a
  apply (div_eq_iff (ne_of_gt (attenuation_den_pos hn hL))).2
  ring

theorem profile_length {n L : ℝ} (hn : 0 < n) (hL : 0 < L) (a b : ℝ) :
    profile n L a b L = b := by
  simp only [profile, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
  change ((a - attenuation n L * b) * attenuation n L +
    (b - attenuation n L * a)) / (1 - attenuation n L ^ 2) = b
  apply (div_eq_iff (ne_of_gt (attenuation_den_pos hn hL))).2
  ring

/-- The energy of a solution of the mode equation is its boundary flux. -/
theorem harmonic_energy_eq_boundary {n L : ℝ} {h g : ℝ → ℝ}
    (hh : ∀ t, HasDerivAt h (g t) t)
    (hg : ∀ t, HasDerivAt g (n ^ 2 * h t) t) :
    energy n L h g = h L * g L - h 0 * g 0 := by
  have hc : Continuous h :=
    continuous_iff_continuousAt.mpr fun t => (hh t).continuousAt
  have gc : Continuous g :=
    continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  unfold energy
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => h t * g t)
  · intro t _ht
    change HasDerivAt (fun s => h s * g s) ((g t) ^ 2 + n ^ 2 * (h t) ^ 2) t
    have hscalar : (g t) ^ 2 + n ^ 2 * (h t) ^ 2 =
        g t * g t + h t * (n ^ 2 * h t) := by ring
    rw [hscalar]
    exact (hh t).mul (hg t)
  · exact ((gc.pow 2).add (continuous_const.mul (hc.pow 2))).intervalIntegrable 0 L

/-- Exact completion of squares in the interval variational problem.
Only continuity at the endpoints and differentiability in the interior are
required of the competitor. -/
theorem energy_decomposition {n L : ℝ} (hL : 0 ≤ L) {h g f f' : ℝ → ℝ}
    (hh : ∀ t, HasDerivAt h (g t) t)
    (hg : ∀ t, HasDerivAt g (n ^ 2 * h t) t)
    (hf : ContinuousOn f (Icc 0 L)) (hf' : ContinuousOn f' (Icc 0 L))
    (hder : ∀ t ∈ Ioo 0 L, HasDerivAt f (f' t) t)
    (hzero : f 0 = h 0) (hlength : f L = h L) :
    energy n L f f' = energy n L h g +
      energy n L (fun t => f t - h t) (fun t => f' t - g t) := by
  have hc : Continuous h :=
    continuous_iff_continuousAt.mpr fun t => (hh t).continuousAt
  have gc : Continuous g :=
    continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hdiff : ContinuousOn (fun t => f t - h t) (Icc 0 L) :=
    hf.sub hc.continuousOn
  have hdiff' : ContinuousOn (fun t => f' t - g t) (Icc 0 L) :=
    hf'.sub gc.continuousOn
  have hcrossc : ContinuousOn
      (fun t => n ^ 2 * h t * (f t - h t) + g t * (f' t - g t)) (Icc 0 L) :=
    ((continuousOn_const.mul hc.continuousOn).mul hdiff).add
      (gc.continuousOn.mul hdiff')
  have hcrossi : IntervalIntegrable
      (fun t => n ^ 2 * h t * (f t - h t) + g t * (f' t - g t)) volume 0 L :=
    hcrossc.intervalIntegrable_of_Icc hL
  have hcross :
      (∫ t in (0 : ℝ)..L,
        n ^ 2 * h t * (f t - h t) + g t * (f' t - g t)) = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun t => g t * (f t - h t)) hL
      (gc.continuousOn.mul hdiff)
      (fun t ht => (hg t).mul ((hder t ht).sub (hh t))) hcrossi
    simpa only [hzero, hlength, sub_self, mul_zero] using hFTC
  have hhi : IntervalIntegrable
      (fun t => (g t) ^ 2 + n ^ 2 * (h t) ^ 2) volume 0 L :=
    ((gc.pow 2).add (continuous_const.mul (hc.pow 2))).intervalIntegrable 0 L
  have hdi : IntervalIntegrable
      (fun t => (f' t - g t) ^ 2 + n ^ 2 * (f t - h t) ^ 2) volume 0 L :=
    ((hdiff'.pow 2).add (continuousOn_const.mul (hdiff.pow 2))).intervalIntegrable_of_Icc hL
  unfold energy
  calc
    (∫ t in (0 : ℝ)..L, (f' t) ^ 2 + n ^ 2 * (f t) ^ 2) =
        ∫ t in (0 : ℝ)..L,
          ((g t) ^ 2 + n ^ 2 * (h t) ^ 2) +
          ((f' t - g t) ^ 2 + n ^ 2 * (f t - h t) ^ 2) +
          2 * (n ^ 2 * h t * (f t - h t) + g t * (f' t - g t)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      ring
    _ = (∫ t in (0 : ℝ)..L, (g t) ^ 2 + n ^ 2 * (h t) ^ 2) +
        (∫ t in (0 : ℝ)..L, (f' t - g t) ^ 2 + n ^ 2 * (f t - h t) ^ 2) +
        2 * (∫ t in (0 : ℝ)..L,
          n ^ 2 * h t * (f t - h t) + g t * (f' t - g t)) := by
      rw [intervalIntegral.integral_add (hhi.add hdi) (hcrossi.const_mul 2),
        intervalIntegral.integral_add hhi hdi, intervalIntegral.integral_const_mul]
    _ = _ := by rw [hcross]; ring

/-- The mode form is the energy of the explicit harmonic interpolation. -/
theorem profile_energy {n L : ℝ} (hn : 0 < n) (hL : 0 < L) (a b : ℝ) :
    energy n L (profile n L a b) (profileDeriv n L a b) =
      n * AnnularModeContraction.mode (attenuation n L) a b := by
  rw [harmonic_energy_eq_boundary (hasDerivAt_profile n L a b)
    (hasDerivAt_profileDeriv n L a b), profile_length hn hL, profile_zero hn hL]
  simp only [profileDeriv, sub_self, mul_zero, neg_zero, Real.exp_zero,
    mul_one, sub_zero]
  change b * (n * (-((a - attenuation n L * b) * attenuation n L) +
    (b - attenuation n L * a)) / (1 - attenuation n L ^ 2)) -
    a * (n * (-(a - attenuation n L * b) +
      (b - attenuation n L * a) * attenuation n L) / (1 - attenuation n L ^ 2)) = _
  unfold AnnularModeContraction.mode
  ring

/-- Every continuously differentiable competitor has at least the mode energy. -/
theorem mode_le_energy {n L a b : ℝ} (hn : 0 < n) (hL : 0 < L)
    {f f' : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 L))
    (hf' : ContinuousOn f' (Icc 0 L))
    (hder : ∀ t ∈ Ioo 0 L, HasDerivAt f (f' t) t)
    (hzero : f 0 = a) (hlength : f L = b) :
    n * AnnularModeContraction.mode (attenuation n L) a b ≤ energy n L f f' := by
  have hsplit := energy_decomposition hL.le (hasDerivAt_profile n L a b)
    (hasDerivAt_profileDeriv n L a b) hf hf' hder
    (hzero.trans (profile_zero hn hL a b).symm)
    (hlength.trans (profile_length hn hL a b).symm)
  have hnonneg : 0 ≤ energy n L (fun t => f t - profile n L a b t)
      (fun t => f' t - profileDeriv n L a b t) := by
    apply intervalIntegral.integral_nonneg_of_forall hL.le
    intro t
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg n) (sq_nonneg _))
  rw [profile_energy hn hL a b] at hsplit
  linarith

/-- Energy values of the literal closed-interval variational problem. -/
def c1EnergyValues (n L a b : ℝ) : Set ℝ :=
  {E | ∃ f f' : ℝ → ℝ,
    ContinuousOn f (Icc 0 L) ∧ ContinuousOn f' (Icc 0 L) ∧
    (∀ t ∈ Ioo 0 L, HasDerivAt f (f' t) t) ∧
    f 0 = a ∧ f L = b ∧ E = energy n L f f'}

/-- The scalar mode form is the attained minimum of the actual Dirichlet
energy, not merely the value at a trial profile. -/
theorem mode_isLeast_energy {n L : ℝ} (hn : 0 < n) (hL : 0 < L) (a b : ℝ) :
    IsLeast (c1EnergyValues n L a b)
      (n * AnnularModeContraction.mode (attenuation n L) a b) := by
  constructor
  · refine ⟨profile n L a b, profileDeriv n L a b,
      (continuous_profile n L a b).continuousOn,
      (continuous_profileDeriv n L a b).continuousOn,
      fun t _ht => hasDerivAt_profile n L a b t,
      profile_zero hn hL a b, profile_length hn hL a b, ?_⟩
    exact (profile_energy hn hL a b).symm
  · rintro E ⟨f, f', hf, hf', hder, hzero, hlength, rfl⟩
    exact mode_le_energy hn hL hf hf' hder hzero hlength

end
end AnnularFourierTrace
