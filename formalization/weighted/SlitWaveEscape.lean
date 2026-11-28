import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Quantitative escape cutoff for geometric curve families

The line measure is one-dimensional Hausdorff measure on the geometric
trace. No finite-length or differentiability condition is imposed. A
continuous curve that crosses a round shell has at least the shell's
radial thickness of Hausdorff length in that shell. Disjoint dyadic
shells turn this into a common small-area admissible density for every
curve leaving a large disk.
-/

namespace SlitWaveEscape

open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-- Half-open radial shells are exactly disjoint at consecutive radii. -/
def shell (r R : ℝ) : Set ℂ := closedBall 0 R \ closedBall 0 r

theorem measurableSet_shell (r R : ℝ) : MeasurableSet (shell r R) :=
  isClosed_closedBall.measurableSet.diff isClosed_closedBall.measurableSet

theorem mem_shell {r R : ℝ} {z : ℂ} : z ∈ shell r R ↔ r < ‖z‖ ∧ ‖z‖ ≤ R := by
  simp only [shell, mem_sdiff, mem_closedBall, dist_zero_right, not_le]
  exact and_comm

/-- Every intermediate radius occurs on the interior of the path. The
trace may omit both endpoint values. -/
theorem radial_interval_subset {γ : ℝ → ℂ} {S : Set ℂ} {r R : ℝ}
    (hγ : ContinuousOn γ (Icc 0 1))
    (htrace : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ S)
    (hstart : ‖γ 0‖ ≤ r) (hend : R ≤ ‖γ 1‖) :
    Ioo r R ⊆ (fun z : ℂ => ‖z‖) '' (S ∩ shell r R) := by
  intro y hy
  obtain ⟨t, ht, hyt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hγ.norm (show y ∈ Icc ‖γ 0‖ ‖γ 1‖ from
      ⟨hstart.trans hy.1.le, hy.2.le.trans hend⟩)
  change ‖γ t‖ = y at hyt
  have ht0 : 0 < t := by
    by_contra hn
    have he : t = 0 := le_antisymm (not_lt.mp hn) ht.1
    subst t
    linarith [hy.1]
  have ht1 : t < 1 := by
    by_contra hn
    have he : t = 1 := le_antisymm ht.2 (not_lt.mp hn)
    subst t
    linarith [hy.2]
  refine ⟨γ t, ⟨htrace t ⟨ht0, ht1⟩, ?_⟩, hyt⟩
  rw [mem_shell, hyt]
  exact ⟨hy.1, hy.2.le⟩

/-- Radial projection is one-Lipschitz, so the complete geometric trace
has at least `R-r` units of one-dimensional Hausdorff measure in the
shell. This includes curves of infinite length. -/
theorem hausdorff_shell_lower {γ : ℝ → ℂ} {S : Set ℂ} {r R : ℝ}
    (hγ : ContinuousOn γ (Icc 0 1))
    (htrace : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ S)
    (hstart : ‖γ 0‖ ≤ r) (hend : R ≤ ‖γ 1‖) :
    ENNReal.ofReal (R-r) ≤ μH[1] (S ∩ shell r R) := by
  have hrad := measure_mono (μ := (μH[1] : Measure ℝ))
    (radial_interval_subset hγ htrace hstart hend)
  have hlip := LipschitzWith.hausdorffMeasure_image_le
    (lipschitzWith_one_norm : LipschitzWith 1 (fun z : ℂ => ‖z‖))
    (d := 1) (by norm_num) (S ∩ shell r R)
  rw [hausdorffMeasure_real, Real.volume_Ioo] at hrad
  rw [hausdorffMeasure_real] at hlip
  simpa using hrad.trans hlip

/-- The same lower bound stated directly for a connected geometric
trace, so it applies without choosing any path parametrization. -/
theorem hausdorff_shell_lower_of_isPreconnected {S : Set ℂ} {r R : ℝ}
    (hS : IsPreconnected S) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hstart : ‖a‖ ≤ r) (hend : R ≤ ‖b‖) :
    ENNReal.ofReal (R-r) ≤ μH[1] (S ∩ shell r R) := by
  have hradial : Ioo r R ⊆ (fun z : ℂ => ‖z‖) '' (S ∩ shell r R) := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hS.intermediate_value ha hb continuous_norm.continuousOn
      (show y ∈ Icc ‖a‖ ‖b‖ from ⟨hstart.trans hy.1.le, hy.2.le.trans hend⟩)
    change ‖z‖ = y at hzy
    refine ⟨z, ⟨hz, ?_⟩, hzy⟩
    rw [mem_shell, hzy]
    exact ⟨hy.1, hy.2.le⟩
  have hrad := measure_mono (μ := (μH[1] : Measure ℝ)) hradial
  have hlip := LipschitzWith.hausdorffMeasure_image_le
    (lipschitzWith_one_norm : LipschitzWith 1 (fun z : ℂ => ‖z‖))
    (d := 1) (by norm_num) (S ∩ shell r R)
  rw [hausdorffMeasure_real, Real.volume_Ioo] at hrad
  rw [hausdorffMeasure_real] at hlip
  simpa using hrad.trans hlip

/-- A shell carries its reciprocal radial-thickness density. -/
def shellDensity (r : ℝ) : ℂ → ℝ≥0∞ :=
  (shell r (2*r)).indicator (fun _ => ENNReal.ofReal (1/r))

theorem shellDensity_measurable (r : ℝ) : Measurable (shellDensity r) :=
  measurable_const.indicator (measurableSet_shell r (2*r))

/-- One shell contributes unit length on every continuous crossing,
measured on the geometric trace with Hausdorff measure. -/
theorem shellDensity_length {γ : ℝ → ℂ} {S : Set ℂ} {r : ℝ}
    (hr : 0 < r) (hγ : ContinuousOn γ (Icc 0 1))
    (htrace : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ S)
    (hstart : ‖γ 0‖ ≤ r) (hend : 2*r ≤ ‖γ 1‖) :
    1 ≤ ∫⁻ z, shellDensity r z ∂(μH[1].restrict S) := by
  have hrad := hausdorff_shell_lower hγ htrace hstart hend
  have hgap : 2*r-r = r := by ring
  rw [hgap] at hrad
  rw [shellDensity, lintegral_indicator_const (measurableSet_shell r (2*r)),
    Measure.restrict_apply (measurableSet_shell r (2*r)), inter_comm]
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal (1/r) * ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/r)]
      simp [hr.ne']
    _ ≤ ENNReal.ofReal (1/r) * μH[1] (S ∩ shell r (2*r)) := mul_le_mul_left' hrad _

theorem shellDensity_length_of_isPreconnected {S : Set ℂ} {r : ℝ}
    (hr : 0 < r) (hS : IsPreconnected S) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hstart : ‖a‖ ≤ r) (hend : 2*r ≤ ‖b‖) :
    1 ≤ ∫⁻ z, shellDensity r z ∂(μH[1].restrict S) := by
  have hrad := hausdorff_shell_lower_of_isPreconnected hS ha hb hstart hend
  have hgap : 2*r-r = r := by ring
  rw [hgap] at hrad
  rw [shellDensity, lintegral_indicator_const (measurableSet_shell r (2*r)),
    Measure.restrict_apply (measurableSet_shell r (2*r)), inter_comm]
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal (1/r) * ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/r)]
      simp [hr.ne']
    _ ≤ ENNReal.ofReal (1/r) * μH[1] (S ∩ shell r (2*r)) := mul_le_mul_left' hrad _

/-- Exact planar area of a dyadic shell. -/
theorem volume_shell {r : ℝ} (hr : 0 < r) :
    volume (shell r (2*r)) = ENNReal.ofReal (3*Real.pi*r^2) := by
  have hR : 0 ≤ 2*r := by positivity
  rw [shell, measure_sdiff (closedBall_subset_closedBall (by linarith : r ≤ 2*r))
    isClosed_closedBall.measurableSet.nullMeasurableSet measure_closedBall_lt_top.ne]
  simp only [Complex.volume_closedBall]
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_pow hr.le,
    ← ENNReal.ofReal_mul (sq_nonneg (2*r)), ← ENNReal.ofReal_mul (sq_nonneg r),
    ← ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ r^2*Real.pi)]
  congr 1
  ring

/-- A single unit crossing density has energy `3π`, independent of its
radial scale. -/
theorem shellDensity_area {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : ℂ, shellDensity r z ^ (2 : ℕ)) = ENNReal.ofReal (3*Real.pi) := by
  have heq : (fun z : ℂ => shellDensity r z ^ (2 : ℕ)) =
      (shell r (2*r)).indicator (fun _ => ENNReal.ofReal (1/r) ^ (2 : ℕ)) := by
    funext z
    by_cases hz : z ∈ shell r (2*r) <;> simp [shellDensity, hz]
  rw [heq, lintegral_indicator_const (measurableSet_shell r (2*r)), volume_shell hr,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1/r),
    ← ENNReal.ofReal_mul (sq_nonneg (1/r))]
  congr 1
  field_simp

/-- Inner radius of shell `j`, starting from a fixed positive radius. -/
def dyadicRadius (r : ℝ) (j : ℕ) : ℝ := (2 : ℝ)^j*r

theorem dyadicRadius_pos {r : ℝ} (hr : 0 < r) (j : ℕ) : 0 < dyadicRadius r j := by
  unfold dyadicRadius
  positivity

theorem dyadicRadius_succ (r : ℝ) (j : ℕ) :
    dyadicRadius r (j+1) = 2*dyadicRadius r j := by
  simp only [dyadicRadius, pow_succ]
  ring

theorem dyadicRadius_mono {r : ℝ} (hr : 0 ≤ r) : Monotone (dyadicRadius r) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij) hr

theorem dyadic_shells_disjoint {r : ℝ} (hr : 0 ≤ r) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (shell (dyadicRadius r i) (2*dyadicRadius r i))
      (shell (dyadicRadius r j) (2*dyadicRadius r j)) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  rw [mem_shell] at hzi hzj
  rcases lt_or_gt_of_ne hij with hij | hij
  · have hle := dyadicRadius_mono hr (Nat.succ_le_of_lt hij)
    rw [dyadicRadius_succ] at hle
    exact (not_lt_of_ge (hzi.2.trans hle)) hzj.1
  · have hle := dyadicRadius_mono hr (Nat.succ_le_of_lt hij)
    rw [dyadicRadius_succ] at hle
    exact (not_lt_of_ge (hzj.2.trans hle)) hzi.1

/-- Averaging the dyadic shell crossing densities gives the escape
cutoff. Its support lies between the initial and final radii. -/
def escapeDensity (r : ℝ) (N : ℕ) : ℂ → ℝ≥0∞ := fun z =>
  (N : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range N, shellDensity (dyadicRadius r j) z

theorem escapeDensity_measurable (r : ℝ) (N : ℕ) : Measurable (escapeDensity r N) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun j _ => shellDensity_measurable _

/-- Every connected trace joining the fixed inner disk to radius
`2^N*r` has cutoff length at least one. -/
theorem escapeDensity_length {S : Set ℂ} {r : ℝ} {N : ℕ}
    (hr : 0 < r) (hN : 0 < N) (hS : IsPreconnected S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hstart : ‖a‖ ≤ r) (hend : dyadicRadius r N ≤ ‖b‖) :
    1 ≤ ∫⁻ z, escapeDensity r N z ∂(μH[1].restrict S) := by
  have hmeas : Measurable (fun z : ℂ => ∑ j ∈ Finset.range N,
      shellDensity (dyadicRadius r j) z) :=
    Finset.measurable_sum _ fun j _ => shellDensity_measurable _
  unfold escapeDensity
  rw [lintegral_const_mul _ hmeas,
    lintegral_finsetSum _ (fun j _ => shellDensity_measurable _)]
  have hone : (N : ℝ≥0∞) ≤ ∑ j ∈ Finset.range N,
      ∫⁻ z, shellDensity (dyadicRadius r j) z ∂(μH[1].restrict S) := by
    calc
      (N : ℝ≥0∞) = ∑ _j ∈ Finset.range N, (1 : ℝ≥0∞) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        apply shellDensity_length_of_isPreconnected (dyadicRadius_pos hr j) hS ha hb
        · have hbase := dyadicRadius_mono hr.le (Nat.zero_le j)
          have hbase' : r ≤ dyadicRadius r j := by
            simpa only [dyadicRadius, pow_zero, one_mul] using hbase
          exact hstart.trans hbase'
        · have hle := dyadicRadius_mono hr.le (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
          rw [dyadicRadius_succ] at hle
          exact hle.trans hend
  calc
    (1 : ℝ≥0∞) = (N : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞) := by
      symm
      exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hN.ne') (ENNReal.natCast_ne_top N)
    _ ≤ _ := mul_le_mul_left' hone _

private theorem dyadic_density_sum_square {r : ℝ} (hr : 0 ≤ r) (N : ℕ) (z : ℂ) :
    (∑ j ∈ Finset.range N, shellDensity (dyadicRadius r j) z) ^ (2 : ℕ) =
      ∑ j ∈ Finset.range N, shellDensity (dyadicRadius r j) z ^ (2 : ℕ) := by
  classical
  by_cases hex : ∃ i ∈ Finset.range N, shellDensity (dyadicRadius r i) z ≠ 0
  · obtain ⟨i, hi, hvi⟩ := hex
    have hzi : z ∈ shell (dyadicRadius r i) (2*dyadicRadius r i) := by
      by_contra hn
      exact hvi (by simp [shellDensity, hn])
    have hzero (j : ℕ) (_hj : j ∈ Finset.range N) (hji : j ≠ i) :
        shellDensity (dyadicRadius r j) z = 0 := by
      have hzj : z ∉ shell (dyadicRadius r j) (2*dyadicRadius r j) := by
        intro hzj
        exact Set.disjoint_left.mp (dyadic_shells_disjoint hr hji) hzj hzi
      simp [shellDensity, hzj]
    rw [Finset.sum_eq_single_of_mem i hi hzero,
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hzero j hj hji]; simp)]
  · have hzero : ∀ j ∈ Finset.range N, shellDensity (dyadicRadius r j) z = 0 := by
      intro j hj
      by_contra hn
      exact hex ⟨j, hj, hn⟩
    have hsum : (∑ j ∈ Finset.range N,
        shellDensity (dyadicRadius r j) z ^ (2 : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hzero j hj]
      norm_num
    rw [Finset.sum_eq_zero hzero, hsum]
    norm_num

/-- Exact energy of the common escape cutoff. The factor `1/N`
comes from disjointness of the shells, not an estimate for a sampled
curve or a chosen foliation. -/
theorem escapeDensity_area {r : ℝ} {N : ℕ} (hr : 0 < r) (hN : 0 < N) :
    (∫⁻ z : ℂ, escapeDensity r N z ^ (2 : ℕ)) =
      ENNReal.ofReal (3*Real.pi/(N : ℝ)) := by
  have hsq : (fun z : ℂ => escapeDensity r N z ^ (2 : ℕ)) =
      fun z => (N : ℝ≥0∞)⁻¹ ^ (2 : ℕ) *
        ∑ j ∈ Finset.range N, shellDensity (dyadicRadius r j) z ^ (2 : ℕ) := by
    funext z
    rw [escapeDensity, mul_pow, dyadic_density_sum_square hr.le]
  have hmeas : Measurable (fun z : ℂ => ∑ j ∈ Finset.range N,
      shellDensity (dyadicRadius r j) z ^ (2 : ℕ)) :=
    Finset.measurable_sum _ fun j _ => (shellDensity_measurable _).pow_const 2
  rw [hsq, lintegral_const_mul _ hmeas,
    lintegral_finsetSum _ (fun j _ => (shellDensity_measurable _).pow_const 2)]
  simp_rw [shellDensity_area (dyadicRadius_pos hr _)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hN), ENNReal.ofReal_natCast]
  calc
    (N : ℝ≥0∞)⁻¹ ^ (2 : ℕ) * ((N : ℝ≥0∞) * ENNReal.ofReal (3*Real.pi)) =
        (N : ℝ≥0∞)⁻¹ * (((N : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞)) *
          ENNReal.ofReal (3*Real.pi)) := by ring
    _ = ENNReal.ofReal (3*Real.pi)/(N : ℝ≥0∞) := by
      rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hN.ne') (ENNReal.natCast_ne_top N)]
      simp [div_eq_mul_inv, mul_comm]

/-- The concrete common density and its exact area bound, with a
quantifier over all connected escaping traces. -/
theorem exists_escape_density {r : ℝ} {N : ℕ} (hr : 0 < r) (hN : 0 < N) :
    ∃ ρ : ℂ → ℝ≥0∞, Measurable ρ ∧
      (∫⁻ z : ℂ, ρ z ^ (2 : ℕ)) = ENNReal.ofReal (3*Real.pi/(N : ℝ)) ∧
      ∀ S : Set ℂ, IsPreconnected S →
        (∃ a ∈ S, ‖a‖ ≤ r) →
        (∃ b ∈ S, dyadicRadius r N ≤ ‖b‖) →
        1 ≤ ∫⁻ z, ρ z ∂(μH[1].restrict S) := by
  refine ⟨escapeDensity r N, escapeDensity_measurable r N, escapeDensity_area hr hN, ?_⟩
  intro S hS ha hb
  obtain ⟨a, ha, hstart⟩ := ha
  obtain ⟨b, hb, hend⟩ := hb
  exact escapeDensity_length hr hN hS ha hb hstart hend

end
end SlitWaveEscape
