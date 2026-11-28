import ActualChildSupremum
import ChildSlitPositive

/-!
# Nonzero physical and limiting independent child optima

One explicit upper semicircular ribbon fits the literal child electrodes
for every certified actual tip of period at least seventeen. The proved
source inradius contains this ribbon. Its geometric modulus supplies the
uniform lower bound `1/(3π)` for the full physical optimum and for its
finite limiting value.
-/

namespace ActualChildPositive

open Set Filter Metric
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter ActualParentMarks ActualChildMarks
open ActualChildSource ActualChildSupremum ChildSlitPositive
open scoped Topology ENNReal

noncomputable section

theorem limitingChildWidth_lower {k : ℝ} (hk : k ∈ parameterInterval) :
    ENNReal.ofReal (1/(3*Real.pi)) ≤ limitingChildWidth k hk := by
  obtain ⟨h2l, h2u, h5l, h5u, _, _⟩ := limit_cut_boxes hk
  have h4 := parameter_orbit_bounds hk
  have ha := limitAlpha_bracket hk
  apply width_lower_of_fixed_windows (limitMarking k hk) univ
  · change -criticalOrbit k 4 < -9/10
    linarith [h4.2.2.1]
  · change -17/20 < criticalOrbit k 2
    linarith
  · change criticalOrbit k 5 < -13/20
    linarith
  · change -3/5 < -limitAlpha k
    linarith [ha.2]
  · exact subset_univ _

theorem limitingChildWidth_pos {k : ℝ} (hk : k ∈ parameterInterval) :
    0 < limitingChildWidth k hk := by
  have hp : 0 < ENNReal.ofReal (1/(3*Real.pi)) := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  exact hp.trans_le (limitingChildWidth_lower hk)

theorem limitingChildWidth_toReal_pos {k : ℝ} (hk : k ∈ parameterInterval) :
    0 < (limitingChildWidth k hk).toReal :=
  ENNReal.toReal_pos (limitingChildWidth_pos hk).ne' (limitingChildWidth_ne_top k hk)

private theorem actual_unit_disk {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : closedBall (0 : ℂ) 1 ⊆ normalizedSource c p := by
  have hp8 : 8 ≤ p/2 := by omega
  have hpow : (2 : ℝ)^8 ≤ (2 : ℝ)^(p/2) :=
    pow_le_pow_right₀ (by norm_num) hp8
  norm_num at hpow
  have hr := innerRadius_lower hc
  have h1 : 1 ≤ innerRadius c p := by linarith
  exact (closedBall_subset_closedBall h1).trans
    (closedBall_subset_normalizedSource hp hc)

/-- The witness uses the actual critical-iterate electrodes and lies
inside the exact source component for every stated period. -/
theorem actualChildWidth_lower {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    ENNReal.ofReal (1/(3*Real.pi)) ≤ actualChildWidth hp hc hk hroot := by
  obtain ⟨h2l, h2u, h5l, h5u, _, _⟩ := limit_cut_boxes hk
  have h4 := parameter_orbit_bounds hk
  have ha := actualAlpha_spec hp hc
  have he1 := abs_lt.mp (actualChildCuts_error_lt hp hc hk hroot 1)
  have he2 := abs_lt.mp (actualChildCuts_error_lt hp hc hk hroot 2)
  have he3 := abs_lt.mp (actualChildCuts_error_lt hp hc hk hroot 3)
  change -(1/150 : ℝ) < -normalizedCut c p 4 - -criticalOrbit k 4 ∧
    -normalizedCut c p 4 - -criticalOrbit k 4 < 1/150 at he1
  change -(1/150 : ℝ) < normalizedCut c p 2 - criticalOrbit k 2 ∧
    normalizedCut c p 2 - criticalOrbit k 2 < 1/150 at he2
  change -(1/150 : ℝ) < normalizedCut c p 5 - criticalOrbit k 5 ∧
    normalizedCut c p 5 - criticalOrbit k 5 < 1/150 at he3
  apply width_lower_of_fixed_windows (actualMarking hp hc hk hroot) (normalizedSource c p)
  · change -normalizedCut c p 4 < -9/10
    linarith [he1.2, h4.2.2.1]
  · change -17/20 < normalizedCut c p 2
    linarith [he2.1]
  · change normalizedCut c p 5 < -13/20
    linarith [he3.2]
  · change -3/5 < -actualAlpha c p
    linarith [ha.1.2]
  · exact actual_unit_disk hp hc

theorem actualChildWidth_pos {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    0 < actualChildWidth hp hc hk hroot := by
  have hp' : 0 < ENNReal.ofReal (1/(3*Real.pi)) := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  exact hp'.trans_le (actualChildWidth_lower hp hc hk hroot)

theorem physicalChildWidth_lower {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    ENNReal.ofReal (1/(3*Real.pi)) ≤ physicalChildWidth hp hc hk hroot := by
  rw [physicalChildWidth_eq_actual]
  exact actualChildWidth_lower hp hc hk hroot

theorem physicalChildWidth_toReal_pos {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    0 < (physicalChildWidth hp hc hk hroot).toReal := by
  rw [physicalChildWidth_eq_actual]
  exact ENNReal.toReal_pos (actualChildWidth_pos hp hc hk hroot).ne'
    (actualChildWidth_ne_top hp hc hk hroot)

/-- Actual parameter existence, finite positive physical optima, and a
finite positive physical limit are proved in one unconditional statement. -/
theorem exists_positive_physical_child_optima_converging :
    ∃ (k : ℝ) (hk : k ∈ parameterInterval) (hroot : relation k = 0),
      ∃ (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)),
        (∀ n, 0 < (physicalChildWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal) ∧
        0 < (limitingChildWidth k hk).toReal ∧
        Tendsto (fun n => (physicalChildWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
          atTop (𝓝 (limitingChildWidth k hk).toReal) := by
  classical
  obtain ⟨k, ⟨hk, hroot⟩, _⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  exact ⟨k, hk, hroot, c, hc,
    fun n => physicalChildWidth_toReal_pos (by omega) (hc n) hk hroot,
    limitingChildWidth_toReal_pos hk, physical_child_optimum_real_converges hk hroot c hc⟩

end
end ActualChildPositive
