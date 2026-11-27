import LimitingCrestCoefficient
import LimitingCrestEndpoint

/-!
# A positive full limiting-model coefficient

The upper integration endpoint is the unique terminal collision, not an
assumed numerical optimizer. This is the proposed model integral itself;
convergence of physical marked widths to it is a separate assertion.
-/

namespace LimitingCrest

open Set MeasureTheory
noncomputable section

theorem crossingCos_radial_coordinate {κ s : ℝ} (hs : s ≠ 0) :
    crossingCos κ s = (radialAbscissa κ s + 3/4)/s := by
  unfold crossingCos radialAbscissa radialDiscriminant
  field_simp [hs]
  <;> ring

/-- The entire proposed parent branch has a nondegenerate angle. -/
theorem full_crossingCos_bounds {κ s : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hs : s ∈ Icc (1/16) (1/8)) :
    crossingCos κ s ∈ Ioo (-1) 1 := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hv := radial_ordinate_pos hk hs
  have hc := radial_circle_identity hk hs
  have hupper : radialAbscissa κ s + 3/4 < s := by
    by_contra h
    have hp := pow_le_pow_left₀ hs0.le (le_of_not_gt h) 2
    nlinarith only [hp, hc, hv]
  have hlower : -s < radialAbscissa κ s + 3/4 := by
    by_contra h
    have hh : s ≤ -(radialAbscissa κ s + 3/4) := by linarith
    have hp := pow_le_pow_left₀ hs0.le hh 2
    nlinarith only [hp, hc, hv]
  rw [crossingCos_radial_coordinate hs0.ne']
  constructor
  · apply (lt_div_iff₀ hs0).mpr
    linarith
  · apply (div_lt_iff₀ hs0).mpr
    linarith

theorem full_integrand_continuousOn {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) :
    ContinuousOn (fun s => 1/(s*Real.arccos (crossingCos κ s)))
      (Icc (1/16) (1/8)) := by
  have hroot : ContinuousOn (crossingCos κ) (Icc (1/16) (1/8)) := by
    unfold crossingCos
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro s hs
      have : 0 < s := by linarith [hs.1]
      positivity
  apply ContinuousOn.div continuousOn_const
  · exact continuousOn_id.mul hroot.arccos
  · intro s hs
    have ha : 0 < Real.arccos (crossingCos κ s) :=
      Real.arccos_pos.mpr (full_crossingCos_bounds hk hs).2
    exact ne_of_gt (mul_pos (by linarith [hs.1]) ha)

/-- The source's full candidate coefficient, for one selected descendant. -/
def fullModelCoefficient (κ r : ℝ) : ℝ :=
  (2*Real.pi/Real.log 2) *
    ∫ s in (1/16 : ℝ)..r, 1/(s*Real.arccos (crossingCos κ s))

/-- The certified interior integral is a lower bound for the full model
integral whenever the endpoint contains the certified subinterval. -/
theorem selected_coefficient_le_full {κ r : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hr : r ∈ Icc (33/500) (1/8)) :
    selectedCoefficient κ ≤ fullModelCoefficient κ r := by
  have hab : (1/16 : ℝ) ≤ r := by linarith [hr.1]
  have hc : ContinuousOn (fun s => 1/(s*Real.arccos (crossingCos κ s)))
      (Icc (1/16) r) :=
    (full_integrand_continuousOn hk).mono
      (fun _ hs => ⟨hs.1, hs.2.trans hr.2⟩)
  have hi : IntervalIntegrable
      (fun s => 1/(s*Real.arccos (crossingCos κ s))) volume (1/16) r :=
    ContinuousOn.intervalIntegrable_of_Icc hab hc
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (1/16 : ℝ) r)]
      (fun s => 1/(s*Real.arccos (crossingCos κ s))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Icc (1/16 : ℝ) (1/8) := ⟨hs.1.le, hs.2.trans hr.2⟩
    have ha : 0 < Real.arccos (crossingCos κ s) :=
      Real.arccos_pos.mpr (full_crossingCos_bounds hk hs').2
    have hs0 : 0 < s := by linarith [hs.1]
    positivity
  have hm := intervalIntegral.integral_mono_interval
    (by norm_num : (1/16 : ℝ) ≤ 63/1000)
    (by norm_num : (63/1000 : ℝ) ≤ 33/500) hr.1 hn hi
  have hp : 0 ≤ 2*Real.pi/Real.log 2 := by
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  exact mul_le_mul_of_nonneg_left hm hp

/-- The unique terminal endpoint yields the positive full model integral
and the complete third-image radial gate, with no guessed endpoint. -/
theorem exists_positive_full_model_coefficient :
    ∃ κ r : ℝ, κ ∈ Icc (17903/10000) (17904/10000) ∧
      LoopsLimitingCrestParameter.relation κ = 0 ∧
      r ∈ Ioo (663/10000) (133/2000) ∧
      crestTerminal κ r = -1 ∧
      (1/4 : ℝ) < fullModelCoefficient κ r ∧
      (∀ s ∈ Icc (1/16 : ℝ) (1/8),
        crestTerminal κ s = -1 ↔ s = r) ∧
      (∀ s ∈ Icc (1/16 : ℝ) (1/8),
        (-1 < crestTerminal κ s ∧
          crestTerminal κ s < -(realMap κ)^[4] 0) ↔ s < r) := by
  obtain ⟨κ, hk, _⟩ := LoopsLimitingCrestParameter.exists_unique_limiting_parameter
  obtain ⟨r, hr, he, hu, hg⟩ := unique_model_endpoint hk.1
  have hr' : r ∈ Icc (33/500 : ℝ) (1/8) := by
    constructor <;> linarith [hr.1, hr.2]
  have hpos := (selectedCoefficient_gt_quarter hk.1).trans_le
    (selected_coefficient_le_full hk.1 hr')
  refine ⟨κ, r, hk.1, hk.2, hr, he, hpos, hu, ?_⟩
  intro s hs
  constructor
  · intro h
    exact (hg s hs).mp h.1
  · intro h
    exact ⟨(hg s hs).mpr h, crestTerminal_upper_gate hk.1 hs⟩

end
end LimitingCrest
