import QuadraticPeriodicMotion

/-!
# Exact period and multiplier type along actual quadratic periodic motion

The branch constructed by the complex implicit function theorem retains its
minimal positive period. Its actual spatial multiplier varies analytically,
so an attracting or repelling cycle retains that type locally. The
neighborhood depends on the selected cycle; there is no uniform statement
over all periods or any assertion of global dynamical stability.
-/

namespace LoopsQuadraticTransversality

open Filter
open scoped Topology ContDiff

noncomputable section

/-- The actual return multiplier is jointly analytic in parameter and point. -/
theorem returnMultiplier_contDiff (p : ℕ) :
    ContDiff ℂ ω (fun v : ℂ × ℂ => returnMultiplier v.1 v.2 p) := by
  induction p with
  | zero => exact contDiff_const
  | succ p ih => exact (contDiff_const.mul (returnOrbit_contDiff p)).mul ih

private theorem motion_exact_period (c z : ℂ) (p : ℕ) (hp : 0 < p)
    (hmin : ∀ k : ℕ, 0 < k → k < p → returnOrbit c z k ≠ z)
    (ζ : ℂ → ℂ) (hself : ζ c = z) (hcont : ContinuousAt ζ c)
    (hret : (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ) :
    ∀ᶠ w in 𝓝 c, Function.minimalPeriod (fun u : ℂ => u ^ 2 + w) (ζ w) = p := by
  have hshort : ∀ᶠ w in 𝓝 c, ∀ k : Fin p,
      0 < k.val → returnOrbit w (ζ w) k.val ≠ ζ w := by
    apply Filter.eventually_all.mpr
    intro k
    by_cases hk : 0 < k.val
    · have hc : ContinuousAt (fun w : ℂ => returnOrbit w (ζ w) k.val - ζ w) c :=
        (((returnOrbit_contDiff k.val).continuous.continuousAt).comp
          (continuousAt_id.prodMk hcont)).sub hcont
      have hne : returnOrbit c (ζ c) k.val - ζ c ≠ 0 := by
        rw [hself]
        exact sub_ne_zero.mpr (hmin k.val hk k.isLt)
      filter_upwards [hc.eventually_ne hne] with w hw
      exact fun _ => sub_ne_zero.mp hw
    · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
  filter_upwards [hret, hshort] with w hw hs
  have hperiod : Function.IsPeriodicPt (fun u : ℂ => u ^ 2 + w) p (ζ w) := by
    simpa only [returnOrbit_eq_iterate, Function.IsPeriodicPt, Function.IsFixedPt] using hw
  apply le_antisymm (hperiod.minimalPeriod_le hp)
  by_contra hn
  have hlt : Function.minimalPeriod (fun u : ℂ => u ^ 2 + w) (ζ w) < p :=
    Nat.lt_of_not_ge hn
  apply hs ⟨_, hlt⟩ (hperiod.minimalPeriod_pos hp)
  simpa only [returnOrbit_eq_iterate, Function.IsPeriodicPt, Function.IsFixedPt] using
    Function.isPeriodicPt_minimalPeriod (fun u : ℂ => u ^ 2 + w) (ζ w)

/-- A periodic point whose specified return multiplier differs from one has
an analytic motion retaining its exact minimal period. Along that same
motion the multiplier is analytic, and any strict attracting or repelling
inequality at the base persists locally. -/
theorem periodic_point_exact_period_stability (c z : ℂ) (p : ℕ) (hp : 0 < p)
    (hper : returnOrbit c z p = z)
    (hmin : ∀ k : ℕ, 0 < k → k < p → returnOrbit c z k ≠ z)
    (hmult : returnMultiplier c z p ≠ 1) :
    ∃ ζ : ℂ → ℂ,
      ζ c = z ∧ AnalyticAt ℂ ζ c ∧
      AnalyticAt ℂ (fun w => returnMultiplier w (ζ w) p) c ∧
      ∀ᶠ w in 𝓝 c,
        Function.minimalPeriod (fun u : ℂ => u ^ 2 + w) (ζ w) = p ∧
        (‖returnMultiplier c z p‖ < 1 → ‖returnMultiplier w (ζ w) p‖ < 1) ∧
        (1 < ‖returnMultiplier c z p‖ → 1 < ‖returnMultiplier w (ζ w) p‖) := by
  obtain ⟨ζ, hself, han, hret, _, _⟩ := periodic_point_motion c z p hper hmult
  have hmul : AnalyticAt ℂ (fun w => returnMultiplier w (ζ w) p) c :=
    ((returnMultiplier_contDiff p).contDiffAt.analyticAt).comp
      (analyticAt_id.prod han)
  have hnorm : Tendsto (fun w => ‖returnMultiplier w (ζ w) p‖) (𝓝 c)
      (𝓝 ‖returnMultiplier c z p‖) := by
    simpa only [hself] using hmul.continuousAt.norm.tendsto
  have hattr : ∀ᶠ w in 𝓝 c,
      ‖returnMultiplier c z p‖ < 1 → ‖returnMultiplier w (ζ w) p‖ < 1 := by
    by_cases h : ‖returnMultiplier c z p‖ < 1
    · exact (hnorm.eventually_lt_const h).mono fun _ hw _ => hw
    · exact Filter.Eventually.of_forall fun _ hw => (h hw).elim
  have hrep : ∀ᶠ w in 𝓝 c,
      1 < ‖returnMultiplier c z p‖ → 1 < ‖returnMultiplier w (ζ w) p‖ := by
    by_cases h : 1 < ‖returnMultiplier c z p‖
    · exact (hnorm.eventually_const_lt h).mono fun _ hw _ => hw
    · exact Filter.Eventually.of_forall fun _ hw => (h hw).elim
  refine ⟨ζ, hself, han, hmul, ?_⟩
  filter_upwards [motion_exact_period c z p hp hmin ζ hself han.continuousAt hret,
    hattr, hrep] with w hw ha hr
  exact ⟨hw, ha, hr⟩

/-- At every algebraic-integer parameter, an exact-period cycle continues
with the same exact period and the same attracting or repelling type.
Arithmetic excludes a neutral base multiplier, and continuity excludes
neutral multipliers throughout a neighborhood of the selected branch. -/
theorem integral_parameter_periodic_point_stability (c z : ℂ)
    (hc : IsIntegral ℤ c) (p : ℕ) (hp : 0 < p)
    (hper : returnOrbit c z p = z)
    (hmin : ∀ k : ℕ, 0 < k → k < p → returnOrbit c z k ≠ z) :
    ∃ ζ : ℂ → ℂ,
      ζ c = z ∧ AnalyticAt ℂ ζ c ∧
      AnalyticAt ℂ (fun w => returnMultiplier w (ζ w) p) c ∧
      ∀ᶠ w in 𝓝 c,
        Function.minimalPeriod (fun u : ℂ => u ^ 2 + w) (ζ w) = p ∧
        (‖returnMultiplier w (ζ w) p‖ < 1 ↔ ‖returnMultiplier c z p‖ < 1) ∧
        (1 < ‖returnMultiplier w (ζ w) p‖ ↔ 1 < ‖returnMultiplier c z p‖) ∧
        ‖returnMultiplier w (ζ w) p‖ ≠ 1 := by
  have hz : IsIntegral ℤ z := integral_of_spatial_collision hc 0 p hp
    (show returnOrbit c z 0 = returnOrbit c z p from hper.symm)
  have hnon : ‖returnMultiplier c z p‖ ≠ 1 := returnMultiplier_not_neutral hc hz p hp
  have hm : returnMultiplier c z p ≠ 1 := by
    intro h
    apply hnon
    rw [h, norm_one]
  obtain ⟨ζ, hself, han, hmul, hstable⟩ :=
    periodic_point_exact_period_stability c z p hp hper hmin hm
  refine ⟨ζ, hself, han, hmul, ?_⟩
  filter_upwards [hstable] with w hw
  rcases lt_or_gt_of_ne hnon with ha | hr
  · have hwa := hw.2.1 ha
    exact ⟨hw.1, iff_of_true hwa ha,
      iff_of_false (not_lt_of_gt hwa) (not_lt_of_gt ha), ne_of_lt hwa⟩
  · have hwr := hw.2.2 hr
    exact ⟨hw.1, iff_of_false (not_lt_of_gt hwr) (not_lt_of_gt hr),
      iff_of_true hwr hr, ne_of_gt hwr⟩

end

end LoopsQuadraticTransversality
