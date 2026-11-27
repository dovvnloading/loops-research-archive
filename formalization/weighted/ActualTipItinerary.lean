import NearTwoTip

/-!
# Retaining the actual positive inverse itinerary

The archived shooting construction already produces this itinerary, but
the `ActualTip` interface forgets it.  Retain the witness at the same
intermediate-value selection so the physical first-return and period
arguments can use the actual constructed parameter.
-/

namespace ActualTipItinerary

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open CriticalReturnRelationStability

noncomputable section

/-- The actual signed-tip construction retains its positive inverse
shooting itinerary; no itinerary is supplied as an extra existence premise. -/
theorem exists_actual_tip_with_itinerary (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧
      shooting (p-2) (criticalValue c p) c = 0 := by
  obtain ⟨a,b,h⟩ := exists_sharp_chart p hp
  let F : ℝ → ℝ := fun c => criticalValue c (6*p)+criticalValue c (3*p)
  have hF : Continuous F :=
    (continuous_criticalValue (6*p)).add (continuous_criticalValue (3*p))
  have ha : a ∈ Icc a b := left_mem_Icc.mpr h.ordered.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr h.ordered.le
  have hs {c : ℝ} (hc : c ∈ Icc a b) : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using (h.return_range c hc).2
  have hpos : 0 < F a := actual_relation_positive a p hp
    (SharpChart.critical_orbit_bound hp h ha) (h.return_range a ha).1
    (hs ha) h.left_coefficient
  have hneg : F b < 0 := actual_relation_negative b p hp
    (SharpChart.critical_orbit_bound hp h hb) (h.return_range b hb).1
    (hs hb) h.right_coefficient
  obtain ⟨c,hc,hzero⟩ := intermediate_value_Icc' h.ordered.le hF.continuousOn
    (show (0 : ℝ) ∈ Icc (F b) (F a) from ⟨hneg.le,hpos.le⟩)
  refine ⟨c,?_,h.itinerary c hc⟩
  refine ⟨h.parameter_range c hc,(h.return_range c hc).1,
    (h.return_range c hc).2,h.coefficient_range hc,hzero,?_,
    SharpChart.critical_orbit_bound hp h hc⟩
  exact actual_third_return_negative c p hp
    (SharpChart.critical_orbit_bound hp h hc) (h.return_range c hc).1
    (hs hc) (h.coefficient_range hc)

end
end ActualTipItinerary
