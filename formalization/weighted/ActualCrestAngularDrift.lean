import ActualCrestQuarticCrossing
import CrestEndpointQuantitative
import CrestIntegralLimit

/-!
# Ordered actual crest angles

The signed quartic perturbation places the limiting crossing strictly on
the negative side of the actual crossing equation.  The established
strict angular ordering therefore compares the very same selected actual
and limiting branches at every radius of the full parent interval.
-/

namespace ActualCrestAngularDrift

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter GlobalCrestCrossing QuadraticCrestCrossing
open ActualCrestQuarticCrossing CrestEndpointQuantitative CrestIntegralLimit

noncomputable section

/-- The cosine of the actual selected crossing is strictly larger than
the limiting cosine, throughout the full circular parent. -/
theorem actual_crossing_cos_gt {p : ℕ} (hp : 100 ≤ p) {c k₀ s : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) :
    crossingCos k₀ s < realAngle F s := by
  let ss : GlobalCrestCrossing.Radius := ⟨s,hs⟩
  have hm := radial_model_realization hk₀ hs
  have hz : ‖radialPoint k₀ s‖ ≤ 3/2 :=
    (model_point_norm_le hk₀ hs).trans (by norm_num)
  have hzero : (complexMap k₀ (radialPoint k₀ s)).re = 0 := by
    rw [hm.2.2.1]
    simp
  have hnegative := actual_return_negative_at_model_crossing hp hc hk₀ hroot hz hzero
  rw [GlobalCrestCrossing.radialPoint_eq_circlePoint hk₀ hs] at hnegative
  have hu := (GlobalCrestCrossing.crossingCos_spec hk₀ hs).1
  have hv := F.angle_mem ss
  rw [realAngle,radiusProjection_eq hs]
  change crossingCos k₀ s < F.angle ss
  by_contra h
  have hle : F.angle ss ≤ crossingCos k₀ s := le_of_not_gt h
  have hg := GlobalCrestCrossing.actual_crossing_growth (by omega : 17 ≤ p) hc hs
    (show F.angle ss ∈ Icc (-1/10 : ℝ) (1/10) from ⟨hv.1.le,hv.2.le⟩)
    (show crossingCos k₀ s ∈ Icc (-1/10 : ℝ) (1/10) from ⟨hu.1.le,hu.2.le⟩) hle
  rw [F.crossing ss] at hg
  linarith only [hg,hnegative,hle]

/-- The actual positive angular height is smaller than the limiting
height; this is the height entering the all-density modulus formula. -/
theorem actual_arccos_lt {p : ℕ} (hp : 100 ≤ p) {c k₀ s : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) :
    Real.arccos (realAngle F s) < Real.arccos (crossingCos k₀ s) := by
  have hcos := actual_crossing_cos_gt hp hc hk₀ hroot F hs
  have hm := (GlobalCrestCrossing.crossingCos_spec hk₀ hs).1
  have ha : realAngle F s ∈ Ioo (-1/10 : ℝ) (1/10) :=
    F.angle_mem (radiusProjection s)
  exact Real.arccos_lt_arccos (by linarith [hm.1]) hcos (by linarith [ha.2])

/-- At each common radius, the exact actual radial modulus density is
strictly larger than its limiting value. -/
theorem actual_radialIntegrand_gt {p : ℕ} (hp : 100 ≤ p) {c k₀ s : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) :
    radialIntegrand (crossingCos k₀) s < radialIntegrand (realAngle F) s := by
  have hangle := actual_arccos_lt hp hc hk₀ hroot F hs
  have ha : realAngle F s ∈ Ioo (-1/10 : ℝ) (1/10) :=
    F.angle_mem (radiusProjection s)
  have hpos : 0 < Real.arccos (realAngle F s) :=
    Real.arccos_pos.mpr (by linarith [ha.2])
  have hs0 : 0 < s := by linarith [hs.1]
  have hpactual := mul_pos hs0 hpos
  have hprod := mul_lt_mul_of_pos_left hangle hs0
  unfold radialIntegrand
  apply (div_lt_div_iff₀ (hpactual.trans hprod) hpactual).mpr
  simpa only [one_mul] using hprod

end
end ActualCrestAngularDrift
