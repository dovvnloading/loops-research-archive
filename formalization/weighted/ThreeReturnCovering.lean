import ThreeReturnDegree
import ThreeReturnDomain
import Mathlib.Topology.Homotopy.Lifting

/-!
# The actual two-sheet covering outside the critical value

The exact signed collision theorem constructs local inverse sheets in
open half-planes.  Properness then produces evenly covered neighborhoods,
and the actual fiber census identifies their sheet set with `Fin 2`.
The final theorem applies this construction to the canonical component
of the complete actual three-return polynomial pullback.
-/

namespace ThreeReturnCovering

open Set Function Filter Metric
open ComplexConjugate
open scoped Topology
open LimitingCrestQuadraticReturn NearTwoTip
open ThreeReturnDegree ThreeReturnEstimates ThreeReturnDomain

noncomputable section

/-- Exact signed collisions give local inverse sheets outside the
critical fiber.  The sheets lie in literal open half-planes. -/
theorem signed_restriction_local_homeomorph (H : ℂ → ℂ) (W V : Set ℂ)
    (hW : IsOpen W) (hV : IsOpen V) (hm : MapsTo H W V)
    (hH : Continuous H) (ho : IsOpenMap H)
    (hcollision : ∀ {z w : ℂ}, z ∈ W → w ∈ W →
      (H z = H w ↔ z = w ∨ z = -w)) :
    IsLocalHomeomorphOn (MapsTo.restrict H W V hm)
      ((MapsTo.restrict H W V hm) ⁻¹' {v : V | (v : ℂ) ≠ H 0}) := by
  let F := MapsTo.restrict H W V hm
  have hF : Continuous F := (hH.comp continuous_subtype_val).subtype_mk _
  have hFo : IsOpenMap F :=
    hV.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr (ho.restrict hW)
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro z hz
  have hz0 : (z : ℂ) ≠ 0 := by
    intro he
    change H z ≠ H 0 at hz
    exact hz (congrArg H he)
  let U : Set W := {u | 0 < ((u : ℂ) * conj (z : ℂ)).re}
  have hU : IsOpen U := isOpen_lt continuous_const
    (Complex.continuous_re.comp (continuous_subtype_val.mul continuous_const))
  have hzU : z ∈ U := by
    change 0 < ((z : ℂ) * conj (z : ℂ)).re
    simpa only [Complex.mul_conj, Complex.ofReal_re] using
      (Complex.normSq_pos.mpr hz0)
  refine ⟨U, hU.mem_nhds hzU, ?_⟩
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hF.comp continuous_subtype_val
  · intro a b hab
    have he : H (a : W) = H (b : W) := congrArg Subtype.val hab
    rcases (hcollision a.val.property b.val.property).mp he with he | he
    · exact Subtype.ext (Subtype.ext he)
    · have ha := a.property
      have hb := b.property
      change 0 < (((a : W) : ℂ) * conj (z : ℂ)).re at ha
      change 0 < (((b : W) : ℂ) * conj (z : ℂ)).re at hb
      rw [he, neg_mul, Complex.neg_re] at ha
      linarith
  · exact hFo.restrict hU

private theorem signed_restriction_fiber_finite (H : ℂ → ℂ) (W V : Set ℂ)
    (hm : MapsTo H W V)
    (hcollision : ∀ {z w : ℂ}, z ∈ W → w ∈ W →
      (H z = H w ↔ z = w ∨ z = -w))
    (hsym : ∀ z ∈ W, -z ∈ W) (honto : SurjOn H W V) (v : V) :
    ((MapsTo.restrict H W V hm) ⁻¹' {v}).Finite := by
  obtain ⟨z, hz, hzv⟩ := honto v.property
  have hfiber : {w : ℂ | w ∈ W ∧ H w = (v : ℂ)} = {z, -z} := by
    rw [← hzv]
    exact symmetric_fiber_pair H W hcollision hsym hz
  have hfinite : (((↑) : W → ℂ) ⁻¹' ({z, -z} : Set ℂ)).Finite :=
    (Set.Finite.insert z (finite_singleton (-z))).preimage Subtype.val_injective.injOn
  apply hfinite.subset
  intro w hw
  have hw' : (w : ℂ) ∈ {u : ℂ | u ∈ W ∧ H u = (v : ℂ)} :=
    ⟨w.property, congrArg Subtype.val hw⟩
  change (w : ℂ) ∈ ({z, -z} : Set ℂ)
  simpa only [hfiber] using hw'

/-- A proper open restriction with the exact signed fibers is a genuine
two-sheet covering after deleting the unique critical value. -/
theorem signed_two_sheet_cover (H : ℂ → ℂ) (W V : Set ℂ)
    (hW : IsOpen W) (hV : IsOpen V) (hm : MapsTo H W V)
    (hH : Continuous H) (ho : IsOpenMap H)
    (hp : IsProperMap (MapsTo.restrict H W V hm))
    (hcollision : ∀ {z w : ℂ}, z ∈ W → w ∈ W →
      (H z = H w ↔ z = w ∨ z = -w))
    (hsym : ∀ z ∈ W, -z ∈ W) (honto : SurjOn H W V) :
    IsCoveringMapOn (MapsTo.restrict H W V hm)
        {v : V | (v : ℂ) ≠ H 0} ∧
      (∀ v : V, (v : ℂ) ≠ H 0 →
        IsEvenlyCovered (MapsTo.restrict H W V hm) v (Fin 2)) ∧
      IsCoveringMap
        ({v : V | (v : ℂ) ≠ H 0}.restrictPreimage (MapsTo.restrict H W V hm)) := by
  let F := MapsTo.restrict H W V hm
  let S : Set V := {v | (v : ℂ) ≠ H 0}
  have hcover : IsCoveringMapOn F S :=
    hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun v _ => signed_restriction_fiber_finite H W V hm hcollision hsym honto v)
      (signed_restriction_local_homeomorph H W V hW hV hm hH ho hcollision)
  refine ⟨hcover, ?_, hcover.isCoveringMap_restrictPreimage⟩
  intro v hv
  have heven := hcover v hv
  have hfinite := signed_restriction_fiber_finite H W V hm hcollision hsym honto v
  letI : Finite (F ⁻¹' {v}) := hfinite
  letI : DiscreteTopology (F ⁻¹' {v}) := heven.discreteTopology_fiber
  obtain ⟨z, hz, _, hsign, hfiber⟩ :=
    noncritical_fiber_pair H W V hcollision hsym honto v.property hv
  have hzv : H z = (v : ℂ) := by
    have h : z ∈ {w : ℂ | w ∈ W ∧ H w = (v : ℂ)} := by
      rw [hfiber]
      simp
    exact h.2
  have hnzv : H (-z) = (v : ℂ) := by
    have h : -z ∈ {w : ℂ | w ∈ W ∧ H w = (v : ℂ)} := by
      rw [hfiber]
      simp
    exact h.2
  let Z : F ⁻¹' {v} := ⟨⟨z, hz⟩, Subtype.ext hzv⟩
  let N : F ⁻¹' {v} := ⟨⟨-z, hsym z hz⟩, Subtype.ext hnzv⟩
  have hcard : Nat.card (F ⁻¹' {v}) = 2 := by
    apply Nat.card_eq_two_iff.mpr
    refine ⟨Z, N, ?_, ?_⟩
    · intro he
      exact hsign (congrArg (fun q : F ⁻¹' {v} => ((q : W) : ℂ)) he)
    · apply Set.eq_univ_of_forall
      intro q
      have hq : ((q : W) : ℂ) ∈ {w : ℂ | w ∈ W ∧ H w = (v : ℂ)} :=
        ⟨q.val.property, congrArg Subtype.val q.property⟩
      rw [hfiber] at hq
      rcases hq with hq | hq
      · exact Or.inl (Subtype.ext (Subtype.ext hq))
      · exact Or.inr (Subtype.ext (Subtype.ext hq))
  exact heven.of_fiber_homeomorph
    (Finite.equivFinOfCardEq hcard).toHomeomorphOfDiscrete

/-- The complete canonical actual three-return component is proper,
and its punctured return is evenly covered by exactly two sheets. -/
theorem actual_two_sheet_cover {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ∃ hm : MapsTo (threeReturn c p) (source c p) (ball 0 (1/6)),
      IsProperMap (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm) ∧
      IsCoveringMapOn
        (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm)
        {v : ball (0 : ℂ) (1/6) | (v : ℂ) ≠ threeReturn c p 0} ∧
      (∀ v : ball (0 : ℂ) (1/6), (v : ℂ) ≠ threeReturn c p 0 →
        IsEvenlyCovered
          (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm) v (Fin 2)) ∧
      IsCoveringMap
        ({v : ball (0 : ℂ) (1/6) | (v : ℂ) ≠ threeReturn c p 0}.restrictPreimage
          (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm)) := by
  have hd : criticalValue c p ≠ 0 := hc.2.1.ne'
  have hproper := threeReturn_proper c p hd
  have hopen := threeReturn_open c p hd
  have hzero : ‖threeReturn c p 0‖ < 1/6 := actual_critical_value_bound hp hc
  have hcl := component_closure_inside_barrier (threeReturn c p) hproper.continuous
    (3/20) (1/6) (by norm_num) hzero (by
      intro z hz
      have h := actual_annular_barrier hp hc (by simpa [innerRadius] using hz.ge)
        (show ‖z‖ ≤ outerRadius by rw [hz]; norm_num [outerRadius])
      change 1/6 + 1/500 < ‖threeReturn c p z‖ at h
      linarith)
  have hnorm : ∀ z ∈ source c p, ‖z‖ ≤ 1/6 := by
    intro z hz
    have h : ‖z‖ < 3/20 := by simpa using hcl.1 (subset_closure hz)
    linarith
  have hW : IsOpen (source c p) :=
    (isOpen_ball.preimage hproper.continuous).connectedComponentIn
  have hm : MapsTo (threeReturn c p) (source c p) (ball 0 (1/6)) :=
    connectedComponentIn_subset _ _
  have hrest : IsProperMap
      (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm) :=
    component_proper (threeReturn c p) hproper (ball 0 (1/6)) 0 isOpen_ball
  have hcollision : ∀ {z w : ℂ}, z ∈ source c p → w ∈ source c p →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w) := by
    intro z w hz hw
    exact actual_three_return_collision_iff hp hc (hnorm z hz) (hnorm w hw)
  have hsym := source_symmetric c p (by omega) hzero
  have honto : SurjOn (threeReturn c p) (source c p) (ball 0 (1/6)) := by
    intro y hy
    exact (source_image c p hd hzero).symm ▸ hy
  exact ⟨hm, hrest, signed_two_sheet_cover (threeReturn c p) (source c p)
    (ball 0 (1/6)) hW isOpen_ball hm hproper.continuous hopen hrest hcollision hsym honto⟩

end

end ThreeReturnCovering
