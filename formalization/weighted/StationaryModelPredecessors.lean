import StationaryUniqueBranch

/-!
# Complete one-step predecessor fibers and actual lifted sheets

The unique coincident-pair theorem removes the earlier extra premise
that a selected model point distinguish its opposite physical roots.
-/

namespace LoopsStationaryModelPredecessors

open Set Function
open LoopsStationaryFiberDynamics LoopsStationaryLightModel
open LoopsStationaryUniqueBranch

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- A surjective map whose predecessor pairs are the orbits of a
unique-fixed-point symmetry has one singleton target fiber and all
other target fibers have exactly two elements. -/
theorem unique_fixed_pair_predecessor_census
    (G S : Y → Y) (b : Y) (hsurj : Surjective G)
    (hpair : ∀ y : Y, G ⁻¹' {G y} = {y, S y})
    (hfix : ∀ y : Y, S y = y ↔ y = b) (w : Y) :
    ∃ A : Finset Y, (∀ y : Y, y ∈ A ↔ G y = w) ∧
      A.card = if w = G b then 1 else 2 := by
  classical
  by_cases hw : w = G b
  · have hb : S b = b := (hfix b).mpr rfl
    refine ⟨{b}, ?_, ?_⟩
    · intro y
      rw [Finset.mem_singleton]
      rw [hw]
      change y ∈ ({b} : Set Y) ↔ y ∈ G ⁻¹' {G b}
      rw [hpair b, hb]
      simp
    · simp [hw]
  · obtain ⟨y, hy⟩ := hsurj w
    have hne : S y ≠ y := by
      intro he
      have hyb : y = b := (hfix y).mp he
      exact hw (hy.symm.trans (congrArg G hyb))
    refine ⟨{y, S y}, ?_, ?_⟩
    · intro z
      rw [Finset.mem_insert, Finset.mem_singleton]
      rw [← hy]
      change z ∈ ({y, S y} : Set Y) ↔ z ∈ G ⁻¹' {G y}
      rw [hpair y]
    · simp [hw, hne, Ne.symm hne]

/-- Exact one-step model degree, at every target, without any singleton
geometric target-fiber hypothesis. -/
theorem quadratic_model_predecessor_census
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅) (w : Y) :
    ∃ A : Finset Y, (∀ y : Y, y ∈ A ↔ G y = w) ∧
      A.card = if w = G (p crit) then 1 else 2 := by
  obtain ⟨S, _, _, _, _, hpair, hfix⟩ :=
    quadratic_filled_unique_model_involution c p G hp hsurj hs hf hlight crit hcrit hKi
  have hGsurj : Surjective G := by
    intro y
    obtain ⟨a, ha⟩ := hsurj y
    obtain ⟨x, hx⟩ := LoopsTerminalFiberExclusion.quadratic_filled_map_surjective c a
    exact ⟨p x, (hs x).symm.trans ((congrArg p hx).trans ha)⟩
  exact unique_fixed_pair_predecessor_census G S (p crit) hGsurj hpair hfix w

/-- The unique singleton inverse target is the projected actual critical
value, since semiconjugacy gives G(p(0)) = p(c). -/
theorem quadratic_model_critical_value_preimage
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅) :
    G ⁻¹' {G (p crit)} = {p crit} := by
  obtain ⟨S, _, _, _, _, hpair, hfix⟩ :=
    quadratic_filled_unique_model_involution c p G hp hsurj hs hf hlight crit hcrit hKi
  exact (involution_singleton_fiber_iff G S hpair (p crit)).mpr
    ((hfix (p crit)).mpr rfl)

/-- Every noncritical geometric fiber maps bijectively to its entire
successor fiber under the actual physical quadratic map. -/
theorem quadratic_noncritical_geometric_fiber_bijOn
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅) (y : Y) (hy : y ≠ p crit) :
    BijOn (quadraticFilledMap c) (p ⁻¹' {y}) (p ⁻¹' {G y}) := by
  have himage := quadratic_filled_light_fiber_image c p G hp hsurj hs hf hlight
  refine ⟨?_, quadratic_noncritical_geometric_fiber_injective
    c p hp hf crit hcrit hKi y hy, ?_⟩
  · intro x hx
    change p (quadraticFilledMap c x) = G y
    change p x = y at hx
    rw [hs x, hx]
  · intro z hz
    rw [← himage y] at hz
    exact hz

/-- Every target other than the projected critical value has two open
model sheets with disjoint exact full physical lifts. The whole target
neighborhood avoids the critical value; no sign-distinguishing premise
on selected physical representatives is left over. -/
theorem quadratic_model_two_sheets_off_critical_value
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅)
    (w : Y) (hw : w ≠ G (p crit)) :
    ∃ U V W : Set Y, IsOpen U ∧ IsOpen V ∧ IsOpen W ∧
      w ∈ W ∧ G (p crit) ∉ W ∧ Disjoint U V ∧
      G ⁻¹' W = U ∪ V ∧ BijOn G U W ∧ BijOn G V W ∧
      Disjoint (p ⁻¹' U) (p ⁻¹' V) ∧
      quadraticFilledMap c ⁻¹' (p ⁻¹' W) = p ⁻¹' U ∪ p ⁻¹' V ∧
      BijOn (quadraticFilledMap c) (p ⁻¹' U) (p ⁻¹' W) ∧
      BijOn (quadraticFilledMap c) (p ⁻¹' V) (p ⁻¹' W) := by
  obtain ⟨a, ha⟩ := hsurj w
  obtain ⟨x, hx⟩ := LoopsTerminalFiberExclusion.quadratic_filled_map_surjective c a
  have hxw : G (p x) = w := (hs x).symm.trans ((congrArg p hx).trans ha)
  have hxne : p x ≠ p crit := by
    intro h
    exact hw (hxw.symm.trans (congrArg G h))
  let z : quadraticFilled c :=
    ⟨-(x : ℂ), (LoopsTerminalFiberExclusion.quadratic_filled_neg_mem c (x : ℂ)).mpr
      x.property⟩
  have hz : (z : ℂ) = -(x : ℂ) := rfl
  have hne : p z ≠ p x := by
    intro h
    exact hxne (quadratic_collapsed_reflection_is_critical c p hp hf crit hcrit hKi x z hz h)
  obtain ⟨U, V, W, hU, hV, hW, _, _, hyW, hUV, hpre, hGU, hGV,
    hdis, hphys, hFU, hFV⟩ :=
    quadratic_filled_light_lifted_two_sheets c p G hp hsurj hs hf hlight x z hz hne
  have hsingle := quadratic_model_critical_value_preimage c p G hp hsurj hs hf
    hlight crit hcrit hKi
  have havoid : G (p crit) ∉ W := by
    intro hbW
    obtain ⟨u, hu, heu⟩ := hGU.surjOn hbW
    obtain ⟨v, hv, hev⟩ := hGV.surjOn hbW
    have hucrit : u = p crit := by
      have hu' : u ∈ G ⁻¹' {G (p crit)} := heu
      rw [hsingle] at hu'
      exact hu'
    have hvcrit : v = p crit := by
      have hv' : v ∈ G ⁻¹' {G (p crit)} := hev
      rw [hsingle] at hv'
      exact hv'
    subst u
    subst v
    exact (Set.disjoint_left.mp hUV) hu hv
  rw [hxw] at hyW
  exact ⟨U, V, W, hU, hV, hW, hyW, havoid, hUV, hpre, hGU, hGV,
    hdis, hphys, hFU, hFV⟩

end LoopsStationaryModelPredecessors
