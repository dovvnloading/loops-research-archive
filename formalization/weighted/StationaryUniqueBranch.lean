import StationaryLightModel
import StationaryCompactContact

/-!
# The unique coincident-pair locus in an actual quadratic geometric model

Empty interior of the actual filled set prevents a compact connected
geometric fiber away from zero from containing both quadratic roots.
Together with the existing descended reflection this identifies its
entire fixed locus. No identification with a named KKL quotient is assumed.
-/

namespace LoopsStationaryUniqueBranch

open Set Function
open LoopsStationaryFiberDynamics LoopsStationaryLightModel
open LoopsStationaryCompactContact

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- Compactness closes the remaining accumulation alternative in the
actual filled-set bypass theorem. -/
theorem quadratic_compact_injective_away_zero
    (c : ℂ) (E : Set ℂ)
    (hKi : interior (quadraticFilled c) = ∅)
    (hEc : IsCompact E) (hE : IsPreconnected E)
    (hEK : E ⊆ quadraticFilled c) (hzero : (0 : ℂ) ∉ E) :
    InjOn (fun z : ℂ => z^2+c) E := by
  by_contra h
  have hz := quadratic_filled_bypass_accumulates_zero c E hKi hE hEK hzero h
  rw [hEc.isClosed.closure_eq] at hz
  exact hzero hz

/-- Every geometric fiber except the fiber containing the physical
critical point carries an injective actual quadratic restriction. -/
theorem quadratic_noncritical_geometric_fiber_injective
    (c : ℂ) (p : quadraticFilled c → Y)
    (hp : Continuous p) (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅)
    (y : Y) (hy : y ≠ p crit) :
    InjOn (quadraticFilledMap c) (p ⁻¹' {y}) := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  let E : Set ℂ := Subtype.val '' (p ⁻¹' {y})
  have hEc : IsCompact E :=
    ((isClosed_singleton.preimage hp).isCompact).image continuous_subtype_val
  have hE : IsPreconnected E :=
    (hf y).image Subtype.val continuous_subtype_val.continuousOn
  have hEK : E ⊆ quadraticFilled c := by
    rintro z ⟨x, _, rfl⟩
    exact x.property
  have hzero : (0 : ℂ) ∉ E := by
    rintro ⟨x, hx, hxzero⟩
    have he : x = crit := Subtype.ext (hxzero.trans hcrit.symm)
    change p x = y at hx
    exact hy (hx.symm.trans (congrArg p he))
  have hinj := quadratic_compact_injective_away_zero c E hKi hEc hE hEK hzero
  intro x hx z hz he
  apply Subtype.ext
  apply hinj ⟨x, hx, rfl⟩ ⟨z, hz, rfl⟩
  exact congrArg (fun w : quadraticFilled c => (w : ℂ)) he

/-- A collapsed pair of opposite physical points must belong to the
critical geometric fiber. This direction needs no model dynamics. -/
theorem quadratic_collapsed_reflection_is_critical
    (c : ℂ) (p : quadraticFilled c → Y)
    (hp : Continuous p) (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅)
    (x z : quadraticFilled c) (hz : (z : ℂ) = -(x : ℂ))
    (he : p z = p x) : p x = p crit := by
  by_contra hn
  have hinj := quadratic_noncritical_geometric_fiber_injective
    c p hp hf crit hcrit hKi (p x) hn
  have hmap : quadraticFilledMap c x = quadraticFilledMap c z := by
    apply Subtype.ext
    change (x : ℂ)^2+c = (z : ℂ)^2+c
    rw [hz]
    ring
  have hxz : x = z := hinj rfl he hmap
  have hxneg : (x : ℂ) = -(x : ℂ) :=
    (congrArg (fun w : quadraticFilled c => (w : ℂ)) hxz).trans hz
  have hxzero : (x : ℂ) = 0 := by linear_combination (1/2 : ℂ) * hxneg
  have hxcrit : x = crit := Subtype.ext (hxzero.trans hcrit.symm)
  exact hn (congrArg p hxcrit)

/-- The descended physical reflection has exactly one fixed model
point. This identifies pair coincidence, not local branch behavior at
an isolated point of a degenerate model. -/
theorem quadratic_descended_reflection_fixed_iff
    (c : ℂ) (p : quadraticFilled c → Y) (S : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅)
    (hS : ∀ x z : quadraticFilled c,
      (z : ℂ) = -(x : ℂ) → S (p x) = p z) (y : Y) :
    S y = y ↔ y = p crit := by
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := hsurj y
    let z : quadraticFilled c :=
      ⟨-(x : ℂ), (LoopsTerminalFiberExclusion.quadratic_filled_neg_mem c (x : ℂ)).mpr
        x.property⟩
    have hz : (z : ℂ) = -(x : ℂ) := rfl
    have he : p z = p x := (hS x z hz).symm.trans hy
    exact quadratic_collapsed_reflection_is_critical c p hp hf crit hcrit hKi x z hz he
  · rintro rfl
    exact hS crit crit (by simp [hcrit])

/-- The genuine filled quadratic induces a model involution whose
fixed locus is exactly the projection of zero. The lightness premise
is the existing route to whole-fiber transport. -/
theorem quadratic_filled_unique_model_involution
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hKi : interior (quadraticFilled c) = ∅) :
    ∃ S : Y → Y, Continuous S ∧ Involutive S ∧ IsOpenMap G ∧
      (∀ x z : quadraticFilled c, (z : ℂ) = -(x : ℂ) → S (p x) = p z) ∧
      (∀ y : Y, G ⁻¹' {G y} = {y, S y}) ∧
      (∀ y : Y, S y = y ↔ y = p crit) := by
  obtain ⟨S, hSc, hSi, hGo, hS, hpair⟩ :=
    quadratic_filled_light_model_involution c p G hp hsurj hs hf hlight
  exact ⟨S, hSc, hSi, hGo, hS, hpair,
    quadratic_descended_reflection_fixed_iff c p S hp hsurj hf crit hcrit hKi hS⟩

end LoopsStationaryUniqueBranch
