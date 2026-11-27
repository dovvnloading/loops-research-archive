import StationaryLightModel
import StationaryCompactContact

/-!
# Critical-fiber recognition in an actual quadratic geometric quotient

The compact bypass theorem identifies the critical geometric fiber from
the actual map. Combined with light model transport, it gives the exact
one-step predecessor census even when geometric fibers are nontrivial.
-/

namespace LoopsStationaryCriticalFiber

open Set Function Classical
open LoopsStationaryFiberDynamics LoopsStationaryLightModel
open LoopsStationaryCompactContact

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- Any compact connected collision witness in an empty-interior
quadratic filled set must contain the actual critical point. -/
theorem compact_quadratic_collision_contains_zero (c : ℂ) (E : Set ℂ)
    (hKi : interior (quadraticFilled c) = ∅)
    (hE : IsCompact E) (hc : IsPreconnected E)
    (hsub : E ⊆ quadraticFilled c)
    (hbad : ¬ InjOn (fun z : ℂ => z^2+c) E) :
    (0 : ℂ) ∈ E := by
  by_contra hz
  have hcl := quadratic_filled_bypass_accumulates_zero c E hKi hc hsub hz hbad
  rw [hE.isClosed.closure_eq] at hcl
  exact hz hcl

/-- The actual quadratic is injective on every geometric fiber other
than the one containing zero. No local connectivity of the physical
filled set or singleton assumption on that fiber is needed. -/
theorem quadratic_filled_noncritical_fiber_injective
    (c : ℂ) (p : quadraticFilled c → Y) (hp : Continuous p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (a : quadraticFilled c) (ha : (a : ℂ) = 0)
    (y : Y) (hy : y ≠ p a) :
    InjOn (quadraticFilledMap c) (p ⁻¹' {y}) := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  let E : Set ℂ := (Subtype.val : quadraticFilled c → ℂ) '' (p ⁻¹' {y})
  have hE : IsCompact E :=
    (isClosed_singleton.preimage hp).isCompact.image continuous_subtype_val
  have hc : IsPreconnected E :=
    (hf y).image _ continuous_subtype_val.continuousOn
  have hsub : E ⊆ quadraticFilled c := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hzero : (0 : ℂ) ∉ E := by
    rintro ⟨z, hz, hze⟩
    have hza : z = a := Subtype.ext (hze.trans ha.symm)
    change p z = y at hz
    exact hy (hz.symm.trans (congrArg p hza))
  have hinj : InjOn (fun z : ℂ => z^2+c) E := by
    by_contra hbad
    exact hzero (compact_quadratic_collision_contains_zero c E hKi hE hc hsub hbad)
  intro x hx z hz h
  apply Subtype.ext
  apply hinj ⟨x, hx, rfl⟩ ⟨z, hz, rfl⟩
  exact congrArg (fun w : quadraticFilled c => (w : ℂ)) h

/-- In a light monotone geometric quotient, opposite physical roots
are identified precisely on the fiber containing the actual critical
point. This supplies the missing converse to critical-value uniqueness. -/
theorem quadratic_filled_identified_opposites_iff
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (a : quadraticFilled c) (ha : (a : ℂ) = 0)
    (x z : quadraticFilled c) (hz : (z : ℂ) = -(x : ℂ)) :
    p z = p x ↔ p x = p a := by
  have hF : quadraticFilledMap c z = quadraticFilledMap c x := by
    apply Subtype.ext
    change (z : ℂ)^2+c = (x : ℂ)^2+c
    rw [hz]
    ring
  constructor
  · intro hpx
    by_contra hn
    have hinj := quadratic_filled_noncritical_fiber_injective
      c p hp hf hKi a ha (p x) hn
    have he : x = z := hinj rfl hpx hF.symm
    have hx0 : (x : ℂ) = 0 := by
      have h := congrArg (fun w : quadraticFilled c => (w : ℂ)) he
      rw [hz] at h
      linear_combination (1/2 : ℂ) * h
    exact hn (congrArg p (Subtype.ext (hx0.trans ha.symm)))
  · intro hpx
    have himage := quadratic_filled_light_fiber_image c p G hp hsurj hs hf hlight
    have hcrit := quadratic_model_critical_preimage c (quadraticFilled c)
      (quadraticFilledMap c) (fun _ => rfl) p G hs himage a ha
    have hG : G (p z) = p (quadraticFilledMap c a) := by
      calc
        G (p z) = p (quadraticFilledMap c z) := (hs z).symm
        _ = p (quadraticFilledMap c x) := congrArg p hF
        _ = G (p x) := hs x
        _ = G (p a) := congrArg G hpx
        _ = p (quadraticFilledMap c a) := (hs a).symm
    have hzpre : p z ∈ G ⁻¹' ({p (quadraticFilledMap c a)} : Set Y) := hG
    rw [hcrit] at hzpre
    exact (show p z = p a from hzpre).trans hpx.symm

/-- The descended reflection has exactly one fixed point, the image
of zero, while retaining its continuous involution and full-fiber
pair identities. All geometric fibers may be nonsingletons. -/
theorem quadratic_filled_model_unique_critical_involution
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (a : quadraticFilled c) (ha : (a : ℂ) = 0) :
    ∃ S : Y → Y, Continuous S ∧ Involutive S ∧ IsOpenMap G ∧
      (∀ x z : quadraticFilled c, (z : ℂ) = -(x : ℂ) → S (p x) = p z) ∧
      (∀ y : Y, G ⁻¹' {G y} = {y, S y}) ∧
      (∀ y : Y, S y = y ↔ y = p a) := by
  obtain ⟨S, hSc, hSi, ho, hS, hpair⟩ :=
    quadratic_filled_light_model_involution c p G hp hsurj hs hf hlight
  refine ⟨S, hSc, hSi, ho, hS, hpair, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have himage := quadratic_filled_light_fiber_image c p G hp hsurj hs hf hlight
  obtain ⟨z, hz, _⟩ := quadratic_filled_model_fiber_pair c p G hs himage x
  rw [hS x z hz]
  exact quadratic_filled_identified_opposites_iff
    c p G hp hsurj hs hf hlight hKi a ha x z hz

omit [TopologicalSpace Y] [T2Space Y] in
/-- Surjectivity descends from the actual completely invariant
quadratic filled set to every surjective semiconjugate model. -/
theorem quadratic_filled_model_surjective
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hsurj : Surjective p) (hs : Semiconj p (quadraticFilledMap c) G) :
    Surjective G := by
  intro y
  obtain ⟨w, hw⟩ := hsurj y
  obtain ⟨z, hz⟩ := LoopsQuadraticCriticalFiberCensus.quadratic_surjective c (w : ℂ)
  change z^2+c = (w : ℂ) at hz
  have hzK : z ∈ quadraticFilled c := by
    apply (quadratic_filled_complete_invariant c z).mp
    rw [hz]
    exact w.property
  let x : quadraticFilled c := ⟨z, hzK⟩
  have hFx : quadraticFilledMap c x = w := Subtype.ext hz
  exact ⟨p x, (hs x).symm.trans ((congrArg p hFx).trans hw)⟩

/-- Every model target has exactly two predecessors, except the
actual critical value, which has exactly one. This includes targets
with nontrivial physical fibers. -/
theorem quadratic_filled_model_predecessor_census
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (a : quadraticFilled c) (ha : (a : ℂ) = 0) (y : Y) :
    (G ⁻¹' {y}).Finite ∧
      (G ⁻¹' {y}).ncard + (if y = G (p a) then 1 else 0) = 2 := by
  classical
  obtain ⟨S, hSc, hSi, ho, hS, hpair, hfixed⟩ :=
    quadratic_filled_model_unique_critical_involution
      c p G hp hsurj hs hf hlight hKi a ha
  obtain ⟨u, rfl⟩ := quadratic_filled_model_surjective c p G hsurj hs y
  rw [hpair u]
  refine ⟨(Set.finite_singleton _).insert _, ?_⟩
  have himage := quadratic_filled_light_fiber_image c p G hp hsurj hs hf hlight
  have hcrit := quadratic_model_critical_preimage c (quadraticFilled c)
    (quadraticFilledMap c) (fun _ => rfl) p G hs himage a ha
  by_cases hu : u = p a
  · subst u
    rw [(hfixed (p a)).mpr rfl]
    simp
  · have hsu : S u ≠ u := fun h => hu ((hfixed u).mp h)
    have hG : G u ≠ G (p a) := by
      intro h
      have hmem : u ∈ G ⁻¹' ({p (quadraticFilledMap c a)} : Set Y) :=
        h.trans (hs a).symm
      rw [hcrit] at hmem
      exact hu hmem
    rw [Set.ncard_pair (Ne.symm hsu), if_neg hG]

end LoopsStationaryCriticalFiber
