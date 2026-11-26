import StationaryFiberDynamics

/-!
# Light geometric quotient dynamics of the actual quadratic

Compact connected components of an open closed map onto a connected
target already map onto that target. This removes finiteness from
the fiber-transport argument when the model fibers are totally disconnected.
-/

namespace LoopsStationaryLightModel

open Set Function
open LoopsStationaryFiberDynamics LoopsStationaryGeometricFibers

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every connected component of the compact source of an open closed
map onto a preconnected target maps onto the entire target. No local
connectedness or finiteness of the components is necessary. -/
theorem component_image_univ [CompactSpace X] [T2Space X] [T1Space Y]
    [PreconnectedSpace Y] (f : X → Y) (hf : Continuous f)
    (ho : IsOpenMap f) (hc : IsClosedMap f) (x : X) :
    f '' connectedComponent x = univ := by
  classical
  apply Subset.antisymm (subset_univ _)
  intro y _
  by_contra hn
  let A : Set X := f ⁻¹' {y}
  have hA : IsCompact A := (isClosed_singleton.preimage hf).isCompact
  have he : A ∩ connectedComponent x = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hn ⟨z, hz.2, hz.1⟩
  rw [connectedComponent_eq_iInter_isClopen] at he
  obtain ⟨s, hs⟩ := hA.elim_finite_subfamily_closed
    (fun i : {S : Set X // IsClopen S ∧ x ∈ S} => (i : Set X))
    (fun i => i.2.1.isClosed) he
  let U : Set X := ⋂ i ∈ s, (i : Set X)
  have hU : IsClopen U := isClopen_biInter_finset fun i _ => i.2.1
  have hx : x ∈ U := by
    simp only [U, mem_iInter]
    intro i _
    exact i.2.2
  have hIm : IsClopen (f '' U) := ⟨hc _ hU.isClosed, ho _ hU.isOpen⟩
  have hall : (univ : Set Y) ⊆ f '' U :=
    isPreconnected_univ.subset_isClopen hIm
      ⟨f x, mem_univ _, x, hx, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hall (mem_univ y)
  have hz' : z ∈ A ∩ U := ⟨hzy, hz⟩
  rw [show A ∩ U = ∅ from hs] at hz'
  exact hz'

/-- A light model (all model point preimages totally disconnected)
suffices for whole-fiber transport. In particular the model point
preimages are not assumed finite or discrete. -/
theorem fiber_image_eq_of_light_model [CompactSpace X] [T2Space X] [T1Space Y]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hp : Continuous p) (hF : Continuous F) (hsurj : Surjective p)
    (hs : Semiconj p F G) (ho : IsOpenMap F) (hc : IsClosedMap F)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y})) (y : Y) :
    F '' (p ⁻¹' {y}) = p ⁻¹' {G y} := by
  let B : Set X := p ⁻¹' {G y}
  have hB : IsClosed B := isClosed_singleton.preimage hp
  let A : Set X := F ⁻¹' B
  letI : CompactSpace A :=
    isCompact_iff_compactSpace.mp (hB.preimage hF).isCompact
  letI : PreconnectedSpace B :=
    isPreconnected_iff_preconnectedSpace.mp (hf (G y))
  let f : A → B := B.restrictPreimage F
  obtain ⟨a, ha⟩ := hsurj y
  have haA : a ∈ A := by
    change p (F a) = G y
    rw [hs a, ha]
  let a' : A := ⟨a, haA⟩
  have hcomp : f '' connectedComponent a' = univ :=
    component_image_univ f hF.restrictPreimage
      (ho.restrictPreimage B) (hc.restrictPreimage B) a'
  have hpa : Continuous (fun z : A => p (z : X)) :=
    hp.comp continuous_subtype_val
  have hsub : (fun z : A => p (z : X)) '' connectedComponent a' ⊆
      G ⁻¹' {G y} := by
    rintro _ ⟨z, _, rfl⟩
    change G (p (z : X)) = G y
    have hz : p (F (z : X)) = G y := z.property
    rw [← hs (z : X)]
    exact hz
  have hsingle := hlight (G y) _ hsub
    (isPreconnected_connectedComponent.image _ hpa.continuousOn)
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change p z = y at hz
    change p (F z) = G y
    rw [hs z, hz]
  · intro w hw
    let w' : B := ⟨w, hw⟩
    have hw' : w' ∈ f '' connectedComponent a' := by
      rw [hcomp]
      exact mem_univ _
    obtain ⟨z, hz, hzw⟩ := hw'
    have hzy : p (z : X) = y := by
      calc
        p (z : X) = p a := hsingle ⟨z, hz, rfl⟩
          ⟨a', mem_connectedComponent, rfl⟩
        _ = y := ha
    exact ⟨(z : X), hzy, congrArg (fun v : B => (v : X)) hzw⟩

/-- The actual bounded-orbit filled set needs no assumed physical
compactness or backward invariance to apply the light-model theorem. -/
theorem quadratic_filled_light_fiber_image [T1Space Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y})) (y : Y) :
    quadraticFilledMap c '' (p ⁻¹' {y}) = p ⁻¹' {G y} := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  have hcont : Continuous (quadraticFilledMap c) := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val : Continuous
      (Subtype.val : quadraticFilled c → ℂ)).pow 2).add continuous_const
  exact fiber_image_eq_of_light_model p (quadraticFilledMap c) G hp hcont
    hsurj hs (quadratic_restriction_open c (quadraticFilled c)
      (quadraticFilledMap c) (fun _ => rfl)
      (fun z hz => (quadratic_filled_complete_invariant c z).mp hz))
    hcont.isClosedMap hf hlight y

/-- Exact model predecessor fiber for the genuine quadratic: it
consists of the images of the two opposite physical roots, possibly
coinciding. The proof uses whole-fiber transport, not a postulated
model degree bound. -/
theorem quadratic_filled_model_fiber_pair
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (himage : ∀ y : Y, quadraticFilledMap c '' (p ⁻¹' {y}) = p ⁻¹' {G y})
    (x : quadraticFilled c) :
    ∃ z : quadraticFilled c, (z : ℂ) = -(x : ℂ) ∧
      G ⁻¹' {G (p x)} = {p x, p z} := by
  have hzK : -(x : ℂ) ∈ quadraticFilled c := by
    apply (quadratic_filled_complete_invariant c (-(x : ℂ))).mp
    have he : (-(x : ℂ))^2+c = (x : ℂ)^2+c := by ring
    rw [he]
    exact (quadraticFilledMap c x).property
  let z : quadraticFilled c := ⟨-(x : ℂ), hzK⟩
  have hFz : quadraticFilledMap c z = quadraticFilledMap c x := by
    apply Subtype.ext
    change (-(x : ℂ))^2+c = (x : ℂ)^2+c
    ring
  refine ⟨z, rfl, ?_⟩
  ext y
  constructor
  · intro hy
    change G y = G (p x) at hy
    have hw : quadraticFilledMap c x ∈ p ⁻¹' {G y} := by
      change p (quadraticFilledMap c x) = G y
      rw [hs x, hy]
    rw [← himage y] at hw
    obtain ⟨u, hu, hux⟩ := hw
    change p u = y at hu
    have hv := congrArg (fun v : quadraticFilled c => (v : ℂ)) hux
    change (u : ℂ)^2+c = (x : ℂ)^2+c at hv
    have hm : ((u : ℂ)-(x : ℂ))*((u : ℂ)+(x : ℂ)) = 0 := by
      calc
        _ = ((u : ℂ)^2+c)-((x : ℂ)^2+c) := by ring
        _ = 0 := by rw [hv, sub_self]
    rw [mem_insert_iff, mem_singleton_iff]
    rcases mul_eq_zero.mp hm with h | h
    · have he : u = x := Subtype.ext (sub_eq_zero.mp h)
      exact Or.inl (hu.symm.trans (congrArg p he))
    · have he : u = z := by
        apply Subtype.ext
        change (u : ℂ) = -(x : ℂ)
        linear_combination h
      exact Or.inr (hu.symm.trans (congrArg p he))
  · intro hy
    rw [mem_insert_iff, mem_singleton_iff] at hy
    change G y = G (p x)
    rcases hy with rfl | rfl
    · rfl
    · rw [← hs z, hFz, hs x]

/-- Lightness forces finiteness of every model point fiber of the
actual quadratic. The preceding theorem supplies the sharper exact
pair whenever the fiber is nonempty. -/
theorem quadratic_filled_light_model_finite [T1Space Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y})) (y : Y) :
    (G ⁻¹' {y}).Finite := by
  classical
  by_cases hy : ∃ v : Y, G v = y
  · obtain ⟨v, rfl⟩ := hy
    obtain ⟨x, rfl⟩ := hsurj v
    obtain ⟨z, _, hz⟩ := quadratic_filled_model_fiber_pair c p G hs
      (quadratic_filled_light_fiber_image c p G hp hsurj hs hf hlight) x
    rw [hz]
    exact (finite_singleton (p z)).insert (p x)
  · have he : (G ⁻¹' {y} : Set Y) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact hy ⟨v, hv⟩
    rw [he]
    exact finite_empty

end LoopsStationaryLightModel
