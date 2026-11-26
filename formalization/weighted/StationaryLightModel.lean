import StationaryFiberDynamics
import QuadraticCriticalFiberCensus

/-!
# Light geometric quotient dynamics of the actual quadratic

Compact connected components of an open closed map onto a connected
target already map onto that target. This removes finiteness from
the fiber-transport argument when the model fibers are totally disconnected.
-/

namespace LoopsStationaryLightModel

open Set Function
open LoopsStationaryFiberDynamics LoopsStationaryGeometricFibers
open LoopsQuadraticCriticalFiberCensus

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


/-- Whole-fiber transport is exactly the missing saturation in the
proof that openness descends to a geometric quotient. -/
theorem model_open_of_fiber_transport [CompactSpace X] [T2Space Y]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p) (hs : Semiconj p F G)
    (ho : IsOpenMap F)
    (himage : ∀ y : Y, F '' (p ⁻¹' {y}) = p ⁻¹' {G y}) :
    IsOpenMap G := by
  intro U hU
  have he : p ⁻¹' (G '' U) = F '' (p ⁻¹' U) := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, hyz⟩ := hz
      have hz' : z ∈ p ⁻¹' {G y} := hyz.symm
      rw [← himage y] at hz'
      obtain ⟨x, hx, hxz⟩ := hz'
      change p x = y at hx
      refine ⟨x, ?_, hxz⟩
      change p x ∈ U
      rwa [hx]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨p x, hx, (hs x).symm⟩
  have hq := Topology.IsQuotientMap.of_surjective_continuous hsurj hp
  apply hq.isCoinducing.isOpen_preimage.mp
  rw [he]
  exact ho _ (hU.preimage hp)

/-- A degree-two physical map and an open model map cannot have
three different model predecessors if targets with singleton physical
fibers are dense. The model is not assumed finite-to-one. -/
theorem three_predecessors_collide_of_dense_singleton_targets [T2Space Y]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hsurj : Surjective p) (hs : Semiconj p F G) (ho : IsOpenMap G)
    (hdegree : ∀ x u v : X, F x = F u → F x = F v →
      x = u ∨ x = v ∨ u = v)
    (hdense : Dense {y : Y | (p ⁻¹' ({y} : Set Y)).Subsingleton})
    (a b d : Y) (hab : G a = G b) (had : G a = G d) :
    a = b ∨ a = d ∨ b = d := by
  classical
  by_contra hn
  have hneab : a ≠ b := fun h => hn (Or.inl h)
  have hnead : a ≠ d := fun h => hn (Or.inr (Or.inl h))
  have hnebd : b ≠ d := fun h => hn (Or.inr (Or.inr h))
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hneab
  obtain ⟨U', W, hU', hW, haU', hdW, hUW⟩ := t2_separation hnead
  obtain ⟨V', W', hV', hW', hbV', hdW', hVW⟩ := t2_separation hnebd
  let A := U ∩ U'
  let B := V ∩ V'
  let D := W ∩ W'
  have hA : IsOpen A := hU.inter hU'
  have hB : IsOpen B := hV.inter hV'
  have hD : IsOpen D := hW.inter hW'
  have hmeet : ((G '' A ∩ G '' B) ∩ G '' D).Nonempty :=
    ⟨G a, ⟨⟨⟨a, ⟨haU, haU'⟩, rfl⟩,
      ⟨b, ⟨hbV, hbV'⟩, hab.symm⟩⟩, ⟨d, ⟨hdW, hdW'⟩, had.symm⟩⟩⟩
  obtain ⟨t, ht, htAB⟩ := hdense.exists_mem_open
    (((ho A hA).inter (ho B hB)).inter (ho D hD)) hmeet
  change (p ⁻¹' ({t} : Set Y)).Subsingleton at ht
  obtain ⟨a', ha', hGa'⟩ := htAB.1.1
  obtain ⟨b', hb', hGb'⟩ := htAB.1.2
  obtain ⟨d', hd', hGd'⟩ := htAB.2
  have hnab : a' ≠ b' := by
    intro he
    exact (Set.disjoint_left.mp hUV) ha'.1 (he.symm ▸ hb'.1)
  have hnad : a' ≠ d' := by
    intro he
    exact (Set.disjoint_left.mp hUW) ha'.2 (he.symm ▸ hd'.1)
  have hnbd : b' ≠ d' := by
    intro he
    exact (Set.disjoint_left.mp hVW) hb'.2 (he.symm ▸ hd'.2)
  obtain ⟨x, hx⟩ := hsurj a'
  obtain ⟨u, hu⟩ := hsurj b'
  obtain ⟨v, hv⟩ := hsurj d'
  have hxF : F x ∈ p ⁻¹' ({t} : Set Y) := by
    change p (F x) = t
    rw [hs x, hx, hGa']
  have huF : F u ∈ p ⁻¹' ({t} : Set Y) := by
    change p (F u) = t
    rw [hs u, hu, hGb']
  have hvF : F v ∈ p ⁻¹' ({t} : Set Y) := by
    change p (F v) = t
    rw [hs v, hv, hGd']
  rcases hdegree x u v (ht hxF huF) (ht hxF hvF) with he | he | he
  · exact hnab (hx.symm.trans ((congrArg p he).trans hu))
  · exact hnad (hx.symm.trans ((congrArg p he).trans hv))
  · exact hnbd (hu.symm.trans ((congrArg p he).trans hv))

/-- The three-predecessor collision criterion gives a finite point
fiber without any topology or nonemptiness premise. -/
theorem finite_of_no_three_predecessors (G : Y → Y)
    (hdegree : ∀ a b d : Y, G a = G b → G a = G d →
      a = b ∨ a = d ∨ b = d) (y : Y) :
    (G ⁻¹' {y}).Finite := by
  classical
  by_cases hy : ∃ a : Y, G a = y
  · obtain ⟨a, ha⟩ := hy
    by_cases hb : ∃ b : Y, G b = y ∧ b ≠ a
    · obtain ⟨b, hb, hba⟩ := hb
      apply ((finite_singleton b).insert a).subset
      intro d hd
      change G d = y at hd
      rw [mem_insert_iff, mem_singleton_iff]
      rcases hdegree a b d (ha.trans hb.symm) (ha.trans hd.symm) with h | h | h
      · exact False.elim (hba h.symm)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · apply (finite_singleton a).subset
      intro d hd
      change d = a
      by_contra hda
      exact hb ⟨d, hd, hda⟩
  · have he : (G ⁻¹' {y} : Set Y) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hy ⟨a, ha⟩
    rw [he]
    exact finite_empty

/-- The actual filled-set map has no three distinct preimages of a
point, including at the ramified critical value. -/
theorem quadratic_filled_no_three_predecessors (c : ℂ)
    (x u v : quadraticFilled c)
    (hu : quadraticFilledMap c x = quadraticFilledMap c u)
    (hv : quadraticFilledMap c x = quadraticFilledMap c v) :
    x = u ∨ x = v ∨ u = v := by
  have hroot (z : quadraticFilled c)
      (hz : quadraticFilledMap c x = quadraticFilledMap c z) :
      z = x ∨ (z : ℂ) = -(x : ℂ) := by
    have he := congrArg (fun w : quadraticFilled c => (w : ℂ)) hz
    change (x : ℂ)^2+c = (z : ℂ)^2+c at he
    have hm : ((z : ℂ)-(x : ℂ))*((z : ℂ)+(x : ℂ)) = 0 := by
      calc
        _ = ((z : ℂ)^2+c)-((x : ℂ)^2+c) := by ring
        _ = 0 := by rw [he, sub_self]
    rcases mul_eq_zero.mp hm with h | h
    · exact Or.inl (Subtype.ext (sub_eq_zero.mp h))
    · right
      linear_combination h
  rcases hroot u hu with h | h
  · exact Or.inl h.symm
  · rcases hroot v hv with h' | h'
    · exact Or.inr (Or.inl h'.symm)
    · exact Or.inr (Or.inr (Subtype.ext (h.trans h'.symm)))

/-- Density of the full backward orbit of one singleton anchor
implies density of singleton geometric target fibers. No uniform
radius of the anchor fibers is required. -/
theorem dense_singleton_targets_of_dense_backward_orbit [T1Space X]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p) (hs : Semiconj p F G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hfinite : ∀ x : X, (F ⁻¹' {x}).Finite)
    (a : X) (ha : p ⁻¹' ({p a} : Set Y) = {a})
    (hdense : Dense {x : X | ∃ n : ℕ, (F^[n]) x = a}) :
    Dense {y : Y | (p ⁻¹' ({y} : Set Y)).Subsingleton} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, hx⟩ := hsurj y
  have hne' : (p ⁻¹' U).Nonempty := by
    refine ⟨x, ?_⟩
    change p x ∈ U
    rwa [hx]
  obtain ⟨z, hz, hzU⟩ := hdense.exists_mem_open (hU.preimage hp) hne'
  obtain ⟨n, hn⟩ := hz
  have hsingle := singleton_fiber_of_iterate p F G hf hs hfinite a z ha n hn
  refine ⟨p z, hzU, ?_⟩
  change (p ⁻¹' ({p z} : Set Y)).Subsingleton
  rw [hsingle]
  exact subsingleton_singleton

/-- Alternative source certificate: on the actual quadratic filled
set, an open model, one singleton anchor and its dense backward orbit
suffice for the finite-model-fiber premise and whole-fiber transport. -/
theorem quadratic_filled_open_model_transport_of_anchor [T2Space Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G) (ho : IsOpenMap G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (a : quadraticFilled c) (ha : p ⁻¹' ({p a} : Set Y) = {a})
    (hdense : Dense {x : quadraticFilled c |
      ∃ n : ℕ, ((quadraticFilledMap c)^[n]) x = a}) :
    ∀ y : Y, (G ⁻¹' {y}).Finite ∧
      quadraticFilledMap c '' (p ⁻¹' {y}) = p ⁻¹' {G y} := by
  have hphys : ∀ x : quadraticFilled c,
      ((quadraticFilledMap c) ⁻¹' {x}).Finite :=
    quadratic_restricted_fiber_finite c (quadraticFilled c)
      (quadraticFilledMap c) (fun _ => rfl)
  have hd := dense_singleton_targets_of_dense_backward_orbit
    p (quadraticFilledMap c) G hp hsurj hs hf hphys a ha hdense
  have hdegree := three_predecessors_collide_of_dense_singleton_targets
    p (quadraticFilledMap c) G hsurj hs ho
    (quadratic_filled_no_three_predecessors c) hd
  have hfinite := finite_of_no_three_predecessors G hdegree
  intro y
  exact ⟨hfinite y, quadratic_filled_fiber_image c p G hp hsurj hs hf hfinite y⟩

/-- In this genuine quadratic setting lightness is equivalent to
finite point fibers, rather than merely a separate sufficient premise. -/
theorem quadratic_filled_light_iff_finite [T1Space Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y})) :
    (∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y})) ↔
      (∀ y : Y, (G ⁻¹' {y}).Finite) := by
  constructor
  · intro h
    exact quadratic_filled_light_model_finite c p G hp hsurj hs hf h
  · intro h y S hS hconn
    exact preconnected_finite_subsingleton hconn ((h y).subset hS)


/-- At every depth, the complete model predecessor set is the image
of the physical preimages of any one point in its target fiber.
This is stronger than a global model degree bound. -/
theorem model_iterate_preimage_projection
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hs : Semiconj p F G)
    (himage : ∀ y : Y, F '' (p ⁻¹' {y}) = p ⁻¹' {G y})
    (a : X) (n : ℕ) :
    (G^[n]) ⁻¹' {p a} = p '' ((F^[n]) ⁻¹' {a}) := by
  ext y
  constructor
  · intro hy
    have hw : a ∈ p ⁻¹' ({(G^[n]) y} : Set Y) := by
      change p a = (G^[n]) y
      exact hy.symm
    rw [← iterate_fiber_image_eq p F G himage n y] at hw
    obtain ⟨x, hx, hxa⟩ := hw
    exact ⟨x, hxa, hx⟩
  · rintro ⟨x, hx, rfl⟩
    change (F^[n]) x = a at hx
    change (G^[n]) (p x) = p a
    rw [← hs.iterate_right n x, hx]

/-- At a singleton target anchor the exact predecessor projection
does not require lightness or full-fiber transport anywhere else. -/
theorem model_anchor_iterate_preimage_projection
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hsurj : Surjective p) (hs : Semiconj p F G)
    (a : X) (ha : p ⁻¹' ({p a} : Set Y) = {a}) (n : ℕ) :
    (G^[n]) ⁻¹' {p a} = p '' ((F^[n]) ⁻¹' {a}) := by
  ext y
  constructor
  · intro hy
    change (G^[n]) y = p a at hy
    obtain ⟨x, hx⟩ := hsurj y
    have h : (F^[n]) x ∈ p ⁻¹' ({p a} : Set Y) := by
      change p ((F^[n]) x) = p a
      rw [hs.iterate_right n x, hx, hy]
    rw [ha] at h
    exact ⟨x, h, hx⟩
  · rintro ⟨x, hx, rfl⟩
    change (F^[n]) x = a at hx
    change (G^[n]) (p x) = p a
    rw [← hs.iterate_right n x, hx]

/-- All predecessor labels of a singleton anchor remain distinct
under a connected-fiber semiconjugacy of finite-to-one physical
dynamics. No model degree assumption is needed. -/
theorem model_anchor_iterate_preimage_injective [T1Space X]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hs : Semiconj p F G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hfinite : ∀ x : X, (F ⁻¹' {x}).Finite)
    (a : X) (ha : p ⁻¹' ({p a} : Set Y) = {a}) (n : ℕ) :
    InjOn p ((F^[n]) ⁻¹' {a}) := by
  intro x hx z _ h
  have hsingle := singleton_fiber_of_iterate p F G hf hs hfinite a x ha n hx
  have hz : z ∈ p ⁻¹' ({p x} : Set Y) := h.symm
  rw [hsingle] at hz
  exact (show z = x from hz).symm

/-- Complete invariance of the genuine filled set persists through
every finite iterate of the ambient complex quadratic. -/
theorem quadratic_filled_iterate_mem_iff (c z : ℂ) (n : ℕ) :
    ((fun w : ℂ => w^2+c)^[n]) z ∈ quadraticFilled c ↔
      z ∈ quadraticFilled c := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    exact quadratic_filled_complete_invariant c z

/-- Transfer the genuine global inverse-point census across an exact
projection identity. The result retains the physical ramification
count; injectivity on the inverse set gives equality of counts. -/
theorem quadratic_filled_model_census_of_projection
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (a : quadraticFilled c) (n : ℕ)
    (hproj : (G^[n]) ⁻¹' {p a} =
      p '' (((quadraticFilledMap c)^[n]) ⁻¹' {a})) :
    ∃ M : Finset Y,
      (∀ y : Y, y ∈ M ↔ (G^[n]) y = p a) ∧
      M.card ≤ (globalFiber c n (a : ℂ)).card ∧
      (InjOn p (((quadraticFilledMap c)^[n]) ⁻¹' {a}) →
        M.card = (globalFiber c n (a : ℂ)).card) := by
  classical
  let A := globalFiber c n (a : ℂ)
  have hmem (z : ℂ) (hz : z ∈ A) : z ∈ quadraticFilled c := by
    apply (quadratic_filled_iterate_mem_iff c z n).mp
    rw [(mem_globalFiber c n (a : ℂ) z).mp hz]
    exact a.property
  let lift : ↥A → quadraticFilled c := fun z => ⟨(z : ℂ), hmem z z.property⟩
  let q : ↥A → Y := fun z => p (lift z)
  let M := A.attach.image q
  have hsem : Semiconj (Subtype.val : quadraticFilled c → ℂ)
      (quadraticFilledMap c) (fun w : ℂ => w^2+c) := fun _ => rfl
  have hroot (z : ↥A) : ((quadraticFilledMap c)^[n]) (lift z) = a := by
    apply Subtype.ext
    rw [hsem.iterate_right n (lift z)]
    exact (mem_globalFiber c n (a : ℂ) (z : ℂ)).mp z.property
  have hM (y : Y) : y ∈ M ↔ (G^[n]) y = p a := by
    change y ∈ A.attach.image q ↔ _
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, _, rfl⟩
      change (G^[n]) (p (lift z)) = p a
      rw [← hs.iterate_right n (lift z), hroot z]
    · intro hy
      have hy' : y ∈ (G^[n]) ⁻¹' {p a} := hy
      rw [hproj] at hy'
      obtain ⟨x, hx, hxp⟩ := hy'
      change ((quadraticFilledMap c)^[n]) x = a at hx
      have hxA : (x : ℂ) ∈ A := by
        apply (mem_globalFiber c n (a : ℂ) (x : ℂ)).mpr
        rw [← hsem.iterate_right n x, hx]
      let z : ↥A := ⟨(x : ℂ), hxA⟩
      refine ⟨z, Finset.mem_attach _ _, ?_⟩
      have hzx : lift z = x := Subtype.ext rfl
      change p (lift z) = y
      rwa [hzx]
  refine ⟨M, hM, ?_, ?_⟩
  · calc
      M.card ≤ A.attach.card := Finset.card_image_le
      _ = A.card := Finset.card_attach
  · intro hi
    have hqi : Injective q := by
      intro z t he
      apply Subtype.ext
      have hl : lift z = lift t := hi (hroot z) (hroot t) he
      exact congrArg (fun w : quadraticFilled c => (w : ℂ)) hl
    calc
      M.card = A.attach.card := Finset.card_image_of_injective _ hqi
      _ = A.card := Finset.card_attach

/-- In the light-model setting the model's inverse census is bounded
by the actual critical-value-adjusted count at every depth, not just
the unramified global degree. -/
theorem quadratic_filled_light_model_ramification_bound [T1Space Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (a : quadraticFilled c) (n : ℕ) :
    ∃ M : Finset Y,
      (∀ y : Y, y ∈ M ↔ (G^[n]) y = p a) ∧
      M.card + criticalFiberDefect c (a : ℂ) n ≤ 2^n := by
  have hproj := model_iterate_preimage_projection p (quadraticFilledMap c) G hs
    (quadratic_filled_light_fiber_image c p G hp hsurj hs hf hlight) a n
  obtain ⟨M, hM, hcard, _⟩ :=
    quadratic_filled_model_census_of_projection c p G hs a n hproj
  refine ⟨M, hM, ?_⟩
  have he := globalFiber_card_exact c (a : ℂ) n
  omega

/-- Exact ramification-aware count for a singleton geometric anchor.
No model lightness, openness, finite degree, or even global
whole-fiber transport is required for this inverse census. -/
theorem quadratic_filled_singleton_anchor_ramification_exact
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hsurj : Surjective p) (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (a : quadraticFilled c) (ha : p ⁻¹' ({p a} : Set Y) = {a}) (n : ℕ) :
    ∃ M : Finset Y,
      (∀ y : Y, y ∈ M ↔ (G^[n]) y = p a) ∧
      M.card + criticalFiberDefect c (a : ℂ) n = 2^n := by
  have hphys : ∀ x : quadraticFilled c,
      ((quadraticFilledMap c) ⁻¹' {x}).Finite :=
    quadratic_restricted_fiber_finite c (quadraticFilled c)
      (quadraticFilledMap c) (fun _ => rfl)
  have hproj := model_anchor_iterate_preimage_projection
    p (quadraticFilledMap c) G hsurj hs a ha n
  have hI := model_anchor_iterate_preimage_injective
    p (quadraticFilledMap c) G hs hf hphys a ha n
  obtain ⟨M, hM, _, heq⟩ :=
    quadratic_filled_model_census_of_projection c p G hs a n hproj
  refine ⟨M, hM, ?_⟩
  rw [heq hI]
  exact globalFiber_card_exact c (a : ℂ) n

/-- If the singleton anchor avoids every critical value of the
iterate, the model has the entire unramified binary predecessor
level, with no label collision. -/
theorem quadratic_filled_singleton_anchor_full_degree
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hsurj : Surjective p) (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (a : quadraticFilled c) (ha : p ⁻¹' ({p a} : Set Y) = {a}) (n : ℕ)
    (havoid : ∀ k < n, ((fun w : ℂ => w^2+c)^[k]) c ≠ (a : ℂ)) :
    ∃ M : Finset Y, (∀ y : Y, y ∈ M ↔ (G^[n]) y = p a) ∧ M.card = 2^n := by
  obtain ⟨M, hM, heq⟩ :=
    quadratic_filled_singleton_anchor_ramification_exact c p G hsurj hs hf a ha n
  have hz := (criticalFiberDefect_zero_iff c (a : ℂ) n).mpr havoid
  refine ⟨M, hM, ?_⟩
  omega

end LoopsStationaryLightModel
