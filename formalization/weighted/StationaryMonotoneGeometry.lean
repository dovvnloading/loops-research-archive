import Mathlib

/-!
# Closed monotone quotients and geometric marked continua

The physical filled Julia set and its canonical rational-cut quotient
must be supplied separately. All the statements here use actual sets
and their topologies, not a finite tree of incidence labels.
-/

namespace LoopsStationaryMonotoneGeometry

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Closed maps with preconnected fibers pull back arbitrary preconnected
sets. Neither local connectivity nor compactness of the target subset
is required. -/
theorem preconnected_preimage_closed_fibers (p : X → Y)
    (hp : IsClosedMap p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    {S : Set Y} (hS : IsPreconnected S) :
    IsPreconnected (p ⁻¹' S) := by
  apply isPreconnected_closed_iff.mpr
  intro U V hU hV hcover hleft hright
  let A : Set Y := p '' U
  let B : Set Y := p '' V
  have hc : S ⊆ A ∪ B := by
    intro y hy
    obtain ⟨x, hxy⟩ := hsurj y
    have hx : x ∈ p ⁻¹' S := by
      change p x ∈ S
      rwa [hxy]
    rcases hcover hx with hxU | hxV
    · exact Or.inl ⟨x, hxU, hxy⟩
    · exact Or.inr ⟨x, hxV, hxy⟩
  have ha : (S ∩ A).Nonempty := by
    obtain ⟨x, hx, hxU⟩ := hleft
    exact ⟨p x, hx, ⟨x, hxU, rfl⟩⟩
  have hb : (S ∩ B).Nonempty := by
    obtain ⟨x, hx, hxV⟩ := hright
    exact ⟨p x, hx, ⟨x, hxV, rfl⟩⟩
  obtain ⟨y, hy, hyA, hyB⟩ :=
    (isPreconnected_closed_iff.mp hS) A B (hp U hU) (hp V hV) hc ha hb
  obtain ⟨a, haU, hay⟩ := hyA
  obtain ⟨b, hbV, hby⟩ := hyB
  have hsub : p ⁻¹' ({y} : Set Y) ⊆ U ∪ V := by
    intro z hz
    apply hcover
    change p z ∈ S
    change p z = y at hz
    rwa [hz]
  obtain ⟨z, hz, hzU, hzV⟩ :=
    (isPreconnected_closed_iff.mp (hf y)) U V hU hV hsub
      ⟨a, hay, haU⟩ ⟨b, hby, hbV⟩
  refine ⟨z, ?_, hzU, hzV⟩
  change p z ∈ S
  change p z = y at hz
  rwa [hz]

/-- Exact connected-component transport on every saturated subset. -/
theorem component_preimage_closed_fibers (p : X → Y)
    (hp : IsClosedMap p) (hc : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (S : Set Y) (x : X) (hx : p x ∈ S) :
    connectedComponentIn (p ⁻¹' S) x =
      p ⁻¹' connectedComponentIn S (p x) := by
  apply Subset.antisymm
  · have hconn : IsPreconnected (p '' connectedComponentIn (p ⁻¹' S) x) :=
      isPreconnected_connectedComponentIn.image p hc.continuousOn
    have hmem : p x ∈ p '' connectedComponentIn (p ⁻¹' S) x :=
      ⟨x, mem_connectedComponentIn hx, rfl⟩
    have hsub : p '' connectedComponentIn (p ⁻¹' S) x ⊆ S := by
      rintro _ ⟨z, hz, rfl⟩
      exact connectedComponentIn_subset _ _ hz
    intro z hz
    exact hconn.subset_connectedComponentIn hmem hsub ⟨z, hz, rfl⟩
  · have hconn : IsPreconnected (p ⁻¹' connectedComponentIn S (p x)) :=
      preconnected_preimage_closed_fibers p hp hsurj hf isPreconnected_connectedComponentIn
    exact hconn.subset_connectedComponentIn (mem_connectedComponentIn hx)
      (fun _ hz => connectedComponentIn_subset _ _ hz)

/-- In the compact Hausdorff quotient setting, a singleton fiber at a
root is sufficient for exact transport of the entire punctured
component, not just its image or a marked vertex. -/
theorem punctured_component_full_lift [CompactSpace X] [T2Space Y]
    (p : X → Y) (hc : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (a x : X) (ha : p ⁻¹' ({p a} : Set Y) = {a}) (hx : x ≠ a) :
    connectedComponentIn ({a} : Set X)ᶜ x =
      p ⁻¹' connectedComponentIn ({p a} : Set Y)ᶜ (p x) := by
  have heq : p ⁻¹' ({p a} : Set Y)ᶜ = ({a} : Set X)ᶜ := by
    rw [preimage_compl, ha]
  rw [← heq]
  apply component_preimage_closed_fibers p hc.isClosedMap hc hsurj hf
  change p x ≠ p a
  intro h
  have h' : x ∈ p ⁻¹' ({p a} : Set Y) := h
  rw [ha] at h'
  exact hx h'

/-- Hereditary unicoherence rules out two disjoint connected bridges
joining the same two disjoint nonempty closed connected marks.
No path or local-connectivity hypothesis is used. -/
theorem disjoint_bridges_impossible
    (A B C D : Set X)
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (hAc : IsClosed A) (hBc : IsClosed B) (hCc : IsClosed C) (hDc : IsClosed D)
    (hA : IsConnected A) (hB : IsConnected B)
    (hC : IsConnected C) (hD : IsConnected D)
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hAC : (A ∩ C).Nonempty) (hBC : (B ∩ C).Nonempty)
    (hAD : (A ∩ D).Nonempty) (hBD : (B ∩ D).Nonempty) : False := by
  have h1 : IsConnected (A ∪ C ∪ B) := by
    apply IsConnected.union _ (IsConnected.union hAC hA hC) hB
    obtain ⟨b, hb, hbC⟩ := hBC
    exact ⟨b, Or.inr hbC, hb⟩
  have h2 : IsConnected (A ∪ D ∪ B) := by
    apply IsConnected.union _ (IsConnected.union hAD hA hD) hB
    obtain ⟨b, hb, hbD⟩ := hBD
    exact ⟨b, Or.inr hbD, hb⟩
  have hi := hu (A ∪ C ∪ B) (A ∪ D ∪ B)
    ((hAc.union hCc).union hBc) ((hAc.union hDc).union hBc) h1 h2
  have heq : (A ∪ C ∪ B) ∩ (A ∪ D ∪ B) = A ∪ B := by
    ext z
    simp only [mem_inter_iff, mem_union]
    have hd : ¬ (z ∈ C ∧ z ∈ D) := fun h => Set.disjoint_left.mp hCD h.1 h.2
    tauto
  rw [heq] at hi
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨b, hb⟩ := hB.nonempty
  obtain ⟨z, _, hzA, hzB⟩ := (isPreconnected_closed_iff.mp hi) A B hAc hBc
    Subset.rfl ⟨a, Or.inl ha, ha⟩ ⟨b, Or.inr hb, hb⟩
  exact Set.disjoint_left.mp hAB hzA hzB

/-- A semiconjugacy with connected fibers cannot identify two disjoint
invariant geometric continua if all nonsingleton fibers are nonfixed
under the specified return. This is the wandering-fiber argument
applied to the return map, with hereditary unicoherence explicit. -/
theorem invariant_marks_disjoint_image [T1Space Y]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hp : Continuous p) (hf : ∀ y : Y, IsConnected (p ⁻¹' {y}))
    (hsemi : ∀ x, p (F x) = G (p x))
    (hw : ∀ y : Y, ¬ (p ⁻¹' {y}).Subsingleton → G y ≠ y)
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (A B : Set X) (hAc : IsClosed A) (hBc : IsClosed B)
    (hA : IsConnected A) (hB : IsConnected B) (hAB : Disjoint A B)
    (hFA : MapsTo F A A) (hFB : MapsTo F B B) :
    Disjoint (p '' A) (p '' B) := by
  apply Set.disjoint_left.mpr
  intro y hyA hyB
  obtain ⟨a, ha, hay⟩ := hyA
  obtain ⟨b, hb, hby⟩ := hyB
  let C : Set X := p ⁻¹' {y}
  let D : Set X := p ⁻¹' {G y}
  have haC : a ∈ C := hay
  have hbC : b ∈ C := hby
  have hn : ¬ C.Subsingleton := by
    intro hs
    have hab : a = b := hs haC hbC
    exact Set.disjoint_left.mp hAB (hab ▸ ha) hb
  have hneq : G y ≠ y := hw y hn
  have hCD : Disjoint C D := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    change p z = y at hz
    change p z = G y at hz'
    exact hneq (hz'.symm.trans hz)
  have haD : F a ∈ D := by
    change p (F a) = G y
    rw [hsemi, hay]
  have hbD : F b ∈ D := by
    change p (F b) = G y
    rw [hsemi, hby]
  exact disjoint_bridges_impossible A B C D hu hAc hBc
    (isClosed_singleton.preimage hp) (isClosed_singleton.preimage hp)
    (hA) (hB) (hf y) (hf (G y)) hAB hCD
    ⟨a, ha, haC⟩ ⟨b, hb, hbC⟩ ⟨F a, hFA ha, haD⟩ ⟨F b, hFB hb, hbD⟩

end LoopsStationaryMonotoneGeometry
