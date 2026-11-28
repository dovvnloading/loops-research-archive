import Mathlib

/-!
# The topological implication from a singleton monotone fiber

This file supplies only classical supporting topology.  The quadratic-family
input is proved in the companion susceptibility development.  No identification
of an arbitrary quotient with the canonical combinatorial model is made here.

The elementary separation proof of `preconnected_preimage_closed_fibers` is
reproduced from `LoopsStationaryMonotoneGeometry.preconnected_preimage_closed_fibers`
in the archive, without importing its dynamical constructions.  Neither this
lemma nor the singleton-fiber implication is claimed as new mathematics.
-/

namespace LoopsQuadraticMonotoneFiberTopology

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed surjection with preconnected fibers pulls back preconnected sets. -/
theorem preconnected_preimage_closed_fibers (q : X → Y)
    (hq : IsClosedMap q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    {S : Set Y} (hS : IsPreconnected S) :
    IsPreconnected (q ⁻¹' S) := by
  apply isPreconnected_closed_iff.mpr
  intro U V hU hV hcover hleft hright
  let A : Set Y := q '' U
  let B : Set Y := q '' V
  have hc : S ⊆ A ∪ B := by
    intro y hy
    obtain ⟨x, hxy⟩ := hsurj y
    have hx : x ∈ q ⁻¹' S := by
      change q x ∈ S
      rwa [hxy]
    rcases hcover hx with hxU | hxV
    · exact Or.inl ⟨x, hxU, hxy⟩
    · exact Or.inr ⟨x, hxV, hxy⟩
  have ha : (S ∩ A).Nonempty := by
    obtain ⟨x, hx, hxU⟩ := hleft
    exact ⟨q x, hx, ⟨x, hxU, rfl⟩⟩
  have hb : (S ∩ B).Nonempty := by
    obtain ⟨x, hx, hxV⟩ := hright
    exact ⟨q x, hx, ⟨x, hxV, rfl⟩⟩
  obtain ⟨y, hy, hyA, hyB⟩ :=
    (isPreconnected_closed_iff.mp hS) A B (hq U hU) (hq V hV) hc ha hb
  obtain ⟨a, haU, hay⟩ := hyA
  obtain ⟨b, hbV, hby⟩ := hyB
  have hsub : q ⁻¹' ({y} : Set Y) ⊆ U ∪ V := by
    intro z hz
    apply hcover
    change q z ∈ S
    change q z = y at hz
    rwa [hz]
  obtain ⟨z, hz, hzU, hzV⟩ :=
    (isPreconnected_closed_iff.mp (hf y)) U V hU hV hsub
      ⟨a, hay, haU⟩ ⟨b, hby, hbV⟩
  refine ⟨z, ?_, hzU, hzV⟩
  change q z ∈ S
  change q z = y at hz
  rwa [hz]

/-- A singleton fiber of a continuous monotone surjection from a compact space
to a Hausdorff locally connected space gives an open connected neighborhood
basis at the corresponding point of the domain. -/
theorem connected_open_basis_of_singleton_fiber
    [CompactSpace X] [T2Space Y] [LocallyConnectedSpace Y]
    (q : X → Y) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (x : X) (hsingle : q ⁻¹' ({q x} : Set Y) = {x}) :
    ∀ U ∈ 𝓝 x, ∃ V : Set X,
      V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V := by
  intro U hU
  obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.mp hU
  have himage : IsClosed (q '' Oᶜ) := hq.isClosedMap Oᶜ hO.isClosed_compl
  have hximage : q x ∈ (q '' Oᶜ)ᶜ := by
    rintro ⟨z, hz, hzq⟩
    have hzfiber : z ∈ q ⁻¹' ({q x} : Set Y) := hzq
    rw [hsingle] at hzfiber
    have hzx : z = x := hzfiber
    subst z
    exact hz hxO
  obtain ⟨W, ⟨hW, hxW, hWconn⟩, hWsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (q x)).mem_iff.mp
      (himage.isOpen_compl.mem_nhds hximage)
  refine ⟨q ⁻¹' W, ?_, hW.preimage hq, hxW, ?_⟩
  · intro z hz
    apply hOU
    by_contra hzO
    exact hWsub hz ⟨z, hzO, rfl⟩
  · exact ⟨⟨x, hxW⟩,
      preconnected_preimage_closed_fibers q hq.isClosedMap hsurj hf
        hWconn.isPreconnected⟩

end LoopsQuadraticMonotoneFiberTopology
