import Mathlib

/-!
# Component quotients under finite product splittings

The second factor may be disconnected. A splitting of a nonempty space
into two copies of itself therefore forces infinitely many actual
connected components, without identifying those components as points.
-/

namespace LoopsComponentDoubling

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {N : ℕ}

/-- A component of a discrete product has one fixed label and one
actual component in the second factor. -/
theorem product_component_eq_fiber (e : X ≃ₜ (Fin N × Y)) (x : X) :
    connectedComponent x =
      {z | (e z).1 = (e x).1 ∧ (e z).2 ∈ connectedComponent (e x).2} := by
  apply Set.Subset.antisymm
  · intro z hz
    exact ⟨isPreconnected_connectedComponent.constant
      (continuous_fst.comp e.continuous).continuousOn hz mem_connectedComponent,
      (continuous_snd.comp e.continuous).mapsTo_connectedComponent x hz⟩
  · intro z hz
    have hsec : Continuous (fun y : Y => e.symm ((e x).1, y)) :=
      e.symm.continuous.comp (continuous_const.prodMk continuous_id)
    have hm := hsec.mapsTo_connectedComponent (e x).2 hz.2
    have hc : e.symm ((e x).1, (e x).2) = x := by simp
    have he : e.symm ((e x).1, (e z).2) = z := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact Prod.ext hz.1.symm rfl
    simpa only [hc, he] using hm

/-- The second coordinate is a homeomorphism from each component onto
its actual parent component, even when the parent space is disconnected. -/
def productComponentHomeomorph (e : X ≃ₜ (Fin N × Y)) (x : X) :
    connectedComponent x ≃ₜ connectedComponent (e x).2 where
  toFun z := ⟨(e z.val).2,
    (continuous_snd.comp e.continuous).mapsTo_connectedComponent x z.property⟩
  invFun y := ⟨e.symm ((e x).1, y.val), by
    rw [product_component_eq_fiber e x]
    simp only [e.apply_symm_apply]
    exact ⟨rfl, y.property⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    have hz := (Set.ext_iff.mp (product_component_eq_fiber e x) z.val).mp z.property
    exact Prod.ext hz.1.symm rfl
  right_inv y := by
    apply Subtype.ext
    simp
  continuous_toFun :=
    (continuous_snd.comp (e.continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    (e.symm.continuous.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

/-- The component homeomorphism uses the original second-coordinate map. -/
theorem productComponentHomeomorph_apply (e : X ≃ₜ (Fin N × Y)) (x : X)
    (z : connectedComponent x) :
    (productComponentHomeomorph e x z : Y) = (e z.val).2 := rfl

/-- A finite discrete product decomposition descends to the component
quotient, with no connectedness hypothesis on the second factor. -/
def productComponentEquiv (e : X ≃ₜ (Fin N × Y)) :
    ConnectedComponents X ≃ (Fin N × ConnectedComponents Y) where
  toFun q :=
    ((continuous_fst.comp e.continuous).connectedComponentsLift q,
      (continuous_snd.comp e.continuous).connectedComponentsMap q)
  invFun q :=
    (show Continuous (fun y : Y => e.symm (q.1, y)) from
      e.symm.continuous.comp (continuous_const.prodMk continuous_id)).connectedComponentsMap q.2
  left_inv q := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    change ConnectedComponents.mk (e.symm ((e x).1, (e x).2)) = ConnectedComponents.mk x
    simp
  right_inv q := by
    rcases q with ⟨i, q⟩
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
    change ((e (e.symm (i, y))).1,
      ConnectedComponents.mk ((e (e.symm (i, y))).2)) =
      (i, ConnectedComponents.mk y)
    simp

/-- The quotient equivalence records the original label and the component
of the original second coordinate. -/
theorem productComponentEquiv_mk (e : X ≃ₜ (Fin N × Y)) (x : X) :
    productComponentEquiv e (ConnectedComponents.mk x) =
      ((e x).1, ConnectedComponents.mk (e x).2) := rfl

/-- The exact cardinal identity holds for every finite splitting. -/
theorem component_product_card (e : X ≃ₜ (Fin N × Y)) :
    Nat.card (ConnectedComponents X) = N * Nat.card (ConnectedComponents Y) := by
  rw [Nat.card_congr (productComponentEquiv e), Nat.card_prod, Nat.card_fin]

/-- A nonempty topological space homeomorphic to two disjoint copies of
itself has infinitely many connected components. -/
theorem self_double_components_infinite [Nonempty X]
    (e : X ≃ₜ (Fin 2 × X)) : Infinite (ConnectedComponents X) := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  letI : Finite (ConnectedComponents X) := hfinite
  have hpos : 0 < Nat.card (ConnectedComponents X) := Nat.card_pos
  have hcard := component_product_card e
  omega

end LoopsComponentDoubling
