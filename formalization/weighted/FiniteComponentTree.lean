import Mathlib

/-!
# Components of a finite product decomposition

A homeomorphism to a finite discrete index times a preconnected space
identifies the actual connected components with its label fibers. The
component count needs only nonemptiness of the second factor; compactness
is used separately to obtain compact components.
-/

namespace LoopsFiniteComponentTree

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [PreconnectedSpace Y] {N : ℕ}

/-- The first coordinate of a finite product decomposition is the exact
connected-component label, rather than merely a finite partition. -/
theorem component_eq_label_fiber (e : X ≃ₜ (Fin N × Y)) (x : X) :
    connectedComponent x = {z | (e z).1 = (e x).1} := by
  apply Subset.antisymm
  · intro z hz
    exact isPreconnected_connectedComponent.constant
      (continuous_fst.comp e.continuous).continuousOn hz mem_connectedComponent
  · let f : Y → X := fun y => e.symm ((e x).1, y)
    have hf : Continuous f :=
      e.symm.continuous.comp (continuous_const.prodMk continuous_id)
    have hx : x ∈ range f := by
      refine ⟨(e x).2, ?_⟩
      simp [f]
    have hsub := (isPreconnected_range hf).subset_connectedComponent hx
    intro z hz
    apply hsub
    refine ⟨(e z).2, ?_⟩
    apply e.injective
    change e (e.symm ((e x).1, (e z).2)) = e z
    rw [e.apply_symm_apply]
    exact Prod.ext hz.symm rfl

/-- Each component is exactly the image of its fixed-label inverse
section, which is useful for transporting actual maps between components. -/
theorem component_eq_range (e : X ≃ₜ (Fin N × Y)) (x : X) :
    connectedComponent x = range (fun y : Y => e.symm ((e x).1, y)) := by
  rw [component_eq_label_fiber e x]
  ext z
  constructor
  · intro hz
    refine ⟨(e z).2, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext hz.symm rfl
  · rintro ⟨y, rfl⟩
    simp

/-- The second coordinate restricts to a homeomorphism on each actual
connected component. -/
def componentHomeomorph (e : X ≃ₜ (Fin N × Y)) (x : X) :
    connectedComponent x ≃ₜ Y where
  toFun z := (e z.val).2
  invFun y := ⟨e.symm ((e x).1, y), by
    rw [component_eq_label_fiber e x]
    simp⟩
  left_inv z := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    have hz := z.property
    rw [component_eq_label_fiber e x] at hz
    exact Prod.ext hz.symm rfl
  right_inv y := by simp
  continuous_toFun := continuous_snd.comp (e.continuous.comp continuous_subtype_val)
  continuous_invFun :=
    (e.symm.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _

/-- Finitely many labels make each actual connected component open as
well as closed. -/
theorem component_isClopen (e : X ≃ₜ (Fin N × Y)) (x : X) :
    IsClopen (connectedComponent x) := by
  rw [component_eq_label_fiber e x]
  exact (isClopen_discrete ({(e x).1} : Set (Fin N))).preimage
    (continuous_fst.comp e.continuous)

/-- Compactness of the common factor gives compactness of every component. -/
theorem component_isCompact [CompactSpace Y]
    (e : X ≃ₜ (Fin N × Y)) (x : X) : IsCompact (connectedComponent x) := by
  rw [component_eq_range e x]
  exact isCompact_range
    (e.symm.continuous.comp (continuous_const.prodMk continuous_id))

/-- The component quotient is equivalent to the finite label type. -/
noncomputable def componentEquiv [Nonempty Y] (e : X ≃ₜ (Fin N × Y)) :
    ConnectedComponents X ≃ Fin N :=
  Equiv.ofBijective (continuous_fst.comp e.continuous).connectedComponentsLift (by
    constructor
    · intro a b hab
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
      change (e x).1 = (e y).1 at hab
      apply ConnectedComponents.coe_eq_coe'.2
      rw [component_eq_label_fiber e y]
      exact hab
    · intro i
      let y : Y := Classical.choice (inferInstance : Nonempty Y)
      refine ⟨ConnectedComponents.mk (e.symm (i, y)), ?_⟩
      change (e (e.symm (i, y))).1 = i
      simp)

/-- The quotient equivalence retains the label of every original point. -/
theorem componentEquiv_mk [Nonempty Y] (e : X ≃ₜ (Fin N × Y)) (x : X) :
    componentEquiv e (ConnectedComponents.mk x) = (e x).1 := rfl

/-- Exact component count, with no local connectedness assumption. -/
theorem component_count [Nonempty Y] (e : X ≃ₜ (Fin N × Y)) :
    Nat.card (ConnectedComponents X) = N := by
  rw [Nat.card_congr (componentEquiv e), Nat.card_fin]

end LoopsFiniteComponentTree
