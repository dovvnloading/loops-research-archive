import TelescopeCollarRecognition
import QuadraticEscapeFullness

/-!
# Parameter-stable trapping of the whole critical quadratic pullback

Properness separates a compact target from the image of the complement of
its prescribed source neighborhood. A tube argument then controls the
full inverse image simultaneously in the parameter and the target. Both
signed roots are controlled, including at the critical value.
-/

namespace LoopsQuadraticCriticalTrapping

open Set

/-- A preconnected target containing the critical value has just one
quadratic pullback component. The equality is with the entire physical
preimage, and does not require openness or simple connectivity. -/
theorem quadratic_critical_component_eq_preimage (c : ℂ) (D : Set ℂ)
    (hD : IsPreconnected D) (hc : c ∈ D) :
    connectedComponentIn ((fun z : ℂ => z^2+c) ⁻¹' D) 0 =
      (fun z : ℂ => z^2+c) ⁻¹' D := by
  have hpre :=
    LoopsQuadraticEscapeFullness.quadratic_critical_preimage_preconnected c D hD hc
  have hzero : (0 : ℂ) ∈ (fun z : ℂ => z^2+c) ⁻¹' D := by
    simpa using hc
  exact Subset.antisymm (connectedComponentIn_subset _ _)
    (hpre.subset_connectedComponentIn hzero (Subset.refl _))

/-- Whole-preimage containment over a compact target persists on one
open parameter neighborhood and one open target neighborhood. The target
need not be connected and need not contain the critical value. -/
theorem quadratic_full_preimage_parameter_neighborhood (c : ℂ)
    (D W : Set ℂ) (hD : IsCompact D) (hW : IsOpen W)
    (htrap : (fun z : ℂ => z^2+c) ⁻¹' D ⊆ W) :
    ∃ P V : Set ℂ, IsOpen P ∧ c ∈ P ∧ IsOpen V ∧ D ⊆ V ∧
      ∀ d ∈ P, (fun z : ℂ => z^2+d) ⁻¹' V ⊆ W := by
  have hq : IsProperMap (fun z : ℂ => z^2+c) :=
    LoopsTelescopeCollar.orbit_proper c 1
  let S : Set ℂ := ((fun z : ℂ => z^2+c) '' Wᶜ)ᶜ
  have hS : IsOpen S := (hq.isClosedMap _ hW.isClosed_compl).isOpen_compl
  have hDS : D ⊆ S := by
    intro y hy
    change y ∉ (fun z : ℂ => z^2+c) '' Wᶜ
    rintro ⟨z, hz, rfl⟩
    exact hz (htrap hy)
  let T : ℂ × ℂ → ℂ := fun p => p.2+c-p.1
  have hT : Continuous T :=
    (continuous_snd.add continuous_const).sub continuous_fst
  let O : Set (ℂ × ℂ) := T ⁻¹' S
  have hO : IsOpen O := hS.preimage hT
  have hbase : ({c} : Set ℂ) ×ˢ D ⊆ O := by
    intro p hp
    have hpc : p.1 = c := mem_singleton_iff.mp hp.1
    change p.2+c-p.1 ∈ S
    rw [hpc, add_sub_cancel_right]
    exact hDS hp.2
  obtain ⟨P, V, hP, hV, hcP, hDV, hPV⟩ :=
    generalized_tube_lemma isCompact_singleton hD hO hbase
  refine ⟨P, V, hP, hcP (by simp), hV, hDV, ?_⟩
  intro d hd z hz
  have ht : (z^2+d)+c-d ∈ S :=
    hPV (show (d, z^2+d) ∈ P ×ˢ V from ⟨hd, hz⟩)
  have he : (z^2+d)+c-d = z^2+c := by ring
  rw [he] at ht
  by_contra hnot
  exact ht ⟨z, hnot, rfl⟩

/-- The common target can have compact closure, and every nearby full
pullback of that closure still lies inside the prescribed source set. -/
theorem quadratic_full_preimage_parameter_collar (c : ℂ)
    (D W : Set ℂ) (hD : IsCompact D) (hW : IsOpen W)
    (htrap : (fun z : ℂ => z^2+c) ⁻¹' D ⊆ W) :
    ∃ P V : Set ℂ, IsOpen P ∧ c ∈ P ∧ IsOpen V ∧ D ⊆ V ∧
      IsCompact (closure V) ∧
      ∀ d ∈ P, (fun z : ℂ => z^2+d) ⁻¹' closure V ⊆ W := by
  obtain ⟨P, O, hP, hcP, hO, hDO, htrapO⟩ :=
    quadratic_full_preimage_parameter_neighborhood c D W hD hW htrap
  obtain ⟨V, hV, hDV, hVO, hVc⟩ :=
    exists_open_between_and_isCompact_closure hD hO hDO
  refine ⟨P, V, hP, hcP, hV, hDV, hVc, ?_⟩
  intro d hd z hz
  exact htrapO d hd (hVO hz)

end LoopsQuadraticCriticalTrapping
