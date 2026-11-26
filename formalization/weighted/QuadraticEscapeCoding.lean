import QuadraticEscapeComponents
import CompactBinaryCoding

/-!
# All binary itineraries and the exact component cardinality

For every quadratic parameter with escaping critical point, the actual
bounded-orbit set has a continuous full binary shift factor. The coding
descends to components and proves that there are exactly continuum many.
No diameter contraction or singleton-impression premise is supplied.
-/

namespace LoopsQuadraticEscapeTree

open Set Function QuadraticEscape LoopsStationaryFiberDynamics
open LoopsCompactBinaryCoding
open scoped Cardinal

set_option maxHeartbeats 1000000

/-- Transport the constructed zero-height splitting to the existing
filled-set type, preserving the exact physical quadratic self-map. -/
theorem filled_two_sheet (c : ℂ) (hc : 0 < escape c 0) :
    ∃ e : quadraticFilled c ≃ₜ (Fin 2 × quadraticFilled c),
      ∀ z, (e z).2 = quadraticFilledMap c z := by
  obtain ⟨e, he⟩ := sublevel_split c 0 le_rfl hc
  let source : sublevel c 0 ≃ₜ quadraticFilled c :=
    Homeomorph.setCongr (sublevel_zero_eq_filled c)
  let target : sublevel c (2*0) ≃ₜ quadraticFilled c :=
    Homeomorph.setCongr (by rw [mul_zero, sublevel_zero_eq_filled c])
  let E : quadraticFilled c ≃ₜ (Fin 2 × quadraticFilled c) :=
    (source.symm.trans e).trans ((Homeomorph.refl (Fin 2)).prodCongr target)
  refine ⟨E, ?_⟩
  intro z
  apply Subtype.ext
  change ((e (source.symm z)).2 : ℂ) = (z : ℂ)^2+c
  exact he (source.symm z)

/-- Every infinite binary itinerary is realized by an actual bounded
quadratic orbit. The continuous coding intertwines the polynomial and
the shift, and factors continuously and surjectively through the actual
component quotient. This is a factor, not a claimed conjugacy. -/
theorem filled_binary_coding (c : ℂ) (hc : 0 < escape c 0) :
    ∃ code : quadraticFilled c → (ℕ → Fin 2),
      ∃ componentCode : ConnectedComponents (quadraticFilled c) → (ℕ → Fin 2),
        Continuous code ∧ Surjective code ∧
        Semiconj code (quadraticFilledMap c) shift ∧
        Continuous componentCode ∧ Surjective componentCode ∧
        ∀ z, componentCode (ConnectedComponents.mk z) = code z := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  obtain ⟨z, hz⟩ := sublevel_nonempty c 0 le_rfl
  have hzK : z ∈ quadraticFilled c := by
    rwa [sublevel_zero_eq_filled c] at hz
  letI : Nonempty (quadraticFilled c) := ⟨⟨z, hzK⟩⟩
  obtain ⟨e, he⟩ := filled_two_sheet c hc
  have hstep : step e = quadraticFilledMap c := funext he
  refine ⟨address e, componentAddress e, address_continuous e,
    address_surjective e, ?_, componentAddress_continuous e,
    componentAddress_surjective e, componentAddress_mk e⟩
  simpa only [hstep] using address_semiconj e

/-- The number of connected components is exactly the continuum for
every escaping-critical quadratic parameter. The upper bound uses the
actual embedding in the complex plane; the lower bound uses all binary
addresses, rather than just arbitrarily large finite component counts. -/
theorem filled_component_cardinality (c : ℂ) (hc : 0 < escape c 0) :
    Cardinal.mk (ConnectedComponents (quadraticFilled c)) = Cardinal.continuum := by
  obtain ⟨_, componentCode, _, _, _, _, hsurj, _⟩ := filled_binary_coding c hc
  apply le_antisymm
  · calc
      Cardinal.mk (ConnectedComponents (quadraticFilled c)) ≤
          Cardinal.mk (quadraticFilled c) :=
        Cardinal.mk_le_of_surjective ConnectedComponents.surjective_coe
      _ ≤ Cardinal.mk ℂ := Cardinal.mk_le_of_injective
        (Subtype.val_injective : Injective (Subtype.val : quadraticFilled c → ℂ))
      _ = Cardinal.continuum := Cardinal.mk_complex
  · have hb : Cardinal.mk (ℕ → Fin 2) = Cardinal.continuum := by
      simp only [Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.mk_nat,
        Cardinal.lift_id, Nat.cast_ofNat, Cardinal.two_power_aleph0]
    rw [← hb]
    exact Cardinal.mk_le_of_surjective hsurj

/-- A typeclass form of the component-cardinality theorem. -/
theorem filled_component_uncountable (c : ℂ) (hc : 0 < escape c 0) :
    Uncountable (ConnectedComponents (quadraticFilled c)) := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  obtain ⟨z, hz⟩ := sublevel_nonempty c 0 le_rfl
  have hzK : z ∈ quadraticFilled c := by
    rwa [sublevel_zero_eq_filled c] at hz
  letI : Nonempty (quadraticFilled c) := ⟨⟨z, hzK⟩⟩
  obtain ⟨e, _⟩ := filled_two_sheet c hc
  exact component_uncountable e

end LoopsQuadraticEscapeTree
