import QuadraticCylinderRamification

/-!
# Actual quadratic component fiber degrees

A connected pullback component has either disjoint signed inverse
sheets or a reflection-invariant sheet. No simple connectivity of
the target is assumed.
-/

namespace LoopsQuadraticComponentFiberDegree

open Set Function Classical
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticCylinderRamification LoopsStationarySeparatorTransport

noncomputable section

/-- A single reflected pair forces the entire component to be
reflection invariant. -/
theorem even_component_reflection_of_pair (F : ℂ → ℂ) (V : Set ℂ)
    (heven : ∀ z, F (-z) = F z) (x a : ℂ)
    (ha : a ∈ connectedComponentIn (F ⁻¹' V) x)
    (hna : -a ∈ connectedComponentIn (F ⁻¹' V) x) :
    ∀ z ∈ connectedComponentIn (F ⁻¹' V) x,
      -z ∈ connectedComponentIn (F ⁻¹' V) x := by
  let C := connectedComponentIn (F ⁻¹' V) x
  have hconn : IsPreconnected ((fun w : ℂ => -w) '' C) :=
    isPreconnected_connectedComponentIn.image _ continuous_neg.continuousOn
  have hhit : -a ∈ (fun w : ℂ => -w) '' C := ⟨a, ha, rfl⟩
  have hsub : (fun w : ℂ => -w) '' C ⊆ F ⁻¹' V := by
    rintro _ ⟨w, hw, rfl⟩
    change F (-w) ∈ V
    rw [heven]
    exact connectedComponentIn_subset (F ⁻¹' V) x hw
  have h := hconn.subset_connectedComponentIn hhit hsub
  rw [← connectedComponentIn_eq hna] at h
  intro z hz
  exact h ⟨z, hz, rfl⟩

theorem quadratic_eq_or_neg (c a b : ℂ) (h : quad c a = quad c b) :
    a = b ∨ a = -b := by
  change a^2+c = b^2+c at h
  have hp : (a-b)*(a+b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hp with hp | hp
  · exact Or.inl (sub_eq_zero.mp hp)
  · exact Or.inr (by linear_combination hp)

/-- Outside the invariant case the first quadratic step is
globally injective on the actual pullback component. -/
theorem quadratic_component_nonsymmetric_inj (c : ℂ) (n : ℕ)
    (V : Set ℂ) (x : ℂ)
    (hn : ¬ (∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x)) :
    InjOn (quad c) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) := by
  intro a ha b hb he
  rcases quadratic_eq_or_neg c a b he with hab | hab
  · exact hab
  · exfalso
    apply hn
    have hna : -b ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x := hab ▸ ha
    exact even_component_reflection_of_pair ((quad c)^[n+1]) V
      (quadratic_positive_iterate_even c (n+1) (by omega)) x b hb hna

/-- Exact first-step transport of the actual finite localized fiber,
with no univalence or simple connectivity assumption. -/
theorem quadratic_component_fiber_image (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V) :
    (localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y).image
      (quad c) =
    localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y := by
  classical
  let f := quad c
  let C := connectedComponentIn (f^[n+1] ⁻¹' V) x
  let D := connectedComponentIn (f^[n] ⁻¹' V) (f x)
  have hfirst : f '' C = D := by
    simpa only [Function.iterate_one] using
      quadratic_prefix_component_image c n 1 V hVo x hx
  change (localFiber c (n+1) C y).image f = localFiber c n D y
  ext w
  simp only [Finset.mem_image, mem_localFiber]
  constructor
  · rintro ⟨z, ⟨hz, hzy⟩, rfl⟩
    have hw' : f z ∈ f '' C := ⟨z, hz, rfl⟩
    have hw : f z ∈ D := hfirst ▸ hw'
    exact ⟨hw, by simpa only [Function.iterate_succ_apply] using hzy⟩
  · rintro ⟨hw, hwy⟩
    have hw' : w ∈ f '' C := hfirst.symm ▸ hw
    obtain ⟨z, hz, rfl⟩ := hw'
    exact ⟨z, ⟨hz, by simpa only [Function.iterate_succ_apply] using hwy⟩, rfl⟩

/-- A non-reflection-invariant component preserves the entire
tail fiber cardinality, even for a critical target. -/
theorem quadratic_component_nonsymmetric_count (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V)
    (hn : ¬ (∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x)) :
    (localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y).card =
    (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y).card := by
  classical
  let C := connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
  let A := localFiber c (n+1) C y
  have hi := quadratic_component_nonsymmetric_inj c n V x hn
  have hAi : InjOn (quad c) (↑A : Set ℂ) := by
    intro a ha b hb hab
    exact hi ((mem_localFiber c (n+1) C y a).mp ha).1
      ((mem_localFiber c (n+1) C y b).mp hb).1 hab
  have he := Finset.card_image_of_injOn hAi
  simpa only [A, C, quadratic_component_fiber_image c n V hVo x y hx] using he.symm

/-- The invariant case doubles the actual tail fiber, with exactly
one lost point if the tail contains the critical value over y. -/
theorem quadratic_component_symmetric_count (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V)
    (hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) :
    (localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y).card +
      (if c ∈ localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y
        then 1 else 0) =
    2 * (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y).card := by
  classical
  let f := quad c
  let C := connectedComponentIn (f^[n+1] ⁻¹' V) x
  let D := connectedComponentIn (f^[n] ⁻¹' V) (f x)
  let B := localFiber c n D y
  have hfirst : f '' C = D := by
    simpa only [Function.iterate_one] using
      quadratic_prefix_component_image c n 1 V hVo x hx
  have hposmem (w : ℂ) : fiberRoot c w ∈ C ↔ w ∈ D := by
    constructor
    · intro hw
      rw [← hfirst]
      exact ⟨fiberRoot c w, hw, fiberRoot_spec c w⟩
    · intro hw
      have hw' : w ∈ f '' C := hfirst.symm ▸ hw
      obtain ⟨a, ha, haw⟩ := hw'
      have he : f a = f (fiberRoot c w) :=
        haw.trans (fiberRoot_spec c w).symm
      rcases quadratic_eq_or_neg c a (fiberRoot c w) he with h | h
      · exact h ▸ ha
      · have h' : -a ∈ C := hs a ha
        rw [h, neg_neg] at h'
        exact h'
  have hnegmem (w : ℂ) : -fiberRoot c w ∈ C ↔ w ∈ D := by
    constructor
    · intro hw
      have h : -(-fiberRoot c w) ∈ C := hs _ hw
      rw [neg_neg] at h
      exact (hposmem w).mp h
    · intro hw
      exact hs _ ((hposmem w).mpr hw)
  have hpos : (globalFiber c n y).filter (fun w => fiberRoot c w ∈ C) = B := by
    ext w
    simp only [B, Finset.mem_filter, mem_globalFiber, mem_localFiber, hposmem]
    exact and_comm
  have hneg : ((globalFiber c n y).erase c).filter (fun w => -fiberRoot c w ∈ C) =
      B.erase c := by
    ext w
    simp only [B, Finset.mem_filter, Finset.mem_erase, mem_globalFiber,
      mem_localFiber, hnegmem]
    tauto
  change (localFiber c (n+1) C y).card + (if c ∈ B then 1 else 0) = 2 * B.card
  rw [localFiber_signed_count, hpos, hneg]
  by_cases hc : c ∈ B
  · rw [if_pos hc, Finset.card_erase_of_mem hc]
    have hp : 0 < B.card := Finset.card_pos.mpr ⟨c, hc⟩
    omega
  · rw [if_neg hc, Finset.erase_eq_of_notMem hc]
    omega

end
end LoopsQuadraticComponentFiberDegree
