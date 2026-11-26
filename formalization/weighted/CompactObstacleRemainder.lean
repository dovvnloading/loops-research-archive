import Mathlib
import LeastSaturatedCarrier

/-!
# Compact ambient obstacle remainders

The retained carrier is a geometric subset. Compact separation of the
omitted inventory is stronger than individual absorption of each obstacle.
The directed-limit criterion detects exactly when that separation survives.
-/

namespace LoopsCompactRemainder

open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- The entire inventory is covered by the retained carrier and a disjoint
compact remainder. The remainder need not be prescribed in advance. -/
def HasRemainder (K U : Set X) : Prop :=
  ∃ E : Set X, IsCompact E ∧ Disjoint K E ∧ U ⊆ K ∪ E

/-- Compact separation is exactly the absence of accumulation of omitted
inventory at the carrier, provided the whole inventory lies in a compact set. -/
theorem remainder_iff_closure_disjoint (K U J : Set X)
    (hJ : IsCompact J) (hUJ : U ⊆ J) :
    HasRemainder K U ↔ Disjoint K (closure (U \ K)) := by
  constructor
  · rintro ⟨E, hE, hd, hcover⟩
    have hsub : U \ K ⊆ E := by
      intro x hx
      exact (hcover hx.1).resolve_left hx.2
    exact hd.mono_right (closure_minimal hsub hE.isClosed)
  · intro hd
    have hsub : closure (U \ K) ⊆ J :=
      closure_minimal (fun _ hx => hUJ hx.1) hJ.isClosed
    refine ⟨closure (U \ K), hJ.of_isClosed_subset isClosed_closure hsub, hd, ?_⟩
    intro x hx
    by_cases hk : x ∈ K
    · exact Or.inl hk
    · exact Or.inr (subset_closure ⟨hx, hk⟩)

/-- When the complete inventory is compact and the carrier is closed,
the omitted trace itself is the canonical compact remainder. -/
theorem remainder_iff_compact_difference (K U : Set X)
    (hU : IsCompact U) :
    HasRemainder K U ↔ IsCompact (U \ K) := by
  constructor
  · rintro ⟨E, hE, hd, hcover⟩
    have heq : U \ K = U ∩ E := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, (hcover hx.1).resolve_left hx.2⟩
      · intro hx
        exact ⟨hx.1, fun hk => (Set.disjoint_left.mp hd) hk hx.2⟩
    rw [heq]
    exact hU.inter_right hE.isClosed
  · intro h
    refine ⟨U \ K, h, ?_, ?_⟩
    · exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
    · intro x hx
      by_cases hk : x ∈ K
      · exact Or.inl hk
      · exact Or.inr ⟨hx, hk⟩

/-- A compact whole inventory automatically yields a relatively closed
omitted trace whenever it admits a separated remainder. Every connected
obstacle in that inventory is then entirely retained or entirely omitted. -/
theorem connected_inventory_obstacle_absorbed
    (K U A : Set X) (hK : IsClosed K) (h : HasRemainder K U)
    (hA : IsPreconnected A) (hAU : A ⊆ U)
    (hmeet : (K ∩ A).Nonempty) : A ⊆ K := by
  obtain ⟨E, hE, hd, hcover⟩ := h
  exact LoopsLeastCarrier.connected_obstacle_forced K E A hK hE.isClosed hd
    hA (hAU.trans hcover) hmeet

/-- The canonical omitted traces form forward-compatible compact
remainders, with absorption into the next carrier allowed. This is an
exact one-arrow result, so it applies to every arrow of a finite forest. -/
theorem canonical_remainder_forward {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (K U : Set X) (L V : Set Y)
    (hU : IsCompact U) (hV : IsCompact V)
    (hsrc : HasRemainder K U) (htgt : HasRemainder L V)
    (hmap : f '' U ⊆ L ∪ V) :
    IsCompact (U \ K) ∧ IsCompact (V \ L) ∧
      f '' (U \ K) ⊆ L ∪ (V \ L) := by
  refine ⟨(remainder_iff_compact_difference K U hU).mp hsrc,
    (remainder_iff_compact_difference L V hV).mp htgt, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hy := hmap (show f x ∈ f '' U from ⟨x, hx.1, rfl⟩)
  by_cases hl : f x ∈ L
  · exact Or.inl hl
  · exact Or.inr ⟨hy.resolve_left hl, hl⟩

/-- Exact directed-limit criterion: separation of the limit carrier holds
if and only if some stage already has the final trace on the inventory.
Neither shrinking carriers nor stagewise compact separation alone suffice. -/
theorem directed_remainder_iff_stabilizes {ι : Type*} [Nonempty ι]
    (K : ι → Set X) (U : Set X)
    (hc : ∀ i, IsClosed (K i)) (hd : Directed (· ⊇ ·) K)
    (hs : ∀ i, HasRemainder (K i) U) :
    HasRemainder (⋂ i, K i) U ↔
      ∃ i, U ∩ K i = U ∩ (⋂ i, K i) := by
  constructor
  · rintro ⟨E, hE, hdis, hcover⟩
    have he : E ∩ (⋂ i, K i) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (Set.disjoint_left.mp hdis) hx.2 hx.1
    obtain ⟨i, hi⟩ := hE.elim_directed_family_closed K hc he hd
    refine ⟨i, Subset.antisymm ?_ ?_⟩
    · intro x hx
      refine ⟨hx.1, ?_⟩
      rcases hcover hx.1 with hlim | hE'
      · exact hlim
      · have hx' : x ∈ E ∩ K i := ⟨hE', hx.2⟩
        rw [hi] at hx'
        exact hx'.elim
    · intro x hx
      exact ⟨hx.1, mem_iInter.mp hx.2 i⟩
  · rintro ⟨i, hi⟩
    obtain ⟨E, hE, hdis, hcover⟩ := hs i
    refine ⟨E, hE, hdis.mono_left (iInter_subset K i), ?_⟩
    intro x hx
    rcases hcover hx with hk | he
    · have hx' : x ∈ U ∩ K i := ⟨hx, hk⟩
      rw [hi] at hx'
      exact Or.inl hx'.2
    · exact Or.inr he

/-- The criterion specializes to a true quadratic arrow, without
substituting a symbolic map for the physical complex polynomial. -/
theorem quadratic_canonical_remainder_forward (c : ℂ)
    (K U L V : Set ℂ) (hU : IsCompact U) (hV : IsCompact V)
    (hsrc : HasRemainder K U) (htgt : HasRemainder L V)
    (hmap : (fun z : ℂ => z^2+c) '' U ⊆ L ∪ V) :
    IsCompact (U \ K) ∧ IsCompact (V \ L) ∧
      (fun z : ℂ => z^2+c) '' (U \ K) ⊆ L ∪ (V \ L) :=
  canonical_remainder_forward _ K U L V hU hV hsrc htgt hmap

end LoopsCompactRemainder
