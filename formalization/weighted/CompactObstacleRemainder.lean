import Mathlib
import LeastSaturatedCarrier
import ChebyshevFibers

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
  have hcov : A ⊆ K ∪ E := hAU.trans hcover
  intro x hx
  by_contra hxK
  obtain ⟨a, haK, haA⟩ := hmeet
  have haE : a ∉ E := fun h => (Set.disjoint_left.mp hd) haK h
  have hsep : A ⊆ Eᶜ ∪ Kᶜ := by
    intro z hz
    by_cases hzK : z ∈ K
    · exact Or.inl (fun h => (Set.disjoint_left.mp hd) hzK h)
    · exact Or.inr hzK
  obtain ⟨z, hzA, hzE, hzK⟩ := hA Eᶜ Kᶜ hE.isClosed.isOpen_compl
    hK.isOpen_compl hsep ⟨a, haA, haE⟩ ⟨x, hx, hxK⟩
  exact (hcov hzA).elim hzK hzE

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


/-- If only the ambient bound is compact, the least closed omitted trace
still propagates correctly through a continuous physical arrow. -/
theorem closure_remainder_forward {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (K U : Set X) (L V : Set Y)
    (hL : IsClosed L) (hmap : f '' U ⊆ L ∪ V) :
    f '' closure (U \ K) ⊆ L ∪ closure (V \ L) := by
  have hsub : U \ K ⊆ f ⁻¹' (L ∪ closure (V \ L)) := by
    intro x hx
    change f x ∈ L ∪ closure (V \ L)
    have hy := hmap (show f x ∈ f '' U from ⟨x, hx.1, rfl⟩)
    by_cases hl : f x ∈ L
    · exact Or.inl hl
    · exact Or.inr (subset_closure ⟨hy.resolve_left hl, hl⟩)
  have hclosed : IsClosed (f ⁻¹' (L ∪ closure (V \ L))) :=
    (hL.union isClosed_closure).preimage hf
  rintro y ⟨x, hx, rfl⟩
  exact closure_minimal hsub hclosed hx

/-- The closure is the least compact remainder whenever separation
is possible and the inventory lies in a compact ambient set. -/
theorem least_compact_remainder (K U J : Set X)
    (hJ : IsCompact J) (hUJ : U ⊆ J) (h : HasRemainder K U) :
    IsCompact (closure (U \ K)) ∧ Disjoint K (closure (U \ K)) ∧
      U ⊆ K ∪ closure (U \ K) ∧
      ∀ E : Set X, IsCompact E → U ⊆ K ∪ E → closure (U \ K) ⊆ E := by
  have hd := (remainder_iff_closure_disjoint K U J hJ hUJ).mp h
  refine ⟨hJ.of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ hx => hUJ hx.1) hJ.isClosed), hd, ?_, ?_⟩
  · intro x hx
    by_cases hk : x ∈ K
    · exact Or.inl hk
    · exact Or.inr (subset_closure ⟨hx, hk⟩)
  · intro E hE hcover
    apply closure_minimal _ hE.isClosed
    intro x hx
    exact (hcover hx.1).resolve_left hx.2

/-!
## A physical compact carrier obstruction at c = -2

The ambient bounded-orbit set is the actual real segment for the
Chebyshev quadratic, as established in ChebyshevFibers.
-/

open LoopsParabolic

noncomputable section

def reciprocalRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem reciprocalRadius_pos (n : ℕ) : 0 < reciprocalRadius n := by
  unfold reciprocalRadius
  positivity

private theorem reciprocalRadius_strictAnti : StrictAnti reciprocalRadius := by
  intro m n hmn
  unfold reciprocalRadius
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hn : 0 < (n : ℝ) + 1 := by positivity
  apply (div_lt_div_iff₀ hn hm).2
  have hcast : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  nlinarith

def chebyshevCarrier (n : ℕ) : Set ℂ := realSegment (reciprocalRadius n)

def chebyshevInventory : Set ℂ :=
  closure (range (fun n : ℕ => (reciprocalRadius n : ℂ)))

private theorem realSegment_mono_local {a b : ℝ} (h : a ≤ b) :
    realSegment a ⊆ realSegment b := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, ⟨by linarith [hx.1], hx.2.trans h⟩, rfl⟩

private theorem radius_point_mem_carrier (n : ℕ) :
    (reciprocalRadius n : ℂ) ∈ chebyshevCarrier n :=
  ⟨reciprocalRadius n, ⟨by linarith [reciprocalRadius_pos n], le_rfl⟩, rfl⟩

private theorem radius_point_not_mem_next (n : ℕ) :
    (reciprocalRadius n : ℂ) ∉ chebyshevCarrier (n+1) := by
  intro h
  have hle := (mem_realSegment_iff.mp h).2.2
  change reciprocalRadius n ≤ reciprocalRadius (n+1) at hle
  exact (not_lt_of_ge hle) (reciprocalRadius_strictAnti (Nat.lt_succ_self n))

private theorem carrier_zero (n : ℕ) : (0 : ℂ) ∈ chebyshevCarrier n := by
  exact ⟨0, ⟨by linarith [reciprocalRadius_pos n],
    (reciprocalRadius_pos n).le⟩, by simp⟩

/-- The inventory is compact and belongs to the true bounded-orbit set
of the Chebyshev quadratic. -/
theorem chebyshev_inventory_compact :
    IsCompact chebyshevInventory ∧
      ∀ z ∈ chebyshevInventory, LoopsChebyshev.BoundedOrbit z := by
  have hsub : chebyshevInventory ⊆ realSegment 2 := by
    apply closure_minimal _ (realSegment_compact 2).isClosed
    rintro z ⟨n, rfl⟩
    have hle := reciprocalRadius_strictAnti.antitone (Nat.zero_le n)
    have hzero : reciprocalRadius 0 = 1 := by norm_num [reciprocalRadius]
    rw [hzero] at hle
    exact realSegment_mono_local (by linarith : reciprocalRadius n ≤ 2)
      (radius_point_mem_carrier n)
  exact ⟨(realSegment_compact 2).of_isClosed_subset isClosed_closure hsub,
    fun z hz => (LoopsChebyshev.bounded_iff_realSegment z).mpr (hsub hz)⟩

/-- Each finite stage is a compact connected physical carrier containing
the critical point, with a compact separated (indeed finite) remainder. -/
theorem chebyshev_stage_admissible (n : ℕ) :
    IsCompact (chebyshevCarrier n) ∧ IsConnected (chebyshevCarrier n) ∧
      (0 : ℂ) ∈ chebyshevCarrier n ∧
      (∀ z ∈ chebyshevCarrier n, LoopsChebyshev.BoundedOrbit z) ∧
      HasRemainder (chebyshevCarrier n) chebyshevInventory := by
  have hc := realSegment_compact (reciprocalRadius n)
  have hp := realSegment_connected (reciprocalRadius_pos n).le
  have hle := reciprocalRadius_strictAnti.antitone (Nat.zero_le n)
  have hzero : reciprocalRadius 0 = 1 := by norm_num [reciprocalRadius]
  rw [hzero] at hle
  have hsub : chebyshevCarrier n ⊆ realSegment 2 :=
    realSegment_mono_local (by linarith)
  refine ⟨hc, hp, carrier_zero n,
    fun z hz => (LoopsChebyshev.bounded_iff_realSegment z).mpr (hsub hz), ?_⟩
  let E : Set ℂ := range (fun k : Fin n => (reciprocalRadius k.val : ℂ))
  have hE : IsCompact E :=
    (Set.finite_range (fun k : Fin n => (reciprocalRadius k.val : ℂ))).isCompact
  have hd : Disjoint (chebyshevCarrier n) E := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨k, rfl⟩
    have hle' := (mem_realSegment_iff.mp hz).2.2
    change reciprocalRadius k.val ≤ reciprocalRadius n at hle'
    exact (not_lt_of_ge hle') (reciprocalRadius_strictAnti k.isLt)
  refine ⟨E, hE, hd, ?_⟩
  apply closure_minimal _ (hc.isClosed.union hE.isClosed)
  rintro z ⟨k, rfl⟩
  by_cases hk : k < n
  · exact Or.inr ⟨⟨k, hk⟩, rfl⟩
  · exact Or.inl (realSegment_mono_local
      (reciprocalRadius_strictAnti.antitone (le_of_not_gt hk)) (radius_point_mem_carrier k))

/-- The intersection of all these physical carriers is precisely the
critical point. -/
theorem chebyshev_carrier_intersection :
    (⋂ n, chebyshevCarrier n) = ({0} : Set ℂ) := by
  ext z
  constructor
  · intro hz
    have him := (mem_realSegment_iff.mp (mem_iInter.mp hz 0)).1
    have hre : z.re = 0 := by
      by_contra hne
      have hpos : 0 < |z.re| := abs_pos.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / |z.re|)
      have hmul := (div_lt_iff₀ hpos).mp hn
      have hsmall : reciprocalRadius n < |z.re| := by
        unfold reciprocalRadius
        apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
        nlinarith
      have hm := (mem_realSegment_iff.mp (mem_iInter.mp hz n)).2
      have habs : |z.re| ≤ reciprocalRadius n := abs_le.mpr hm
      exact (not_lt_of_ge habs) hsmall
    exact mem_singleton_iff.mpr (Complex.ext hre him)
  · intro hz
    have hz' : z = 0 := mem_singleton_iff.mp hz
    subst z
    exact mem_iInter.mpr carrier_zero

/-- Every stage passes compact separation, but the true critical-point
limit fails it: at every stage a new inventory point is still retained. -/
theorem chebyshev_limit_remainder_failure :
    ¬ HasRemainder ({0} : Set ℂ) chebyshevInventory := by
  intro h
  rw [← chebyshev_carrier_intersection] at h
  have hd : Directed (· ⊇ ·) chebyshevCarrier := by
    intro i j
    exact ⟨max i j, realSegment_mono_local
      (reciprocalRadius_strictAnti.antitone (le_max_left i j)),
      realSegment_mono_local (reciprocalRadius_strictAnti.antitone (le_max_right i j))⟩
  obtain ⟨n, hn⟩ := (directed_remainder_iff_stabilizes
    chebyshevCarrier chebyshevInventory
    (fun i => (chebyshev_stage_admissible i).1.isClosed) hd
    (fun i => (chebyshev_stage_admissible i).2.2.2.2)).mp h
  have hp : (reciprocalRadius n : ℂ) ∈ chebyshevInventory ∩ chebyshevCarrier n :=
    ⟨subset_closure ⟨n, rfl⟩, radius_point_mem_carrier n⟩
  rw [hn] at hp
  exact radius_point_not_mem_next n (mem_iInter.mp hp.2 (n+1))

/-- A least connected compact carrier containing the actual critical
point need not exist when compact separation of the inventory is imposed.
This is an obstruction inside the true bounded-orbit set at c = -2. -/
theorem chebyshev_no_least_separated_carrier :
    ¬ ∃ K : Set ℂ,
      IsCompact K ∧ IsConnected K ∧ (0 : ℂ) ∈ K ∧
      (∀ z ∈ K, LoopsChebyshev.BoundedOrbit z) ∧
      HasRemainder K chebyshevInventory ∧
      ∀ L : Set ℂ, IsCompact L → IsConnected L → (0 : ℂ) ∈ L →
        (∀ z ∈ L, LoopsChebyshev.BoundedOrbit z) →
        HasRemainder L chebyshevInventory → K ⊆ L := by
  rintro ⟨K, _, _, h0, _, hK, hleast⟩
  have hsub : K ⊆ ⋂ n, chebyshevCarrier n := by
    intro x hx
    apply mem_iInter.mpr
    intro n
    obtain ⟨hc, hp, hz, hb, hr⟩ := chebyshev_stage_admissible n
    exact hleast _ hc hp hz hb hr hx
  rw [chebyshev_carrier_intersection] at hsub
  have heq : K = ({0} : Set ℂ) := Subset.antisymm hsub (singleton_subset_iff.mpr h0)
  rw [heq] at hK
  exact chebyshev_limit_remainder_failure hK

end

end LoopsCompactRemainder
