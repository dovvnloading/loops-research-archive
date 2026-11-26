import CompactBinaryCoding
import LeastSaturatedCarrier

/-!
# Connected fibers from coherent compact inverse cylinders

A compact binary splitting need not by itself have connected address fibers.
Here the inverse sections extend coherently to disjoint continuous branches
on a compact connected ambient space. If every nested cylinder limit lies in
the invariant compact set, then every address fiber is exactly one connected
component. Its component dynamics is conjugate to the full binary shift.
-/

namespace LoopsConnectedBinaryCoding

open Set Function LoopsCompactBinaryCoding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The compact ambient cylinder obtained by following a finite inverse word. -/
def cylinder (b : Fin 2 → X → X) (a : ℕ → Fin 2) : ℕ → Set X
  | 0 => univ
  | n + 1 => b (a 0) '' cylinder b (shift a) n

omit [TopologicalSpace X] in
theorem cylinder_antitone (b : Fin 2 → X → X) (a : ℕ → Fin 2) :
    Antitone (cylinder b a) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n generalizing a with
  | zero => exact subset_univ _
  | succ n ih => exact image_mono (ih (shift a))

theorem cylinder_compact [CompactSpace X] (b : Fin 2 → X → X)
    (hb : ∀ i, Continuous (b i)) (a : ℕ → Fin 2) (n : ℕ) :
    IsCompact (cylinder b a n) := by
  induction n generalizing a with
  | zero => exact isCompact_univ
  | succ n ih => exact (ih (shift a)).image (hb (a 0))

theorem cylinder_preconnected [PreconnectedSpace X] (b : Fin 2 → X → X)
    (hb : ∀ i, Continuous (b i)) (a : ℕ → Fin 2) (n : ℕ) :
    IsPreconnected (cylinder b a n) := by
  induction n generalizing a with
  | zero => exact isPreconnected_univ
  | succ n ih => exact (ih (shift a)).image _ (hb (a 0)).continuousOn

/-- The infinite ambient inverse cylinder retains connectedness. -/
theorem cylinder_limit_preconnected [CompactSpace X] [PreconnectedSpace X]
    [T2Space X] (b : Fin 2 → X → X) (hb : ∀ i, Continuous (b i))
    (a : ℕ → Fin 2) : IsPreconnected (⋂ n, cylinder b a n) := by
  apply LoopsLeastCarrier.directed_carrier_preconnected univ isCompact_univ
    (cylinder b a) (cylinder_compact b hb a) (cylinder_preconnected b hb a)
    (fun _ => subset_univ _)
  intro m n
  exact ⟨max m n, cylinder_antitone b a (le_max_left m n),
    cylinder_antitone b a (le_max_right m n)⟩

omit [TopologicalSpace X] in
/-- Coherence and disjoint inverse branches make ambient cylinder membership
equivalent to the prescribed finite itinerary on the invariant compact set. -/
theorem cylinder_mem_iff (j : Y → X) (e : Y ≃ₜ (Fin 2 × Y))
    (b : Fin 2 → X → X)
    (hbi : Injective (fun p : Fin 2 × X => b p.1 p.2))
    (hjb : ∀ i y, j (e.symm (i, y)) = b i (j y))
    (a : ℕ → Fin 2) (n : ℕ) (y : Y) :
    j y ∈ cylinder b a n ↔ ∀ k < n, address e y k = a k := by
  have hrep (y : Y) : j y = b (e y).1 (j (step e y)) := by
    calc
      j y = j (e.symm ((e y).1, (e y).2)) := by simp
      _ = b (e y).1 (j (step e y)) := hjb (e y).1 (e y).2
  induction n generalizing a y with
  | zero => simp [cylinder]
  | succ n ih =>
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hp : (a 0, x) = ((e y).1, j (step e y)) :=
        hbi (hxy.trans (hrep y))
      have hlabel : a 0 = (e y).1 := congrArg Prod.fst hp
      have hxj : x = j (step e y) := congrArg Prod.snd hp
      rw [hxj] at hx
      have htail := (ih (shift a) (step e y)).mp hx
      intro k hk
      cases k with
      | zero => exact hlabel.symm
      | succ k =>
        rw [address_succ]
        exact htail k (by omega)
    · intro h
      refine ⟨j (step e y), (ih (shift a) (step e y)).mpr ?_, ?_⟩
      · intro k hk
        exact (address_succ e y k).symm.trans (h (k+1) (by omega))
      · have hzero : (e y).1 = a 0 := h 0 (Nat.zero_lt_succ n)
        rw [← hzero]
        exact (hrep y).symm

omit [TopologicalSpace X] in
/-- The geometric nested limit is exactly the image of the entire address
fiber, including all its points rather than a selected representative. -/
theorem address_fiber_image (j : Y → X) (e : Y ≃ₜ (Fin 2 × Y))
    (b : Fin 2 → X → X)
    (hbi : Injective (fun p : Fin 2 × X => b p.1 p.2))
    (hjb : ∀ i y, j (e.symm (i, y)) = b i (j y))
    (hlim : ∀ a, (⋂ n, cylinder b a n) ⊆ range j) (a : ℕ → Fin 2) :
    j '' {y | address e y = a} = ⋂ n, cylinder b a n := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact mem_iInter.mpr fun n =>
      (cylinder_mem_iff j e b hbi hjb a n y).mpr fun k _ => congrFun hy k
  · intro x hx
    obtain ⟨y, rfl⟩ := hlim a hx
    refine ⟨y, funext fun k => ?_, rfl⟩
    exact (cylinder_mem_iff j e b hbi hjb a (k+1) y).mp
      (mem_iInter.mp hx (k+1)) k (Nat.lt_succ_self k)

/-- Connectedness of address fibers is a conclusion of the coherent ambient
construction, not a hypothesis on the compact invariant set. -/
theorem address_fiber_preconnected [CompactSpace X] [PreconnectedSpace X]
    [T2Space X] [CompactSpace Y]
    (j : Y → X) (hj : Continuous j) (hji : Injective j)
    (e : Y ≃ₜ (Fin 2 × Y)) (b : Fin 2 → X → X)
    (hb : ∀ i, Continuous (b i))
    (hbi : Injective (fun p : Fin 2 × X => b p.1 p.2))
    (hjb : ∀ i y, j (e.symm (i, y)) = b i (j y))
    (hlim : ∀ a, (⋂ n, cylinder b a n) ⊆ range j) (a : ℕ → Fin 2) :
    IsPreconnected {y | address e y = a} := by
  apply (hj.isClosedEmbedding hji).isEmbedding.isInducing.isPreconnected_image.mp
  rw [address_fiber_image j e b hbi hjb hlim a]
  exact cylinder_limit_preconnected b hb a

/-- Every infinite word has a nonempty connected fiber. -/
theorem address_fiber_connected [CompactSpace X] [PreconnectedSpace X]
    [T2Space X] [CompactSpace Y] [Nonempty Y]
    (j : Y → X) (hj : Continuous j) (hji : Injective j)
    (e : Y ≃ₜ (Fin 2 × Y)) (b : Fin 2 → X → X)
    (hb : ∀ i, Continuous (b i))
    (hbi : Injective (fun p : Fin 2 × X => b p.1 p.2))
    (hjb : ∀ i y, j (e.symm (i, y)) = b i (j y))
    (hlim : ∀ a, (⋂ n, cylinder b a n) ⊆ range j) (a : ℕ → Fin 2) :
    IsConnected {y | address e y = a} := by
  obtain ⟨y, hy⟩ := address_surjective e a
  exact ⟨⟨y, hy⟩, address_fiber_preconnected j hj hji e b hb hbi hjb hlim a⟩

/-- The itinerary fiber is precisely the actual connected component. -/
theorem component_eq_address_fiber [CompactSpace X] [PreconnectedSpace X]
    [T2Space X] [CompactSpace Y]
    (j : Y → X) (hj : Continuous j) (hji : Injective j)
    (e : Y ≃ₜ (Fin 2 × Y)) (b : Fin 2 → X → X)
    (hb : ∀ i, Continuous (b i))
    (hbi : Injective (fun p : Fin 2 × X => b p.1 p.2))
    (hjb : ∀ i y, j (e.symm (i, y)) = b i (j y))
    (hlim : ∀ a, (⋂ n, cylinder b a n) ⊆ range j) (y : Y) :
    connectedComponent y = {z | address e z = address e y} := by
  apply Subset.antisymm
  · intro z hz
    have hh : IsPreconnected ((address e) '' connectedComponent y) :=
      isPreconnected_connectedComponent.image _ (address_continuous e).continuousOn
    exact hh.subsingleton (mem_image_of_mem _ hz)
      (mem_image_of_mem _ mem_connectedComponent)
  · exact (address_fiber_preconnected j hj hji e b hb hbi hjb hlim
      (address e y)).subset_connectedComponent rfl

/-- A continuous binary factor with these geometric inverse cylinders is
an actual topological conjugacy after passing to connected components. -/
theorem component_conjugacy [CompactSpace X] [PreconnectedSpace X]
    [T2Space X] [CompactSpace Y] [Nonempty Y]
    (j : Y → X) (hj : Continuous j) (hji : Injective j)
    (e : Y ≃ₜ (Fin 2 × Y)) (b : Fin 2 → X → X)
    (hb : ∀ i, Continuous (b i))
    (hbi : Injective (fun p : Fin 2 × X => b p.1 p.2))
    (hjb : ∀ i y, j (e.symm (i, y)) = b i (j y))
    (hlim : ∀ a, (⋂ n, cylinder b a n) ⊆ range j) :
    ∃ E : ConnectedComponents Y ≃ₜ (ℕ → Fin 2),
      (∀ y, E (ConnectedComponents.mk y) = address e y) ∧
      Semiconj E (componentStep e) shift := by
  have hi : Injective (componentAddress e) := by
    intro q r hqr
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe r
    apply ConnectedComponents.coe_eq_coe'.2
    rw [component_eq_address_fiber j hj hji e b hb hbi hjb hlim z]
    exact hqr
  let E : ConnectedComponents Y ≃ₜ (ℕ → Fin 2) :=
    (Equiv.ofBijective (componentAddress e)
      ⟨hi, componentAddress_surjective e⟩).toHomeomorphOfContinuousClosed
      (componentAddress_continuous e) (componentAddress_continuous e).isClosedMap
  exact ⟨E, fun _ => rfl, componentAddress_semiconj e⟩

end LoopsConnectedBinaryCoding
