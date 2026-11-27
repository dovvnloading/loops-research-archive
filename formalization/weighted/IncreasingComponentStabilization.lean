import Mathlib

/-!
# Finite component records under an infinite sequence of enlargements

An increasing union of open sets does not create a component connection
that is absent at every finite stage. In a locally connected space this
follows from relative closedness of the union of the anchored components.
Consequently finitely many actual anchor/probe pairs have a common stage
after which their component relations agree with the final open union.

The index of that stage is existential. The theorem does not identify a
prescribed finite inspection horizon with a future-complete certificate.
-/

namespace LoopsIncreasingComponentStabilization

open Set Function

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

/-- The selected component commutes with an increasing open union.
The ambient sets may be disconnected; only their openness and the
initial anchor membership are required. -/
theorem connectedComponentIn_increasing_union (S : ℕ → Set X)
    (hmono : Monotone S) (hopen : ∀ m, IsOpen (S m))
    (x : X) (hx : x ∈ S 0) :
    connectedComponentIn (⋃ m, S m) x =
      ⋃ m, connectedComponentIn (S m) x := by
  let V : Set X := ⋃ m, S m
  let C : Set X := ⋃ m, connectedComponentIn (S m) x
  change connectedComponentIn V x = C
  have hCo : IsOpen C := isOpen_iUnion fun m => (hopen m).connectedComponentIn
  have hCV : C ⊆ connectedComponentIn V x := by
    intro z hz
    obtain ⟨m, hm⟩ := mem_iUnion.mp hz
    exact connectedComponentIn_mono x
      (show S m ⊆ V from fun _ hw => mem_iUnion_of_mem m hw) hm
  have hCx : x ∈ C := mem_iUnion_of_mem 0 (mem_connectedComponentIn hx)
  have hxV : x ∈ connectedComponentIn V x :=
    mem_connectedComponentIn (mem_iUnion_of_mem 0 hx)
  have hrel : closure C ∩ connectedComponentIn V x ⊆ C := by
    intro z hz
    have hzV : z ∈ V := connectedComponentIn_subset V x hz.2
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzV
    obtain ⟨w, hwj, hwC⟩ := mem_closure_iff.mp hz.1
      (connectedComponentIn (S j) z) (hopen j).connectedComponentIn
      (mem_connectedComponentIn hj)
    obtain ⟨i, hwi⟩ := mem_iUnion.mp hwC
    have hwiK : w ∈ connectedComponentIn (S (max i j)) x :=
      connectedComponentIn_mono x (hmono (le_max_left i j)) hwi
    have hwjK : w ∈ connectedComponentIn (S (max i j)) z :=
      connectedComponentIn_mono z (hmono (le_max_right i j)) hwj
    have hzK : z ∈ connectedComponentIn (S (max i j)) x := by
      rw [connectedComponentIn_eq hwiK, ← connectedComponentIn_eq hwjK]
      exact mem_connectedComponentIn (hmono (le_max_right i j) hj)
    exact mem_iUnion_of_mem (max i j) hzK
  exact Subset.antisymm
    (isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      hCo ⟨x, hxV, hCx⟩ hrel) hCV

private theorem finite_uniform_stage {ι : Type*} (A : Finset ι)
    (P : ι → ℕ → Prop) :
    (∀ i ∈ A, ∃ N : ℕ, ∀ m, N ≤ m → P i m) →
      ∃ N : ℕ, ∀ m, N ≤ m → ∀ i ∈ A, P i m := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨0, ?_⟩
      intro m hm i hi
      exact (Finset.notMem_empty i hi).elim
  | @insert a A ha ih =>
      intro hP
      obtain ⟨Na, hNa⟩ := hP a (Finset.mem_insert_self a A)
      obtain ⟨N, hN⟩ := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
      refine ⟨max Na N, ?_⟩
      intro m hm i hi
      rcases Finset.mem_insert.mp hi with hia | hiA
      · subst i
        exact hNa m ((le_max_left Na N).trans hm)
      · exact hN m ((le_max_right Na N).trans hm) i hiA

/-- A finite set of actual anchors and probes has an eventual exact
component relation, equal to its relation in the entire open union.
The stage is uniform in all pairs and in every later enlargement.
Only the anchors, not the probes, must be present initially. -/
theorem finite_anchor_relations_stabilize (S : ℕ → Set X)
    (hmono : Monotone S) (hopen : ∀ m, IsOpen (S m))
    (A B : Finset X) (hA : ∀ x ∈ A, x ∈ S 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ x ∈ A, ∀ y ∈ B,
      (y ∈ connectedComponentIn (S m) x ↔
        y ∈ connectedComponentIn (⋃ j, S j) x) := by
  classical
  let P : X × X → ℕ → Prop := fun p m =>
    p.2 ∈ connectedComponentIn (⋃ j, S j) p.1 →
      p.2 ∈ connectedComponentIn (S m) p.1
  have hP : ∀ p ∈ A.product B, ∃ N : ℕ, ∀ m, N ≤ m → P p m := by
    rintro ⟨x, y⟩ hp
    have hxA : x ∈ A := (Finset.mem_product.mp hp).1
    by_cases hxy : y ∈ connectedComponentIn (⋃ j, S j) x
    · have hxy' : y ∈ ⋃ j, connectedComponentIn (S j) x := by
        rw [← connectedComponentIn_increasing_union S hmono hopen x (hA x hxA)]
        exact hxy
      obtain ⟨N, hN⟩ := mem_iUnion.mp hxy'
      refine ⟨N, ?_⟩
      intro m hm _
      exact connectedComponentIn_mono x (hmono hm) hN
    · refine ⟨0, ?_⟩
      intro m hm h
      exact (hxy h).elim
  obtain ⟨N, hN⟩ := finite_uniform_stage (A.product B) P hP
  refine ⟨N, ?_⟩
  intro m hm x hxA y hyB
  constructor
  · intro h
    exact connectedComponentIn_mono x
      (show S m ⊆ ⋃ j, S j from fun _ hw => mem_iUnion_of_mem m hw) h
  · exact hN m hm (x, y) (Finset.mem_product.mpr ⟨hxA, hyB⟩)

/-- One stage works simultaneously for finitely many component
problems. In a fixed quadratic horizon the index can represent every
intermediate iterate, retaining all component relations together. -/
theorem finite_family_anchor_relations_stabilize {ι : Type*}
    (K : Finset ι) (S : ι → ℕ → Set X)
    (hmono : ∀ i ∈ K, Monotone (S i))
    (hopen : ∀ i ∈ K, ∀ m, IsOpen (S i m))
    (A B : ι → Finset X)
    (hA : ∀ i ∈ K, ∀ x ∈ A i, x ∈ S i 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ i ∈ K,
      ∀ x ∈ A i, ∀ y ∈ B i,
        (y ∈ connectedComponentIn (S i m) x ↔
          y ∈ connectedComponentIn (⋃ j, S i j) x) := by
  let P : ι → ℕ → Prop := fun i m =>
    ∀ x ∈ A i, ∀ y ∈ B i,
      (y ∈ connectedComponentIn (S i m) x ↔
        y ∈ connectedComponentIn (⋃ j, S i j) x)
  exact finite_uniform_stage K P (fun i hi =>
    finite_anchor_relations_stabilize (S i) (hmono i hi) (hopen i hi)
      (A i) (B i) (hA i hi))

/-- The stabilization theorem also captures every point of a finite
subset of the final anchored component inside one finite stage.
This is the form used for a finite polynomial inverse fiber. -/
theorem finite_subset_component_captured (S : ℕ → Set X)
    (hmono : Monotone S) (hopen : ∀ m, IsOpen (S m))
    (x : X) (hx : x ∈ S 0) (B : Finset X)
    (hB : ∀ y ∈ B, y ∈ connectedComponentIn (⋃ j, S j) x) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ y ∈ B,
      y ∈ connectedComponentIn (S m) x := by
  classical
  obtain ⟨N, hN⟩ := finite_anchor_relations_stabilize S hmono hopen
    ({x} : Finset X) B (by
      intro a ha
      have hax : a = x := Finset.mem_singleton.mp ha
      simpa only [hax] using hx)
  refine ⟨N, ?_⟩
  intro m hm y hy
  exact (hN m hm x (Finset.mem_singleton_self x) y hy).mpr (hB y hy)

end LoopsIncreasingComponentStabilization
