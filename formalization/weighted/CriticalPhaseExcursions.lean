import CriticalPhaseCensus

/-!
# The intrinsic regular-excursion inventory

The index consists of the actual nonempty connected components of the
regular locus in its original topology. No excursion partition is supplied
by the caller. Local connectedness makes these components open.
-/

namespace LoopsCriticalPhase

open Set Function

variable {X : Type*} [TopologicalSpace X]

/-- Actual nonempty connected components of the regular locus. -/
def RegularExcursions (R : Set X) :=
  {U : Set X // ∃ x ∈ R, U = connectedComponentIn R x}

/-- Every phase cut is exactly an independent Boolean choice on the
actual connected components of the open regular locus. -/
theorem phaseCut_regularExcursions_equiv [LocallyConnectedSpace X]
    (R : Set X) (hR : IsOpen R) :
    Nonempty (PhaseCut R ≃ (RegularExcursions R → Bool)) := by
  let U : RegularExcursions R → Set X := fun C => C.val
  have hopen (C : RegularExcursions R) : IsOpen (U C) := by
    obtain ⟨x, hx, hC⟩ := C.property
    change IsOpen C.val
    rw [hC]
    exact hR.connectedComponentIn
  have hconn (C : RegularExcursions R) : IsPreconnected (U C) := by
    obtain ⟨x, hx, hC⟩ := C.property
    change IsPreconnected C.val
    rw [hC]
    exact isPreconnected_connectedComponentIn
  have hne (C : RegularExcursions R) : (U C).Nonempty := by
    obtain ⟨x, hx, hC⟩ := C.property
    change C.val.Nonempty
    rw [hC]
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hdis : Pairwise (fun C D => Disjoint (U C) (U D)) := by
    intro C D hCD
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    obtain ⟨x, hx, hC⟩ := C.property
    obtain ⟨y, hy, hD⟩ := D.property
    change z ∈ C.val at hzC
    change z ∈ D.val at hzD
    rw [hC] at hzC
    rw [hD] at hzD
    have heq : C.val = D.val := by
      rw [hC, hD]
      exact (connectedComponentIn_eq hzC).trans (connectedComponentIn_eq hzD).symm
    exact hCD (Subtype.ext heq)
  have hcover : R = ⋃ C, U C := by
    ext z
    constructor
    · intro hz
      exact mem_iUnion.mpr
        ⟨⟨connectedComponentIn R z, z, hz, rfl⟩, mem_connectedComponentIn hz⟩
    · intro hz
      obtain ⟨C, hzC⟩ := mem_iUnion.mp hz
      obtain ⟨x, hx, hC⟩ := C.property
      change z ∈ C.val at hzC
      rw [hC] at hzC
      exact connectedComponentIn_subset R x hzC
  obtain ⟨e, _⟩ := phaseCut_excursion_equiv R U hopen hconn hne hdis hcover
  exact ⟨e⟩

/-- The exact finite census uses the canonical component inventory. -/
theorem phaseCut_regularExcursions_count [LocallyConnectedSpace X]
    (R : Set X) (hR : IsOpen R) [Fintype (RegularExcursions R)] :
    Nat.card (PhaseCut R) = 2 ^ Fintype.card (RegularExcursions R) := by
  classical
  obtain ⟨e⟩ := phaseCut_regularExcursions_equiv R hR
  calc
    Nat.card (PhaseCut R) = Nat.card (RegularExcursions R → Bool) :=
      Nat.card_congr e
    _ = 2 ^ Fintype.card (RegularExcursions R) := by
      simp [Nat.card_eq_fintype_card]

end LoopsCriticalPhase
