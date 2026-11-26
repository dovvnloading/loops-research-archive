import BinaryShiftPeriodic

/-!
# Topological exactness of the binary component model

Every nonempty open set of one-sided binary sequences maps onto the whole
sequence space under every sufficiently large shift iterate. A homeomorphic
conjugacy transfers this property to the original dynamical space.
-/

namespace LoopsBinaryShiftExactness

open Set Function LoopsCompactBinaryCoding LoopsBinaryShiftPeriodic

/-- Any open set contains a finite-prefix cylinder, whose sufficiently long
shift image is the entire binary sequence space. -/
theorem shift_open_eventually_onto (U : Set (ℕ → Fin 2))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, (shift^[n]) '' U = univ := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU a ha
  let N := I.sup id + 1
  refine ⟨N, ?_⟩
  intro n hn
  apply Set.eq_univ_of_forall
  intro target
  let b : ℕ → Fin 2 := fun k => if k < n then a k else target (k-n)
  refine ⟨b, hsub ?_, ?_⟩
  · intro k hk
    have hkN : k < N := by
      have h : k ≤ I.sup id := Finset.le_sup (f := id) hk
      dsimp [N]
      omega
    have hkn : k < n := lt_of_lt_of_le hkN hn
    change (if k < n then a k else target (k-n)) ∈ u k
    rw [if_pos hkn]
    exact (hu k hk).2
  · funext k
    rw [shift_iterate_apply]
    have hkn : ¬ k+n < n := by omega
    simp only [b, if_neg hkn, Nat.add_sub_cancel]

/-- Exactness transports through a homeomorphism intertwining the dynamics.
The original map is not assumed surjective or exact separately. -/
theorem conjugate_open_eventually_onto {X : Type*} [TopologicalSpace X]
    (f : X → X) (E : X ≃ₜ (ℕ → Fin 2)) (hE : Semiconj E f shift)
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, (f^[n]) '' U = univ := by
  obtain ⟨N, hN⟩ := shift_open_eventually_onto (E '' U)
    (E.isOpenMap U hU) (hne.image E)
  refine ⟨N, ?_⟩
  intro n hn
  apply Set.eq_univ_of_forall
  intro x
  have hx : E x ∈ (shift^[n]) '' (E '' U) := by
    rw [hN n hn]
    exact mem_univ _
  obtain ⟨b, ⟨y, hy, hEy⟩, hshift⟩ := hx
  refine ⟨y, hy, E.injective ?_⟩
  calc
    E ((f^[n]) y) = (shift^[n]) (E y) := hE.iterate_right n y
    _ = (shift^[n]) b := congrArg (shift^[n]) hEy
    _ = E x := hshift

/-- In particular every open source eventually meets every nonempty target
under all later iterates; the target need not itself be open. -/
theorem conjugate_eventual_intersection {X : Type*} [TopologicalSpace X]
    (f : X → X) (E : X ≃ₜ (ℕ → Fin 2)) (hE : Semiconj E f shift)
    (U V : Set X) (hU : IsOpen U) (hneU : U.Nonempty) (hneV : V.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, ((f^[n]) '' U ∩ V).Nonempty := by
  obtain ⟨N, hN⟩ := conjugate_open_eventually_onto f E hE U hU hneU
  refine ⟨N, ?_⟩
  intro n hn
  rw [hN n hn, univ_inter]
  exact hneV

end LoopsBinaryShiftExactness
