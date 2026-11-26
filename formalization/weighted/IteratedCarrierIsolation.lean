import Mathlib.Topology.Connected.Clopen
import Mathlib.Order.Monotone.Basic

/-!
# Exact isolation through every finite return horizon

A one-step open isolating neighborhood has an explicit recursive refinement
that isolates the carrier in every pullback through any prescribed finite
horizon. The windows are open and decreasing. No common neighborhood for
all infinite horizons, uniform clearance, or dynamical realization is
asserted.
-/

namespace LoopsIteratedCarrierIsolation

open Set Function

variable {X : Type*}

/-- The points whose first n orbit positions stay in the one-step window. -/
def isolationWindow (F : X → X) (V : Set X) : ℕ → Set X
  | 0 => univ
  | n + 1 => V ∩ F ⁻¹' isolationWindow F V n

/-- A forward-invariant carrier contained in the initial window remains
inside every finite recursive window. -/
theorem isolationWindow_contains (F : X → X) (V A : Set X)
    (hAV : A ⊆ V) (hFA : MapsTo F A A) (n : ℕ) :
    A ⊆ isolationWindow F V n := by
  induction n with
  | zero => exact Set.subset_univ A
  | succ n ih =>
    intro x hx
    exact ⟨hAV hx, ih (hFA hx)⟩

/-- One more required orbit position can only decrease the window. -/
theorem isolationWindow_succ_subset (F : X → X) (V : Set X) (n : ℕ) :
    isolationWindow F V (n + 1) ⊆ isolationWindow F V n := by
  induction n with
  | zero => exact Set.subset_univ _
  | succ n ih =>
    intro x hx
    exact ⟨hx.1, ih hx.2⟩

theorem isolationWindow_antitone (F : X → X) (V : Set X) :
    Antitone (isolationWindow F V) :=
  antitone_nat_of_succ_le (isolationWindow_succ_subset F V)

/-- One-step isolation propagates to the exact n-step pullback, including
the zero horizon. No topological assumptions are needed for this identity. -/
theorem isolationWindow_exact (F : X → X) (V A : Set X)
    (hiso : V ∩ F ⁻¹' A = A) (n : ℕ) :
    isolationWindow F V n ∩ (F^[n]) ⁻¹' A = A := by
  induction n with
  | zero =>
    ext x
    simp [isolationWindow]
  | succ n ih =>
    ext x
    change ((x ∈ V ∧ F x ∈ isolationWindow F V n) ∧
      (F^[n + 1]) x ∈ A) ↔ x ∈ A
    rw [Function.iterate_succ_apply]
    constructor
    · rintro ⟨⟨hxV, hxW⟩, hxF⟩
      have hFx : F x ∈ A := by
        have hx' : F x ∈ isolationWindow F V n ∩ (F^[n]) ⁻¹' A :=
          ⟨hxW, hxF⟩
        simpa only [ih] using hx'
      have hx' : x ∈ V ∩ F ⁻¹' A := ⟨hxV, hFx⟩
      simpa only [hiso] using hx'
    · intro hx
      have hx' : x ∈ V ∩ F ⁻¹' A := by
        simpa only [hiso] using hx
      have hFxA : F x ∈ A := hx'.2
      have hFx : F x ∈ isolationWindow F V n ∩ (F^[n]) ⁻¹' A := by
        rw [ih]
        exact hFxA
      exact ⟨⟨hx'.1, hFx.1⟩, hFx.2⟩

/-- The window for a fixed horizon isolates every earlier pullback as well. -/
theorem isolationWindow_horizon_exact (F : X → X) (V A : Set X)
    (hiso : V ∩ F ⁻¹' A = A) (H k : ℕ) (hk : k ≤ H) :
    isolationWindow F V H ∩ (F^[k]) ⁻¹' A = A := by
  have hH := isolationWindow_exact F V A hiso H
  have hK := isolationWindow_exact F V A hiso k
  ext x
  constructor
  · rintro ⟨hxH, hxF⟩
    have hxK : x ∈ isolationWindow F V k :=
      isolationWindow_antitone F V hk hxH
    have hx' : x ∈ isolationWindow F V k ∩ (F^[k]) ⁻¹' A :=
      ⟨hxK, hxF⟩
    simpa only [hK] using hx'
  · intro hx
    have hxH : x ∈ isolationWindow F V H ∩ (F^[H]) ⁻¹' A := by
      simpa only [hH] using hx
    have hxK : x ∈ isolationWindow F V k ∩ (F^[k]) ⁻¹' A := by
      simpa only [hK] using hx
    exact ⟨hxH.1, hxK.2⟩

variable [TopologicalSpace X]

/-- Every finite window is open for continuous dynamics and an open
one-step window. -/
theorem isolationWindow_isOpen (F : X → X) (V : Set X)
    (hF : Continuous F) (hV : IsOpen V) (n : ℕ) :
    IsOpen (isolationWindow F V n) := by
  induction n with
  | zero => exact isOpen_univ
  | succ n ih => exact hV.inter (ih.preimage hF)

/-- An actual open neighborhood simultaneously isolates all pullbacks
through a supplied finite horizon. The neighborhood may depend on H. -/
theorem finite_horizon_isolation (F : X → X) (V A : Set X)
    (hF : Continuous F) (hV : IsOpen V)
    (hiso : V ∩ F ⁻¹' A = A) (H : ℕ) :
    ∃ W : Set X, IsOpen W ∧ A ⊆ W ∧
      ∀ k ≤ H, W ∩ (F^[k]) ⁻¹' A = A := by
  refine ⟨isolationWindow F V H, isolationWindow_isOpen F V hF hV H, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ isolationWindow F V H ∩ (F^[H]) ⁻¹' A := by
      simpa only [isolationWindow_exact F V A hiso H] using hx
    exact hx'.1
  · intro k hk
    exact isolationWindow_horizon_exact F V A hiso H k hk

/-- A closed preconnected set isolated inside B by an ambient open
neighborhood is exactly the connected component of any of its points.
The ambient space and B need not be locally connected. -/
theorem connectedComponent_eq_of_open_isolation
    {A B V : Set X} {a : X}
    (hA : IsClosed A) (hpre : IsPreconnected A) (hV : IsOpen V)
    (ha : a ∈ A) (hiso : V ∩ B = A) :
    connectedComponentIn B a = A := by
  classical
  have hback : A ⊆ V ∩ B := by
    intro x hx
    simpa only [hiso] using hx
  have hAV : A ⊆ V := fun x hx => (hback hx).1
  have hAB : A ⊆ B := fun x hx => (hback hx).2
  have hcover : connectedComponentIn B a ⊆ A ∪ Vᶜ := by
    intro x hx
    by_cases hxV : x ∈ V
    · have hx' : x ∈ V ∩ B :=
        ⟨hxV, connectedComponentIn_subset B a hx⟩
      exact Or.inl (by simpa only [hiso] using hx')
    · exact Or.inr hxV
  have hdisjoint : connectedComponentIn B a ∩ (A ∩ Vᶜ) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    exact hx.2.2 (hAV hx.2.1)
  have hsplit := (isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_connectedComponentIn : IsPreconnected (connectedComponentIn B a)))
    A Vᶜ hA hV.isClosed_compl hcover hdisjoint
  apply Set.Subset.antisymm
  · rcases hsplit with h | h
    · exact h
    · exact False.elim ((h (mem_connectedComponentIn (hAB ha))) (hAV ha))
  · exact hpre.subset_connectedComponentIn ha hAB

/-- A closed preconnected one-step isolated invariant carrier is the
exact component of every finite iterated preimage through an anchor.
No inverse limit or fixed infinite-horizon neighborhood is asserted. -/
theorem iterated_preimage_component (F : X → X) (V A : Set X)
    (hF : Continuous F) (hA : IsClosed A) (hpre : IsPreconnected A)
    (hV : IsOpen V) (hiso : V ∩ F ⁻¹' A = A)
    (a : X) (ha : a ∈ A) (n : ℕ) :
    connectedComponentIn ((F^[n]) ⁻¹' A) a = A := by
  exact connectedComponent_eq_of_open_isolation hA hpre
    (isolationWindow_isOpen F V hF hV n) ha
    (isolationWindow_exact F V A hiso n)

end LoopsIteratedCarrierIsolation
