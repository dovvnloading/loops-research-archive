import Mathlib

/-!
# Proof-used predecessor recognition without local connectivity

Connected components are taken in the actual carrier. A marked root contact
and one point in the selected limb at each intermediate level suffice, provided
the restriction supplies connected endpoint sets with the stated forward maps.
The critical-limb inverse branch is a geometric input.
-/

namespace LoopsStationaryProofUsedItinerary

open Set

variable {X : Type*} [TopologicalSpace X]

def limb (a l : X) : Set X := connectedComponentIn ({a} : Set X)ᶜ l

theorem limb_avoids_root (a l : X) : a ∉ limb a l := by
  intro ha
  exact connectedComponentIn_subset ({a} : Set X)ᶜ l ha (mem_singleton a)

/-- One genuine limb witness suffices for a connected set avoiding the root. -/
theorem connected_in_limb_of_hit (a l : X) (E : Set X)
    (hE : IsPreconnected E) (havoid : a ∉ E)
    (hhit : (E ∩ limb a l).Nonempty) : E ⊆ limb a l := by
  obtain ⟨z, hzE, hzL⟩ := hhit
  have hsub : E ⊆ ({a} : Set X)ᶜ := by
    intro y hy hy'
    have he : y = a := hy'
    exact havoid (he ▸ hy)
  have he := hE.subset_connectedComponentIn hzE hsub
  change z ∈ connectedComponentIn ({a} : Set X)ᶜ l at hzL
  rw [← connectedComponentIn_eq hzL] at he
  exact he

/-- Exact recognition of the full ambient pullback component on the
critical inverse branch, even when the target itself is disconnected. -/
theorem inverse_branch_component (F g : X → X) (a l : X)
    (S : Set X) (x : X)
    (hF : Continuous F) (hfix : F a = a)
    (hg : ContinuousOn g (limb a l))
    (hgm : MapsTo g (limb a l) (limb a l))
    (hsection : ∀ y ∈ limb a l, F (g y) = y)
    (hleft : ∀ z ∈ limb a l, F z ∈ limb a l → g (F z) = z)
    (hS : S ⊆ limb a l) (hx : x ∈ S) :
    connectedComponentIn (F ⁻¹' S) (g x) =
      g '' connectedComponentIn S x := by
  let C := connectedComponentIn (F ⁻¹' S) (g x)
  have hxL : x ∈ limb a l := hS hx
  have hxC : g x ∈ C := mem_connectedComponentIn (show F (g x) ∈ S by
    rw [hsection x hxL]
    exact hx)
  have hCsub : C ⊆ F ⁻¹' S := connectedComponentIn_subset _ _
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCavoid : a ∉ C := by
    intro ha
    have hFa : F a ∈ S := hCsub ha
    rw [hfix] at hFa
    exact limb_avoids_root a l (hS hFa)
  have hCL : C ⊆ limb a l :=
    connected_in_limb_of_hit a l C hCpre hCavoid ⟨g x, hxC, hgm hxL⟩
  have hFsub : F '' C ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hCsub hz
  have hFx : x ∈ F '' C := ⟨g x, hxC, hsection x hxL⟩
  have hFimg : F '' C ⊆ connectedComponentIn S x :=
    (hCpre.image F hF.continuousOn).subset_connectedComponentIn hFx hFsub
  apply Subset.antisymm
  · intro z hz
    exact ⟨F z, hFimg ⟨z, hz, rfl⟩, hleft z (hCL hz) (hS (hCsub hz))⟩
  · have hpre : IsPreconnected (g '' connectedComponentIn S x) :=
      isPreconnected_connectedComponentIn.image g
        (hg.mono ((connectedComponentIn_subset S x).trans hS))
    apply hpre.subset_connectedComponentIn
    · exact ⟨x, mem_connectedComponentIn hx, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyS := connectedComponentIn_subset S x hy
      change F (g y) ∈ S
      rw [hsection y (hS hyS)]
      exact hyS

/-- The first predecessor maps onto precisely the selected component of
the target, not necessarily the entire disconnected target. -/
theorem inverse_branch_component_image (F g : X → X) (a l : X)
    (S : Set X) (x : X)
    (hF : Continuous F) (hfix : F a = a)
    (hg : ContinuousOn g (limb a l))
    (hgm : MapsTo g (limb a l) (limb a l))
    (hsection : ∀ y ∈ limb a l, F (g y) = y)
    (hleft : ∀ z ∈ limb a l, F z ∈ limb a l → g (F z) = z)
    (hS : S ⊆ limb a l) (hx : x ∈ S) :
    F '' connectedComponentIn (F ⁻¹' S) (g x) = connectedComponentIn S x := by
  rw [inverse_branch_component F g a l S x hF hfix hg hgm hsection hleft hS hx]
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    rw [hsection w (hS (connectedComponentIn_subset S x hw))]
    exact hw
  · intro hy
    exact ⟨g y, ⟨y, hy, rfl⟩, hsection y (hS (connectedComponentIn_subset S x hy))⟩

/-- Finite-horizon selection for independently supplied connected endpoint
sets. Only root contact with the marked continuum is needed, not contact
with every selected predecessor. Root avoidance propagates automatically
through the forward maps because the omitted point is fixed. -/
theorem endpoint_itinerary_selection (F g : X → X) (a l : X)
    (P E : ℕ → Set X) (q : ℕ → X) (Q : Set X) (H : ℕ)
    (hF : Continuous F) (hfix : F a = a)
    (hg : ContinuousOn g (limb a l))
    (hgm : MapsTo g (limb a l) (limb a l))
    (hsection : ∀ y ∈ limb a l, F (g y) = y)
    (hleft : ∀ z ∈ limb a l, F z ∈ limb a l → g (F z) = z)
    (hP0 : P 0 ⊆ limb a l)
    (hq : ∀ i ≤ H, q i ∈ P i)
    (hqstep : ∀ i < H, q (i+1) = g (q i))
    (hP : ∀ i < H, P (i+1) = connectedComponentIn (F ⁻¹' P i) (q (i+1)))
    (hQ : IsPreconnected Q) (hq0 : q 0 ∈ Q) (hQsub : Q ⊆ P 0)
    (hE : ∀ i ≤ H, IsPreconnected (E i)) (hE0 : E 0 ⊆ P 0)
    (hcontact : (E 0 ∩ Q).Nonempty)
    (hroute : ∀ i < H, MapsTo F (E (i+1)) (E i))
    (hhit : ∀ i < H, (E (i+1) ∩ limb a l).Nonempty) :
    ∀ i ≤ H, P i ⊆ limb a l ∧ E i ⊆ connectedComponentIn (P i) (q i) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨hP0, ?_⟩
    obtain ⟨y, hyE, hyQ⟩ := hcontact
    have hyC : y ∈ connectedComponentIn (P 0) (q 0) :=
      hQ.subset_connectedComponentIn hq0 hQsub hyQ
    have he := (hE 0 (Nat.zero_le H)).subset_connectedComponentIn hyE hE0
    rw [← connectedComponentIn_eq hyC] at he
    exact he
  | succ i ih =>
    intro hi
    have hil : i < H := by omega
    obtain ⟨hPL, hEP⟩ := ih (by omega)
    have hnext : P (i+1) = g '' connectedComponentIn (P i) (q i) := by
      rw [hP i hil, hqstep i hil]
      exact inverse_branch_component F g a l (P i) (q i) hF hfix hg hgm
        hsection hleft hPL (hq i (by omega))
    have hNL : P (i+1) ⊆ limb a l := by
      rw [hnext]
      rintro _ ⟨y, hy, rfl⟩
      exact hgm (hPL (connectedComponentIn_subset (P i) (q i) hy))
    have hENavoid : a ∉ E (i+1) := by
      intro haE
      have haP : F a ∈ E i := hroute i hil haE
      rw [hfix] at haP
      exact limb_avoids_root a l (hPL (connectedComponentIn_subset (P i) (q i) (hEP haP)))
    have hEL : E (i+1) ⊆ limb a l :=
      connected_in_limb_of_hit a l (E (i+1)) (hE _ hi) hENavoid (hhit i hil)
    have hEsub : E (i+1) ⊆ P (i+1) := by
      rw [hnext]
      intro z hz
      have hy := hEP (hroute i hil hz)
      exact ⟨F z, hy, hleft z (hEL hz)
        (hPL (connectedComponentIn_subset (P i) (q i) hy))⟩
    have hc : IsPreconnected (P (i+1)) := by
      rw [hP i hil]
      exact isPreconnected_connectedComponentIn
    exact ⟨hNL, hEsub.trans (hc.subset_connectedComponentIn (hq _ hi) Subset.rfl)⟩

/-- If the independently supplied address records whole pullback
components, endpoint containment identifies the entire ordered address,
not just the last component or its symbolic name. -/
theorem supplied_address_eq (F : X → X) (P R E : ℕ → Set X)
    (q r : ℕ → X) (H : ℕ)
    (h0 : R 0 = P 0)
    (hP : ∀ i < H, P (i+1) = connectedComponentIn (F ⁻¹' P i) (q (i+1)))
    (hR : ∀ i < H, R (i+1) = connectedComponentIn (F ⁻¹' R i) (r (i+1)))
    (hr : ∀ i ≤ H, r i ∈ E i)
    (hselected : ∀ i ≤ H, E i ⊆ P i) :
    ∀ i ≤ H, R i = P i := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    have hil : i < H := by omega
    have hr' : r (i+1) ∈ connectedComponentIn (F ⁻¹' P i) (q (i+1)) := by
      rw [← hP i hil]
      exact hselected _ hi (hr _ hi)
    rw [hR i hil, ih (by omega), hP i hil]
    exact (connectedComponentIn_eq hr').symm

end LoopsStationaryProofUsedItinerary
