import Mathlib

/-!
# Full-carrier component transport across multi-point interfaces

The exterior may meet a selected sheet in many points. What matters is
whether these contacts belong to one component of the retained sheet.
All sets have their ambient topology; local connectivity is not assumed.
-/

namespace LoopsStationaryMultiInterface

open Set

variable {X : Type*} [TopologicalSpace X]

/-- A preconnected subset stays preconnected on restriction to a closed
sheet if its entire interface is absorbed by a preconnected subset of
that restriction. The absorbing subset need not equal the interface. -/
theorem preconnected_inter_of_absorbed_interface
    (C A B K : Set X) (hC : IsPreconnected C)
    (hA : IsClosed A) (hB : IsClosed B) (hcover : C ⊆ A ∪ B)
    (hK : IsPreconnected K) (hKsub : K ⊆ C ∩ A)
    (hinterface : C ∩ A ∩ B ⊆ K) :
    IsPreconnected (C ∩ A) := by
  apply isPreconnected_closed_iff.mpr
  intro U V hU hV hcov hleft hright
  by_contra hnone
  have hno (z : X) (hz : z ∈ C ∩ A) (hu : z ∈ U) (hv : z ∈ V) : False :=
    hnone ⟨z, hz, hu, hv⟩
  have finish (P R : Set X) (hP : IsClosed P) (hR : IsClosed R)
      (hPR : C ∩ A ⊆ P ∪ R)
      (hPhit : ((C ∩ A) ∩ P).Nonempty)
      (hRhit : ((C ∩ A) ∩ R).Nonempty)
      (hKP : K ⊆ P)
      (hPRno : ∀ z ∈ C ∩ A, z ∈ P → z ∈ R → False) : False := by
    have hcov' : C ⊆ (P ∪ B) ∪ (A ∩ R) := by
      intro z hz
      rcases hcover hz with hzA | hzB
      · rcases hPR ⟨hz, hzA⟩ with hzP | hzR
        · exact Or.inl (Or.inl hzP)
        · exact Or.inr ⟨hzA, hzR⟩
      · exact Or.inl (Or.inr hzB)
    obtain ⟨p, hpCA, hpP⟩ := hPhit
    obtain ⟨r, hrCA, hrR⟩ := hRhit
    obtain ⟨z, hzC, hzPB, hzAR⟩ :=
      (isPreconnected_closed_iff.mp hC)
        (P ∪ B) (A ∩ R) (hP.union hB) (hA.inter hR) hcov'
        ⟨p, hpCA.1, Or.inl hpP⟩ ⟨r, hrCA.1, hrCA.2, hrR⟩
    have hzP : z ∈ P := by
      rcases hzPB with hzP | hzB
      · exact hzP
      · exact hKP (hinterface ⟨⟨hzC, hzAR.1⟩, hzB⟩)
    exact hPRno z ⟨hzC, hzAR.1⟩ hzP hzAR.2
  by_cases hhit : (K ∩ U).Nonempty
  · have hKU : K ⊆ U := by
      intro z hzK
      by_contra hzU
      have hzV : z ∈ V := (hcov (hKsub hzK)).resolve_left hzU
      obtain ⟨w, hwK, hwU, hwV⟩ :=
        (isPreconnected_closed_iff.mp hK) U V hU hV
          (hKsub.trans hcov) hhit ⟨z, hzK, hzV⟩
      exact hno w (hKsub hwK) hwU hwV
    exact finish U V hU hV hcov hleft hright hKU hno
  · have hKV : K ⊆ V := by
      intro z hzK
      rcases hcov (hKsub hzK) with hzU | hzV
      · exact (hhit ⟨z, hzK, hzU⟩).elim
      · exact hzV
    exact finish V U hV hU
      (fun z hz => (hcov hz).symm) hright hleft hKV
      (fun z hz hv hu => hno z hz hu hv)

/-- Exact ambient component restriction with multiple contacts.
The retained set S is arbitrary, including a carrier after deletion of
a critical continuum. A and B need only be closed in the ambient space
(which may itself be a subspace). No compactness is needed. -/
theorem component_inter_of_single_interface_component
    (S A B : Set X) (a x : X)
    (hA : IsClosed A) (hB : IsClosed B) (hcover : S ⊆ A ∪ B)
    (hattach : S ∩ A ∩ B ⊆ connectedComponentIn (S ∩ A) a)
    (hx : x ∈ S ∩ A) :
    connectedComponentIn S x ∩ A = connectedComponentIn (S ∩ A) x := by
  let C := connectedComponentIn S x
  have hC : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCS : C ⊆ S := connectedComponentIn_subset S x
  have hCx : x ∈ C := mem_connectedComponentIn hx.1
  have hCsub : C ⊆ A ∪ B := hCS.trans hcover
  have hconn : IsPreconnected (C ∩ A) := by
    by_cases hhit : (C ∩ A ∩ B).Nonempty
    · obtain ⟨z, hzCA, hzB⟩ := hhit
      let K := connectedComponentIn (S ∩ A) a
      have hzK : z ∈ K := hattach ⟨⟨hCS hzCA.1, hzCA.2⟩, hzB⟩
      have hK : IsPreconnected K := isPreconnected_connectedComponentIn
      have hKS : K ⊆ S ∩ A := connectedComponentIn_subset (S ∩ A) a
      have hKC : K ⊆ C := by
        have hh := hK.subset_connectedComponentIn hzK (fun w hw => (hKS hw).1)
        have he : connectedComponentIn S z = C := connectedComponentIn_eq hzCA.1
        rw [he] at hh
        exact hh
      exact preconnected_inter_of_absorbed_interface C A B K hC hA hB hCsub
        hK (fun w hw => ⟨hKC hw, (hKS hw).2⟩)
        (fun w hw => hattach ⟨⟨hCS hw.1.1, hw.1.2⟩, hw.2⟩)
    · exact preconnected_inter_of_absorbed_interface C A B ∅ hC hA hB hCsub
        isPreconnected_empty (empty_subset _) (fun w hw => (hhit ⟨w, hw⟩).elim)
  apply Subset.antisymm
  · exact hconn.subset_connectedComponentIn ⟨hCx, hx.2⟩
      (fun w hw => ⟨hCS hw.1, hw.2⟩)
  · have hlocal : connectedComponentIn (S ∩ A) x ⊆ C :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hx)
        (fun w hw => (connectedComponentIn_subset (S ∩ A) x hw).1)
    exact fun w hw => ⟨hlocal hw, (connectedComponentIn_subset (S ∩ A) x hw).2⟩

/-- When the retained exterior is preconnected and touches the sheet,
the single-component attachment criterion is also necessary. This
distinguishes multiple harmless contacts from genuine exterior bypass. -/
theorem no_bypass_iff_single_interface_component
    (S A B : Set X) (a : X)
    (hA : IsClosed A) (hB : IsClosed B) (hcover : S ⊆ A ∪ B)
    (hBconn : IsPreconnected (S ∩ B)) (ha : a ∈ S ∩ A ∩ B) :
    (∀ x ∈ S ∩ A, connectedComponentIn S x ∩ A =
        connectedComponentIn (S ∩ A) x) ↔
      S ∩ A ∩ B ⊆ connectedComponentIn (S ∩ A) a := by
  constructor
  · intro h z hz
    have hext : S ∩ B ⊆ connectedComponentIn S a :=
      hBconn.subset_connectedComponentIn ⟨ha.1.1, ha.2⟩ (fun w hw => hw.1)
    rw [← h a ha.1]
    exact ⟨hext ⟨hz.1.1, hz.2⟩, hz.1.2⟩
  · intro h x hx
    exact component_inter_of_single_interface_component S A B a x hA hB hcover h hx

/-- A connected exterior bridge between distinct local components is
an explicit certificate of failure of full-carrier separation. -/
theorem exterior_bridge_obstructs_separator
    (S A E : Set X) (x y : X)
    (hE : IsPreconnected E) (hES : E ⊆ S) (hx : x ∈ E) (hy : y ∈ E)
    (hyA : y ∈ A) (hsep : y ∉ connectedComponentIn (S ∩ A) x) :
    y ∈ connectedComponentIn S x ∧
      connectedComponentIn S x ∩ A ≠ connectedComponentIn (S ∩ A) x := by
  have hyC := hE.subset_connectedComponentIn hx hES hy
  refine ⟨hyC, ?_⟩
  intro heq
  apply hsep
  rw [← heq]
  exact ⟨hyC, hyA⟩

end LoopsStationaryMultiInterface
