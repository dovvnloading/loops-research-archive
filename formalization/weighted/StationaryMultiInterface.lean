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
        have he : connectedComponentIn S z = C := (connectedComponentIn_eq hzCA.1).symm
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

/-- A finite union of exterior patches, retaining the selected sheet. -/
def patchedCarrier {ι : Type*} (A : Set X) (B : ι → Set X) (t : Finset ι) : Set X :=
  A ∪ ⋃ i ∈ t, B i

theorem patchedCarrier_insert {ι : Type*} [DecidableEq ι]
    (A : Set X) (B : ι → Set X) (i : ι) (t : Finset ι) :
    patchedCarrier A B (insert i t) = patchedCarrier A B t ∪ B i := by
  ext z
  simp only [patchedCarrier, mem_union, mem_iUnion, Finset.mem_insert, exists_prop]
  constructor
  · rintro (hz | ⟨j, hj, hz⟩)
    · exact Or.inl (Or.inl hz)
    · rcases hj with hji | hj
      · subst j
        exact Or.inr hz
      · exact Or.inl (Or.inr ⟨j, hj, hz⟩)
  · rintro ((hz | ⟨j, hj, hz⟩) | hz)
    · exact Or.inl hz
    · exact Or.inr ⟨j, Or.inr hj, hz⟩
    · exact Or.inr ⟨i, Or.inl rfl, hz⟩

theorem patchedCarrier_closed {ι : Type*}
    (A : Set X) (B : ι → Set X) (t : Finset ι)
    (hA : IsClosed A) (hB : ∀ i, IsClosed (B i)) :
    IsClosed (patchedCarrier A B t) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa [patchedCarrier] using hA
  | @insert i t hi ih =>
    rw [patchedCarrier_insert]
    exact ih.union (hB i)

/-- Finite exterior patches may overlap outside the selected sheet.
Each retained patch is preconnected and anchored in the sheet. It
cannot merge distinct local components if its interface stays in
the anchor component and every retained overlap has compatible anchors. -/
theorem component_inter_finite_patches {ι : Type*}
    (S A : Set X) (B : ι → Set X) (anchor : ι → X)
    (t : Finset ι) (x : X)
    (hA : IsClosed A) (hB : ∀ i, IsClosed (B i))
    (hBconn : ∀ i, IsPreconnected (S ∩ B i))
    (hanchor : ∀ i, anchor i ∈ S ∩ A ∩ B i)
    (hattach : ∀ i, S ∩ A ∩ B i ⊆ connectedComponentIn (S ∩ A) (anchor i))
    (hoverlap : ∀ i j, (S ∩ B j ∩ B i).Nonempty →
      anchor j ∈ connectedComponentIn (S ∩ A) (anchor i))
    (hx : x ∈ S ∩ A) :
    connectedComponentIn (S ∩ patchedCarrier A B t) x ∩ A =
      connectedComponentIn (S ∩ A) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have he : patchedCarrier A B ∅ = A := by simp [patchedCarrier]
    rw [he]
    exact inter_eq_left.mpr (fun z hz => (connectedComponentIn_subset (S ∩ A) x hz).2)
  | @insert i t hi ih =>
    rw [patchedCarrier_insert]
    let P := patchedCarrier A B t
    change connectedComponentIn (S ∩ (P ∪ B i)) x ∩ A =
      connectedComponentIn (S ∩ A) x
    have hAP : A ⊆ P := fun _ hz => Or.inl hz
    have hP : IsClosed P := patchedCarrier_closed A B t hA hB
    have hlocal : (S ∩ (P ∪ B i)) ∩ P = S ∩ P := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1.1, hz.2⟩
      · intro hz
        exact ⟨⟨hz.1, Or.inl hz.2⟩, hz.2⟩
    have hbase : connectedComponentIn (S ∩ A) (anchor i) ⊆
        connectedComponentIn (S ∩ P) (anchor i) :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (hanchor i).1)
        (fun z hz => ⟨(connectedComponentIn_subset (S ∩ A) (anchor i) hz).1,
          hAP (connectedComponentIn_subset (S ∩ A) (anchor i) hz).2⟩)
    have hatt : (S ∩ (P ∪ B i)) ∩ P ∩ B i ⊆
        connectedComponentIn ((S ∩ (P ∪ B i)) ∩ P) (anchor i) := by
      rw [hlocal]
      intro z hz
      have hzP : z ∈ A ∪ ⋃ j ∈ t, B j := hz.1.2
      rcases hzP with hzA | hzJ
      · exact hbase (hattach i ⟨⟨hz.1.1, hzA⟩, hz.2⟩)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hzJ
        obtain ⟨hjt, hzj⟩ := mem_iUnion.mp hj
        have hanchors : anchor j ∈ connectedComponentIn (S ∩ P) (anchor i) :=
          hbase (hoverlap i j ⟨z, ⟨hz.1.1, hzj⟩, hz.2⟩)
        have hjsub : S ∩ B j ⊆ S ∩ P := by
          intro w hw
          refine ⟨hw.1, Or.inr ?_⟩
          exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjt, hw.2⟩⟩
        have hjconn : S ∩ B j ⊆ connectedComponentIn (S ∩ P) (anchor j) :=
          (hBconn j).subset_connectedComponentIn ⟨(hanchor j).1.1, (hanchor j).2⟩ hjsub
        rw [← connectedComponentIn_eq hanchors] at hjconn
        exact hjconn ⟨hz.1.1, hzj⟩
    have hxx : x ∈ (S ∩ (P ∪ B i)) ∩ P := by
      rw [hlocal]
      exact ⟨hx.1, hAP hx.2⟩
    have hstep := component_inter_of_single_interface_component
      (S ∩ (P ∪ B i)) P (B i) (anchor i) x hP (hB i) (fun z hz => hz.2) hatt hxx
    rw [hlocal] at hstep
    calc
      connectedComponentIn (S ∩ (P ∪ B i)) x ∩ A =
          (connectedComponentIn (S ∩ (P ∪ B i)) x ∩ P) ∩ A := by
        ext z
        constructor
        · intro hz
          exact ⟨⟨hz.1, hAP hz.2⟩, hz.2⟩
        · intro hz
          exact ⟨hz.1.1, hz.2⟩
      _ = connectedComponentIn (S ∩ A) x := by
        rw [hstep]
        exact ih

/-- Exact finite-network no-bypass test. Both the individual interface
condition and the overlap condition are necessary; together they are
sufficient for arbitrary retained subsets and arbitrary closed covers.
An overlap may be outside the selected sheet. -/
theorem finite_patches_no_bypass_iff {ι : Type*}
    (S A : Set X) (B : ι → Set X) (anchor : ι → X) (t : Finset ι)
    (hA : IsClosed A) (hB : ∀ i, IsClosed (B i))
    (hBconn : ∀ i, IsPreconnected (S ∩ B i))
    (hanchor : ∀ i, anchor i ∈ S ∩ A ∩ B i)
    (hcover : S ⊆ patchedCarrier A B t) :
    (∀ x ∈ S ∩ A, connectedComponentIn S x ∩ A =
      connectedComponentIn (S ∩ A) x) ↔
      (∀ i, S ∩ A ∩ B i ⊆ connectedComponentIn (S ∩ A) (anchor i)) ∧
      (∀ i j, (S ∩ B j ∩ B i).Nonempty →
        anchor j ∈ connectedComponentIn (S ∩ A) (anchor i)) := by
  constructor
  · intro h
    have hext (i : ι) : S ∩ B i ⊆ connectedComponentIn S (anchor i) :=
      (hBconn i).subset_connectedComponentIn ⟨(hanchor i).1.1, (hanchor i).2⟩
        (fun z hz => hz.1)
    refine ⟨?_, ?_⟩
    · intro i z hz
      rw [← h (anchor i) (hanchor i).1]
      exact ⟨hext i ⟨hz.1.1, hz.2⟩, hz.1.2⟩
    · intro i j hhit
      obtain ⟨z, hz⟩ := hhit
      have hzC := hext i ⟨hz.1.1, hz.2⟩
      have hj : S ∩ B j ⊆ connectedComponentIn S z :=
        (hBconn j).subset_connectedComponentIn ⟨hz.1.1, hz.1.2⟩ (fun w hw => hw.1)
      rw [← connectedComponentIn_eq hzC] at hj
      rw [← h (anchor i) (hanchor i).1]
      exact ⟨hj ⟨(hanchor j).1.1, (hanchor j).2⟩, (hanchor j).1.2⟩
  · rintro ⟨hattach, hoverlap⟩ x hx
    have he : S ∩ patchedCarrier A B t = S := inter_eq_left.mpr hcover
    have hh := component_inter_finite_patches S A B anchor t x
      hA hB hBconn hanchor hattach hoverlap hx
    rwa [he] at hh

/-- In a compact Hausdorff space, two closed sets with no connected
component meeting both can be separated by a clopen set. The component
quotient is compact Hausdorff and totally disconnected. -/
theorem compact_clopen_separator_of_component_disjoint
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (L R : Set Y) (hL : IsClosed L) (hR : IsClosed R)
    (hsep : ∀ x ∈ L, ∀ y ∈ R, y ∉ connectedComponent x) :
    ∃ U : Set Y, IsClopen U ∧ L ⊆ U ∧ Disjoint U R := by
  let p : Y → ConnectedComponents Y := ConnectedComponents.mk
  have hp : Continuous p := ConnectedComponents.continuous_coe
  have hLc : IsClosed (p '' L) := (hL.isCompact.image hp).isClosed
  have hRc : IsClosed (p '' R) := (hR.isCompact.image hp).isClosed
  have hsub : p '' L ⊆ (p '' R)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have hcomp : y ∈ connectedComponent x :=
      ConnectedComponents.coe_eq_coe'.mp he
    exact hsep x hx y hy hcomp
  obtain ⟨V, hV, hLV, hVR⟩ :=
    exists_clopen_of_closed_subset_open hLc hRc.isOpen_compl hsub
  refine ⟨p ⁻¹' V, ⟨hV.1.preimage hp, hV.2.preimage hp⟩, ?_, ?_⟩
  · intro x hx
    exact hLV ⟨x, hx, rfl⟩
  · rw [Set.disjoint_left]
    intro x hx hxR
    exact (hVR hx) ⟨x, hxR, rfl⟩

/-- Compact-carrier no-bypass criterion without a finite patch cover.
It is necessary and sufficient that any two retained interface points
in the same exterior component already lie in the same selected-sheet
component. There may be infinitely many exterior components, and
components with no interface points require no anchor. -/
theorem compact_closed_cover_no_bypass_iff [T2Space X]
    (S A B : Set X) (hS : IsCompact S)
    (hA : IsClosed A) (hB : IsClosed B) (hcover : S ⊆ A ∪ B) :
    (∀ x ∈ S ∩ A, connectedComponentIn S x ∩ A =
      connectedComponentIn (S ∩ A) x) ↔
    (∀ u v, u ∈ S ∩ A ∩ B → v ∈ S ∩ A ∩ B →
      v ∈ connectedComponentIn (S ∩ B) u →
      v ∈ connectedComponentIn (S ∩ A) u) := by
  constructor
  · intro h u v hu hv hvB
    rw [← h u hu.1]
    exact ⟨connectedComponentIn_mono u inter_subset_left hvB, hv.1.2⟩
  · intro h x hx
    classical
    let T := S ∩ A
    let E := S ∩ B
    letI : CompactSpace T := isCompact_iff_compactSpace.mp (hS.inter_right hA)
    letI : CompactSpace E := isCompact_iff_compactSpace.mp (hS.inter_right hB)
    have partition (D : Set X) (U : Set D) :
        D ⊆ ((↑) : D → X) '' U ∪ ((↑) : D → X) '' Uᶜ ∧
        Disjoint (((↑) : D → X) '' U) (((↑) : D → X) '' Uᶜ) := by
      constructor
      · intro z hz
        let w : D := ⟨z, hz⟩
        by_cases hw : w ∈ U
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
      · rw [Set.disjoint_left]
        rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
        have he' : v = u := Subtype.ext he
        exact hv (he'.symm ▸ hu)
    apply Subset.antisymm
    · intro y hy
      by_contra hnot
      let x' : T := ⟨x, hx⟩
      let y' : T := ⟨y, ⟨connectedComponentIn_subset S x hy.1, hy.2⟩⟩
      have hyn : y' ∉ connectedComponent x' := by
        intro hm
        apply hnot
        rw [connectedComponentIn_eq_image hx]
        exact ⟨y', hm, rfl⟩
      rw [connectedComponent_eq_iInter_isClopen x'] at hyn
      have hs : ∃ U : {U : Set T // IsClopen U ∧ x' ∈ U},
          y' ∉ U.val := by
        by_contra hn
        apply hyn
        exact mem_iInter.mpr (fun U => by
          by_contra hu
          exact hn ⟨U, hu⟩)
      obtain ⟨U, hyU⟩ := hs
      have hU : IsClopen U.val := U.property.1
      let L := ((↑) : T → X) '' U.val
      let R := ((↑) : T → X) '' U.valᶜ
      have hL : IsClosed L := (hU.1.isCompact.image continuous_subtype_val).isClosed
      have hR : IsClosed R := (hU.compl.1.isCompact.image continuous_subtype_val).isClosed
      have hxL : x ∈ L := ⟨x', U.property.2, rfl⟩
      have hyR : y ∈ R := ⟨y', hyU, rfl⟩
      let LB : Set E := ((↑) : E → X) ⁻¹' L
      let RB : Set E := ((↑) : E → X) ⁻¹' R
      have hLB : IsClosed LB := hL.preimage continuous_subtype_val
      have hRB : IsClosed RB := hR.preimage continuous_subtype_val
      have hsep : ∀ u ∈ LB, ∀ v ∈ RB, v ∉ connectedComponent u := by
        intro u hu v hv huv
        obtain ⟨u', hu', heu⟩ := hu
        obtain ⟨v', hv', hev⟩ := hv
        have huT : (u : X) ∈ T := heu ▸ u'.property
        have hvT : (v : X) ∈ T := hev ▸ v'.property
        have huvB : (v : X) ∈ connectedComponentIn E (u : X) := by
          rw [connectedComponentIn_eq_image u.property]
          exact ⟨v, huv, rfl⟩
        have huvA := h (u : X) (v : X) ⟨huT, u.property.2⟩
          ⟨hvT, v.property.2⟩ huvB
        have hAcomp : (v' : X) ∈ connectedComponentIn T (u' : X) := by
          rw [heu, hev]
          exact huvA
        rw [connectedComponentIn_eq_image u'.property] at hAcomp
        obtain ⟨w, hw, he⟩ := hAcomp
        have he' : w = v' := Subtype.ext he
        exact hv' (hU.connectedComponent_subset hu' (he' ▸ hw))
      obtain ⟨W, hW, hLBW, hWRB⟩ :=
        compact_clopen_separator_of_component_disjoint LB RB hLB hRB hsep
      let M := ((↑) : E → X) '' W
      let N := ((↑) : E → X) '' Wᶜ
      have hM : IsClosed M := (hW.1.isCompact.image continuous_subtype_val).isClosed
      have hN : IsClosed N := (hW.compl.1.isCompact.image continuous_subtype_val).isClosed
      have hcoverC : connectedComponentIn S x ⊆ (L ∪ M) ∪ (R ∪ N) := by
        intro z hz
        have hzS := connectedComponentIn_subset S x hz
        rcases hcover hzS with hzA | hzB
        · rcases (partition T U.val).1 ⟨hzS, hzA⟩ with hzL | hzR
          · exact Or.inl (Or.inl hzL)
          · exact Or.inr (Or.inl hzR)
        · rcases (partition E W).1 ⟨hzS, hzB⟩ with hzM | hzN
          · exact Or.inl (Or.inr hzM)
          · exact Or.inr (Or.inr hzN)
      have hdis : Disjoint (L ∪ M) (R ∪ N) := by
        rw [Set.disjoint_left]
        intro z hz hz'
        rcases hz with hzL | hzM <;> rcases hz' with hzR | hzN
        · exact Set.disjoint_left.mp (partition T U.val).2 hzL hzR
        · obtain ⟨w, hw, he⟩ := hzN
          have hwL : w ∈ LB := by
            change (w : X) ∈ L
            rwa [he]
          exact hw (hLBW hwL)
        · obtain ⟨w, hw, he⟩ := hzM
          have hwR : w ∈ RB := by
            change (w : X) ∈ R
            rwa [he]
          exact Set.disjoint_left.mp hWRB hw hwR
        · exact Set.disjoint_left.mp (partition E W).2 hzM hzN
      obtain ⟨z, _, hz, hz'⟩ := (isPreconnected_closed_iff.mp
        (isPreconnected_connectedComponentIn (F := S) (x := x)))
        (L ∪ M) (R ∪ N) (hL.union hM) (hR.union hN) hcoverC
        ⟨x, mem_connectedComponentIn hx.1, Or.inl hxL⟩
        ⟨y, hy.1, Or.inl hyR⟩
      exact Set.disjoint_left.mp hdis hz hz'
    · intro y hy
      exact ⟨connectedComponentIn_mono x inter_subset_left hy,
        (connectedComponentIn_subset (S ∩ A) x hy).2⟩

end LoopsStationaryMultiInterface
