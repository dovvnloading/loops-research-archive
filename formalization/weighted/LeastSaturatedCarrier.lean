import Mathlib

/-!
# Least connected carriers, forced absorption, and directed saturation

All carriers are subsets of the ambient topological space; no abstract
cell-tree vertex is substituted for a geometric point. The hereditary
intersection condition is explicit and does not assert local connectivity.
-/

namespace LoopsLeastCarrier

open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]

/-- Compact carriers retain preconnectedness under arbitrary nonempty
downward-directed intersections in a common compact carrier. -/
theorem directed_carrier_preconnected {ι : Type*} [Nonempty ι]
    (J : Set X) (hJ : IsCompact J) (K : ι → Set X)
    (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i))
    (hsub : ∀ i, K i ⊆ J) (hd : Directed (· ⊇ ·) K) :
    IsPreconnected (⋂ i, K i) := by
  classical
  let H := ⋂ i, K i
  have hHclosed : IsClosed H := isClosed_iInter (fun i => (hc i).isClosed)
  change IsPreconnected H
  intro U V hU hV hcover hmeetU hmeetV
  by_contra hnone
  have hdis : Disjoint (H ∩ Vᶜ) (H ∩ Uᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hcover hx.1 with hu | hv
    · exact hy.2 hu
    · exact hx.2 hv
  obtain ⟨P, Q, hP, hQ, hleft, hright, hPQ⟩ :=
    normal_separation (hHclosed.inter hV.isClosed_compl)
      (hHclosed.inter hU.isClosed_compl) hdis
  have hHPQ : H ⊆ P ∪ Q := by
    intro x hx
    by_cases hv : x ∈ V
    · have hu : x ∉ U := fun hu => hnone ⟨x, hx, hu, hv⟩
      exact Or.inr (hright ⟨hx, hu⟩)
    · exact Or.inl (hleft ⟨hx, hv⟩)
  have hbad : IsCompact (J ∩ (P ∪ Q)ᶜ) :=
    hJ.inter_right (hP.union hQ).isClosed_compl
  have hempty : (J ∩ (P ∪ Q)ᶜ) ∩ (⋂ i, K i) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1.2 (hHPQ hx.2)
  obtain ⟨i, hi⟩ := hbad.elim_directed_family_closed K
    (fun j => (hc j).isClosed) hempty hd
  have hiPQ : K i ⊆ P ∪ Q := by
    intro x hx
    by_contra hnot
    have hh : x ∈ (J ∩ (P ∪ Q)ᶜ) ∩ K i := ⟨⟨hsub i hx, hnot⟩, hx⟩
    rw [hi] at hh
    exact hh
  obtain ⟨a, haH, haU⟩ := hmeetU
  obtain ⟨b, hbH, hbV⟩ := hmeetV
  have haV : a ∉ V := fun h => hnone ⟨a, haH, haU, h⟩
  have hbU : b ∉ U := fun h => hnone ⟨b, hbH, h, hbV⟩
  obtain ⟨z, _, hzP, hzQ⟩ := hp i P Q hP hQ hiPQ
    ⟨a, mem_iInter.mp haH i, hleft ⟨haH, haV⟩⟩
    ⟨b, mem_iInter.mp hbH i, hright ⟨hbH, hbU⟩⟩
  exact (Set.disjoint_left.mp hPQ) hzP hzQ

/-- A carrier must contain the package, remain in the ambient carrier,
and absorb every obstacle it meets. The obstacle family may be infinite. -/
structure Admissible (J S : Set X) (O : Set (Set X)) (K : Set X) : Prop where
  compact : IsCompact K
  preconnected : IsPreconnected K
  package : S ⊆ K
  inside : K ⊆ J
  absorb : ∀ A ∈ O, (K ∩ A).Nonempty → A ⊆ K

/-- A separated closed obstacle split forces every connected obstacle
which meets the retained carrier to be absorbed in it. -/
theorem connected_obstacle_forced (K E A : Set X)
    (hK : IsClosed K) (hE : IsClosed E) (hd : Disjoint K E)
    (hA : IsPreconnected A) (hcover : A ⊆ K ∪ E)
    (hmeet : (K ∩ A).Nonempty) : A ⊆ K := by
  intro x hx
  by_contra hxK
  obtain ⟨a, haK, haA⟩ := hmeet
  have haE : a ∉ E := fun h => (Set.disjoint_left.mp hd) haK h
  have hcover' : A ⊆ Eᶜ ∪ Kᶜ := by
    intro z hz
    by_cases hzK : z ∈ K
    · exact Or.inl (fun h => (Set.disjoint_left.mp hd) hzK h)
    · exact Or.inr hzK
  obtain ⟨z, hzA, hzE, hzK⟩ := hA Eᶜ Kᶜ hE.isOpen_compl hK.isOpen_compl
    hcover' ⟨a, haA, haE⟩ ⟨x, hx, hxK⟩
  exact (hcover hzA).elim hzK hzE

/-- Arbitrarily many obstacle constraints have a least admissible carrier
whenever any solution exists. Hereditary continuum-intersection of the
ambient carrier is the explicit geometric input. -/
theorem least_admissible_carrier (J S : Set X) (O : Set (Set X))
    (hJ : IsCompact J) (hS : S.Nonempty)
    (hhered : ∀ A B : Set X, IsCompact A → IsCompact B →
      IsPreconnected A → IsPreconnected B → A ⊆ J → B ⊆ J →
      (A ∩ B).Nonempty → IsPreconnected (A ∩ B))
    (hex : ∃ W, Admissible J S O W) :
    ∃ K, Admissible J S O K ∧ ∀ L, Admissible J S O L → K ⊆ L := by
  classical
  obtain ⟨W, hW⟩ := hex
  let I := {L : Set X // Admissible J S O L}
  letI : Nonempty I := ⟨⟨W, hW⟩⟩
  let T : I → Set X := fun i => i.val
  have hT (i : I) : Admissible J S O (T i) := i.property
  have hd : Directed (· ⊇ ·) T := by
    intro i j
    have hpkg : S ⊆ T i ∩ T j := fun _ hx =>
      ⟨(hT i).package hx, (hT j).package hx⟩
    have hn : (T i ∩ T j).Nonempty := hS.mono hpkg
    have hnew : Admissible J S O (T i ∩ T j) := {
      compact := (hT i).compact.inter_right (hT j).compact.isClosed
      preconnected := hhered _ _ (hT i).compact (hT j).compact
        (hT i).preconnected (hT j).preconnected (hT i).inside (hT j).inside hn
      package := hpkg
      inside := fun _ hx => (hT i).inside hx.1
      absorb := by
        intro A hA hmeet x hx
        obtain ⟨z, hz, hzA⟩ := hmeet
        exact ⟨(hT i).absorb A hA ⟨z, hz.1, hzA⟩ hx,
          (hT j).absorb A hA ⟨z, hz.2, hzA⟩ hx⟩ }
    exact ⟨⟨T i ∩ T j, hnew⟩, inter_subset_left, inter_subset_right⟩
  let K := ⋂ i, T i
  have hKJ : K ⊆ J := (iInter_subset T (⟨W, hW⟩ : I)).trans hW.inside
  have hKclosed : IsClosed K := isClosed_iInter fun i => (hT i).compact.isClosed
  refine ⟨K, ?_, ?_⟩
  · refine {
      compact := hJ.of_isClosed_subset hKclosed hKJ
      preconnected := directed_carrier_preconnected J hJ T
        (fun i => (hT i).compact) (fun i => (hT i).preconnected)
        (fun i => (hT i).inside) hd
      package := fun _ hx => mem_iInter.mpr fun i => (hT i).package hx
      inside := hKJ
      absorb := ?_ }
    intro A hA hmeet x hx
    obtain ⟨z, hz, hzA⟩ := hmeet
    exact mem_iInter.mpr fun i =>
      (hT i).absorb A hA ⟨z, mem_iInter.mp hz i, hzA⟩ hx
  · intro L hL
    exact iInter_subset T (⟨L, hL⟩ : I)

/-- Continuous images commute with directed intersections of compact
carriers. Each surviving target point has a single surviving physical
preimage, not merely an unrelated preimage at every stage. -/
theorem directed_image_intersection {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {ι : Type*} [Nonempty ι] (f : X → Y) (hf : Continuous f)
    (K : ι → Set X) (hc : ∀ i, IsCompact (K i))
    (hd : Directed (· ⊇ ·) K) :
    f '' (⋂ i, K i) = ⋂ i, f '' K i := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact mem_iInter.mpr fun i => ⟨x, mem_iInter.mp hx i, rfl⟩
  · intro y hy
    let F : ι → Set X := fun i => K i ∩ f ⁻¹' ({y} : Set Y)
    have hFcompact (i : ι) : IsCompact (F i) :=
      (hc i).inter_right (isClosed_singleton.preimage hf)
    have hFnonempty (i : ι) : (F i).Nonempty := by
      obtain ⟨x, hx, hxy⟩ := mem_iInter.mp hy i
      exact ⟨x, hx, mem_singleton_iff.mpr hxy⟩
    have hFd : Directed (· ⊇ ·) F := by
      intro i j
      obtain ⟨k, hki, hkj⟩ := hd i j
      exact ⟨k, fun _ hx => ⟨hki hx.1, hx.2⟩, fun _ hx => ⟨hkj hx.1, hx.2⟩⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      F hFd hFnonempty hFcompact (fun i => (hFcompact i).isClosed)
    refine ⟨x, mem_iInter.mpr (fun i => (mem_iInter.mp hx i).1), ?_⟩
    exact mem_singleton_iff.mp (mem_iInter.mp hx
      (Classical.choice (inferInstance : Nonempty ι))).2

/-- Exact selected-component saturation survives arbitrary directed
compact intersections at a fixed physical anchor. -/
theorem directed_component_intersection {Y : Type*} {ι : Type*} [Nonempty ι]
    (f : X → Y) (J : Set X) (hJ : IsCompact J)
    (K : ι → Set X) (D : ι → Set Y) (x : X)
    (hc : ∀ i, IsCompact (K i)) (hsub : ∀ i, K i ⊆ J)
    (hd : Directed (· ⊇ ·) K) (hx : ∀ i, x ∈ K i)
    (hsat : ∀ i, K i = connectedComponentIn (f ⁻¹' D i) x) :
    (⋂ i, K i) = connectedComponentIn (f ⁻¹' (⋂ i, D i)) x := by
  have hp (i : ι) : IsPreconnected (K i) := by
    rw [hsat i]
    exact isPreconnected_connectedComponentIn
  have hpre := directed_carrier_preconnected J hJ K hc hp hsub hd
  apply Subset.antisymm
  · apply hpre.subset_connectedComponentIn (mem_iInter.mpr hx)
    intro z hz
    change f z ∈ ⋂ i, D i
    apply mem_iInter.mpr
    intro i
    have hzi : z ∈ K i := mem_iInter.mp hz i
    rw [hsat i] at hzi
    exact connectedComponentIn_subset (f ⁻¹' D i) x hzi
  · intro z hz
    apply mem_iInter.mpr
    intro i
    rw [hsat i]
    exact connectedComponentIn_mono
      (show f ⁻¹' (⋂ j, D j) ⊆ f ⁻¹' D i from fun _ hw => mem_iInter.mp hw i) hz

/-- Actual quadratic stages retain both exact geometric saturation and
surjectivity at directed compact limits. No local connectivity assumed. -/
theorem quadratic_directed_stage_limit {ι : Type*} [Nonempty ι]
    (c x : ℂ) (J : Set ℂ) (hJ : IsCompact J)
    (K D : ι → Set ℂ)
    (hc : ∀ i, IsCompact (K i)) (hsub : ∀ i, K i ⊆ J)
    (hd : Directed (· ⊇ ·) K) (hx : ∀ i, x ∈ K i)
    (hsat : ∀ i, K i = connectedComponentIn ((fun z : ℂ => z^2+c) ⁻¹' D i) x)
    (honto : ∀ i, (fun z : ℂ => z^2+c) '' K i = D i) :
    (⋂ i, K i) = connectedComponentIn ((fun z : ℂ => z^2+c) ⁻¹' (⋂ i, D i)) x ∧
      (fun z : ℂ => z^2+c) '' (⋂ i, K i) = ⋂ i, D i := by
  refine ⟨directed_component_intersection _ J hJ K D x hc hsub hd hx hsat, ?_⟩
  have hf : Continuous (fun z : ℂ => z^2+c) :=
    (continuous_id.pow 2).add continuous_const
  rw [directed_image_intersection _ hf K hc hd]
  simp only [honto]

end LoopsLeastCarrier
