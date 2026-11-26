import Mathlib
import SaturatedTelescope

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
    exact connectedComponentIn_mono x
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


/-- A finite family of compact connected obstacle objects admits an exact
separated compact complement iff every obstacle meeting the carrier is
absorbed. No arbitrary choice of obstacle split is required. -/
theorem finite_obstacle_split_iff (K : Set X) (O : Set (Set X))
    (hK : IsCompact K) (hfin : O.Finite)
    (hc : ∀ A ∈ O, IsCompact A) (hp : ∀ A ∈ O, IsPreconnected A) :
    (∃ E : Set X, IsCompact E ∧ Disjoint K E ∧ ∀ A ∈ O, A ⊆ K ∪ E) ↔
      ∀ A ∈ O, (K ∩ A).Nonempty → A ⊆ K := by
  constructor
  · rintro ⟨E, hE, hd, hcover⟩ A hA hmeet
    exact connected_obstacle_forced K E A hK.isClosed hE.isClosed hd
      (hp A hA) (hcover A hA) hmeet
  · intro habs
    let B : Set (Set X) := {A ∈ O | Disjoint K A}
    let E : Set X := ⋃₀ B
    have hB : B ⊆ O := fun _ h => h.1
    have hE : IsCompact E := (hfin.subset hB).isCompact_sUnion
      (fun A hA => hc A (hB hA))
    refine ⟨E, hE, ?_, ?_⟩
    · apply Set.disjoint_left.mpr
      intro x hx hxE
      obtain ⟨A, hA, hxA⟩ := mem_sUnion.mp hxE
      exact (Set.disjoint_left.mp hA.2) hx hxA
    · intro A hA x hx
      by_cases hd : Disjoint K A
      · exact Or.inr (mem_sUnion.mpr ⟨A, ⟨hA, hd⟩, hx⟩)
      · have hm : (K ∩ A).Nonempty := by
          by_contra hn
          apply hd
          apply Set.disjoint_left.mpr
          intro z hzK hzA
          exact hn ⟨z, hzK, hzA⟩
        exact Or.inl (habs A hA hm hx)

/-- Exact existence test: close all internal obstacles first, then reject
only if the least core leaves the authorized region or meets an obstacle
which cannot lie wholly in the ambient carrier. The ambient carrier itself
witnesses existence for the internal constraints. -/
theorem least_carrier_obstruction_criterion (J S : Set X) (O : Set (Set X))
    (hJ : IsCompact J) (hpJ : IsPreconnected J) (hSJ : S ⊆ J)
    (hS : S.Nonempty)
    (hhered : ∀ A B : Set X, IsCompact A → IsCompact B →
      IsPreconnected A → IsPreconnected B → A ⊆ J → B ⊆ J →
      (A ∩ B).Nonempty → IsPreconnected (A ∩ B)) :
    ∃ K, Admissible J S {A ∈ O | A ⊆ J} K ∧
      (∀ L, Admissible J S {A ∈ O | A ⊆ J} L → K ⊆ L) ∧
      ∀ U : Set X, (∃ L, Admissible J S O L ∧ L ⊆ U) ↔
        K ⊆ U ∧ ∀ A ∈ O, (K ∩ A).Nonempty → A ⊆ J := by
  let B : Set (Set X) := {A ∈ O | A ⊆ J}
  have hbase : Admissible J S B J := {
    compact := hJ
    preconnected := hpJ
    package := hSJ
    inside := Subset.rfl
    absorb := fun _ hA _ => hA.2 }
  obtain ⟨K, hK, hleast⟩ := least_admissible_carrier J S B hJ hS hhered ⟨J, hbase⟩
  refine ⟨K, hK, hleast, ?_⟩
  intro U
  constructor
  · rintro ⟨L, hL, hLU⟩
    have hLB : Admissible J S B L := {
      compact := hL.compact
      preconnected := hL.preconnected
      package := hL.package
      inside := hL.inside
      absorb := fun A hA hm => hL.absorb A hA.1 hm }
    have hKL := hleast L hLB
    refine ⟨hKL.trans hLU, ?_⟩
    intro A hA hm
    obtain ⟨z, hzK, hzA⟩ := hm
    exact (hL.absorb A hA ⟨z, hKL hzK, hzA⟩).trans hL.inside
  · rintro ⟨hKU, htest⟩
    refine ⟨K, ?_, hKU⟩
    exact {
      compact := hK.compact
      preconnected := hK.preconnected
      package := hK.package
      inside := hK.inside
      absorb := fun A hA hm => hK.absorb A ⟨hA, htest A hA hm⟩ hm }

/-- Hereditary pairwise intersection extends to arbitrary compact carriers
with a common anchor, without any directedness assumption on the family. -/
theorem hereditary_carrier_intersection {ι : Type*} [Nonempty ι]
    (J : Set X) (hJ : IsCompact J) (K : ι → Set X) (x : X)
    (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i))
    (hsub : ∀ i, K i ⊆ J) (hx : ∀ i, x ∈ K i)
    (hhered : ∀ A B : Set X, IsCompact A → IsCompact B →
      IsPreconnected A → IsPreconnected B → A ⊆ J → B ⊆ J →
      (A ∩ B).Nonempty → IsPreconnected (A ∩ B)) :
    IsPreconnected (⋂ i, K i) := by
  classical
  let S : Set X := ⋂ i, K i
  have hS : S.Nonempty := ⟨x, mem_iInter.mpr hx⟩
  have hA (i : ι) : Admissible J S ∅ (K i) := {
    compact := hc i
    preconnected := hp i
    package := iInter_subset K i
    inside := hsub i
    absorb := by simp }
  obtain ⟨L, hL, hleast⟩ := least_admissible_carrier J S ∅ hJ hS hhered
    ⟨K (Classical.choice (inferInstance : Nonempty ι)), hA _⟩
  have heq : L = S := Subset.antisymm
    (fun _ hz => mem_iInter.mpr fun i => hleast _ (hA i) hz) hL.package
  change IsPreconnected S
  rw [← heq]
  exact hL.preconnected

/-- At the actual quadratic critical point even nondirected intersections
preserve component saturation and image equality. The sign involution
removes the otherwise real ambiguity between incompatible inverse fibers. -/
theorem quadratic_critical_arbitrary_intersection {ι : Type*} [Nonempty ι]
    (c : ℂ) (J : Set ℂ) (hJ : IsCompact J) (K D : ι → Set ℂ)
    (hc : ∀ i, IsCompact (K i)) (hsub : ∀ i, K i ⊆ J)
    (hx : ∀ i, (0 : ℂ) ∈ K i)
    (hhered : ∀ A B : Set ℂ, IsCompact A → IsCompact B →
      IsPreconnected A → IsPreconnected B → A ⊆ J → B ⊆ J →
      (A ∩ B).Nonempty → IsPreconnected (A ∩ B))
    (hsat : ∀ i, K i = connectedComponentIn ((fun z : ℂ => z^2+c) ⁻¹' D i) 0)
    (honto : ∀ i, (fun z : ℂ => z^2+c) '' K i = D i) :
    (⋂ i, K i) = connectedComponentIn ((fun z : ℂ => z^2+c) ⁻¹' (⋂ i, D i)) 0 ∧
      (fun z : ℂ => z^2+c) '' (⋂ i, K i) = ⋂ i, D i := by
  have hp (i : ι) : IsPreconnected (K i) := by
    rw [hsat i]
    exact isPreconnected_connectedComponentIn
  have hpre := hereditary_carrier_intersection J hJ K 0 hc hp hsub hx hhered
  refine ⟨?_, ?_⟩
  · apply Subset.antisymm
    · apply hpre.subset_connectedComponentIn (mem_iInter.mpr hx)
      intro z hz
      change z^2+c ∈ ⋂ i, D i
      apply mem_iInter.mpr
      intro i
      have hzi : z ∈ K i := mem_iInter.mp hz i
      rw [hsat i] at hzi
      exact connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D i) 0 hzi
    · intro z hz
      apply mem_iInter.mpr
      intro i
      rw [hsat i]
      exact connectedComponentIn_mono 0
        (show (fun w : ℂ => w^2+c) ⁻¹' (⋂ j, D j) ⊆
          (fun w : ℂ => w^2+c) ⁻¹' D i from fun _ hw => mem_iInter.mp hw i) hz
  · apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      apply mem_iInter.mpr
      intro i
      rw [← honto i]
      exact ⟨z, mem_iInter.mp hz i, rfl⟩
    · intro y hy
      let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
      have hy₀ : y ∈ (fun z : ℂ => z^2+c) '' K i₀ := by
        rw [honto i₀]
        exact mem_iInter.mp hy i₀
      obtain ⟨z, hz, hzy⟩ := hy₀
      refine ⟨z, mem_iInter.mpr ?_, hzy⟩
      intro i
      have hyi : y ∈ (fun z : ℂ => z^2+c) '' K i := by
        rw [honto i]
        exact mem_iInter.mp hy i
      obtain ⟨w, hw, hwy⟩ := hyi
      rcases (LoopsSaturatedTelescope.quadratic_eq_iff c z w).mp (hzy.trans hwy.symm)
        with heq | heq
      · rw [heq]
        exact hw
      · rw [heq, hsat i]
        have hzero := hx i
        rw [hsat i] at hzero
        have hci : c ∈ D i := by
          have h := connectedComponentIn_subset ((fun u : ℂ => u^2+c) ⁻¹' D i) 0 hzero
          change (0 : ℂ)^2+c ∈ D i at h
          simpa using h
        rw [hsat i] at hw
        exact LoopsSaturatedTelescope.quadratic_critical_component_symmetric c (D i)
          hci w hw


/-- For a quadratic map, loss of a common inverse point at an arbitrary
intersection is exactly a pair of incompatible sign choices. The
obstruction is witnessed by two actual carriers, not by an abstract graph. -/
theorem quadratic_image_loss_iff_conflicting_signs {ι : Type*} [Nonempty ι]
    (c y : ℂ) (K : ι → Set ℂ)
    (hy : y ∈ ⋂ i, (fun z : ℂ => z^2+c) '' K i) :
    y ∉ (fun z : ℂ => z^2+c) '' (⋂ i, K i) ↔
      ∃ i j z, z^2+c=y ∧ z ∈ K i ∧ -z ∉ K i ∧ -z ∈ K j ∧ z ∉ K j ∧ z ≠ -z := by
  classical
  constructor
  · intro hbad
    let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    obtain ⟨z, hz, hzy⟩ := mem_iInter.mp hy i₀
    have hznot : ¬ ∀ i, z ∈ K i := fun h => hbad ⟨z, mem_iInter.mpr h, hzy⟩
    push_neg at hznot
    obtain ⟨j, hj⟩ := hznot
    obtain ⟨w, hw, hwy⟩ := mem_iInter.mp hy j
    have hnegj : -z ∈ K j := by
      rcases (LoopsSaturatedTelescope.quadratic_eq_iff c w z).mp (hwy.trans hzy.symm)
        with heq | heq
      · rw [heq] at hw
        exact False.elim (hj hw)
      · rw [heq] at hw
        exact hw
    have hnzy : (-z)^2+c=y := by
      calc
        (-z)^2+c = z^2+c := by ring
        _ = y := hzy
    have hnegnot : ¬ ∀ i, -z ∈ K i :=
      fun h => hbad ⟨-z, mem_iInter.mpr h, hnzy⟩
    push_neg at hnegnot
    obtain ⟨i, hi⟩ := hnegnot
    obtain ⟨v, hv, hvy⟩ := mem_iInter.mp hy i
    have hzi : z ∈ K i := by
      rcases (LoopsSaturatedTelescope.quadratic_eq_iff c v z).mp (hvy.trans hzy.symm)
        with heq | heq
      · rw [heq] at hv
        exact hv
      · rw [heq] at hv
        exact False.elim (hi hv)
    refine ⟨i, j, z, hzy, hzi, hi, hnegj, hj, ?_⟩
    intro heq
    rw [← heq] at hnegj
    exact hj hnegj
  · rintro ⟨i, j, z, hzy, _, hni, _, hnj, _⟩ ⟨w, hw, hwy⟩
    rcases (LoopsSaturatedTelescope.quadratic_eq_iff c w z).mp (hwy.trans hzy.symm)
      with heq | heq
    · have hwj := mem_iInter.mp hw j
      rw [heq] at hwj
      exact hnj hwj
    · have hwi := mem_iInter.mp hw i
      rw [heq] at hwi
      exact hni hwi

/-- Pairwise inverse compatibility is necessary and sufficient for
image/intersection commutation for the actual quadratic map, even for
an arbitrary infinite family with no directedness or compactness. -/
theorem quadratic_image_intersection_iff_pairwise {ι : Type*} [Nonempty ι]
    (c : ℂ) (K : ι → Set ℂ) :
    (fun z : ℂ => z^2+c) '' (⋂ i, K i) = (⋂ i, (fun z : ℂ => z^2+c) '' K i) ↔
      ∀ y ∈ (⋂ i, (fun z : ℂ => z^2+c) '' K i), ∀ i j,
        y ∈ (fun z : ℂ => z^2+c) '' (K i ∩ K j) := by
  constructor
  · intro h y hy i j
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨z, ⟨mem_iInter.mp hz i, mem_iInter.mp hz j⟩, hzy⟩
  · intro hp
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact mem_iInter.mpr fun i => ⟨z, mem_iInter.mp hz i, rfl⟩
    · intro y hy
      by_contra hbad
      obtain ⟨i, j, z, hzy, _, hni, _, hnj, _⟩ :=
        (quadratic_image_loss_iff_conflicting_signs c y K hy).mp hbad
      obtain ⟨w, hw, hwy⟩ := hp y hy i j
      rcases (LoopsSaturatedTelescope.quadratic_eq_iff c w z).mp (hwy.trans hzy.symm)
        with heq | heq
      · have hwj := hw.2
        rw [heq] at hwj
        exact hnj hwj
      · have hwi := hw.1
        rw [heq] at hwi
        exact hni hwi

/-- A compact connected carrier disjoint from its reflected copy is
the entire selected quadratic pullback component over its own image. -/
theorem quadratic_reflection_component (c x : ℂ) (K : Set ℂ)
    (hc : IsCompact K) (hp : IsPreconnected K) (hx : x ∈ K)
    (hd : Disjoint K ((fun z : ℂ => -z) '' K)) :
    connectedComponentIn ((fun z : ℂ => z^2+c) ⁻¹'
      ((fun z : ℂ => z^2+c) '' K)) x = K := by
  let C := connectedComponentIn ((fun z : ℂ => z^2+c) ⁻¹'
    ((fun z : ℂ => z^2+c) '' K)) x
  have hxc : x ∈ C := mem_connectedComponentIn
    (show x ∈ (fun z : ℂ => z^2+c) ⁻¹' ((fun z : ℂ => z^2+c) '' K)
      from ⟨x, hx, rfl⟩)
  change C = K
  apply Subset.antisymm
  · refine connected_obstacle_forced K ((fun z : ℂ => -z) '' K) C hc.isClosed
      (hc.image continuous_id.neg).isClosed hd isPreconnected_connectedComponentIn
      ?_ ⟨x, hx, hxc⟩
    intro z hz
    obtain ⟨w, hw, h⟩ := connectedComponentIn_subset
      ((fun z : ℂ => z^2+c) ⁻¹' ((fun z : ℂ => z^2+c) '' K)) x hz
    rcases (LoopsSaturatedTelescope.quadratic_eq_iff c z w).mp h.symm with heq | heq
    · exact Or.inl (heq.symm ▸ hw)
    · exact Or.inr ⟨w, hw, heq.symm⟩
  · apply hp.subset_connectedComponentIn hx
    intro z hz
    exact ⟨z, hz, rfl⟩

/-- Actual noncritical obstruction: the two compact diagonal line
segments from 1 to I and -I have a common anchor and singleton
intersection. Each is an entire selected square-map pullback component
over its own image, yet the common target -1 has no common lift. -/
theorem quadratic_nondirected_noncritical_counterexample :
    ∃ A B : Set ℂ, IsCompact A ∧ IsCompact B ∧ IsPreconnected A ∧ IsPreconnected B ∧
      (1 : ℂ) ∈ A ∩ B ∧
      A = connectedComponentIn ((fun z : ℂ => z^2) ⁻¹' ((fun z : ℂ => z^2) '' A)) 1 ∧
      B = connectedComponentIn ((fun z : ℂ => z^2) ⁻¹' ((fun z : ℂ => z^2) '' B)) 1 ∧
      A ∩ B = ({1} : Set ℂ) ∧
      (-1 : ℂ) ∈ ((fun z : ℂ => z^2) '' A) ∩ ((fun z : ℂ => z^2) '' B) ∧
      (-1 : ℂ) ∉ (fun z : ℂ => z^2) '' (A ∩ B) := by
  let g (s : ℂ) (t : ℝ) : ℂ := 1 - (t : ℂ) + (t : ℂ)*s
  let A := g Complex.I '' Icc (0 : ℝ) 1
  let B := g (-Complex.I) '' Icc (0 : ℝ) 1
  have hg (s : ℂ) : Continuous (g s) :=
    (continuous_const.sub Complex.continuous_ofReal).add
      (Complex.continuous_ofReal.mul continuous_const)
  have hAc : IsCompact A := isCompact_Icc.image (hg Complex.I)
  have hBc : IsCompact B := isCompact_Icc.image (hg (-Complex.I))
  have hAp : IsPreconnected A := (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).isPreconnected.image
    _ (hg Complex.I).continuousOn
  have hBp : IsPreconnected B := (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).isPreconnected.image
    _ (hg (-Complex.I)).continuousOn
  have hA1 : (1 : ℂ) ∈ A := ⟨0, by simp, by simp [g]⟩
  have hB1 : (1 : ℂ) ∈ B := ⟨0, by simp, by simp [g]⟩
  have hAI : Complex.I ∈ A := ⟨1, by simp, by simp [g]⟩
  have hBI : -Complex.I ∈ B := ⟨1, by simp, by simp [g]⟩
  have hAcoord {z : ℂ} (hz : z ∈ A) : z.re+z.im=1 := by
    obtain ⟨t, _, rfl⟩ := hz
    simp [g, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im,
      Complex.sub_im, Complex.mul_im] <;> ring
  have hBcoord {z : ℂ} (hz : z ∈ B) : z.re-z.im=1 := by
    obtain ⟨t, _, rfl⟩ := hz
    simp [g, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im,
      Complex.sub_im, Complex.mul_im, Complex.neg_re, Complex.neg_im] <;> ring
  have hdA : Disjoint A ((fun z : ℂ => -z) '' A) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨w, hw, rfl⟩
    have h1 := hAcoord hz
    have h2 := hAcoord hw
    simp only [Complex.neg_re, Complex.neg_im] at h1
    linarith
  have hdB : Disjoint B ((fun z : ℂ => -z) '' B) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨w, hw, rfl⟩
    have h1 := hBcoord hz
    have h2 := hBcoord hw
    simp only [Complex.neg_re, Complex.neg_im] at h1
    linarith
  have hAB : A ∩ B = ({1} : Set ℂ) := by
    apply Subset.antisymm
    · intro z hz
      have h1 := hAcoord hz.1
      have h2 := hBcoord hz.2
      apply mem_singleton_iff.mpr
      apply Complex.ext
      · simp only [Complex.one_re]
        linarith
      · simp only [Complex.one_im]
        linarith
    · intro z hz
      rw [mem_singleton_iff.mp hz]
      exact ⟨hA1, hB1⟩
  have hsA : A = connectedComponentIn ((fun z : ℂ => z^2) ⁻¹'
      ((fun z : ℂ => z^2) '' A)) 1 := by
    simpa only [add_zero] using (quadratic_reflection_component 0 1 A hAc hAp hA1 hdA).symm
  have hsB : B = connectedComponentIn ((fun z : ℂ => z^2) ⁻¹'
      ((fun z : ℂ => z^2) '' B)) 1 := by
    simpa only [add_zero] using (quadratic_reflection_component 0 1 B hBc hBp hB1 hdB).symm
  refine ⟨A, B, hAc, hBc, hAp, hBp, ⟨hA1, hB1⟩, hsA, hsB, hAB, ?_, ?_⟩
  · refine ⟨⟨Complex.I, hAI, Complex.I_sq⟩, ⟨-Complex.I, hBI, ?_⟩⟩
    calc
      (-Complex.I)^2 = Complex.I^2 := by ring
      _ = -1 := Complex.I_sq
  · rintro ⟨z, hz, hzsq⟩
    rw [hAB] at hz
    rw [mem_singleton_iff.mp hz] at hzsq
    norm_num at hzsq

end LoopsLeastCarrier
