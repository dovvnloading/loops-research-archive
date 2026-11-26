import StationaryFiberDynamics
import QuadraticCriticalFiberCensus
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Terminal carrier properness without a saturation assumption

The model is a geometric topological space. Finite marks are genuine
compact connected sets, not vertices of an incidence graph.
-/

namespace LoopsTerminalFiberExclusion

open Set Function
open LoopsStationaryMonotoneGeometry
open LoopsStationaryFiberDynamics

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A singleton fiber over a fixed model point cannot meet a mark
whose next dynamical phase is disjoint from it. -/
theorem fixed_fiber_avoids_cycle {ι : Type*}
    (q : X → Y) (F : X → X) (G : Y → Y) (hs : Semiconj q F G)
    (b : Y) (hb : G b = b) (hf : (q ⁻¹' ({b} : Set Y)).Subsingleton)
    (K : ι → Set X) (next : ι → ι)
    (hmap : ∀ i, MapsTo F (K i) (K (next i)))
    (hdis : ∀ i, Disjoint (K i) (K (next i))) :
    ∀ i, q '' K i ⊆ ({b} : Set Y)ᶜ := by
  intro i y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change q x ≠ b
  intro hxb
  have hfx : q (F x) = b := by rw [hs x, hxb, hb]
  have he : F x = x := hf hfx hxb
  exact Set.disjoint_left.mp (hdis i) hx (he ▸ hmap i hx)

/-- A finite family of compact connected marks inside a path connected
region fits in a compact connected subset of that region. The region
itself need not be compact or closed. -/
theorem finite_marks_compact_bridge {ι : Type*}
    (K : ι → Set Y) (V : Set Y) (hV : IsPathConnected V)
    (hc : ∀ i, IsCompact (K i)) (hk : ∀ i, IsConnected (K i))
    (hsub : ∀ i, K i ⊆ V) (b : Y) (hb : b ∈ V) (s : Finset ι) :
    ∃ B : Set Y, IsCompact B ∧ IsConnected B ∧ b ∈ B ∧
      B ⊆ V ∧ ∀ i ∈ s, K i ⊆ B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨{b}, isCompact_singleton, isConnected_singleton, mem_singleton b,
      singleton_subset_iff.mpr hb, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨B, hBc, hBk, hbB, hBV, hBs⟩ := ih
    obtain ⟨x, hx⟩ := (hk i).nonempty
    obtain ⟨g, hg⟩ := hV.joinedIn b hb x (hsub i hx)
    let C : Set Y := range (⇑g)
    have hCc : IsCompact C := isCompact_range g.continuous
    have hCk : IsConnected C := isConnected_range g.continuous
    have hCV : C ⊆ V := range_subset_iff.mpr hg
    have hBC : IsConnected (B ∪ C) :=
      IsConnected.union ⟨b, hbB, g.source_mem_range⟩ hBk hCk
    have hBCi : IsConnected (B ∪ C ∪ K i) :=
      IsConnected.union ⟨x, Or.inr g.target_mem_range, hx⟩ hBC (hk i)
    refine ⟨B ∪ C ∪ K i, (hBc.union hCc).union (hc i), hBCi,
      Or.inl (Or.inl hbB), union_subset (union_subset hBV hCV) (hsub i), ?_⟩
    intro j hj z hz
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inr hz
    · exact Or.inl (Or.inl (hBs j hj hz))

/-- A puncture in a locally path connected Hausdorff model is path
connected if its singleton physical fiber is a noncut point. No
identification with a named combinatorial vertex is needed. -/
theorem model_puncture_path_connected [T1Space Y] [LocallyPathConnectedSpace Y]
    (q : X → Y) (hq : Continuous q) (hsurj : Surjective q)
    (a : X) (ha : q ⁻¹' ({q a} : Set Y) = {a})
    (hconn : IsConnected ({a} : Set X)ᶜ) :
    IsPathConnected ({q a} : Set Y)ᶜ := by
  have himg : q '' ({a} : Set X)ᶜ = ({q a} : Set Y)ᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change q x ≠ q a
      intro he
      have h : x ∈ q ⁻¹' ({q a} : Set Y) := he
      rw [ha] at h
      exact hx h
    · intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      refine ⟨x, ?_, rfl⟩
      intro h
      have he : x = a := h
      exact hy (show q x = q a from congrArg q he)
  apply (isClosed_singleton.isOpen_compl.isConnected_iff_isPathConnected).mp
  rw [← himg]
  exact hconn.image q hq.continuousOn

/-- Exact exclusion criterion for a least physical compact connected
carrier. A finite marked union avoids the fiber if and only if the
least carrier avoids it, as long as the punctured model is path
connected. The proof builds a competing compact connected full
inverse, without requiring the least carrier itself to be saturated. -/
theorem least_carrier_fiber_exclusion_iff [CompactSpace X] [T2Space Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : X → Y) (hq : Continuous q) (hsurj : Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (b : Y) (hb : IsPathConnected ({b} : Set Y)ᶜ)
    (K : ι → Set X) (hc : ∀ i, IsCompact (K i))
    (hk : ∀ i, IsConnected (K i))
    (T : Set X) (hKT : ∀ i, K i ⊆ T)
    (hleast : ∀ U : Set X, IsCompact U → IsConnected U →
      (∀ i, K i ⊆ U) → T ⊆ U) :
    Disjoint T (q ⁻¹' ({b} : Set Y)) ↔
      ∀ i, Disjoint (K i) (q ⁻¹' ({b} : Set Y)) := by
  constructor
  · intro h i
    exact Set.disjoint_left.mpr (fun x hx hxf => Set.disjoint_left.mp h (hKT i hx) hxf)
  · intro h
    classical
    have hsub : ∀ i, q '' K i ⊆ ({b} : Set Y)ᶜ := by
      intro i y hy
      obtain ⟨x, hx, rfl⟩ := hy
      change q x ≠ b
      exact fun he => Set.disjoint_left.mp (h i) hx he
    let i₀ : ι := Classical.choice inferInstance
    obtain ⟨x, hx⟩ := (hk i₀).nonempty
    have hxV : q x ∈ ({b} : Set Y)ᶜ := hsub i₀ ⟨x, hx, rfl⟩
    obtain ⟨B, hBc, hBk, _, hBV, hcover⟩ :=
      finite_marks_compact_bridge (fun i => q '' K i) ({b} : Set Y)ᶜ hb
        (fun i => (hc i).image hq) (fun i => (hk i).image q hq.continuousOn)
        hsub (q x) hxV Finset.univ
    have hpre : IsConnected (q ⁻¹' B) := by
      refine ⟨?_, preconnected_preimage_closed_fibers q hq.isClosedMap hsurj hf hBk.isPreconnected⟩
      obtain ⟨y, hy⟩ := hBk.nonempty
      obtain ⟨z, rfl⟩ := hsurj y
      exact ⟨z, hy⟩
    have hTsub : T ⊆ q ⁻¹' B :=
      hleast _ (hBc.isClosed.preimage hq).isCompact hpre
        (fun i z hz => hcover i (Finset.mem_univ i) ⟨z, hz, rfl⟩)
    apply Set.disjoint_left.mpr
    intro z hz hzb
    have hn : q z ≠ b := hBV (hTsub hz)
    exact hn hzb

/-- Terminal primitive-cycle properness through an arbitrary monotone
geometric model. The physical noncut fixed point identifies its own
model puncture; no independent model mark correspondence or carrier
full-preimage identity is assumed. -/
theorem terminal_cycle_least_carrier_proper [CompactSpace X]
    [T2Space Y] [LocallyPathConnectedSpace Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : X → Y) (F : X → X) (G : Y → Y)
    (hq : Continuous q) (hsurj : Surjective q) (hs : Semiconj q F G)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (a : X) (ha : q ⁻¹' ({q a} : Set Y) = {a})
    (hfix : F a = a) (hnoncut : IsConnected ({a} : Set X)ᶜ)
    (K : ι → Set X) (next : ι → ι)
    (hc : ∀ i, IsCompact (K i)) (hk : ∀ i, IsConnected (K i))
    (hmap : ∀ i, MapsTo F (K i) (K (next i)))
    (hdis : ∀ i, Disjoint (K i) (K (next i)))
    (T : Set X) (hKT : ∀ i, K i ⊆ T)
    (hleast : ∀ U : Set X, IsCompact U → IsConnected U →
      (∀ i, K i ⊆ U) → T ⊆ U) :
    Disjoint T (q ⁻¹' ({q a} : Set Y)) ∧ a ∉ T ∧ T ≠ univ := by
  have hG : G (q a) = q a := by
    rw [← hs a, hfix]
  have hsingle : (q ⁻¹' ({q a} : Set Y)).Subsingleton := by
    rw [ha]
    exact Set.subsingleton_singleton
  have havoid := fixed_fiber_avoids_cycle q F G hs (q a) hG hsingle K next hmap hdis
  have hmark : ∀ i, Disjoint (K i) (q ⁻¹' ({q a} : Set Y)) := by
    intro i
    apply Set.disjoint_left.mpr
    intro z hz hzf
    have hn : q z ≠ q a := havoid i ⟨z, hz, rfl⟩
    exact hn hzf
  have hT := (least_carrier_fiber_exclusion_iff q hq hsurj hf (q a)
    (model_puncture_path_connected q hq hsurj a ha hnoncut)
    K hc hk T hKT hleast).mpr hmark
  have hna : a ∉ T := fun hz => Set.disjoint_left.mp hT hz rfl
  exact ⟨hT, hna, fun he => hna (he.symm ▸ mem_univ a)⟩

/-- The preceding exclusion theorem applies to the genuine quadratic
filled set, whose compactness has already been proved from its escape
function. No placeholder physical space is needed. -/
theorem quadratic_terminal_least_carrier_proper
    [T2Space Y] [LocallyPathConnectedSpace Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ℂ) (q : quadraticFilled c → Y) (G : Y → Y)
    (hq : Continuous q) (hsurj : Surjective q)
    (hs : Semiconj q (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (a : quadraticFilled c) (ha : q ⁻¹' ({q a} : Set Y) = {a})
    (hfix : quadraticFilledMap c a = a)
    (hnoncut : IsConnected ({a} : Set (quadraticFilled c))ᶜ)
    (K : ι → Set (quadraticFilled c)) (next : ι → ι)
    (hc : ∀ i, IsCompact (K i)) (hk : ∀ i, IsConnected (K i))
    (hmap : ∀ i, MapsTo (quadraticFilledMap c) (K i) (K (next i)))
    (hdis : ∀ i, Disjoint (K i) (K (next i)))
    (T : Set (quadraticFilled c)) (hKT : ∀ i, K i ⊆ T)
    (hleast : ∀ U : Set (quadraticFilled c), IsCompact U → IsConnected U →
      (∀ i, K i ⊆ U) → T ⊆ U) :
    Disjoint T (q ⁻¹' ({q a} : Set Y)) ∧ a ∉ T ∧ T ≠ univ := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  exact terminal_cycle_least_carrier_proper q (quadraticFilledMap c) G hq hsurj hs hf
    a ha hfix hnoncut K next hc hk hmap hdis T hKT hleast


/-- Compact subsets of connected open regions of compact locally connected
Hausdorff spaces have compact connected neighborhoods inside those regions.
This requires neither path connectivity nor a finite connected decomposition
of the compact subset. -/
theorem compact_connected_envelope [CompactSpace Y] [T2Space Y]
    [LocallyConnectedSpace Y] (V M : Set Y) (hVo : IsOpen V)
    (hVk : IsConnected V) (hMc : IsCompact M) (hMV : M ⊆ V) :
    ∃ B : Set Y, IsCompact B ∧ IsConnected B ∧ B ⊆ V ∧ M ⊆ interior B := by
  obtain ⟨b, hb⟩ := hVk.nonempty
  have hlocal (x : Y) (hx : x ∈ V) :
      ∃ O : Set Y, IsOpen O ∧ x ∈ O ∧ IsCompact (closure O) ∧
        IsConnected (closure O) ∧ closure O ⊆ V := by
    have hd : Disjoint ({x} : Set Y) Vᶜ := by
      apply Set.disjoint_left.mpr
      intro z hz hz'
      have he : z = x := hz
      exact hz' (he.symm ▸ hx)
    obtain ⟨O, P, hO, hP, hxO, hVP, hOP⟩ :=
      normal_separation isClosed_singleton hVo.isClosed_compl hd
    let W := connectedComponentIn O x
    have hxO' : x ∈ O := hxO (mem_singleton x)
    have hWo : IsOpen W := hO.connectedComponentIn
    have hxW : x ∈ W := mem_connectedComponentIn hxO'
    have hWk : IsConnected W := isConnected_connectedComponentIn_iff.mpr hxO'
    have hWP : W ⊆ Pᶜ := by
      intro z hz hzP
      exact Set.disjoint_left.mp hOP (connectedComponentIn_subset O x hz) hzP
    have hclP : closure W ⊆ Pᶜ := hP.isClosed_compl.closure_subset_iff.mpr hWP
    have hWV : closure W ⊆ V := by
      intro z hz
      by_contra hn
      exact hclP hz (hVP hn)
    exact ⟨W, hWo, hxW, isClosed_closure.isCompact, hWk.closure, hWV⟩
  let I := {C : Set Y // IsCompact C ∧ IsConnected C ∧ b ∈ C ∧ C ⊆ V}
  letI : Nonempty I := ⟨⟨{b}, isCompact_singleton, isConnected_singleton,
    mem_singleton b, singleton_subset_iff.mpr hb⟩⟩
  let U : I → Set Y := fun i => interior i.val
  let R : Set Y := ⋃ i : I, U i
  have hRo : IsOpen R := isOpen_iUnion (fun _ => isOpen_interior)
  have hbR : b ∈ R := by
    obtain ⟨O, hO, hbO, hOc, hOk, hOV⟩ := hlocal b hb
    let i : I := ⟨closure O, hOc, hOk, subset_closure hbO, hOV⟩
    exact mem_iUnion.mpr ⟨i, interior_maximal subset_closure hO hbO⟩
  have hr : closure R ∩ V ⊆ R := by
    intro x hx
    obtain ⟨O, hO, hxO, hOc, hOk, hOV⟩ := hlocal x hx.2
    obtain ⟨z, hzO, hzR⟩ := mem_closure_iff.mp hx.1 O hO hxO
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hzR
    have hzC : z ∈ i.val := interior_subset hzi
    let j : I := ⟨i.val ∪ closure O, i.property.1.union hOc,
      IsConnected.union ⟨z, hzC, subset_closure hzO⟩ i.property.2.1 hOk,
      Or.inl i.property.2.2.1, union_subset i.property.2.2.2 hOV⟩
    have hOj : O ⊆ j.val := fun w hw => Or.inr (subset_closure hw)
    exact mem_iUnion.mpr ⟨j, interior_maximal hOj hO hxO⟩
  have hVR : V ⊆ R :=
    hVk.isPreconnected.subset_of_closure_inter_subset hRo ⟨b, hb, hbR⟩ hr
  have hdir : Directed (· ⊆ ·) U := by
    intro i j
    let k : I := ⟨i.val ∪ j.val, i.property.1.union j.property.1,
      IsConnected.union ⟨b, i.property.2.2.1, j.property.2.2.1⟩ i.property.2.1 j.property.2.1,
      Or.inl i.property.2.2.1, union_subset i.property.2.2.2 j.property.2.2.2⟩
    exact ⟨k, interior_mono (show i.val ⊆ k.val from fun _ hz => Or.inl hz),
      interior_mono (show j.val ⊆ k.val from fun _ hz => Or.inr hz)⟩
  obtain ⟨i, hi⟩ := hMc.elim_directed_cover U (fun _ => isOpen_interior)
    (hMV.trans hVR) hdir
  exact ⟨i.val, i.property.1, i.property.2.1, i.property.2.2.2, hi⟩

/-- Exact geometric obstruction for an arbitrary closed forbidden subset.
A least compact connected carrier avoids the forbidden full inverse
precisely when the entire compact marked image lies in a single component
of its complement. The carrier need not be a saturated subset. -/
theorem least_carrier_avoidance_iff_component [CompactSpace X]
    [T2Space Y] [LocallyConnectedSpace Y]
    (q : X → Y) (hq : Continuous q) (hsurj : Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (A : Set Y) (hA : IsClosed A) (M T : Set X)
    (hMc : IsCompact M) (hMn : M.Nonempty) (hT : IsConnected T)
    (hMT : M ⊆ T)
    (hleast : ∀ U : Set X, IsCompact U → IsConnected U → M ⊆ U → T ⊆ U) :
    Disjoint T (q ⁻¹' A) ↔
      ∃ y ∈ q '' M, q '' M ⊆ connectedComponentIn Aᶜ y := by
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := hMn
    have hTA : q '' T ⊆ Aᶜ := by
      rintro _ ⟨z, hz, rfl⟩ hza
      exact Set.disjoint_left.mp hd hz hza
    have hTk : IsPreconnected (q '' T) := (hT.image q hq.continuousOn).isPreconnected
    exact ⟨q x, ⟨x, hx, rfl⟩, (image_mono hMT).trans
      (hTk.subset_connectedComponentIn ⟨x, hMT hx, rfl⟩ hTA)⟩
  · rintro ⟨y, hy, hcover⟩
    let V := connectedComponentIn Aᶜ y
    have hyV : y ∈ Aᶜ := connectedComponentIn_subset Aᶜ y (hcover hy)
    have hVo : IsOpen V := hA.isOpen_compl.connectedComponentIn
    have hVk : IsConnected V := isConnected_connectedComponentIn_iff.mpr hyV
    letI : CompactSpace Y := Function.Surjective.compactSpace hq hsurj
    obtain ⟨B, hBc, hBk, hBV, hMB⟩ :=
      compact_connected_envelope V (q '' M) hVo hVk (hMc.image hq) hcover
    have hpre : IsConnected (q ⁻¹' B) := by
      refine ⟨?_, preconnected_preimage_closed_fibers q hq.isClosedMap hsurj hf hBk.isPreconnected⟩
      obtain ⟨w, hw⟩ := hBk.nonempty
      obtain ⟨z, rfl⟩ := hsurj w
      exact ⟨z, hw⟩
    have hTsub : T ⊆ q ⁻¹' B := hleast _ (hBc.isClosed.preimage hq).isCompact hpre
      (fun z hz => show q z ∈ B from interior_subset (hMB ⟨z, hz, rfl⟩))
    apply Set.disjoint_left.mpr
    intro z hz hza
    exact (connectedComponentIn_subset Aᶜ y (hBV (hTsub hz))) hza

/-- A singleton-fiber physical noncut point yields a connected model
puncture, without a local path connectivity assumption. -/
theorem model_puncture_connected
    (q : X → Y) (hq : Continuous q) (hsurj : Surjective q)
    (a : X) (ha : q ⁻¹' ({q a} : Set Y) = {a})
    (hconn : IsConnected ({a} : Set X)ᶜ) :
    IsConnected ({q a} : Set Y)ᶜ := by
  have himg : q '' ({a} : Set X)ᶜ = ({q a} : Set Y)ᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change q x ≠ q a
      intro he
      have h : x ∈ q ⁻¹' ({q a} : Set Y) := he
      rw [ha] at h
      exact hx h
    · intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      refine ⟨x, ?_, rfl⟩
      intro h
      have he : x = a := h
      exact hy (show q x = q a from congrArg q he)
  rw [← himg]
  exact hconn.image q hq.continuousOn

/-- Terminal least-carrier properness with the locally connected model
hypothesis, replacing local path connectivity by ordinary local
connectivity. -/
theorem terminal_cycle_least_carrier_proper_lc [CompactSpace X]
    [T2Space Y] [LocallyConnectedSpace Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : X → Y) (F : X → X) (G : Y → Y)
    (hq : Continuous q) (hsurj : Surjective q) (hs : Semiconj q F G)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (a : X) (ha : q ⁻¹' ({q a} : Set Y) = {a})
    (hfix : F a = a) (hnoncut : IsConnected ({a} : Set X)ᶜ)
    (K : ι → Set X) (next : ι → ι)
    (hc : ∀ i, IsCompact (K i)) (hk : ∀ i, IsConnected (K i))
    (hmap : ∀ i, MapsTo F (K i) (K (next i)))
    (hdis : ∀ i, Disjoint (K i) (K (next i)))
    (T : Set X) (hT : IsConnected T) (hKT : ∀ i, K i ⊆ T)
    (hleast : ∀ U : Set X, IsCompact U → IsConnected U →
      (∀ i, K i ⊆ U) → T ⊆ U) :
    Disjoint T (q ⁻¹' ({q a} : Set Y)) ∧ a ∉ T ∧ T ≠ univ := by
  have hG : G (q a) = q a := by rw [← hs a, hfix]
  have hsingle : (q ⁻¹' ({q a} : Set Y)).Subsingleton := by
    rw [ha]
    exact Set.subsingleton_singleton
  have havoid := fixed_fiber_avoids_cycle q F G hs (q a) hG hsingle K next hmap hdis
  let M : Set X := ⋃ i, K i
  have hMc : IsCompact M := isCompact_iUnion hc
  have hMn : M.Nonempty := by
    let i : ι := Classical.choice inferInstance
    obtain ⟨x, hx⟩ := (hk i).nonempty
    exact ⟨x, mem_iUnion.mpr ⟨i, hx⟩⟩
  have hMT : M ⊆ T := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hKT i hi
  have hleastM : ∀ U : Set X, IsCompact U → IsConnected U → M ⊆ U → T ⊆ U := by
    intro U hUc hUk hMU
    exact hleast U hUc hUk (fun i x hx => hMU (mem_iUnion.mpr ⟨i, hx⟩))
  have hmark : q '' M ⊆ ({q a} : Set Y)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact havoid i ⟨x, hi, rfl⟩
  obtain ⟨x, hx⟩ := hMn
  have hximg : q x ∈ q '' M := ⟨x, hx, rfl⟩
  have hconn := model_puncture_connected q hq hsurj a ha hnoncut
  have hex : ∃ y ∈ q '' M, q '' M ⊆ connectedComponentIn ({q a} : Set Y)ᶜ y :=
    ⟨q x, hximg, hmark.trans (hconn.isPreconnected.subset_connectedComponentIn (hmark hximg) Subset.rfl)⟩
  have hd := (least_carrier_avoidance_iff_component q hq hsurj hf {q a} isClosed_singleton
    M T hMc ⟨x, hx⟩ hT hMT hleastM).mpr hex
  have hna : a ∉ T := fun hz => Set.disjoint_left.mp hd hz rfl
  exact ⟨hd, hna, fun he => hna (he.symm ▸ mem_univ a)⟩

/-- The locally connected model theorem for the actual quadratic filled set. -/
theorem quadratic_terminal_least_carrier_proper_lc
    [T2Space Y] [LocallyConnectedSpace Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ℂ) (q : quadraticFilled c → Y) (G : Y → Y)
    (hq : Continuous q) (hsurj : Surjective q)
    (hs : Semiconj q (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (a : quadraticFilled c) (ha : q ⁻¹' ({q a} : Set Y) = {a})
    (hfix : quadraticFilledMap c a = a)
    (hnoncut : IsConnected ({a} : Set (quadraticFilled c))ᶜ)
    (K : ι → Set (quadraticFilled c)) (next : ι → ι)
    (hc : ∀ i, IsCompact (K i)) (hk : ∀ i, IsConnected (K i))
    (hmap : ∀ i, MapsTo (quadraticFilledMap c) (K i) (K (next i)))
    (hdis : ∀ i, Disjoint (K i) (K (next i)))
    (T : Set (quadraticFilled c)) (hT : IsConnected T) (hKT : ∀ i, K i ⊆ T)
    (hleast : ∀ U : Set (quadraticFilled c), IsCompact U → IsConnected U →
      (∀ i, K i ⊆ U) → T ⊆ U) :
    Disjoint T (q ⁻¹' ({q a} : Set Y)) ∧ a ∉ T ∧ T ≠ univ := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  exact terminal_cycle_least_carrier_proper_lc q (quadraticFilledMap c) G hq hsurj hs hf
    a ha hfix hnoncut K next hc hk hmap hdis T hT hKT hleast


/-- In a hereditarily unicoherent compact Hausdorff space, inclusion
minimality among compact connected carriers implies absolute leastness.
This isolates the difference between the two meanings of minimal carrier. -/
theorem minimal_compact_carrier_is_least [CompactSpace X] [T2Space X]
    (M T : Set X) (hMn : M.Nonempty) (hTc : IsCompact T)
    (hTk : IsConnected T) (hMT : M ⊆ T)
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (hmin : ∀ U : Set X, IsCompact U → IsConnected U →
      M ⊆ U → U ⊆ T → T ⊆ U) :
    ∀ U : Set X, IsCompact U → IsConnected U → M ⊆ U → T ⊆ U := by
  intro U hUc hUk hMU
  have hMI : M ⊆ T ∩ U := fun z hz => ⟨hMT hz, hMU hz⟩
  have hI : IsConnected (T ∩ U) :=
    ⟨hMn.mono hMI, hu T U hTc.isClosed hUc.isClosed hTk hUk⟩
  have hIc : IsCompact (T ∩ U) := (hTc.isClosed.inter hUc.isClosed).isCompact
  exact (hmin _ hIc hI hMI inter_subset_left).trans inter_subset_right

/-- Reflection preserves the actual quadratic filled Julia set. -/
theorem quadratic_filled_neg_mem (c z : ℂ) :
    -z ∈ quadraticFilled c ↔ z ∈ quadraticFilled c := by
  calc
    -z ∈ quadraticFilled c ↔ (-z)^2+c ∈ quadraticFilled c :=
      (quadratic_filled_complete_invariant c (-z)).symm
    _ ↔ z^2+c ∈ quadraticFilled c := by rw [neg_sq]
    _ ↔ z ∈ quadraticFilled c := quadratic_filled_complete_invariant c z

/-- Surjectivity on the actual filled Julia set follows from ambient
quadratic surjectivity and complete invariance; no extra inverse
branch or surjectivity premise on the filled set is needed. -/
theorem quadratic_filled_map_surjective (c : ℂ) :
    Surjective (quadraticFilledMap c) := by
  intro y
  obtain ⟨z, hz⟩ := LoopsQuadraticCriticalFiberCensus.quadratic_surjective c (y : ℂ)
  change z^2+c = (y : ℂ) at hz
  have hzmem : z ∈ quadraticFilled c :=
    (quadratic_filled_complete_invariant c z).mp (by rw [hz]; exact y.property)
  exact ⟨⟨z, hzmem⟩, Subtype.ext hz⟩

/-- Existence of a proper forward-invariant least carrier in the
actual quadratic filled Julia set, independent of the identity
of any named source carrier. The critical point belongs to one
marked phase; hereditary unicoherence and the monotone locally
connected model are explicit hypotheses. -/
theorem quadratic_exists_proper_invariant_least_carrier
    [T2Space Y] [LocallyConnectedSpace Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ℂ) (q : quadraticFilled c → Y) (G : Y → Y)
    (hq : Continuous q) (hsurj : Surjective q)
    (hs : Semiconj q (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (a : quadraticFilled c) (ha : q ⁻¹' ({q a} : Set Y) = {a})
    (hfix : quadraticFilledMap c a = a)
    (hnoncut : IsConnected ({a} : Set (quadraticFilled c))ᶜ)
    (hKconn : IsConnected (univ : Set (quadraticFilled c)))
    (hu : ∀ U V : Set (quadraticFilled c), IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (K : ι → Set (quadraticFilled c)) (next : ι → ι)
    (hc : ∀ i, IsCompact (K i)) (hk : ∀ i, IsConnected (K i))
    (hmap : ∀ i, MapsTo (quadraticFilledMap c) (K i) (K (next i)))
    (hdis : ∀ i, Disjoint (K i) (K (next i)))
    (crit : quadraticFilled c) (hcrit : (crit : ℂ) = 0)
    (hcritMark : ∃ i, crit ∈ K i) :
    ∃ T : Set (quadraticFilled c), IsCompact T ∧ IsConnected T ∧
      (∀ i, K i ⊆ T) ∧
      (∀ U : Set (quadraticFilled c), IsCompact U → IsConnected U →
        (∀ i, K i ⊆ U) → T ⊆ U) ∧
      MapsTo (quadraticFilledMap c) T T ∧
      Disjoint T (q ⁻¹' ({q a} : Set Y)) ∧ T ≠ univ := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  let M : Set (quadraticFilled c) := ⋃ i, K i
  have hcritM : crit ∈ M := mem_iUnion.mpr hcritMark
  have hMn : M.Nonempty := ⟨crit, hcritM⟩
  obtain ⟨T, hTc, hTk, hMT, hleast⟩ :=
    least_compact_connected_carrier_exists M hMn hKconn hu
  have hKT : ∀ i, K i ⊆ T :=
    fun i z hz => hMT (mem_iUnion.mpr ⟨i, hz⟩)
  have hleastK : ∀ U : Set (quadraticFilled c), IsCompact U → IsConnected U →
      (∀ i, K i ⊆ U) → T ⊆ U := by
    intro U hUc hUk hKU
    apply hleast U hUc hUk
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact hKU i hi
  have hFM : MapsTo (quadraticFilledMap c) M M := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨next i, hmap i hi⟩
  let σ : quadraticFilled c → quadraticFilled c :=
    fun z => ⟨-(z : ℂ), (quadratic_filled_neg_mem c (z : ℂ)).mpr z.property⟩
  have hFT : MapsTo (quadraticFilledMap c) T T :=
    LoopsStationaryGeometricFibers.quadratic_least_carrier_forward_invariant
      c (quadraticFilled c) (quadraticFilledMap c) σ (fun _ => rfl)
      (fun _ => rfl) (quadratic_filled_map_surjective c) crit hcrit
      M T hTc hTk hMT hFM (hFM hcritM) hleast
  obtain ⟨hd, _, hn⟩ := quadratic_terminal_least_carrier_proper_lc
    c q G hq hsurj hs hf a ha hfix hnoncut K next hc hk hmap hdis T hTk hKT hleastK
  exact ⟨T, hTc, hTk, hKT, hleastK, hFT, hd, hn⟩

end LoopsTerminalFiberExclusion
