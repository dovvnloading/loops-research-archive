import StationaryFiberDynamics
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

end LoopsTerminalFiberExclusion
