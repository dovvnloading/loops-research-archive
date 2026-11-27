import StationaryFiberDynamics

/-!
# Local degree exhaustion of embedded quadratic filled sets

A compact embedded copy of an actual quadratic filled set is isolated in
its full ambient inverse image when the ambient map has the same local
one-sheet and two-sheet bounds as the intrinsic quadratic map.  The source
map is open even at the critical point.  Its open images, compactness of
the embedded source, and the two opposite quadratic roots supply every
local sheet; inverse-image saturation is a conclusion.
-/

namespace LoopsLocalDegreeExhaustion

open Set Function LoopsStationaryFiberDynamics

set_option maxHeartbeats 1000000

private theorem compact_open_image_neighborhood
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (h : X → ℂ) (hh : Continuous h) (hi : Injective h)
    (T : Set X) (hT : IsOpen T) :
    ∃ V : Set ℂ, IsOpen V ∧ h ⁻¹' V = T := by
  refine ⟨(h '' Tᶜ)ᶜ, (hT.isClosed_compl.isCompact.image hh).isClosed.isOpen_compl, ?_⟩
  ext x
  change h x ∉ h '' Tᶜ ↔ x ∈ T
  constructor
  · intro hx
    by_contra hxT
    exact hx ⟨x, hxT, rfl⟩
  · intro hx
    rintro ⟨y, hy, he⟩
    have hyx : y = x := hi he
    subst y
    exact hy hx

private theorem local_exhaustion_from_source_neighborhood
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → X) (hg : IsOpenMap g)
    (F : ℂ → ℂ) (hF : Continuous F)
    (h : X → ℂ) (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, F (h x) = h (g x))
    (x : X) (U : Set ℂ) (hU : IsOpen U) (hxU : h x ∈ U)
    (W : Set X) (hW : IsOpen W) (hxW : x ∈ W)
    (hcount : ∀ z ∈ U, ∀ v ∈ W, F z = F (h v) → z ∈ range h) :
    ∃ V : Set ℂ, IsOpen V ∧ h x ∈ V ∧ V ∩ F ⁻¹' range h ⊆ range h := by
  obtain ⟨B, hB, heB⟩ := compact_open_image_neighborhood h hh hi (g '' W) (hg W hW)
  have hxB : F (h x) ∈ B := by
    rw [hc x]
    change g x ∈ h ⁻¹' B
    rw [heB]
    exact ⟨x, hxW, rfl⟩
  refine ⟨U ∩ F ⁻¹' B, hU.inter (hB.preimage hF), ⟨hxU, hxB⟩, ?_⟩
  intro z hz
  obtain ⟨y, hy⟩ := hz.2
  have hyB : h y ∈ B := by
    rw [hy]
    exact hz.1.2
  have hyW : y ∈ g '' W := by
    rw [← heB]
    exact hyB
  obtain ⟨v, hv, hgv⟩ := hyW
  apply hcount z hz.1.1 v hv
  rw [hc v, hgv]
  exact hy.symm

/-- At an intrinsic regular point, ambient local injectivity exhausts
the nearby roots over the embedded actual filled set.  The source root
is produced by openness of the genuine quadratic restriction. -/
theorem quadratic_conjugacy_regular_local_containment
    (q : ℂ) (F : ℂ → ℂ) (h : quadraticFilled q → ℂ)
    (hF : Continuous F) (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, F (h x) = h (quadraticFilledMap q x))
    (x : quadraticFilled q) (U : Set ℂ)
    (hU : IsOpen U) (hxU : h x ∈ U) (hinj : InjOn F U) :
    ∃ V : Set ℂ, IsOpen V ∧ h x ∈ V ∧ V ∩ F ⁻¹' range h ⊆ range h := by
  letI : CompactSpace (quadraticFilled q) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact q)
  have hg : IsOpenMap (quadraticFilledMap q) :=
    quadratic_restriction_open q (quadraticFilled q) (quadraticFilledMap q)
      (fun _ => rfl) (fun z hz => (quadratic_filled_complete_invariant q z).mp hz)
  apply local_exhaustion_from_source_neighborhood (quadraticFilledMap q) hg
    F hF h hh hi hc x U hU hxU (h ⁻¹' U) (hU.preimage hh) hxU
  intro z hz v hv he
  exact ⟨v, (hinj hz hv he).symm⟩

/-- At the intrinsic critical point, symmetric source neighborhoods
provide both distinct roots of every nearby noncritical target.  The
ambient three-point exclusion then forces every nearby root into the
embedded carrier.  The critical target is handled by its singleton fiber. -/
theorem quadratic_conjugacy_critical_local_containment
    (q : ℂ) (F : ℂ → ℂ) (h : quadraticFilled q → ℂ)
    (hF : Continuous F) (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, F (h x) = h (quadraticFilledMap q x))
    (x : quadraticFilled q) (hx0 : (x : ℂ) = 0)
    (U : Set ℂ) (hU : IsOpen U) (hxU : h x ∈ U)
    (htwo : ∀ z ∈ U, ∀ w ∈ U, ∀ v ∈ U,
      F z = F w → F z = F v → z = w ∨ z = v ∨ w = v)
    (hsingle : ∀ z ∈ U, F z = F (h x) → z = h x) :
    ∃ V : Set ℂ, IsOpen V ∧ h x ∈ V ∧ V ∩ F ⁻¹' range h ⊆ range h := by
  letI : CompactSpace (quadraticFilled q) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact q)
  have hnegmem (v : quadraticFilled q) : -(v : ℂ) ∈ quadraticFilled q := by
    apply (quadratic_filled_complete_invariant q (-(v : ℂ))).mp
    have he : (-(v : ℂ)) ^ 2 + q = (v : ℂ) ^ 2 + q := by ring
    rw [he]
    exact (quadraticFilledMap q v).property
  let s : quadraticFilled q → quadraticFilled q := fun v => ⟨-(v : ℂ), hnegmem v⟩
  have hs : Continuous s :=
    ((continuous_subtype_val : Continuous
      (Subtype.val : quadraticFilled q → ℂ)).neg).subtype_mk _
  have hsx : s x = x := by
    apply Subtype.ext
    change -(x : ℂ) = (x : ℂ)
    rw [hx0, neg_zero]
  have hsg (v : quadraticFilled q) :
      quadraticFilledMap q (s v) = quadraticFilledMap q v := by
    apply Subtype.ext
    change (-(v : ℂ)) ^ 2 + q = (v : ℂ) ^ 2 + q
    ring
  have hg : IsOpenMap (quadraticFilledMap q) :=
    quadratic_restriction_open q (quadraticFilled q) (quadraticFilledMap q)
      (fun _ => rfl) (fun z hz => (quadratic_filled_complete_invariant q z).mp hz)
  let W : Set (quadraticFilled q) := (h ⁻¹' U) ∩ s ⁻¹' (h ⁻¹' U)
  have hW : IsOpen W := (hU.preimage hh).inter ((hU.preimage hh).preimage hs)
  have hxW : x ∈ W := ⟨hxU, by change h (s x) ∈ U; rw [hsx]; exact hxU⟩
  apply local_exhaustion_from_source_neighborhood (quadraticFilledMap q) hg
    F hF h hh hi hc x U hU hxU W hW hxW
  intro z hz v hv he
  by_cases hv0 : (v : ℂ) = 0
  · have hvx : v = x := Subtype.ext (hv0.trans hx0.symm)
    have he' : F z = F (h x) := by simpa only [hvx] using he
    exact ⟨x, (hsingle z hz he').symm⟩
  · have hpair : h v ≠ h (s v) := by
      intro heq
      have hvneg : (v : ℂ) = -(v : ℂ) := congrArg Subtype.val (hi heq)
      exact hv0 (by linear_combination (1 / 2 : ℂ) * hvneg)
    have he' : F z = F (h (s v)) := by
      rw [hc (s v), hsg, ← hc v]
      exact he
    rcases htwo z hz (h v) hv.1 (h (s v)) hv.2 he he' with h1 | h2 | h3
    · exact ⟨v, h1.symm⟩
    · exact ⟨s v, h2.symm⟩
    · exact (hpair h3).elim

/-- Matching local one-sheet and simple two-sheet bounds isolate the
entire compact quadratic carrier in its ambient inverse image.  The
open neighborhood is constructed from the local root-exhaustion proofs. -/
theorem quadratic_conjugacy_local_exhaustion
    (q : ℂ) (F : ℂ → ℂ) (h : quadraticFilled q → ℂ)
    (hF : Continuous F) (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, F (h x) = h (quadraticFilledMap q x))
    (hregular : ∀ x : quadraticFilled q, (x : ℂ) ≠ 0 →
      ∃ U : Set ℂ, IsOpen U ∧ h x ∈ U ∧ InjOn F U)
    (hcritical : ∀ x : quadraticFilled q, (x : ℂ) = 0 →
      ∃ U : Set ℂ, IsOpen U ∧ h x ∈ U ∧
        (∀ z ∈ U, ∀ w ∈ U, ∀ v ∈ U,
          F z = F w → F z = F v → z = w ∨ z = v ∨ w = v) ∧
        (∀ z ∈ U, F z = F (h x) → z = h x)) :
    ∃ V : Set ℂ, IsOpen V ∧ range h ⊆ V ∧ V ∩ F ⁻¹' range h = range h := by
  classical
  have hlocal (x : quadraticFilled q) :
      ∃ V : Set ℂ, IsOpen V ∧ h x ∈ V ∧ V ∩ F ⁻¹' range h ⊆ range h := by
    by_cases hx : (x : ℂ) = 0
    · obtain ⟨U, hU, hxU, htwo, hsingle⟩ := hcritical x hx
      exact quadratic_conjugacy_critical_local_containment q F h hF hh hi hc
        x hx U hU hxU htwo hsingle
    · obtain ⟨U, hU, hxU, hinj⟩ := hregular x hx
      exact quadratic_conjugacy_regular_local_containment q F h hF hh hi hc
        x U hU hxU hinj
  choose V hVo hxV hV using hlocal
  refine ⟨⋃ x, V x, isOpen_iUnion hVo, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact mem_iUnion.mpr ⟨x, hxV x⟩
  · apply Subset.antisymm
    · intro z hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp hz.1
      exact hV x ⟨hx, hz.2⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨mem_iUnion.mpr ⟨x, hxV x⟩, ⟨quadraticFilledMap q x, (hc x).symm⟩⟩

/-- The exhausted carrier is both open and closed relative to its full
ambient inverse image.  Closedness follows from actual source compactness. -/
theorem quadratic_conjugacy_preimage_clopen
    (q : ℂ) (F : ℂ → ℂ) (h : quadraticFilled q → ℂ)
    (hF : Continuous F) (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, F (h x) = h (quadraticFilledMap q x))
    (hregular : ∀ x : quadraticFilled q, (x : ℂ) ≠ 0 →
      ∃ U : Set ℂ, IsOpen U ∧ h x ∈ U ∧ InjOn F U)
    (hcritical : ∀ x : quadraticFilled q, (x : ℂ) = 0 →
      ∃ U : Set ℂ, IsOpen U ∧ h x ∈ U ∧
        (∀ z ∈ U, ∀ w ∈ U, ∀ v ∈ U,
          F z = F w → F z = F v → z = w ∨ z = v ∨ w = v) ∧
        (∀ z ∈ U, F z = F (h x) → z = h x)) :
    IsClopen ((Subtype.val : F ⁻¹' range h → ℂ) ⁻¹' range h) := by
  letI : CompactSpace (quadraticFilled q) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact q)
  obtain ⟨V, hV, hAV, heV⟩ :=
    quadratic_conjugacy_local_exhaustion q F h hF hh hi hc hregular hcritical
  have he : (Subtype.val : F ⁻¹' range h → ℂ) ⁻¹' range h =
      (Subtype.val : F ⁻¹' range h → ℂ) ⁻¹' V := by
    ext z
    constructor
    · exact fun hz => hAV hz
    · intro hz
      have hz' : (z : ℂ) ∈ V ∩ F ⁻¹' range h := ⟨hz, z.property⟩
      rwa [heV] at hz'
  refine ⟨(isCompact_range hh).isClosed.preimage continuous_subtype_val, ?_⟩
  rw [he]
  exact hV.preimage continuous_subtype_val

/-- A connected embedded carrier with matched local sheet bounds is
its entire selected ambient pullback component.  This excludes external
connected appendages, including ones without paths or local connectivity. -/
theorem quadratic_conjugacy_component
    (q : ℂ) (F : ℂ → ℂ) (h : quadraticFilled q → ℂ)
    (hF : Continuous F) (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, F (h x) = h (quadraticFilledMap q x))
    (hregular : ∀ x : quadraticFilled q, (x : ℂ) ≠ 0 →
      ∃ U : Set ℂ, IsOpen U ∧ h x ∈ U ∧ InjOn F U)
    (hcritical : ∀ x : quadraticFilled q, (x : ℂ) = 0 →
      ∃ U : Set ℂ, IsOpen U ∧ h x ∈ U ∧
        (∀ z ∈ U, ∀ w ∈ U, ∀ v ∈ U,
          F z = F w → F z = F v → z = w ∨ z = v ∨ w = v) ∧
        (∀ z ∈ U, F z = F (h x) → z = h x))
    (hconnected : IsPreconnected (range h)) (x : quadraticFilled q) :
    range h = connectedComponentIn (F ⁻¹' range h) (h x) := by
  letI : CompactSpace (quadraticFilled q) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact q)
  obtain ⟨V, hV, hAV, heV⟩ :=
    quadratic_conjugacy_local_exhaustion q F h hF hh hi hc hregular hcritical
  have hA : IsClosed (range h) := (isCompact_range hh).isClosed
  have hforward : range h ⊆ F ⁻¹' range h := by
    rintro _ ⟨y, rfl⟩
    exact ⟨quadraticFilledMap q y, (hc y).symm⟩
  have hsub := hconnected.subset_connectedComponentIn (mem_range_self x) hforward
  apply Subset.antisymm hsub
  intro z hz
  by_contra hzA
  have hzV : z ∈ Vᶜ := by
    intro hzV
    apply hzA
    rw [← heV]
    exact ⟨hzV, connectedComponentIn_subset (F ⁻¹' range h) (h x) hz⟩
  have hcover : connectedComponentIn (F ⁻¹' range h) (h x) ⊆ range h ∪ Vᶜ := by
    intro w hw
    by_cases hwV : w ∈ V
    · left
      rw [← heV]
      exact ⟨hwV, connectedComponentIn_subset (F ⁻¹' range h) (h x) hw⟩
    · exact Or.inr hwV
  obtain ⟨w, _, hwA, hwV⟩ :=
    (isPreconnected_closed_iff.mp
      (isPreconnected_connectedComponentIn (F := F ⁻¹' range h) (x := h x)))
      (range h) Vᶜ hA hV.isClosed_compl hcover
      ⟨h x, hsub (mem_range_self x), mem_range_self x⟩ ⟨z, hz, hzV⟩
  exact hwV (hAV hwA)

end LoopsLocalDegreeExhaustion
