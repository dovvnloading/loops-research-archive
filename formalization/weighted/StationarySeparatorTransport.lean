import Mathlib

/-!
# Exact terminal-sheet component transport

The ambient space is the full carrier, not a graph of component labels.
A singleton frontier gives exact connected-component restriction for
arbitrary retained subsets containing the attachment. No local
connectivity, compactness or path-connectedness is required.
-/

namespace LoopsStationarySeparatorTransport
open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def terminalRetract (O : Set X) (a : X) : X → X := by
  classical
  exact O.piecewise id (fun _ => a)

theorem terminalRetract_continuous (O : Set X) (a : X)
    (hfront : frontier O ⊆ {a}) :
    Continuous (terminalRetract O a) := by
  classical
  unfold terminalRetract
  apply Continuous.piecewise
  · intro z hz
    exact (show z = a from hfront hz)
  · exact continuous_id
  · exact continuous_const

theorem terminalRetract_fixed (O : Set X) (a x : X)
    (hx : x ∈ O ∪ {a}) : terminalRetract O a x = x := by
  classical
  rcases hx with hx | hx
  · simp [terminalRetract, Set.piecewise, hx]
  · have he : x = a := hx
    subst x
    by_cases h : a ∈ O <;> simp [terminalRetract, Set.piecewise, h]

theorem terminalRetract_mapsTo (O S : Set X) (a : X)
    (ha : a ∈ S) : MapsTo (terminalRetract O a) S (S ∩ (O ∪ {a})) := by
  classical
  intro z hz
  by_cases h : z ∈ O
  · have hr : terminalRetract O a z = z :=
      terminalRetract_fixed O a z (Or.inl h)
    rw [hr]
    exact ⟨hz, Or.inl h⟩
  · have hr : terminalRetract O a z = a := by
      simp [terminalRetract, Set.piecewise, h]
    rw [hr]
    exact ⟨ha, Or.inr (mem_singleton a)⟩

/-- Restricting an ambient component to the closed terminal sheet
gives exactly the component calculated inside that sheet. This is
valid after arbitrary deletions, as long as the attachment is retained. -/
theorem component_inter_terminalSheet (O S : Set X) (a x : X)
    (hfront : frontier O ⊆ {a}) (ha : a ∈ S)
    (hx : x ∈ S ∩ (O ∪ {a})) :
    connectedComponentIn S x ∩ (O ∪ {a}) =
      connectedComponentIn (S ∩ (O ∪ {a})) x := by
  let r := terminalRetract O a
  have hr : Continuous r := terminalRetract_continuous O a hfront
  have hm : MapsTo r S (S ∩ (O ∪ {a})) := terminalRetract_mapsTo O S a ha
  have hc : IsPreconnected (r '' connectedComponentIn S x) :=
    isPreconnected_connectedComponentIn.image r hr.continuousOn
  have hxr : x ∈ r '' connectedComponentIn S x :=
    ⟨x, mem_connectedComponentIn hx.1, terminalRetract_fixed O a x hx.2⟩
  have hsub : r '' connectedComponentIn S x ⊆ S ∩ (O ∪ {a}) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hm (connectedComponentIn_subset S x hz)
  have hlocal := hc.subset_connectedComponentIn hxr hsub
  apply Subset.antisymm
  · intro z hz
    exact hlocal ⟨z, hz.1, terminalRetract_fixed O a z hz.2⟩
  · intro z hz
    have hglobal : connectedComponentIn (S ∩ (O ∪ {a})) x ⊆
        connectedComponentIn S x :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hx) (fun w hw =>
          (connectedComponentIn_subset (S ∩ (O ∪ {a})) x hw).1)
    exact ⟨hglobal hz, (connectedComponentIn_subset (S ∩ (O ∪ {a})) x hz).2⟩

/-- If a local component misses the attachment, no additional point
of that component can be reached by leaving the sheet. -/
theorem component_eq_local_of_attachment_missing (O S : Set X) (a x : X)
    (hfront : frontier O ⊆ {a}) (ha : a ∈ S)
    (hx : x ∈ S ∩ (O ∪ {a}))
    (hmiss : a ∉ connectedComponentIn (S ∩ (O ∪ {a})) x) :
    connectedComponentIn S x = connectedComponentIn (S ∩ (O ∪ {a})) x := by
  classical
  have heq := component_inter_terminalSheet O S a x hfront ha hx
  let r := terminalRetract O a
  have hr : Continuous r := terminalRetract_continuous O a hfront
  have hc : IsPreconnected (r '' connectedComponentIn S x) :=
    isPreconnected_connectedComponentIn.image r hr.continuousOn
  have hx' : x ∈ r '' connectedComponentIn S x :=
    ⟨x, mem_connectedComponentIn hx.1, terminalRetract_fixed O a x hx.2⟩
  have hsub : r '' connectedComponentIn S x ⊆ S ∩ (O ∪ {a}) := by
    rintro _ ⟨z, hz, rfl⟩
    exact terminalRetract_mapsTo O S a ha (connectedComponentIn_subset S x hz)
  have hlocal := hc.subset_connectedComponentIn hx' hsub
  have hstay : connectedComponentIn S x ⊆ O := by
    intro z hz
    by_contra hn
    have he : r z = a := by simp [r, terminalRetract, Set.piecewise, hn]
    exact hmiss (hlocal ⟨z, hz, he⟩)
  apply Subset.antisymm
  · intro z hz
    exact hlocal ⟨z, hz, terminalRetract_fixed O a z (Or.inl (hstay hz))⟩
  · intro z hz
    have hz' : z ∈ connectedComponentIn S x ∩ (O ∪ {a}) := by
      rw [heq]
      exact hz
    exact hz'.1

/-- An explicit equivalence for the no-bypass clause: inside the
terminal sheet, separation is neither lost nor gained in the full carrier. -/
theorem separator_iff_local (O S : Set X) (a x y : X)
    (hfront : frontier O ⊆ {a}) (ha : a ∈ S)
    (hx : x ∈ S ∩ (O ∪ {a})) (hy : y ∈ O ∪ {a}) :
    y ∉ connectedComponentIn S x ↔
      y ∉ connectedComponentIn (S ∩ (O ∪ {a})) x := by
  rw [← component_inter_terminalSheet O S a x hfront ha hx]
  simp [hy]

/-- A continuous inverse-coordinate map on the retained sheet carries
any potential ambient bypass to a connected bypass in the base. -/
theorem separator_transport (O S : Set X) (A : Set Y) (a y : X)
    (g : X → Y) (hfront : frontier O ⊆ {a}) (ha : a ∈ S)
    (hy : y ∈ O ∪ {a})
    (hg : ContinuousOn g (S ∩ (O ∪ {a})))
    (hm : MapsTo g (S ∩ (O ∪ {a})) A)
    (hsep : g y ∉ connectedComponentIn A (g a)) :
    y ∉ connectedComponentIn S a := by
  have hx : a ∈ S ∩ (O ∪ {a}) := ⟨ha, Or.inr (mem_singleton a)⟩
  apply (separator_iff_local O S a a y hfront ha hx hy).2
  intro hyc
  have hcsub := connectedComponentIn_subset (S ∩ (O ∪ {a})) a
  have hc : IsPreconnected (g '' connectedComponentIn (S ∩ (O ∪ {a})) a) :=
    isPreconnected_connectedComponentIn.image g (hg.mono hcsub)
  have hga : g a ∈ g '' connectedComponentIn (S ∩ (O ∪ {a})) a :=
    ⟨a, mem_connectedComponentIn hx, rfl⟩
  have hsub : g '' connectedComponentIn (S ∩ (O ∪ {a})) a ⊆ A := by
    rintro _ ⟨z, hz, rfl⟩
    exact hm (hcsub hz)
  exact hsep (hc.subset_connectedComponentIn hga hsub ⟨y, hyc, rfl⟩)

/-- The component containing the attachment is exactly the union of
its components on the two sides. Disconnected exterior branches
are not incorrectly added to the global component. -/
theorem attachment_component_union (O S : Set X) (a : X)
    (hfront : frontier O ⊆ {a}) (ha : a ∈ S) (hao : a ∉ O) :
    connectedComponentIn S a =
      connectedComponentIn (S ∩ (O ∪ {a})) a ∪
      connectedComponentIn (S ∩ Oᶜ) a := by
  have h1 := component_inter_terminalSheet O S a a hfront ha
    ⟨ha, Or.inr (mem_singleton a)⟩
  have hf : frontier Oᶜ ⊆ {a} := by simpa only [frontier_compl] using hfront
  have h2 := component_inter_terminalSheet Oᶜ S a a hf ha
    ⟨ha, Or.inr (mem_singleton a)⟩
  have he : Oᶜ ∪ ({a} : Set X) = Oᶜ := by
    apply Subset.antisymm
    · intro z hz
      rcases hz with hz | hz
      · exact hz
      · have hza : z = a := hz
        subst z
        exact hao
    · exact subset_union_left
  rw [he] at h2
  rw [← h1, ← h2]
  ext z
  constructor
  · intro hz
    by_cases h : z ∈ O
    · exact Or.inl ⟨hz, Or.inl h⟩
    · exact Or.inr ⟨hz, h⟩
  · rintro (h | h) <;> exact h.1

/-- Actual quadratic fibers are exactly antipodal pairs, including
the degenerate singleton at the critical point. -/
theorem quadratic_image_preimage_symmetric (c : ℂ) (Q : Set ℂ)
    (hsym : ∀ z ∈ Q, -z ∈ Q) :
    (fun z : ℂ => z^2+c) ⁻¹' ((fun z : ℂ => z^2+c) '' Q) = Q := by
  ext z
  constructor
  · intro hz
    change (z^2+c) ∈ (fun w : ℂ => w^2+c) '' Q at hz
    obtain ⟨w, hw, he⟩ := hz
    change w^2+c = z^2+c at he
    have hprod : (w-z)*(w+z) = 0 := by linear_combination he
    rcases mul_eq_zero.mp hprod with h | h
    · have hwz : w = z := sub_eq_zero.mp h
      rwa [← hwz]
    · have hwz : -w = z := by linear_combination -h
      rw [← hwz]
      exact hsym w hw
  · intro hz
    exact ⟨z, hz, rfl⟩

end LoopsStationarySeparatorTransport
