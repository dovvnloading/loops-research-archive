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
  constructor
  · intro h hn
    exact h hn.1
  · intro h hn
    exact h ⟨hn, hy⟩

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


/-- On any retained connected set avoiding the critical point, a
continuous quadratic inverse section trivializes the two sheets.
The sign cannot change even along a connected set that has no paths. -/
theorem quadratic_injOn_of_continuous_section (c : ℂ) (E U : Set ℂ)
    (s : ℂ → ℂ) (hE : IsPreconnected E) (hzero : (0 : ℂ) ∉ E)
    (hmap : MapsTo (fun z : ℂ => z^2+c) E U)
    (hs : ContinuousOn s U) (hsection : ∀ w ∈ U, (s w)^2+c = w) :
    InjOn (fun z : ℂ => z^2+c) E := by
  let f : ℂ → ℂ := fun z => z^2+c
  let u : ℂ → ℂ := fun z => z / s (f z)
  have hf : Continuous f := (continuous_id.pow 2).add continuous_const
  have hcomp : ContinuousOn (fun z => s (f z)) E :=
    hs.comp hf.continuousOn hmap
  have hrel (z : ℂ) (hz : z ∈ E) : (s (f z))^2 = z^2 := by
    have h := hsection (f z) (hmap hz)
    change (s (f z))^2+c = z^2+c at h
    linear_combination h
  have hsne (z : ℂ) (hz : z ∈ E) : s (f z) ≠ 0 := by
    intro h
    have hh := hrel z hz
    rw [h] at hh
    have hzsq : z*z = 0 := by linear_combination -hh
    rcases mul_eq_zero.mp hzsq with he | he <;> exact hzero (he ▸ hz)
  have hu : ContinuousOn u E := continuous_id.continuousOn.div hcomp hsne
  have hsign (z : ℂ) (hz : z ∈ E) : u z = 1 ∨ u z = -1 := by
    have hh := hrel z hz
    have hp : (z-s (f z))*(z+s (f z)) = 0 := by linear_combination -hh
    rcases mul_eq_zero.mp hp with hp | hp
    · left
      change z / s (f z) = 1
      apply (div_eq_iff (hsne z hz)).2
      simpa using sub_eq_zero.mp hp
    · right
      change z / s (f z) = -1
      apply (div_eq_iff (hsne z hz)).2
      have he : z = -s (f z) := by linear_combination hp
      simpa using he
  have himage : IsPreconnected (u '' E) := hE.image u hu
  have hcover : u '' E ⊆ ({1} : Set ℂ) ∪ {-1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hsign z hz
  have hnot : ¬ ((1 : ℂ) ∈ u '' E ∧ (-1 : ℂ) ∈ u '' E) := by
    rintro ⟨hp, hm⟩
    obtain ⟨w, _, hw1, hw2⟩ := (isPreconnected_closed_iff.mp himage)
      {1} {-1} isClosed_singleton isClosed_singleton hcover
      ⟨1, hp, mem_singleton _⟩ ⟨-1, hm, mem_singleton _⟩
    have h1 : w = 1 := hw1
    have h2 : w = -1 := hw2
    rw [h1] at h2
    norm_num at h2
  intro x hx y hy hxy
  have hr : u x = u y := by
    rcases hsign x hx with hxp | hxm <;> rcases hsign y hy with hyp | hym
    · exact hxp.trans hyp.symm
    · exact False.elim (hnot ⟨⟨x,hx,hxp⟩, ⟨y,hy,hym⟩⟩)
    · exact False.elim (hnot ⟨⟨y,hy,hyp⟩, ⟨x,hx,hxm⟩⟩)
    · exact hxm.trans hym.symm
  change f x = f y at hxy
  change x / s (f x) = y / s (f y) at hr
  rw [← hxy] at hr
  calc
    x = (x / s (f x)) * s (f x) := (div_mul_cancel₀ x (hsne x hx)).symm
    _ = (y / s (f x)) * s (f x) := by rw [hr]
    _ = y := div_mul_cancel₀ y (hsne x hx)

/-- The analytic section is constructed using Mathlib's covering-space
root theorem, not postulated. Any connected set mapping into an open
simply connected domain avoiding the critical value lies in one sheet. -/
theorem quadratic_injOn_over_simplyConnected (c : ℂ) (E U : Set ℂ)
    (hE : IsPreconnected E) (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (hc : c ∉ U) (hmap : MapsTo (fun z : ℂ => z^2+c) E U) :
    InjOn (fun z : ℂ => z^2+c) E := by
  have hzero : (0 : ℂ) ∉ E := by
    intro hz
    apply hc
    simpa using hmap hz
  have hg : ContinuousOn (fun w : ℂ => w-c) U :=
    (continuous_id.sub continuous_const).continuousOn
  have h0 : (0 : ℂ) ∉ (fun w : ℂ => w-c) '' U := by
    rintro ⟨w, hw, he⟩
    change w-c = 0 at he
    exact hc ((sub_eq_zero.mp he) ▸ hw)
  obtain ⟨s, hs, hpow⟩ := Complex.exists_continuousOn_pow_eq
    hUc hUo hg h0 (n := 2) (by norm_num)
  apply quadratic_injOn_of_continuous_section c E U s hE hzero hmap hs
  intro w hw
  rw [hpow]
  ring

/-- A branch domain supplies a full connected-component separator,
not merely the absence of a continuous path between reflected points. -/
theorem reflected_points_separated (c : ℂ) (S U : Set ℂ) (a : ℂ)
    (ha : a ∈ S) (hne : a ≠ 0) (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) (hc : c ∉ U)
    (hmap : MapsTo (fun z : ℂ => z^2+c) S U) :
    -a ∉ connectedComponentIn S a := by
  intro hb
  have hsub := connectedComponentIn_subset S a
  have hinj := quadratic_injOn_over_simplyConnected c
    (connectedComponentIn S a) U isPreconnected_connectedComponentIn
    hUc hUo hc (fun z hz => hmap (hsub hz))
  have he : a = -a :=
    hinj (mem_connectedComponentIn ha) hb (by ring)
  exact hne (by linear_combination (1/2 : ℂ) * he)

/-- Symmetric deletion commutes exactly with the actual quadratic
image; the critical-value cut is in the target, not a chosen deck label. -/
theorem quadratic_image_diff_symmetric (c : ℂ) (K Q : Set ℂ)
    (hsym : ∀ z ∈ Q, -z ∈ Q) :
    (fun z : ℂ => z^2+c) '' (K \ Q) =
      (fun z : ℂ => z^2+c) '' K \ (fun z : ℂ => z^2+c) '' Q := by
  let f : ℂ → ℂ := fun z => z^2+c
  have hsat : f ⁻¹' (f '' Q) = Q := quadratic_image_preimage_symmetric c Q hsym
  change f '' (K \ Q) = f '' K \ f '' Q
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    intro h
    have hzq : z ∈ f ⁻¹' (f '' Q) := h
    rw [hsat] at hzq
    exact hz.2 hzq
  · rintro ⟨⟨z, hzK, rfl⟩, hw⟩
    exact ⟨z, ⟨hzK, fun hzQ => hw ⟨z, hzQ, rfl⟩⟩, rfl⟩

/-- Actual base-separator criterion for the symmetric critical little
filled set. The remaining analytic input is a single simply connected
target domain containing the displayed actual image difference. -/
theorem quadratic_reflected_base_separator (c : ℂ) (K Q U : Set ℂ)
    (a : ℂ) (ha : a ∈ K \ Q) (hne : a ≠ 0)
    (hsym : ∀ z ∈ Q, -z ∈ Q) (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) (hc : c ∉ U)
    (hU : ((fun z : ℂ => z^2+c) '' K \ (fun z : ℂ => z^2+c) '' Q) ⊆ U) :
    -a ∉ connectedComponentIn (K \ Q) a := by
  apply reflected_points_separated c (K \ Q) U a ha hne hUc hUo hc
  intro z hz
  apply hU
  rw [← quadratic_image_diff_symmetric c K Q hsym]
  exact ⟨z, hz, rfl⟩

end LoopsStationarySeparatorTransport
