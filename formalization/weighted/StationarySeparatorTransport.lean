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

open Function Topology unitInterval

/-- A continuous logarithm can be transported along a nonvanishing
homotopy, without any local connectivity assumption on its parameter space. -/
theorem log_lift_homotopy {A : Type*} [TopologicalSpace A]
    (H : I × A → ℂ) (hH : Continuous H) (hne : ∀ z, H z ≠ 0)
    (g0 : C(A, ℂ)) (h0 : ∀ z, H (0,z) = Complex.exp (g0 z)) :
    ∃ g1 : C(A, ℂ), ∀ z, Complex.exp (g1 z) = H (1,z) := by
  let H' : C(I × A, {z : ℂ // z ≠ 0}) :=
    ⟨fun z => ⟨H z, hne z⟩, hH.subtype_mk _⟩
  have h0' (z : A) : H' (0,z) =
      (⟨Complex.exp (g0 z), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) :=
    Subtype.ext (h0 z)
  let L := Complex.isCoveringMap_exp.liftHomotopy H' g0 h0'
  refine ⟨⟨fun z => L (1,z), L.continuous.comp (continuous_const.prodMk continuous_id)⟩, ?_⟩
  intro z
  exact congrArg Subtype.val
    (congrFun (Complex.isCoveringMap_exp.liftHomotopy_lifts H' g0 h0') (1,z))

/-- A compact target avoiding an unbounded connected cut admits a logarithm
about every point of that cut. Move the center from outside a bounding
disk along a path in the open complement of the compact target. This uses
homotopy lifting, not simple connectivity of the target or Jordan separation. -/
theorem log_on_compact_avoiding_unbounded_cut (T D : Set ℂ) (c : ℂ)
    (hT : IsCompact T) (hD : IsPreconnected D) (hc : c ∈ D)
    (hdis : Disjoint D T) (hunb : ∀ R : ℝ, ∃ z ∈ D, R < ‖z‖) :
    ∃ g : C(T, ℂ), ∀ z : T, Complex.exp (g z) = (z : ℂ)-c := by
  obtain ⟨R,hR⟩ := hT.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨d,hdD,hdR⟩ := hunb (max R 0)
  have hdne : d ≠ 0 := by
    intro h
    rw [h,norm_zero] at hdR
    exact (not_lt_of_ge (le_max_right R 0)) hdR
  have hfar (z : T) : ‖(z : ℂ)‖ < ‖d‖ :=
    (hR _ z.property).trans_lt ((le_max_left R 0).trans_lt hdR)
  let H : I × T → ℂ := fun t => (t.1 : ℝ) • (t.2 : ℂ) - d
  have hH : Continuous H := by
    dsimp [H]
    fun_prop
  have hne (t : I × T) : H t ≠ 0 := by
    intro h
    have he : (t.1 : ℝ) • (t.2 : ℂ) = d := sub_eq_zero.mp h
    have hb : ‖(t.1 : ℝ) • (t.2 : ℂ)‖ ≤ ‖(t.2 : ℂ)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.1.property.1]
      exact mul_le_of_le_one_left (norm_nonneg _) t.1.property.2
    rw [he] at hb
    exact (not_lt_of_ge hb) (hfar t.2)
  let g0 : C(T, ℂ) := ContinuousMap.const T (Complex.log (-d))
  have h0 (z : T) : H (0,z) = Complex.exp (g0 z) := by
    change (0 : ℝ) • (z : ℂ) - d = Complex.exp (Complex.log (-d))
    rw [Complex.exp_log (neg_ne_zero.mpr hdne)]
    simp
  obtain ⟨g1,hg1⟩ := log_lift_homotopy H hH hne g0 h0
  have hsub : D ⊆ Tᶜ := fun z hz hzt => Set.disjoint_left.mp hdis hz hzt
  have hdComp := hD.subset_connectedComponentIn hc hsub hdD
  have hcComp := mem_connectedComponentIn (hsub hc)
  have hop : IsOpen (connectedComponentIn Tᶜ c) :=
    hT.isClosed.isOpen_compl.connectedComponentIn
  have hcon : IsConnected (connectedComponentIn Tᶜ c) :=
    isConnected_connectedComponentIn_iff.mpr (hsub hc)
  obtain ⟨p,hp⟩ := (hop.isConnected_iff_isPathConnected.mp hcon).joinedIn d hdComp c hcComp
  let J : I × T → ℂ := fun t => (t.2 : ℂ) - p t.1
  have hJ : Continuous J :=
    (continuous_subtype_val.comp continuous_snd).sub (p.continuous.comp continuous_fst)
  have hjne (t : I × T) : J t ≠ 0 := by
    intro h
    have he : (t.2 : ℂ) = p t.1 := sub_eq_zero.mp h
    exact (connectedComponentIn_subset Tᶜ c (hp t.1)) (he ▸ t.2.property)
  have hj0 (z : T) : J (0,z) = Complex.exp (g1 z) := by
    rw [hg1]
    change (z : ℂ) - p 0 = (1 : ℝ) • (z : ℂ) - d
    rw [p.source, one_smul]
  obtain ⟨g,hg⟩ := log_lift_homotopy J hJ hjne g1 hj0
  refine ⟨g, fun z => ?_⟩
  rw [hg]
  change (z : ℂ) - p 1 = (z : ℂ) - c
  rw [p.target]

/-- No connected set in the preimage of the complement of a closed,
unbounded connected cut containing the critical value can contain
two distinct points of one quadratic fiber. The connected set itself
need not be path connected: use a path in the open ambient complement,
then construct a logarithm on its compact image. -/
theorem quadratic_injOn_avoiding_unbounded_cut (c : ℂ) (E D : Set ℂ)
    (hE : IsPreconnected E) (hD : IsPreconnected D) (hcl : IsClosed D)
    (hc : c ∈ D) (hunb : ∀ R : ℝ, ∃ z ∈ D, R < ‖z‖)
    (hdis : Disjoint D ((fun z : ℂ => z^2+c) '' E)) :
    InjOn (fun z : ℂ => z^2+c) E := by
  classical
  let f : ℂ → ℂ := fun z => z^2+c
  have hf : Continuous f := (continuous_id.pow 2).add continuous_const
  let V := f ⁻¹' Dᶜ
  have hv : IsOpen V := hcl.isOpen_compl.preimage hf
  have hsub : E ⊆ V := fun z hz hzd =>
    Set.disjoint_left.mp hdis hzd ⟨z,hz,rfl⟩
  intro x hx y hy hxy
  have hycomp := hE.subset_connectedComponentIn hx hsub hy
  have hxcomp := mem_connectedComponentIn (hsub hx)
  have hop := hv.connectedComponentIn (x := x)
  have hcon : IsConnected (connectedComponentIn V x) :=
    isConnected_connectedComponentIn_iff.mpr (hsub hx)
  obtain ⟨p,hp⟩ := (hop.isConnected_iff_isPathConnected.mp hcon).joinedIn x hxcomp y hycomp
  let P : Set ℂ := range p
  have hPV : P ⊆ V := by
    rintro _ ⟨t,rfl⟩
    exact connectedComponentIn_subset V x (hp t)
  let T : Set ℂ := f '' P
  have hP : IsCompact P := isCompact_range p.continuous
  have hT : IsCompact T := hP.image hf
  have hdt : Disjoint D T := by
    rw [Set.disjoint_left]
    rintro _ hz ⟨w,hw,rfl⟩
    exact hPV hw hz
  obtain ⟨g,hg⟩ := log_on_compact_avoiding_unbounded_cut T D c hT hD hc hdt hunb
  let s : ℂ → ℂ := fun w => if h : w ∈ T then Complex.exp (g ⟨w,h⟩ / 2) else 0
  have hs : ContinuousOn s T := by
    rw [continuousOn_iff_continuous_restrict]
    have hEq : T.restrict s = fun w : T => Complex.exp (g w / 2) := by
      funext w
      simp [s,Set.restrict,w.property]
    rw [hEq]
    exact Complex.continuous_exp.comp (g.continuous.div_const 2)
  have hsection (w : ℂ) (hw : w ∈ T) : (s w)^2+c = w := by
    rw [show s w = Complex.exp (g ⟨w,hw⟩ / 2) by simp [s,hw],pow_two,← Complex.exp_add]
    rw [show g ⟨w,hw⟩ / 2 + g ⟨w,hw⟩ / 2 = g ⟨w,hw⟩ by ring, hg]
    simp
  have hpc : IsPreconnected P := isPreconnected_range p.continuous
  have hzero : (0 : ℂ) ∉ P := by
    intro hz
    have hzv := hPV hz
    apply hzv
    simpa [f] using hc
  have hi := quadratic_injOn_of_continuous_section c P T s hpc hzero
    (fun z hz => show f z ∈ T from ⟨z,hz,rfl⟩) hs hsection
  exact hi ⟨0,p.source⟩ ⟨1,p.target⟩ hxy

/-- A single unbounded cut from the critical image to infinity, rather than
an externally supplied simply connected domain, suffices for antipodal
base separation. -/
theorem quadratic_reflected_separator_of_unbounded_cut (c : ℂ) (S D : Set ℂ)
    (a : ℂ) (ha : a ∈ S) (hne : a ≠ 0)
    (hD : IsPreconnected D) (hcl : IsClosed D) (hc : c ∈ D)
    (hunb : ∀ R : ℝ, ∃ z ∈ D, R < ‖z‖)
    (hdis : Disjoint D ((fun z : ℂ => z^2+c) '' S)) :
    -a ∉ connectedComponentIn S a := by
  intro hb
  have hsub := connectedComponentIn_subset S a
  have hdis' : Disjoint D ((fun z : ℂ => z^2+c) '' connectedComponentIn S a) :=
    hdis.mono_right (image_mono hsub)
  have hi := quadratic_injOn_avoiding_unbounded_cut c (connectedComponentIn S a) D
    isPreconnected_connectedComponentIn hD hcl hc hunb hdis'
  have he : a = -a := hi (mem_connectedComponentIn ha) hb (by ring)
  exact hne (by linear_combination (1/2 : ℂ) * he)

/-- A compact connected symmetric critical set Q and any closed connected
unbounded exterior ray R meeting f(Q) give the required cut. The ray
must avoid the actual retained image; the native ray construction is
the remaining dynamical input, not a hypothesis of simple connectivity. -/
theorem quadratic_base_separator_of_exterior_ray (c : ℂ) (K Q R : Set ℂ)
    (a : ℂ) (ha : a ∈ K \ Q) (hne : a ≠ 0)
    (hsym : ∀ z ∈ Q, -z ∈ Q) (h0 : 0 ∈ Q)
    (hQ : IsCompact Q) (hQc : IsConnected Q)
    (hR : IsClosed R) (hRc : IsConnected R)
    (hmeet : (((fun z : ℂ => z^2+c) '' Q) ∩ R).Nonempty)
    (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (hdis : Disjoint R ((fun z : ℂ => z^2+c) '' (K \ Q))) :
    -a ∉ connectedComponentIn (K \ Q) a := by
  let f : ℂ → ℂ := fun z => z^2+c
  have hf : Continuous f := (continuous_id.pow 2).add continuous_const
  let D := (f '' Q) ∪ R
  have hDc : IsConnected D := (hQc.image f hf.continuousOn).union hmeet hRc
  have hDcl : IsClosed D := (hQ.image hf).isClosed.union hR
  have hc : c ∈ D := Or.inl ⟨0,h0,by simp [f]⟩
  have hDu (B : ℝ) : ∃ z ∈ D, B < ‖z‖ := by
    obtain ⟨z,hz,hb⟩ := hunb B
    exact ⟨z,Or.inr hz,hb⟩
  have hDQ : Disjoint (f '' Q) (f '' (K \ Q)) := by
    rw [show f '' (K \ Q) = f '' K \ f '' Q from quadratic_image_diff_symmetric c K Q hsym]
    exact Set.disjoint_left.mpr (fun z hz hz' => hz'.2 hz)
  have hDd : Disjoint D (f '' (K \ Q)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases hz with hz | hz
    · exact Set.disjoint_left.mp hDQ hz hz'
    · exact Set.disjoint_left.mp hdis hz hz'
  exact quadratic_reflected_separator_of_unbounded_cut c (K \ Q) D a ha hne
    hDc.isPreconnected hDcl hc hDu hDd

/-- Properness of the actual restricted map gives compact inverse
images in the ambient plane, not just compactness in an abstract domain. -/
theorem proper_restriction_compact_preimage (f : ℂ → ℂ) (U V : Set ℂ)
    (hm : MapsTo f U V)
    (hp : IsProperMap (fun z : U => (⟨f z,hm z.property⟩ : V)))
    (B : Set ℂ) (hB : IsCompact B) (hBV : B ⊆ V) :
    IsCompact (U ∩ f ⁻¹' B) := by
  have hb : IsCompact (((↑) : V → ℂ) ⁻¹' B) :=
    IsInducing.subtypeVal.isCompact_preimage' hB (by
      rw [Subtype.range_coe]
      exact hBV)
  have hpre := hp.isCompact_preimage hb
  have him := hpre.image (continuous_subtype_val : Continuous ((↑) : U → ℂ))
  convert him using 1
  ext z
  constructor
  · rintro ⟨hz,hzf⟩
    exact ⟨⟨z,hz⟩,hzf,rfl⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.property,hw⟩

/-- A connected open proper restriction of an ambient continuous map
is a component of the entire inverse target. No assumption that the
selected restriction exhausts that component is needed. -/
theorem proper_restriction_is_component (f : ℂ → ℂ) (U V : Set ℂ) (a : ℂ)
    (hf : Continuous f) (hUo : IsOpen U) (hVo : IsOpen V)
    (hUc : IsPreconnected U) (ha : a ∈ U) (hm : MapsTo f U V)
    (hp : IsProperMap (fun z : U => (⟨f z,hm z.property⟩ : V))) :
    U = connectedComponentIn (f ⁻¹' V) a := by
  have hrel : closure U ∩ f ⁻¹' V ⊆ U := by
    intro x hx
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hVo (f x) hx.2
    let B := Metric.closedBall (f x) (ε/2)
    have hBV : B ⊆ V :=
      (Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hball
    have hclosed : IsClosed (U ∩ f ⁻¹' B) :=
      (proper_restriction_compact_preimage f U V hm hp B
        (isCompact_closedBall _ _) hBV).isClosed
    have hxb : x ∈ closure (U ∩ f ⁻¹' B) := by
      apply mem_closure_iff.mpr
      intro W hW hxW
      let N := W ∩ f ⁻¹' Metric.ball (f x) (ε/2)
      have hN : IsOpen N := hW.inter (Metric.isOpen_ball.preimage hf)
      have hxN : x ∈ N := ⟨hxW,by simpa using (half_pos hε)⟩
      obtain ⟨z,hzN,hzU⟩ := mem_closure_iff.mp hx.1 N hN hxN
      exact ⟨z,hzN.1,hzU,Metric.ball_subset_closedBall hzN.2⟩
    rw [hclosed.closure_eq] at hxb
    exact hxb.1
  have hu : U ⊆ f ⁻¹' V := hm
  have h1 := hUc.subset_connectedComponentIn ha hu
  apply Subset.antisymm h1
  intro z hz
  by_contra hzu
  have hcover : connectedComponentIn (f ⁻¹' V) a ⊆ closure U ∪ Uᶜ := by
    intro w hw
    by_cases h : w ∈ U
    · exact Or.inl (subset_closure h)
    · exact Or.inr h
  obtain ⟨w,hw,hwU,hwUc⟩ :=
    (isPreconnected_closed_iff.mp
      (isPreconnected_connectedComponentIn (F := f ⁻¹' V) (x := a)))
      (closure U) Uᶜ isClosed_closure hUo.isClosed_compl hcover
      ⟨a,h1 ha,subset_closure ha⟩ ⟨z,hz,hzu⟩
  exact hwUc (hrel ⟨hwU,connectedComponentIn_subset (f ⁻¹' V) a hw⟩)

/-- Every positive iterate of the actual quadratic polynomial is even. -/
theorem quadratic_positive_iterate_even (c : ℂ) (p : ℕ) (hp : 0 < p) (z : ℂ) :
    (fun w : ℂ => w^2+c)^[p] (-z) = (fun w : ℂ => w^2+c)^[p] z := by
  cases p with
  | zero => omega
  | succ p =>
    simp only [Function.iterate_succ_apply]
    congr 1
    ring

/-- The component of an even map's inverse target containing the fixed
point of reflection is itself invariant under reflection. -/
theorem even_preimage_component_symmetric (F : ℂ → ℂ) (V : Set ℂ)
    (heven : ∀ z, F (-z) = F z) :
    ∀ z ∈ connectedComponentIn (F ⁻¹' V) 0,
      -z ∈ connectedComponentIn (F ⁻¹' V) 0 := by
  intro z hz
  let A := connectedComponentIn (F ⁻¹' V) 0
  have h0 : (0 : ℂ) ∈ F ⁻¹' V :=
    connectedComponentIn_nonempty_iff.mp ⟨z,hz⟩
  have hconn : IsPreconnected ((fun w : ℂ => -w) '' A) :=
    isPreconnected_connectedComponentIn.image _ continuous_neg.continuousOn
  have h0' : (0 : ℂ) ∈ (fun w : ℂ => -w) '' A :=
    ⟨0,mem_connectedComponentIn h0,neg_zero⟩
  have hsub : (fun w : ℂ => -w) '' A ⊆ F ⁻¹' V := by
    rintro _ ⟨w,hw,rfl⟩
    change F (-w) ∈ V
    rw [heven]
    exact connectedComponentIn_subset (F ⁻¹' V) 0 hw
  exact hconn.subset_connectedComponentIn h0' hsub ⟨z,hz,rfl⟩

/-- The filled set is defined by all return iterates staying in the
actual restriction domain, including the zeroth iterate. -/
def quadraticReturnFilled (c : ℂ) (p : ℕ) (U : Set ℂ) : Set ℂ :=
  {z | ∀ n : ℕ, ((fun w : ℂ => w^2+c)^[p])^[n] z ∈ U}

/-- Symmetry of the little filled set is derived from actual properness
and connectedness of the return restriction containing zero. -/
theorem quadratic_return_filled_symmetric (c : ℂ) (p : ℕ) (U V : Set ℂ)
    (hp : 0 < p) (hUo : IsOpen U) (hVo : IsOpen V)
    (hUc : IsPreconnected U) (h0 : 0 ∈ U)
    (hm : MapsTo ((fun w : ℂ => w^2+c)^[p]) U V)
    (hproper : IsProperMap (fun z : U =>
      (⟨(fun w : ℂ => w^2+c)^[p] z,hm z.property⟩ : V))) :
    ∀ z ∈ quadraticReturnFilled c p U, -z ∈ quadraticReturnFilled c p U := by
  let F := (fun w : ℂ => w^2+c)^[p]
  have hf : Continuous (fun w : ℂ => w^2+c) := (continuous_id.pow 2).add continuous_const
  have hF : Continuous F := hf.iterate p
  have hU := proper_restriction_is_component F U V 0 hF hUo hVo hUc h0 hm hproper
  have hsym (z : ℂ) (hz : z ∈ U) : -z ∈ U := by
    rw [hU] at hz ⊢
    exact even_preimage_component_symmetric F V (quadratic_positive_iterate_even c p hp) z hz
  intro z hz
  change ∀ n : ℕ, F^[n] z ∈ U at hz
  change ∀ n : ℕ, F^[n] (-z) ∈ U
  intro n
  cases n with
  | zero =>
    exact hsym z (hz 0)
  | succ n =>
    have he : F (-z) = F z := quadratic_positive_iterate_even c p hp z
    rw [Function.iterate_succ_apply, he]
    exact hz (n+1)

/-- All points of a connected successor piece are separated if one is.
This conclusion concerns connected components, not accessibility paths. -/
theorem connected_successor_avoids_component (S B : Set ℂ) (a b : ℂ)
    (hB : IsPreconnected B) (hsub : B ⊆ S) (hb : b ∈ B)
    (hsep : b ∉ connectedComponentIn S a) :
    Disjoint B (connectedComponentIn S a) := by
  rw [Set.disjoint_left]
  intro y hyB hyC
  have hb' := hB.subset_connectedComponentIn hyB hsub hb
  rw [← connectedComponentIn_eq hyC] at hb'
  exact hsep hb'

/-- Combining the actual quadratic exterior-cut theorem with terminal
sheet transport confines the entire ambient successor component to
its sheet. In particular no point outside that sheet can bypass the
separator, even when the retained physical set is not locally connected. -/
theorem terminal_successor_component_confined (O S : Set X) (a y : X)
    (K Q R B : Set ℂ) (c α : ℂ) (g : X → ℂ)
    (hfront : frontier O ⊆ {a}) (ha : a ∈ S) (hy : y ∈ S ∩ O)
    (hg : ContinuousOn g (S ∩ (O ∪ {a})))
    (hmap : MapsTo g (S ∩ (O ∪ {a})) (K \ Q))
    (hga : g a = α) (hgy : g y ∈ B)
    (hB : IsPreconnected B) (hBsub : B ⊆ K \ Q) (hb : -α ∈ B)
    (hne : α ≠ 0)
    (hsym : ∀ z ∈ Q, -z ∈ Q) (h0 : 0 ∈ Q)
    (hQ : IsCompact Q) (hQc : IsConnected Q)
    (hR : IsClosed R) (hRc : IsConnected R)
    (hmeet : (((fun z : ℂ => z^2+c) '' Q) ∩ R).Nonempty)
    (hunb : ∀ M : ℝ, ∃ z ∈ R, M < ‖z‖)
    (hdis : Disjoint R ((fun z : ℂ => z^2+c) '' (K \ Q))) :
    y ∉ connectedComponentIn S a ∧ connectedComponentIn S y ⊆ O := by
  have hα : α ∈ K \ Q := hga ▸ hmap ⟨ha,Or.inr (mem_singleton a)⟩
  have hsep := quadratic_base_separator_of_exterior_ray c K Q R α hα hne
    hsym h0 hQ hQc hR hRc hmeet hunb hdis
  have hBdis := connected_successor_avoids_component (K \ Q) B α (-α)
    hB hBsub hb hsep
  have hgysep : g y ∉ connectedComponentIn (K \ Q) (g a) := by
    rw [hga]
    exact fun h => Set.disjoint_left.mp hBdis hgy h
  have hglobal := separator_transport O S (K \ Q) a y g hfront ha
    (Or.inl hy.2) hg hmap hgysep
  have hylocal : y ∈ S ∩ (O ∪ {a}) := ⟨hy.1,Or.inl hy.2⟩
  have hmiss : a ∉ connectedComponentIn (S ∩ (O ∪ {a})) y := by
    intro h
    have heq := connectedComponentIn_eq h
    have hy' : y ∈ connectedComponentIn (S ∩ (O ∪ {a})) a :=
      heq ▸ mem_connectedComponentIn hylocal
    exact hglobal (connectedComponentIn_mono a inter_subset_left hy')
  refine ⟨hglobal, ?_⟩
  rw [component_eq_local_of_attachment_missing O S a y hfront ha hylocal hmiss]
  intro z hz
  rcases (connectedComponentIn_subset _ _ hz).2 with h | h
  · exact h
  · have he : z = a := h
    exact False.elim (hmiss (he ▸ hz))

end LoopsStationarySeparatorTransport
