import StationaryLimbCollar

/-!
# Ambient collars of complete closed stationary limbs

The closed selected limb includes its attachment points.  Native two-limb
geometry forces all its preterminal images away from the critical point,
so compact injectivity extends to a genuinely open complex neighborhood.
No local connectivity or assumed extension of an inverse branch is used.
-/

namespace LoopsStationaryBoundaryExtension

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsSaturatedTelescope
open LoopsStationaryFiberDynamics LoopsStationaryPhysicalItinerary
open LoopsStationaryLimbCollar LoopsQuadraticUnivalentNeighborhood

variable {X : Type*} [TopologicalSpace X]

/-- A punctured-space component can acquire only the removed point in
its ambient closure. No local connectivity is required. -/
theorem punctured_component_closure_subset (a d : X) :
    closure (connectedComponentIn ({a} : Set X)ᶜ d) ⊆
      insert a (connectedComponentIn ({a} : Set X)ᶜ d) := by
  intro x hx
  change x = a ∨ x ∈ connectedComponentIn ({a} : Set X)ᶜ d
  by_cases hxa : x = a
  · exact Or.inl hxa
  right
  by_cases hd : d ∈ ({a} : Set X)ᶜ
  · have hxsub : x ∈ ({a} : Set X)ᶜ := by simpa using hxa
    have hxc : (⟨x, hxsub⟩ : ({a} : Set X)ᶜ) ∈
        closure (connectedComponent (⟨d, hd⟩ : ({a} : Set X)ᶜ)) := by
      apply closure_subtype.mpr
      rwa [← connectedComponentIn_eq_image hd]
    rw [isClosed_connectedComponent.closure_eq] at hxc
    rw [connectedComponentIn_eq_image hd]
    exact ⟨⟨x, hxsub⟩, hxc, rfl⟩
  · rw [connectedComponentIn_eq_empty hd, closure_empty] at hx
    exact hx.elim

private theorem open_inverse_closure_fiber_unique [T2Space X]
    (F : X → X) (D : Set X) (a b x : X)
    (hF : Continuous F) (hopen : IsOpenMap F) (hD : IsOpen D)
    (hinj : InjOn F (D ∩ F ⁻¹' D))
    (hb : b ∈ D) (hba : F b = a)
    (hx : x ∈ closure (D ∩ F ⁻¹' D)) (hxa : F x = a) :
    x = b := by
  by_contra hxb
  obtain ⟨U, V, hU, hV, hxU, hbV, hUV⟩ := t2_separation hxb
  have hFo : IsOpen (F '' (D ∩ V)) := hopen _ (hD.inter hV)
  have hxFo : x ∈ F ⁻¹' (F '' (D ∩ V)) :=
    ⟨b, ⟨hb, hbV⟩, hba.trans hxa.symm⟩
  obtain ⟨z, hzU, hzL⟩ := mem_closure_iff.mp hx
    (U ∩ F ⁻¹' (F '' (D ∩ V)))
    (hU.inter (hFo.preimage hF)) ⟨hxU, hxFo⟩
  obtain ⟨w, hw, hwz⟩ := hzU.2
  have hwL : w ∈ D ∩ F ⁻¹' D := by
    refine ⟨hw.1, ?_⟩
    change F w ∈ D
    rw [hwz]
    exact hzL.2
  have hzw : z = w := hinj hzL hwL hwz.symm
  exact Set.disjoint_left.mp hUV (hzw ▸ hzU.1) hw.2

private theorem limb_inverse_injOn_closure [T2Space X]
    (F : X → X) (D : Set X) (a : X)
    (hF : Continuous F) (hopen : IsOpenMap F) (hD : IsOpen D)
    (hfix : F a = a) (haD : a ∉ D)
    (hboundary : closure D ⊆ insert a D)
    (hinj : InjOn F (D ∩ F ⁻¹' D)) :
    InjOn F (closure (D ∩ F ⁻¹' D)) := by
  intro x hx y hy hxy
  have hxD : x = a ∨ x ∈ D := hboundary (closure_mono inter_subset_left hx)
  have hyD : y = a ∨ y ∈ D := hboundary (closure_mono inter_subset_left hy)
  have him : F '' (D ∩ F ⁻¹' D) ⊆ D := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  have hxF : F x ∈ closure D :=
    closure_mono him (image_closure_subset_closure_image hF ⟨x, hx, rfl⟩)
  rcases hboundary hxF with hfa | hfd
  · rcases hxD with hxa | hxD
    · rcases hyD with hya | hyD
      · exact hxa.trans hya.symm
      · exact open_inverse_closure_fiber_unique F D a y x hF hopen hD hinj
          hyD (hxy.symm.trans hfa) hx hfa
    · exact (open_inverse_closure_fiber_unique F D a x y hF hopen hD hinj
        hxD hfa hy (hxy.symm.trans hfa)).symm
  · have hxmem : x ∈ D := by
      rcases hxD with rfl | h
      · exact (haD (by simpa only [hfix] using hfd)).elim
      · exact h
    have hymem : y ∈ D := by
      rcases hyD with rfl | h
      · have he : F x = a := hxy.trans hfix
        exact (haD (he ▸ hfd)).elim
      · exact h
    exact hinj ⟨hxmem, hfd⟩ ⟨hymem, hxy ▸ hfd⟩ hxy

/-- Selected inverse injectivity persists on the entire closed limb,
including the dividing attachment points, at every finite depth. -/
theorem limbItinerary_injective_closure [T2Space X]
    (F : X → X) (D : Set X) (a d : X)
    (hfix : F a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set X)ᶜ d)
    (hF : Continuous F) (hopen : IsOpenMap F) (hD : IsOpen D)
    (hinj : InjOn F (D ∩ F ⁻¹' D)) (n : ℕ) :
    InjOn (F^[n]) (closure (limbItinerary F D D n)) := by
  have hboundary : closure D ⊆ insert a D := by
    rw [hDcomp]
    exact punctured_component_closure_subset a d
  have haD : a ∉ D := by
    intro ha
    have hs : D ⊆ ({a} : Set X)ᶜ := by
      rw [hDcomp]
      exact connectedComponentIn_subset _ _
    exact hs ha (mem_singleton a)
  have hstep := limb_inverse_injOn_closure F D a hF hopen hD hfix haD hboundary hinj
  induction n with
  | zero =>
    intro x hx y hy hxy
    simpa using hxy
  | succ n ih =>
    intro x hx y hy hxy
    have him : F '' limbItinerary F D D (n+1) ⊆ limbItinerary F D D n := by
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    have hFx : F x ∈ closure (limbItinerary F D D n) :=
      closure_mono him (image_closure_subset_closure_image hF ⟨x, hx, rfl⟩)
    have hFy : F y ∈ closure (limbItinerary F D D n) :=
      closure_mono him (image_closure_subset_closure_image hF ⟨y, hy, rfl⟩)
    have hEq : F x = F y :=
      ih hFx hFy (by simpa only [Function.iterate_succ_apply] using hxy)
    have hsub : limbItinerary F D D (n+1) ⊆ D ∩ F ⁻¹' D := by
      intro z hz
      exact ⟨hz.1, limbItinerary_subset F D D Subset.rfl n hz.2⟩
    exact hstep (closure_mono hsub hx) (closure_mono hsub hy) hEq

/-- Every prefix of a closed selected itinerary remains in the closed
critical limb. This does not assume an endpoint address. -/
theorem limbItinerary_closure_prefix (F : X → X) (D : Set X)
    (hF : Continuous F) (n : ℕ) (x : X)
    (hx : x ∈ closure (limbItinerary F D D n)) (k : ℕ) (hk : k ≤ n) :
    (F^[k]) x ∈ closure D := by
  have him : (F^[k]) '' limbItinerary F D D n ⊆ D := by
    rintro _ ⟨z, hz, rfl⟩
    have hr := (mem_limbItinerary F D D n z).mp hz
    by_cases hkn : k < n
    · exact hr.1 k hkn
    · have he : k = n := by omega
      simpa only [he] using hr.2
  exact closure_mono him
    (image_closure_subset_closure_image (hF.iterate k) ⟨x, hx, rfl⟩)

/-- Closed selected itineraries still map onto the whole closed limb. -/
theorem limbItinerary_image_closure [CompactSpace X] [T2Space X]
    (F : X → X) (D : Set X) (hF : Continuous F)
    (hcover : D ⊆ F '' D) (n : ℕ) :
    (F^[n]) '' closure (limbItinerary F D D n) = closure D := by
  have honto := limbItinerary_image F D D hcover Subset.rfl n
  have heq : (F^[n]) '' closure (limbItinerary F D D n) =
      closure ((F^[n]) '' limbItinerary F D D n) := by
    apply Subset.antisymm (image_closure_subset_closure_image (hF.iterate n))
    exact closure_minimal (image_mono subset_closure)
      (isClosed_closure.isCompact.image (hF.iterate n)).isClosed
  rwa [honto] at heq

/-- In the genuine critical limb, the second inverse limb excludes
the critical value even from the closure. The dividing fixed point
cannot be that critical value unless it is itself zero. -/
theorem quadratic_closed_limb_critical_value_exclusion (c : ℂ)
    (D E : Set (quadraticFilled c)) (a d : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a) (ha0 : (a : ℂ) ≠ 0)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hDE : Disjoint D E) (hother : D ⊆ quadraticFilledMap c '' E)
    (hzero : (0 : ℂ) ∈ (Subtype.val : quadraticFilled c → ℂ) '' D) :
    c ∉ (Subtype.val : quadraticFilled c → ℂ) '' closure D := by
  let F := quadraticFilledMap c
  obtain ⟨o, hoD, ho0⟩ := hzero
  have hunique (w : quadraticFilled c) (hw : F w = F o) : w = o := by
    apply Subtype.ext
    have hv := congrArg (fun z : quadraticFilled c => (z : ℂ)) hw
    change (w : ℂ)^2+c = (o : ℂ)^2+c at hv
    rw [ho0] at hv
    have hw0 : (w : ℂ) = 0 := by
      simpa using (quadratic_eq_iff c (w : ℂ) 0).mp hv
    exact hw0.trans ho0.symm
  have hFoc : (F o : ℂ) = c := by
    change (o : ℂ)^2+c = c
    simp only [ho0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
  have hboundary : closure D ⊆ insert a D := by
    rw [hDcomp]
    exact punctured_component_closure_subset a d
  rintro ⟨z, hz, hzc⟩
  have hzo : z = F o := Subtype.ext (hzc.trans hFoc.symm)
  have hFo : F o ∈ closure D := hzo ▸ hz
  rcases hboundary hFo with hfa | hfd
  · have hao : a = o := hunique a (hfix.trans hfa.symm)
    exact ha0 ((congrArg (fun z : quadraticFilled c => (z : ℂ)) hao).trans ho0)
  · obtain ⟨w, hwE, hw⟩ := hother hfd
    have hwo := hunique w hw
    exact Set.disjoint_left.mp hDE hoD (hwo ▸ hwE)

/-- Critical-value avoidance on the closed target excludes every
preterminal critical encounter on the whole closed selected source. -/
theorem quadratic_closed_itinerary_critical_free (c : ℂ)
    (D : Set (quadraticFilled c))
    (hcritical : c ∉ (Subtype.val : quadraticFilled c → ℂ) '' closure D)
    (n : ℕ) (x : quadraticFilled c)
    (hx : x ∈ closure (limbItinerary (quadraticFilledMap c) D D n)) :
    ∀ j < n, orbit c j x ≠ 0 := by
  let F := quadraticFilledMap c
  intro j hj hz
  have hp := limbItinerary_closure_prefix F D
    (quadratic_filled_continuous_open c).1 n x hx (j+1) (by omega)
  have hjzero : ((F^[j]) x : ℂ) = 0 := (filled_iterate_val c j x).trans hz
  have hnext : ((F^[j+1]) x : ℂ) = c := by
    rw [Function.iterate_succ_apply']
    change ((F^[j]) x : ℂ)^2+c = c
    simp only [hjzero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
  exact hcritical ⟨(F^[j+1]) x, hp, hnext⟩

/-- All compact-core hypotheses hold for the entire closed canonical
limb, rather than only for compact targets strictly inside the limb. -/
theorem quadratic_closed_itinerary_planar_geometry (c : ℂ)
    (D E : Set (quadraticFilled c)) (a d : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a) (ha0 : (a : ℂ) ≠ 0)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hzero : (0 : ℂ) ∈ (Subtype.val : quadraticFilled c → ℂ) '' D)
    (n : ℕ) :
    let C := (Subtype.val : quadraticFilled c → ℂ) ''
      closure (limbItinerary (quadraticFilledMap c) D D n)
    IsCompact C ∧ IsPreconnected C ∧ InjOn (orbit c n) C ∧
      (∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0) ∧
      orbit c n '' C = (Subtype.val : quadraticFilled c → ℂ) '' closure D := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  let F := quadraticFilledMap c
  let C := (Subtype.val : quadraticFilled c → ℂ) ''
    closure (limbItinerary F D D n)
  change IsCompact C ∧ IsPreconnected C ∧ InjOn (orbit c n) C ∧ _ ∧ _
  have hF := (quadratic_filled_continuous_open c).1
  have hopen := (quadratic_filled_continuous_open c).2
  have hinj := quadratic_critical_limb_injective c D E hDE hother
  have hDconn : IsPreconnected D := by
    rw [hDcomp]
    exact isPreconnected_connectedComponentIn
  have hclosedinj := limbItinerary_injective_closure F D a d
    hfix hDcomp hF hopen hD hinj n
  have hcritical := quadratic_closed_limb_critical_value_exclusion c D E a d
    hfix ha0 hDcomp hDE hother hzero
  have hcompact : IsCompact C :=
    isClosed_closure.isCompact.image continuous_subtype_val
  have hconn : IsPreconnected C :=
    ((limbItinerary_component F D D a d hfix hDcomp hF hopen hD
      hcover hinj Subset.rfl hDconn n).1.closure).image _
        continuous_subtype_val.continuousOn
  have hI : InjOn (orbit c n) C := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have heq : (F^[n]) x = (F^[n]) y := by
      apply Subtype.ext
      rw [filled_iterate_val, filled_iterate_val]
      exact hxy
    exact congrArg (fun z : quadraticFilled c => (z : ℂ)) (hclosedinj hx hy heq)
  refine ⟨hcompact, hconn, hI, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ j hj
    exact quadratic_closed_itinerary_critical_free c D hcritical n x hx j hj
  · have him : orbit c n '' C =
        (Subtype.val : quadraticFilled c → ℂ) ''
          ((F^[n]) '' closure (limbItinerary F D D n)) := by
      simp only [C, Set.image_image, filled_iterate_val]
    rw [him, limbItinerary_image_closure F D hF hcover n]

private theorem compact_core_component (f : ℂ → ℂ)
    (C B A : Set ℂ) (x : ℂ)
    (hC : IsCompact C) (hconn : IsPreconnected C) (honto : f '' C = B)
    (hA : IsOpen A) (hCA : C ⊆ A) (hI : InjOn f A) (hx : x ∈ C) :
    C = connectedComponentIn (f ⁻¹' B) x := by
  have hpre : C ⊆ f ⁻¹' B := by
    intro z hz
    change f z ∈ B
    rw [← honto]
    exact ⟨z, hz, rfl⟩
  have hlocal : A ∩ f ⁻¹' B ⊆ C := by
    intro z hz
    have hzB : f z ∈ f '' C := by
      rw [honto]
      exact hz.2
    obtain ⟨w, hw, hwz⟩ := hzB
    exact (hI (hCA hw) hz.1 hwz) ▸ hw
  apply Subset.antisymm (hconn.subset_connectedComponentIn hx hpre)
  intro z hz
  by_contra hnot
  have hzAc : z ∈ Aᶜ := by
    intro hzA
    exact hnot (hlocal ⟨hzA, connectedComponentIn_subset _ _ hz⟩)
  have hcov : connectedComponentIn (f ⁻¹' B) x ⊆ C ∪ Aᶜ := by
    intro w hw
    by_cases hwA : w ∈ A
    · exact Or.inl (hlocal ⟨hwA, connectedComponentIn_subset _ _ hw⟩)
    · exact Or.inr hwA
  obtain ⟨w, _, hwC, hwAc⟩ :=
    (isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn) C Aᶜ
      hC.isClosed hA.isClosed_compl hcov
      ⟨x, mem_connectedComponentIn (hpre hx), hx⟩ ⟨z, hz, hzAc⟩
  exact hwAc (hCA hwC)

/-- Every complete closed stationary predecessor, including all its
attachment points, has a conformal ambient collar inside any prescribed
open neighborhood. The collar is a whole pullback component, and its
analytic inverse maps the entire closed physical limb exactly onto that
closed predecessor. -/
theorem quadratic_closed_limb_analytic_collar (c : ℂ)
    (D E : Set (quadraticFilled c)) (a d : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a) (ha0 : (a : ℂ) ≠ 0)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hzero : (0 : ℂ) ∈ (Subtype.val : quadraticFilled c → ℂ) '' D)
    (n : ℕ) (W : Set ℂ) (hW : IsOpen W)
    (hCW : (Subtype.val : quadraticFilled c → ℂ) ''
      closure (limbItinerary (quadraticFilledMap c) D D n) ⊆ W) :
    ∃ (x : ℂ) (V : Set ℂ) (g : ℂ → ℂ),
      x ∈ (Subtype.val : quadraticFilled c → ℂ) ''
        closure (limbItinerary (quadraticFilledMap c) D D n) ∧
      IsOpen V ∧ IsPreconnected V ∧
      (Subtype.val : quadraticFilled c → ℂ) '' closure D ⊆ V ∧
      let U := connectedComponentIn (orbit c n ⁻¹' V) x
      IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ W ∧
        InjOn (orbit c n) (closure U) ∧ orbit c n '' U = V ∧
        MapsTo g V U ∧ LeftInvOn g (orbit c n) U ∧
        RightInvOn g (orbit c n) V ∧ AnalyticOnNhd ℂ g V ∧
        g '' ((Subtype.val : quadraticFilled c → ℂ) '' closure D) =
          (Subtype.val : quadraticFilled c → ℂ) ''
            closure (limbItinerary (quadraticFilledMap c) D D n) ∧
        ∀ y ∈ V, HasDerivAt g (deriv (orbit c n) (g y))⁻¹ y ∧ ConformalAt g y := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  let F := quadraticFilledMap c
  let C := (Subtype.val : quadraticFilled c → ℂ) ''
    closure (limbItinerary F D D n)
  let B := (Subtype.val : quadraticFilled c → ℂ) '' closure D
  obtain ⟨hC, hconn, hI, hcrit, honto⟩ :=
    quadratic_closed_itinerary_planar_geometry c D E a d hfix ha0 hDcomp hD hDE
      hcover hother hzero n
  change IsCompact C at hC
  change IsPreconnected C at hconn
  change InjOn (orbit c n) C at hI
  change (∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0) at hcrit
  change orbit c n '' C = B at honto
  obtain ⟨o, hoD, _⟩ := hzero
  have hoB : (o : ℂ) ∈ B := ⟨o, subset_closure hoD, rfl⟩
  rw [← honto] at hoB
  obtain ⟨x, hx, _⟩ := hoB
  obtain ⟨A, hA, hCA, hIA⟩ :=
    quadratic_compact_univalent_neighborhood c n C hC hI hcrit
  have hcomponent := compact_core_component (orbit c n) C B A x
    hC hconn honto hA hCA hIA hx
  have hxB : orbit c n x ∈ B := by
    rw [← honto]
    exact ⟨x, hx, rfl⟩
  have hB : IsCompact B := isClosed_closure.isCompact.image continuous_subtype_val
  have hBconn : IsPreconnected B := by
    have hDc : IsPreconnected D := by
      rw [hDcomp]
      exact isPreconnected_connectedComponentIn
    exact hDc.closure.image _ continuous_subtype_val.continuousOn
  change C ⊆ W at hCW
  rw [hcomponent] at hCW hI hcrit
  obtain ⟨V, g, hVo, hVc, hBV, hUo, hUc, hUW, hUI, hontoU,
      hmap, hleft, hright, hana, hcore, hder⟩ :=
    LoopsTelescopeUnivalentCollars.selected_univalent_analytic_collar
      c n B W x hB hBconn hxB hW hCW hI hcrit
  refine ⟨x, V, g, hx, hVo, hVc, hBV, hUo, hUc, hUW, hUI, hontoU,
    hmap, hleft, hright, hana, ?_, hder⟩
  exact hcore.trans hcomponent.symm

/-- Every closed parent is the exact image of the full closed selected
predecessor, with the original physical time retained. -/
theorem limbItinerary_closed_prefix_image [CompactSpace X] [T2Space X]
    (F : X → X) (D : Set X) (hF : Continuous F)
    (hcover : D ⊆ F '' D) (m k : ℕ) :
    (F^[k]) '' closure (limbItinerary F D D (m+k)) =
      closure (limbItinerary F D D m) := by
  have honto := limbItinerary_prefix_image F D D hcover Subset.rfl m k
  have heq : (F^[k]) '' closure (limbItinerary F D D (m+k)) =
      closure ((F^[k]) '' limbItinerary F D D (m+k)) := by
    apply Subset.antisymm (image_closure_subset_closure_image (hF.iterate k))
    exact closure_minimal (image_mono subset_closure)
      (isClosed_closure.isCompact.image (hF.iterate k)).isClosed
  rwa [honto] at heq


/-- A closed selected itinerary over an interior target is already
the original open itinerary: an intermediate dividing point would
remain fixed through the terminal time. -/
theorem limbItinerary_of_closure_terminal (F : X → X) (D : Set X) (a d : X)
    (hfix : F a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set X)ᶜ d)
    (hF : Continuous F) (n : ℕ) (x : X)
    (hx : x ∈ closure (limbItinerary F D D n))
    (hterminal : (F^[n]) x ∈ D) :
    x ∈ limbItinerary F D D n := by
  have hboundary : closure D ⊆ insert a D := by
    rw [hDcomp]
    exact punctured_component_closure_subset a d
  have haD : a ∉ D := by
    intro ha
    rw [hDcomp] at ha
    exact connectedComponentIn_subset ({a} : Set X)ᶜ d ha (mem_singleton a)
  have hiter (r : ℕ) : (F^[r]) a = a := by
    induction r with
    | zero => rfl
    | succ r ih => rw [Function.iterate_succ_apply, hfix, ih]
  apply (mem_limbItinerary F D D n x).mpr
  refine ⟨?_, hterminal⟩
  intro k hk
  have hp := limbItinerary_closure_prefix F D hF n x hx k (Nat.le_of_lt hk)
  rcases hboundary hp with hka | hDk
  · have heq : (F^[n]) x = a := by
      calc
        (F^[n]) x = (F^[(n-k)+k]) x := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hk)]
        _ = (F^[n-k]) ((F^[k]) x) := by rw [Function.iterate_add_apply]
        _ = a := by rw [hka, hiter]
    exact (haD (heq ▸ hterminal)).elim
  · exact hDk

/-- Native limb data construct one collar of the full closed limb on
which every connected anchored ambient restriction is the canonical
inverse. Target landing at any closed-limb point, including a dividing
attachment point, forces source landing and every exact closed-parent
itinerary. No source endpoint or source Julia-set containment is assumed. -/
theorem quadratic_closed_limb_ambient_landing {T : Type*} [TopologicalSpace T]
    (c : ℂ) (D E : Set (quadraticFilled c)) (a d : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hzero : (0 : ℂ) ∈ (Subtype.val : quadraticFilled c → ℂ) '' D)
    (n : ℕ) (W : Set ℂ) (hW : IsOpen W)
    (hCW : (Subtype.val : quadraticFilled c → ℂ) ''
      closure (limbItinerary (quadraticFilledMap c) D D n) ⊆ W) :
    ∃ (x : ℂ) (V : Set ℂ) (g : ℂ → ℂ),
      x ∈ (Subtype.val : quadraticFilled c → ℂ) ''
        closure (limbItinerary (quadraticFilledMap c) D D n) ∧
      IsOpen V ∧ IsPreconnected V ∧
      (Subtype.val : quadraticFilled c → ℂ) '' closure D ⊆ V ∧
      let U := connectedComponentIn (orbit c n ⁻¹' V) x
      IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ W ∧
        InjOn (orbit c n) (closure U) ∧ AnalyticOnNhd ℂ g V ∧
        g '' ((Subtype.val : quadraticFilled c → ℂ) '' closure D) =
          (Subtype.val : quadraticFilled c → ℂ) ''
            closure (limbItinerary (quadraticFilledMap c) D D n) ∧
        ∀ (S : Set T) (t₀ : T) (γ : T → ℂ),
          IsPreconnected S → t₀ ∈ S → ContinuousOn γ S →
          MapsTo (fun t => orbit c n (γ t)) S V → γ t₀ ∈ U →
          (∀ t ∈ S, γ t = g (orbit c n (γ t))) ∧
          γ '' S = g '' (orbit c n '' (γ '' S)) ∧
          ∀ (l : Filter T) (y : quadraticFilled c),
            (∀ᶠ t in l, t ∈ S) → y ∈ closure D →
            Tendsto (fun t => orbit c n (γ t)) l (𝓝 (y : ℂ)) →
            Tendsto γ l (𝓝 (g y)) ∧ orbit c n (g y) = y ∧
              g y ∈ (Subtype.val : quadraticFilled c → ℂ) ''
                closure (limbItinerary (quadraticFilledMap c) D D n) ∧
              (y ∈ D →
                g y ∈ (Subtype.val : quadraticFilled c → ℂ) ''
                  limbItinerary (quadraticFilledMap c) D D n ∧
                ∀ m k : ℕ, m+k=n →
                  orbit c k (g y) ∈ (Subtype.val : quadraticFilled c → ℂ) ''
                    limbItinerary (quadraticFilledMap c) D D m) ∧
              ∀ m k : ℕ, m+k=n →
                orbit c k (g y) ∈ (Subtype.val : quadraticFilled c → ℂ) ''
                  closure (limbItinerary (quadraticFilledMap c) D D m) ∧
                Tendsto (fun t => orbit c k (γ t)) l (𝓝 (orbit c k (g y))) := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  have ha0 : (a : ℂ) ≠ 0 := by
    intro ha
    obtain ⟨o, hoD, ho0⟩ := hzero
    have hoa : o = a := Subtype.ext (ho0.trans ha.symm)
    have haD : a ∈ D := hoa ▸ hoD
    rw [hDcomp] at haD
    exact connectedComponentIn_subset ({a} : Set (quadraticFilled c))ᶜ d haD
      (mem_singleton a)
  obtain ⟨x, V, g, hx, hVo, hVc, hBV, hUo, hUc, hUW, hUI,
      _, _, hleft, hright, hana, hcore, _⟩ :=
    quadratic_closed_limb_analytic_collar c D E a d hfix ha0 hDcomp hD hDE
      hcover hother hzero n W hW hCW
  refine ⟨x, V, g, hx, hVo, hVc, hBV, hUo, hUc, hUW, hUI, hana, hcore, ?_⟩
  intro S t₀ γ hS ht₀ hγ hproject hanchor
  refine ⟨LoopsStationaryAmbientLanding.anchored_lift_agrees
      (orbit c n) V x g hleft S t₀ γ hS ht₀ hγ hproject hanchor,
    LoopsStationaryAmbientLanding.anchored_lift_image
      (orbit c n) V x g hleft S t₀ γ hS ht₀ hγ hproject hanchor, ?_⟩
  intro l y hmem hy hlimit
  have hyV : (y : ℂ) ∈ V := hBV ⟨y, hy, rfl⟩
  have hland := LoopsStationaryAmbientLanding.anchored_lift_tendsto
    (orbit c n) V x g hleft S t₀ γ hS ht₀ hγ hproject hanchor
    l hmem (y : ℂ) (hana y hyV).continuousAt hlimit
  have hgy : g y ∈ (Subtype.val : quadraticFilled c → ℂ) ''
      closure (limbItinerary (quadraticFilledMap c) D D n) := by
    rw [← hcore]
    exact ⟨y, ⟨y, hy, rfl⟩, rfl⟩
  have hopenRecovery : y ∈ D →
      g y ∈ (Subtype.val : quadraticFilled c → ℂ) ''
        limbItinerary (quadraticFilledMap c) D D n ∧
      ∀ m k : ℕ, m+k=n →
        orbit c k (g y) ∈ (Subtype.val : quadraticFilled c → ℂ) ''
          limbItinerary (quadraticFilledMap c) D D m := by
    intro hyD
    obtain ⟨z, hz, hzg⟩ := hgy
    have hzterm : ((quadraticFilledMap c)^[n]) z = y := by
      apply Subtype.ext
      rw [filled_iterate_val c n z, hzg]
      exact hright hyV
    have hzopen := limbItinerary_of_closure_terminal (quadraticFilledMap c) D a d
      hfix hDcomp (quadratic_filled_continuous_open c).1 n z hz
      (show ((quadraticFilledMap c)^[n]) z ∈ D from hzterm.symm ▸ hyD)
    refine ⟨⟨z, hzopen, hzg⟩, ?_⟩
    intro m k hmk
    have hp : ((quadraticFilledMap c)^[k]) z ∈
        limbItinerary (quadraticFilledMap c) D D m := by
      rw [← limbItinerary_prefix_image (quadraticFilledMap c) D D
        hcover Subset.rfl m k]
      exact ⟨z, by simpa only [hmk] using hzopen, rfl⟩
    refine ⟨((quadraticFilledMap c)^[k]) z, hp, ?_⟩
    rw [filled_iterate_val c k z, hzg]
  refine ⟨hland, hright hyV, hgy, hopenRecovery, ?_⟩
  intro m k hmk
  obtain ⟨z, hz, hzg⟩ := hgy
  have hp : ((quadraticFilledMap c)^[k]) z ∈
      closure (limbItinerary (quadraticFilledMap c) D D m) := by
    rw [← limbItinerary_closed_prefix_image (quadraticFilledMap c) D
      (quadratic_filled_continuous_open c).1 hcover m k]
    exact ⟨z, by simpa only [hmk] using hz, rfl⟩
  refine ⟨⟨((quadraticFilledMap c)^[k]) z, hp, ?_⟩,
    (quadratic_orbit_continuous c k).continuousAt.tendsto.comp hland⟩
  rw [filled_iterate_val c k z, hzg]

end LoopsStationaryBoundaryExtension
