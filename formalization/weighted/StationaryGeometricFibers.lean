import StationaryMonotoneGeometry

/-!
# Geometric fiber saturation and relative carrier transport

The carrier need not be the entire inverse image of its model image.
The relative component theorem below uses hereditary unicoherence of the
physical space, rather than local connectivity or paths in the model.
-/

namespace LoopsStationaryGeometricFibers

open Set
open LoopsStationaryMonotoneGeometry

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A preconnected subset of a finite set in a T1 space has at most one point. -/
theorem preconnected_finite_subsingleton [T1Space X] {S : Set X}
    (hc : IsPreconnected S) (hf : S.Finite) : S.Subsingleton := by
  classical
  intro a ha b hb
  by_contra hab
  have hcover : S ⊆ {a} ∪ (S \ {a}) := by
    intro z hz
    by_cases h : z = a
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  have hclosed : IsClosed (S \ {a}) :=
    (hf.subset diff_subset).isClosed
  obtain ⟨z, _, hz₁, hz₂⟩ := (isPreconnected_closed_iff.mp hc)
    {a} (S \ {a}) isClosed_singleton hclosed hcover
    ⟨a, ha, rfl⟩ ⟨b, hb, hb, Ne.symm hab⟩
  exact hz₂.2 hz₁

/-- Connected fibers propagate singleton fibers backwards through any
finite-to-one semiconjugate map, at every finite predecessor depth. -/
theorem singleton_fiber_of_iterate [T1Space X]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hs : Function.Semiconj p F G)
    (hfinite : ∀ x : X, (F ⁻¹' {x}).Finite)
    (a x : X) (ha : p ⁻¹' ({p a} : Set Y) = {a})
    (n : ℕ) (hn : (F^[n]) x = a) :
    p ⁻¹' ({p x} : Set Y) = {x} := by
  induction n generalizing x with
  | zero =>
    have hx : x = a := by simpa using hn
    subst x
    exact ha
  | succ n ih =>
    have hstep : (F^[n]) (F x) = a := by
      simpa only [Function.iterate_succ_apply] using hn
    have hnext := ih (F x) hstep
    have hsub : p ⁻¹' ({p x} : Set Y) ⊆ F ⁻¹' {F x} := by
      intro z hz
      change p z = p x at hz
      have he : F z ∈ p ⁻¹' ({p (F x)} : Set Y) := by
        change p (F z) = p (F x)
        rw [hs z, hs x, hz]
      rw [hnext] at he
      exact he
    have hsingle := preconnected_finite_subsingleton (hf (p x))
      ((hfinite (F x)).subset hsub)
    apply Subset.antisymm
    · intro z hz
      exact hsingle hz (show x ∈ p ⁻¹' ({p x} : Set Y) from rfl)
    · intro z hz
      have he : z = x := hz
      subst z
      rfl

/-- The actual complex quadratic has finite point fibers, including
the critical value and parameters for which a fiber is empty. -/
theorem quadratic_fiber_finite (c w : ℂ) :
    ({z : ℂ | z^2 + c = w}).Finite := by
  classical
  by_cases h : ∃ z : ℂ, z^2 + c = w
  · obtain ⟨a, ha⟩ := h
    apply ((Set.finite_singleton a).insert (-a)).subset
    intro z hz
    change z^2 + c = w at hz
    have hmul : (z-a)*(z+a) = 0 := by
      calc
        (z-a)*(z+a) = (z^2+c)-(a^2+c) := by ring
        _ = 0 := by rw [hz, ha, sub_self]
    rw [mem_insert_iff, mem_singleton_iff]
    rcases mul_eq_zero.mp hmul with h₁ | h₂
    · exact Or.inr (sub_eq_zero.mp h₁)
    · left
      linear_combination h₂
  · have he : ({z : ℂ | z^2 + c = w}) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact h ⟨z, hz⟩
    rw [he]
    exact Set.finite_empty

/-- A genuine restriction of the quadratic, e.g. to a forward
invariant filled set, inherits finiteness of point fibers. -/
theorem quadratic_restricted_fiber_finite (c : ℂ) (K : Set ℂ)
    (F : K → K) (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2 + c)
    (w : K) : (F ⁻¹' ({w} : Set K)).Finite := by
  have h : ((Subtype.val : K → ℂ) ⁻¹'
      {z : ℂ | z^2 + c = (w : ℂ)}).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn
      (quadratic_fiber_finite c (w : ℂ))
  apply h.subset
  intro z hz
  change F z = w at hz
  change (z : ℂ)^2 + c = (w : ℂ)
  rw [← hF z, hz]

/-- Restricting a closed monotone quotient to any closed continuum
in a compact hereditarily unicoherent space preserves connectedness
of inverse images relative to that carrier. The model subset may
be nonclosed and need not be path connected. -/
theorem relative_preimage_preconnected [CompactSpace X] [T2Space Y]
    (p : X → Y) (hp : Continuous p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (C : Set X) (hCc : IsClosed C) (hC : IsConnected C)
    (S : Set Y) (hSC : S ⊆ p '' C) (hS : IsPreconnected S) :
    IsPreconnected (C ∩ p ⁻¹' S) := by
  apply isPreconnected_closed_iff.mpr
  intro U V hU hV hcover hleft hright
  let A : Set Y := p '' (C ∩ U)
  let B : Set Y := p '' (C ∩ V)
  have hAB : S ⊆ A ∪ B := by
    intro y hy
    obtain ⟨x, hxC, hxy⟩ := hSC hy
    have hxS : x ∈ p ⁻¹' S := by
      change p x ∈ S
      rwa [hxy]
    rcases hcover ⟨hxC, hxS⟩ with hxU | hxV
    · exact Or.inl ⟨x, ⟨hxC, hxU⟩, hxy⟩
    · exact Or.inr ⟨x, ⟨hxC, hxV⟩, hxy⟩
  have ha : (S ∩ A).Nonempty := by
    obtain ⟨x, hx, hxU⟩ := hleft
    exact ⟨p x, hx.2, ⟨x, ⟨hx.1, hxU⟩, rfl⟩⟩
  have hb : (S ∩ B).Nonempty := by
    obtain ⟨x, hx, hxV⟩ := hright
    exact ⟨p x, hx.2, ⟨x, ⟨hx.1, hxV⟩, rfl⟩⟩
  obtain ⟨y, hy, hyA, hyB⟩ := (isPreconnected_closed_iff.mp hS)
    A B (hp.isClosedMap _ (hCc.inter hU)) (hp.isClosedMap _ (hCc.inter hV))
    hAB ha hb
  obtain ⟨a, haCU, hay⟩ := hyA
  obtain ⟨b, hbCV, hby⟩ := hyB
  have hfiber : IsConnected (p ⁻¹' ({y} : Set Y)) :=
    ⟨⟨a, hay⟩, hf y⟩
  have hconn := hu C (p ⁻¹' ({y} : Set Y)) hCc
    (isClosed_singleton.preimage hp) hC hfiber
  have hsub : C ∩ p ⁻¹' ({y} : Set Y) ⊆ U ∪ V := by
    intro z hz
    apply hcover
    refine ⟨hz.1, ?_⟩
    change p z ∈ S
    have he : p z = y := hz.2
    rwa [he]
  obtain ⟨z, hz, hzU, hzV⟩ := (isPreconnected_closed_iff.mp hconn)
    U V hU hV hsub ⟨a, ⟨haCU.1, hay⟩, haCU.2⟩
    ⟨b, ⟨hbCV.1, hby⟩, hbCV.2⟩
  refine ⟨z, ⟨hz.1, ?_⟩, hzU, hzV⟩
  change p z ∈ S
  have he : p z = y := hz.2
  rwa [he]

/-- Exact component correspondence inside a physical continuum,
without requiring that continuum to be a saturated set. -/
theorem relative_component_lift [CompactSpace X] [T2Space Y]
    (p : X → Y) (hp : Continuous p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hu : ∀ U V : Set X, IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (C : Set X) (hCc : IsClosed C) (hC : IsConnected C)
    (S : Set Y) (hSC : S ⊆ p '' C) (x : X) (hx : x ∈ C) (hpx : p x ∈ S) :
    connectedComponentIn (C ∩ p ⁻¹' S) x =
      C ∩ p ⁻¹' connectedComponentIn S (p x) := by
  have hx' : x ∈ C ∩ p ⁻¹' S := ⟨hx, hpx⟩
  apply Subset.antisymm
  · have hconn : IsPreconnected (p '' connectedComponentIn (C ∩ p ⁻¹' S) x) :=
      isPreconnected_connectedComponentIn.image p hp.continuousOn
    have hmem : p x ∈ p '' connectedComponentIn (C ∩ p ⁻¹' S) x :=
      ⟨x, mem_connectedComponentIn hx', rfl⟩
    have hsub : p '' connectedComponentIn (C ∩ p ⁻¹' S) x ⊆ S := by
      rintro _ ⟨z, hz, rfl⟩
      exact (connectedComponentIn_subset (C ∩ p ⁻¹' S) x hz).2
    intro z hz
    exact ⟨(connectedComponentIn_subset (C ∩ p ⁻¹' S) x hz).1,
      hconn.subset_connectedComponentIn hmem hsub ⟨z, hz, rfl⟩⟩
  · have hsub : connectedComponentIn S (p x) ⊆ p '' C :=
      (connectedComponentIn_subset S (p x)).trans hSC
    have hconn := relative_preimage_preconnected p hp hf hu C hCc hC
      (connectedComponentIn S (p x)) hsub isPreconnected_connectedComponentIn
    exact hconn.subset_connectedComponentIn ⟨hx, mem_connectedComponentIn hpx⟩
      (fun z hz => ⟨hz.1, connectedComponentIn_subset S (p x) hz.2⟩)

/-- A closed carrier is saturated if all its frontier points have
singleton full fibers. A crossing fiber must meet the frontier,
so this gives a geometric sufficient condition, not an assumption
of saturation itself. -/
theorem closed_carrier_saturated_of_frontier_singletons
    (p : X → Y) (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (C : Set X) (hC : IsClosed C)
    (hfront : ∀ z ∈ frontier C, p ⁻¹' ({p z} : Set Y) = {z}) :
    p ⁻¹' (p '' C) = C := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨a, ha, haz⟩ := hz
    by_contra hn
    have hcover : p ⁻¹' ({p z} : Set Y) ⊆ C ∪ closure Cᶜ := by
      intro w _
      by_cases hw : w ∈ C
      · exact Or.inl hw
      · exact Or.inr (subset_closure (show w ∈ Cᶜ from hw))
    obtain ⟨w, hw, hwC, hwout⟩ := (isPreconnected_closed_iff.mp (hf (p z)))
      C (closure Cᶜ) hC isClosed_closure hcover
      ⟨a, haz, ha⟩ ⟨z, rfl, subset_closure (show z ∈ Cᶜ from hn)⟩
    have hwfront : w ∈ frontier C := by
      change w ∈ closure C ∧ w ∉ interior C
      rw [closure_compl] at hwout
      exact ⟨subset_closure hwC, hwout⟩
    have he : p w = p z := hw
    have hz' : z ∈ p ⁻¹' ({p w} : Set Y) := he.symm
    rw [hfront w hwfront] at hz'
    have hzw : z = w := hz'
    exact hn (hzw.symm ▸ hwC)
  · intro z hz
    exact ⟨z, hz, rfl⟩

/-- Exact continuum correspondence can be certified from matched
dense anchor sets. No equality between a continuum and a finite-tree
vertex is used. -/
theorem marked_continuum_image_of_dense_anchors [T2Space Y]
    (p : X → Y) (hp : Continuous p) (K A : Set X) (L B : Set Y)
    (hK : IsCompact K) (hA : closure A = K) (hB : closure B = L)
    (hmatch : p '' A = B) : p '' K = L := by
  have hAK : A ⊆ K := by rw [← hA]; exact subset_closure
  have hBL : B ⊆ L := by rw [← hB]; exact subset_closure
  have hLc : IsClosed L := by rw [← hB]; exact isClosed_closure
  have hpre : A ⊆ p ⁻¹' L := by
    intro z hz
    apply hBL
    rw [← hmatch]
    exact ⟨z, hz, rfl⟩
  have hKL : K ⊆ p ⁻¹' L := by
    rw [← hA]
    exact closure_minimal hpre (hLc.preimage hp)
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hKL hz
  · rw [← hB, ← hmatch]
    exact closure_minimal (image_mono hAK) (hK.image hp).isClosed

/-- For marked incidence at a selected predecessor, one actual
quotient contact suffices. Neither global carrier saturation nor
inclusion of the entire marked image in a named model continuum
is assumed. The physical mark must avoid the selected root. -/
theorem selected_mark_from_single_overlap [CompactSpace X] [T2Space Y]
    (p : X → Y) (hp : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (F : X → X) (T K : Set X) (hFT : MapsTo F T T)
    (hKT : K ⊆ T) (hK : IsPreconnected K)
    (a x : X) (ha : p ⁻¹' ({p a} : Set Y) = {a}) (hx : x ≠ a)
    (haK : a ∉ K)
    (hhit : (p '' K ∩ connectedComponentIn ({p a} : Set Y)ᶜ (p x)).Nonempty)
    (n : ℕ) :
    K ⊆ (F^[n]) ⁻¹' T ∩ connectedComponentIn ({a} : Set X)ᶜ x := by
  obtain ⟨y, hyK, hyO⟩ := hhit
  obtain ⟨z, hzK, hzy⟩ := hyK
  have hzO : z ∈ connectedComponentIn ({a} : Set X)ᶜ x := by
    rw [punctured_component_full_lift p hp hsurj hf a x ha hx]
    change p z ∈ connectedComponentIn ({p a} : Set Y)ᶜ (p x)
    rwa [hzy]
  have havoid : K ⊆ ({a} : Set X)ᶜ := by
    intro w hw hw'
    have he : w = a := hw'
    exact haK (he ▸ hw)
  have hsub := hK.subset_connectedComponentIn hzK havoid
  rw [← connectedComponentIn_eq hzO] at hsub
  exact fun w hw => ⟨(hFT.iterate n) (hKT hw), hsub hw⟩


/-- A closed two-sheet orbit map pulls back any preconnected set
containing the image of a fixed point to a preconnected set. This
uses the involutive fiber structure, not path lifting, local
connectivity, or connectedness of individual point fibers. -/
theorem critical_preimage_preconnected
    (f : X → Y) (σ : X → X) (hf : IsClosedMap f)
    (hσc : Continuous σ) (hsurj : Function.Surjective f)
    (hσ : ∀ z, f (σ z) = f z)
    (hfib : ∀ x z, f x = f z → z = x ∨ z = σ x)
    (S : Set Y) (hS : IsPreconnected S)
    (a : X) (hfix : σ a = a) (haS : f a ∈ S) :
    IsPreconnected (f ⁻¹' S) := by
  apply isPreconnected_closed_iff.mpr
  intro U V hU hV hcover hleft hright
  have solve (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
      (hAB : f ⁻¹' S ⊆ A ∪ B) (haA : a ∈ A)
      (hBhit : (f ⁻¹' S ∩ B).Nonempty) :
      ∃ z ∈ f ⁻¹' S, z ∈ A ∧ z ∈ B := by
    let A' : Set Y := f '' (A ∩ σ ⁻¹' A)
    let B' : Set Y := f '' B
    have hcov : S ⊆ A' ∪ B' := by
      intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      have hxσ : σ x ∈ f ⁻¹' S := by
        change f (σ x) ∈ S
        rwa [hσ x]
      rcases hAB (show x ∈ f ⁻¹' S from hy) with hxA | hxB
      · rcases hAB hxσ with hsA | hsB
        · exact Or.inl ⟨x, ⟨hxA, hsA⟩, rfl⟩
        · exact Or.inr ⟨σ x, hsB, hσ x⟩
      · exact Or.inr ⟨x, hxB, rfl⟩
    have hAhit : (S ∩ A').Nonempty := by
      refine ⟨f a, haS, a, ⟨haA, ?_⟩, rfl⟩
      change σ a ∈ A
      rwa [hfix]
    have hBhit' : (S ∩ B').Nonempty := by
      obtain ⟨z, hzS, hzB⟩ := hBhit
      exact ⟨f z, hzS, ⟨z, hzB, rfl⟩⟩
    obtain ⟨y, hyS, hyA, hyB⟩ := (isPreconnected_closed_iff.mp hS)
      A' B' (hf _ (hA.inter (hA.preimage hσc))) (hf _ hB) hcov hAhit hBhit'
    obtain ⟨x, hxA, hxy⟩ := hyA
    obtain ⟨z, hzB, hzy⟩ := hyB
    refine ⟨z, ?_, ?_, hzB⟩
    · change f z ∈ S
      rwa [hzy]
    · rcases hfib x z (hxy.trans hzy.symm) with he | he
      · rw [he]
        exact hxA.1
      · rw [he]
        exact hxA.2
  rcases hcover (show a ∈ f ⁻¹' S from haS) with haU | haV
  · exact solve U V hU hV hcover haU hright
  · have hcov : f ⁻¹' S ⊆ V ∪ U := by
      intro z hz
      rcases hcover hz with h | h
      · exact Or.inr h
      · exact Or.inl h
    obtain ⟨z, hz, hzV, hzU⟩ := solve V U hV hU hcov haV hleft
    exact ⟨z, hz, hzU, hzV⟩

private theorem restricted_quadratic_continuous (c : ℂ) (K : Set ℂ)
    (F : K → K) (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2 + c) :
    Continuous F := by
  have hc : Continuous (fun z : K => (z : ℂ)^2+c) :=
    ((continuous_subtype_val : Continuous (Subtype.val : K → ℂ)).pow 2).add continuous_const
  have hm : ∀ z : K, (z : ℂ)^2+c ∈ K := by
    intro z
    rw [← hF z]
    exact (F z).property
  have he : F = (fun z : K => (⟨(z : ℂ)^2+c, hm z⟩ : K)) := by
    funext z
    exact Subtype.ext (hF z)
  rw [he]
  exact hc.subtype_mk hm

private theorem restricted_reflection_continuous (K : Set ℂ)
    (σ : K → K) (hσ : ∀ z : K, (σ z : ℂ) = -(z : ℂ)) :
    Continuous σ := by
  have hc : Continuous (fun z : K => -(z : ℂ)) :=
    (continuous_subtype_val : Continuous (Subtype.val : K → ℂ)).neg
  have hm : ∀ z : K, -(z : ℂ) ∈ K := by
    intro z
    rw [← hσ z]
    exact (σ z).property
  have he : σ = (fun z : K => (⟨-(z : ℂ), hm z⟩ : K)) := by
    funext z
    exact Subtype.ext (hσ z)
  rw [he]
  exact hc.subtype_mk hm

/-- Actual quadratic pullback of a connected critical-value region
inside any compact reflection-invariant completely invariant set.
No Jordan neighborhoods, conformal coordinates or local
connectivity are needed, even for nonclosed regions. -/
theorem quadratic_restricted_critical_preimage (c : ℂ) (K : Set ℂ)
    [CompactSpace K] (F σ : K → K)
    (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2+c)
    (hσ : ∀ z : K, (σ z : ℂ) = -(z : ℂ))
    (hsurj : Function.Surjective F)
    (a : K) (ha : (a : ℂ) = 0)
    (S : Set K) (hS : IsPreconnected S) (haS : F a ∈ S) :
    IsPreconnected (F ⁻¹' S) := by
  refine critical_preimage_preconnected F σ
    (restricted_quadratic_continuous c K F hF).isClosedMap
    (restricted_reflection_continuous K σ hσ) hsurj ?_ ?_ S hS a ?_ haS
  · intro z
    apply Subtype.ext
    rw [hF (σ z), hσ z, hF z]
    ring
  · intro x z hxz
    have he : (F x : ℂ) = (F z : ℂ) :=
      congrArg (fun w : K => (w : ℂ)) hxz
    rw [hF x, hF z] at he
    have hmul : ((z : ℂ)-(x : ℂ))*((z : ℂ)+(x : ℂ)) = 0 := by
      calc
        _ = ((z : ℂ)^2+c)-((x : ℂ)^2+c) := by ring
        _ = 0 := by rw [he, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · left
      exact Subtype.ext (sub_eq_zero.mp h)
    · right
      apply Subtype.ext
      rw [hσ x]
      linear_combination h
  · apply Subtype.ext
    rw [hσ a, ha, neg_zero]

/-- Forward invariance of the actual least marked continuum follows
from the elementary critical-preimage theorem, provided the marks
are forward invariant and contain the critical value. -/
theorem quadratic_least_carrier_forward_invariant (c : ℂ) (K : Set ℂ)
    [CompactSpace K] (F σ : K → K)
    (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2+c)
    (hσ : ∀ z : K, (σ z : ℂ) = -(z : ℂ))
    (hsurj : Function.Surjective F)
    (a : K) (ha : (a : ℂ) = 0)
    (M T : Set K) (hTc : IsCompact T) (hT : IsConnected T)
    (hMT : M ⊆ T) (hFM : MapsTo F M M) (hcrit : F a ∈ M)
    (hleast : ∀ U : Set K, IsCompact U → IsConnected U → M ⊆ U → T ⊆ U) :
    MapsTo F T T := by
  have hpre := quadratic_restricted_critical_preimage c K F σ hF hσ hsurj
    a ha T hT.isPreconnected (hMT hcrit)
  have hconn : IsConnected (F ⁻¹' T) := ⟨⟨a, hMT hcrit⟩, hpre⟩
  have hc : IsCompact (F ⁻¹' T) :=
    (hTc.isClosed.preimage (restricted_quadratic_continuous c K F hF)).isCompact
  exact hleast _ hc hconn (fun z hz => hMT (hFM hz))

/-- For a forward invariant physical carrier, the *contact* of the
carrier with a selected predecessor has exactly the model contact
image, even when the physical carrier itself is not saturated.
Consequently model exclusion at any depth transfers directly to
physical exclusion, with no marked-continuum matching premise. -/
theorem selected_carrier_contact_image [CompactSpace X] [T2Space Y]
    (p : X → Y) (hp : Continuous p) (hsurj : Function.Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (F : X → X) (G : Y → Y) (hs : Function.Semiconj p F G)
    (T : Set X) (B : Set Y) (himg : p '' T = B) (hFT : MapsTo F T T)
    (a x : X) (ha : p ⁻¹' ({p a} : Set Y) = {a}) (hx : x ≠ a)
    (n : ℕ) :
    p '' (T ∩ ((F^[n]) ⁻¹' T ∩ connectedComponentIn ({a} : Set X)ᶜ x)) =
      B ∩ ((G^[n]) ⁻¹' B ∩ connectedComponentIn ({p a} : Set Y)ᶜ (p x)) := by
  rw [punctured_component_full_lift p hp hsurj hf a x ha hx]
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hzB : p z ∈ B := by
      rw [← himg]
      exact ⟨z, hz.1, rfl⟩
    have hFzB : p ((F^[n]) z) ∈ B := by
      rw [← himg]
      exact ⟨(F^[n]) z, hz.2.1, rfl⟩
    have hGzB : (G^[n]) (p z) ∈ B := by
      rw [← hs.iterate_right n z]
      exact hFzB
    exact ⟨hzB, hGzB, hz.2.2⟩
  · intro y hy
    have hyB : y ∈ p '' T := by
      rw [himg]
      exact hy.1
    obtain ⟨z, hz, hzy⟩ := hyB
    refine ⟨z, ⟨hz, ?_, ?_⟩, hzy⟩
    · exact (hFT.iterate n) hz
    · change p z ∈ connectedComponentIn ({p a} : Set Y)ᶜ (p x)
      rw [hzy]
      exact hy.2.2

end LoopsStationaryGeometricFibers
