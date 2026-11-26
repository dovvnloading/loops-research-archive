import StationaryGeometricFibers
import QuadraticCylinderCensus
import QuadraticEscape

/-!
# Exact dynamics of geometric quotient fibers

A finite model point fiber and openness of the physical dynamics
give surjectivity on each individual geometric quotient fiber.
The quadratic application uses the genuine restricted polynomial,
not a combinatorial vertex map.
-/

namespace LoopsStationaryFiberDynamics

open Set Function
open LoopsStationaryMonotoneGeometry LoopsStationaryGeometricFibers
open LoopsQuadraticCylinderCensus

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Whole-fiber transport, not just the inclusion from semiconjugacy.
Finiteness of a model point fiber makes every chosen predecessor
relatively open in the pullback of its successor fiber. -/
theorem fiber_image_eq_of_finite_model_fibers [T1Space Y]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p F G) (ho : IsOpenMap F) (hc : IsClosedMap F)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hfinite : ∀ y : Y, (G ⁻¹' {y}).Finite) (y : Y) :
    F '' (p ⁻¹' {y}) = p ⁻¹' {G y} := by
  let A : Set X := p ⁻¹' {y}
  let B : Set X := p ⁻¹' {G y}
  let D : Set Y := G ⁻¹' {G y} \ {y}
  let O : Set X := p ⁻¹' Dᶜ
  have hD : IsClosed D := ((hfinite (G y)).subset sdiff_subset).isClosed
  have hO : IsOpen O := hD.isOpen_compl.preimage hp
  have heq : F '' A = B ∩ F '' O := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      change p z = y at hz
      refine ⟨?_, z, ?_, rfl⟩
      · change p (F z) = G y
        rw [hs z, hz]
      · change p z ∉ D
        intro hzD
        exact hzD.2 (show p z ∈ ({y} : Set Y) from hz)
    · rintro ⟨hw, z, hz, rfl⟩
      change p (F z) = G y at hw
      change p z ∉ D at hz
      refine ⟨z, ?_, rfl⟩
      change p z = y
      by_contra hne
      exact hz (show p z ∈ D from ⟨(hs z).symm.trans hw, hne⟩)
  have hAc : IsClosed (F '' A) := hc _ (isClosed_singleton.preimage hp)
  have hOo : IsOpen (F '' O) := ho _ hO
  change F '' A = B
  apply Subset.antisymm
  · rw [heq]
    exact inter_subset_left
  · intro z hz
    by_contra hnot
    have hzout : z ∈ (F '' O)ᶜ := by
      intro h
      apply hnot
      rw [heq]
      exact ⟨hz, h⟩
    obtain ⟨a, ha⟩ := hsurj y
    have haA : F a ∈ F '' A := ⟨a, ha, rfl⟩
    have haB : F a ∈ B := by
      change p (F a) = G y
      rw [hs a, ha]
    have hcover : B ⊆ F '' A ∪ (F '' O)ᶜ := by
      intro w hw
      by_cases h : w ∈ F '' O
      · left
        rw [heq]
        exact ⟨hw, h⟩
      · exact Or.inr h
    obtain ⟨w, _, hwA, hwout⟩ :=
      (isPreconnected_closed_iff.mp (hf (G y))) (F '' A) (F '' O)ᶜ
        hAc hOo.isClosed_compl hcover ⟨F a, haB, haA⟩ ⟨z, hz, hzout⟩
    rw [heq] at hwA
    exact hwout hwA.2

/-- Whole-fiber transport composes at every finite depth. -/
theorem iterate_fiber_image_eq (p : X → Y) (F : X → X) (G : Y → Y)
    (h : ∀ y : Y, F '' (p ⁻¹' {y}) = p ⁻¹' {G y})
    (n : ℕ) (y : Y) :
    (F^[n]) '' (p ⁻¹' {y}) = p ⁻¹' {(G^[n]) y} := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    calc
      (F^[n+1]) '' (p ⁻¹' {y}) = (F^[n]) '' (F '' (p ⁻¹' {y})) := by
        rw [Function.iterate_succ, Set.image_comp]
      _ = (F^[n]) '' (p ⁻¹' {G y}) := by rw [h y]
      _ = p ⁻¹' {(G^[n]) (G y)} := ih (G y)
      _ = p ⁻¹' {(G^[n+1]) y} := by rw [Function.iterate_succ_apply]

/-- A singleton fiber remains a singleton in the forward direction
whenever whole-fiber transport holds. -/
theorem singleton_fiber_forward (p : X → Y) (F : X → X) (G : Y → Y)
    (hs : Semiconj p F G)
    (h : ∀ y : Y, F '' (p ⁻¹' {y}) = p ⁻¹' {G y})
    (a : X) (ha : p ⁻¹' ({p a} : Set Y) = {a}) :
    p ⁻¹' ({p (F a)} : Set Y) = {F a} := by
  rw [hs a, ← h (p a), ha, image_singleton]

/-- The restriction of the actual quadratic to a completely invariant
set is open in its subspace topology. The set need not be open
in the ambient plane. -/
theorem quadratic_restriction_open (c : ℂ) (K : Set ℂ)
    (F : K → K) (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2+c)
    (hback : ∀ z : ℂ, z^2+c ∈ K → z ∈ K) :
    IsOpenMap F := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ :=
    (isOpen_induced_iff (f := (Subtype.val : K → ℂ))).mp hU
  have heq : F '' U = (Subtype.val : K → ℂ) ⁻¹'
      ((fun z : ℂ => z^2+c) '' V) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (F z : ℂ) ∈ (fun z : ℂ => z^2+c) '' V
      refine ⟨(z : ℂ), ?_, (hF z).symm⟩
      rw [← hVU] at hz
      exact hz
    · intro hw
      change (w : ℂ) ∈ (fun z : ℂ => z^2+c) '' V at hw
      obtain ⟨z, hz, hzw⟩ := hw
      change z^2+c = (w : ℂ) at hzw
      have hzK : z^2+c ∈ K := by
        rw [hzw]
        exact w.property
      let x : K := ⟨z, hback z hzK⟩
      refine ⟨x, ?_, Subtype.ext ((hF x).trans hzw)⟩
      rw [← hVU]
      exact hz
  rw [heq]
  exact ((quadratic_open c) V hV).preimage continuous_subtype_val

/-- Actual quadratic fiber transport on a compact completely invariant
physical set, conditional only on the stated geometric model data. -/
theorem quadratic_restriction_fiber_image [T1Space Y]
    (c : ℂ) (K : Set ℂ) [CompactSpace K]
    (F : K → K) (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2+c)
    (hback : ∀ z : ℂ, z^2+c ∈ K → z ∈ K)
    (p : K → Y) (G : Y → Y) (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p F G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hfinite : ∀ y : Y, (G ⁻¹' {y}).Finite) (y : Y) :
    F '' (p ⁻¹' {y}) = p ⁻¹' {G y} := by
  have hcont : Continuous F := by
    have hc : Continuous (fun z : K => (z : ℂ)^2+c) :=
      ((continuous_subtype_val : Continuous (Subtype.val : K → ℂ)).pow 2).add
        continuous_const
    have hm : ∀ z : K, (z : ℂ)^2+c ∈ K := by
      intro z
      rw [← hF z]
      exact (F z).property
    have he : F = (fun z : K => (⟨(z : ℂ)^2+c, hm z⟩ : K)) := by
      funext z
      exact Subtype.ext (hF z)
    rw [he]
    exact hc.subtype_mk hm
  exact fiber_image_eq_of_finite_model_fibers p F G hp hsurj hs
    (quadratic_restriction_open c K F hF hback) hcont.isClosedMap hf hfinite y

private theorem quadratic_restricted_two_roots (c : ℂ) (K : Set ℂ)
    (F : K → K) (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2+c)
    (u v : K) (h : F u = F v) :
    v = u ∨ (v : ℂ) = -(u : ℂ) := by
  have he : (u : ℂ)^2+c = (v : ℂ)^2+c := by
    rw [← hF u, ← hF v, h]
  have hz : ((v : ℂ)-(u : ℂ))*((v : ℂ)+(u : ℂ)) = 0 := by
    calc
      _ = ((v : ℂ)^2+c)-((u : ℂ)^2+c) := by ring
      _ = 0 := by rw [he, sub_self]
  rcases mul_eq_zero.mp hz with h₁ | h₂
  · exact Or.inl (Subtype.ext (sub_eq_zero.mp h₁))
  · right
    linear_combination h₂

/-- A full-fiber semiconjugacy cannot invent a second model predecessor
of the actual critical value. This conclusion is about the model
point fiber, not just its distinguished critical label. -/
theorem quadratic_model_critical_preimage
    (c : ℂ) (K : Set ℂ) (F : K → K)
    (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2+c)
    (p : K → Y) (G : Y → Y) (hs : Semiconj p F G)
    (himage : ∀ y : Y, F '' (p ⁻¹' {y}) = p ⁻¹' {G y})
    (a : K) (ha : (a : ℂ) = 0) :
    G ⁻¹' ({p (F a)} : Set Y) = {p a} := by
  apply Subset.antisymm
  · intro y hy
    change G y = p (F a) at hy
    have hw : F a ∈ p ⁻¹' ({G y} : Set Y) := hy.symm
    rw [← himage y] at hw
    obtain ⟨z, hz, hza⟩ := hw
    have he : z = a := by
      rcases quadratic_restricted_two_roots c K F hF a z hza.symm with h | h
      · exact h
      · apply Subtype.ext
        rw [h, ha, neg_zero]
    change p z = y at hz
    rw [he] at hz
    exact hz.symm
  · intro y hy
    change y = p a at hy
    subst y
    exact (hs a).symm

/-- Over a model point with two distinct model predecessors, the
actual quadratic is one-to-one on each full geometric predecessor
fiber. The other model fiber consumes the other physical sheet. -/
theorem quadratic_two_model_predecessors_injective
    (c : ℂ) (K : Set ℂ) (F : K → K)
    (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2+c)
    (p : K → Y) (G : Y → Y) (hs : Semiconj p F G)
    (himage : ∀ y : Y, F '' (p ⁻¹' {y}) = p ⁻¹' {G y})
    (y y' : Y) (hne : y ≠ y') (hG : G y = G y') :
    InjOn F (p ⁻¹' {y}) := by
  intro u hu v hv huv
  change p u = y at hu
  change p v = y at hv
  by_contra huv'
  have hvneg := (quadratic_restricted_two_roots c K F hF u v huv).resolve_left
    (Ne.symm huv')
  have hw : F u ∈ p ⁻¹' ({G y'} : Set Y) := by
    change p (F u) = G y'
    rw [hs u, hu, hG]
  rw [← himage y'] at hw
  obtain ⟨w, hw, hwu⟩ := hw
  change p w = y' at hw
  have hwu' : w ≠ u := by
    intro h
    rw [h, hu] at hw
    exact hne hw
  have hwneg := (quadratic_restricted_two_roots c K F hF u w hwu.symm).resolve_left hwu'
  have hwv : w = v := Subtype.ext (hwneg.trans hvneg.symm)
  rw [hwv, hv] at hw
  exact hne hw

/-- Exact transport of a recursively selected chain of full inverse
components. Only base saturation and actual component anchor
correspondence are required, not a new saturation hypothesis at
every depth. -/
theorem selected_pullback_chain_full_lift [CompactSpace X] [T2Space Y]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hs : Semiconj p F G)
    (L : ℕ → Set X) (M : ℕ → Set Y) (a : ℕ → X)
    (hbase : L 0 = p ⁻¹' M 0)
    (hL : ∀ n, L (n+1) = connectedComponentIn (F ⁻¹' L n) (a n))
    (hM : ∀ n, M (n+1) = connectedComponentIn (G ⁻¹' M n) (p (a n)))
    (hanchor : ∀ n, F (a n) ∈ L n) :
    ∀ n, L n = p ⁻¹' M n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    have hpre : F ⁻¹' (p ⁻¹' M n) = p ⁻¹' (G ⁻¹' M n) := by
      ext z
      change p (F z) ∈ M n ↔ G (p z) ∈ M n
      rw [hs z]
    have hm : F (a n) ∈ p ⁻¹' M n := by
      rw [← ih]
      exact hanchor n
    change p (F (a n)) ∈ M n at hm
    rw [hs (a n)] at hm
    rw [hL n, ih, hpre, hM n]
    exact component_preimage_closed_fibers p hp.isClosedMap hp hsurj hf
      (G ⁻¹' M n) (a n) hm

/-- A dynamically maximal mark in an open trapping region is saturated
if the mark's model image avoids the region's frontier image.
Only fibers over the mark are tested; the whole trapping region
need not be saturated, nor every frontier fiber a singleton.
The map F can be any return iterate. -/
theorem invariant_trapping_mark_saturated
    (p : X → Y) (F : X → X) (G : Y → Y) (hs : Semiconj p F G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (M U : Set X) (hU : IsOpen U) (hMU : M ⊆ U)
    (hFM : MapsTo F M M)
    (hmax : ∀ x : X, (∀ n : ℕ, (F^[n]) x ∈ U) → x ∈ M)
    (hsep : Disjoint (p '' frontier U) (p '' M)) :
    p ⁻¹' (p '' M) = M := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, hxz⟩ := hz
    apply hmax z
    intro n
    have hxM : (F^[n]) x ∈ M := (hFM.iterate n) hx
    have hxU : (F^[n]) x ∈ U := hMU hxM
    have hsame : p ((F^[n]) x) = p ((F^[n]) z) := by
      rw [hs.iterate_right n x, hs.iterate_right n z, hxz]
    by_contra hzU
    have hcover : p ⁻¹' ({p ((F^[n]) x)} : Set Y) ⊆ closure U ∪ Uᶜ := by
      intro w _
      by_cases hw : w ∈ U
      · exact Or.inl (subset_closure hw)
      · exact Or.inr hw
    obtain ⟨w, hw, hwcl, hwout⟩ :=
      (isPreconnected_closed_iff.mp (hf (p ((F^[n]) x))))
        (closure U) Uᶜ isClosed_closure hU.isClosed_compl hcover
        ⟨(F^[n]) x, rfl, subset_closure hxU⟩
        ⟨(F^[n]) z, hsame.symm, hzU⟩
    have hwfront : w ∈ frontier U := by
      change w ∈ closure U ∧ w ∉ interior U
      rw [hU.interior_eq]
      exact ⟨hwcl, hwout⟩
    have he : p w = p ((F^[n]) x) := hw
    exact Set.disjoint_left.mp hsep ⟨w, hwfront, rfl⟩
      ⟨(F^[n]) x, hxM, he.symm⟩
  · intro z hz
    exact ⟨z, hz, rfl⟩

/-- Exact obstruction criterion: for a maximal invariant mark
inside an open return region, saturation is equivalent to absence
of contact between its model image and the trapping frontier image. -/
theorem invariant_trapping_mark_saturation_iff
    (p : X → Y) (F : X → X) (G : Y → Y) (hs : Semiconj p F G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (M U : Set X) (hU : IsOpen U) (hMU : M ⊆ U)
    (hFM : MapsTo F M M)
    (hmax : ∀ x : X, (∀ n : ℕ, (F^[n]) x ∈ U) → x ∈ M) :
    p ⁻¹' (p '' M) = M ↔ Disjoint (p '' frontier U) (p '' M) := by
  constructor
  · intro hsat
    apply Set.disjoint_left.mpr
    intro y hy₁ hy₂
    obtain ⟨a, ha, rfl⟩ := hy₁
    have haM : a ∈ p ⁻¹' (p '' M) := hy₂
    rw [hsat] at haM
    change a ∈ closure U ∧ a ∉ interior U at ha
    rw [hU.interior_eq] at ha
    exact ha.2 (hMU haM)
  · exact invariant_trapping_mark_saturated p F G hs hf M U hU hMU hFM hmax

/-- Preperiodic frontier anchors with singleton eventual fibers
saturate the entire open return region. Every maximal survivor of
every return iterate is then exactly the full lift of the
corresponding model survivor, with equality of its model image.
No finite-to-one assumption on the model map is used. -/
theorem preperiodic_frontier_trapping_correspondence [T1Space X]
    (p : X → Y) (F : X → X) (G : Y → Y)
    (hsurj : Surjective p) (hs : Semiconj p F G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hfinite : ∀ x : X, (F ⁻¹' {x}).Finite)
    (U : Set X) (hU : IsOpen U)
    (hfront : ∀ z ∈ frontier U, ∃ a : X, ∃ k : ℕ,
      p ⁻¹' ({p a} : Set Y) = {a} ∧ (F^[k]) z = a) :
    p ⁻¹' (p '' U) = U ∧
      ∀ P : ℕ,
        p ⁻¹' {y : Y | ∀ n : ℕ, ((G^[P])^[n]) y ∈ p '' U} =
          {x : X | ∀ n : ℕ, ((F^[P])^[n]) x ∈ U} ∧
        p '' {x : X | ∀ n : ℕ, ((F^[P])^[n]) x ∈ U} =
          {y : Y | ∀ n : ℕ, ((G^[P])^[n]) y ∈ p '' U} := by
  have hsingle (z : X) (hz : z ∈ frontier U) :
      p ⁻¹' ({p z} : Set Y) = {z} := by
    obtain ⟨a, k, ha, hk⟩ := hfront z hz
    exact singleton_fiber_of_iterate p F G hf hs hfinite a z ha k hk
  have hsep : Disjoint (p '' frontier U) (p '' U) := by
    apply Set.disjoint_left.mpr
    intro y hy₁ hy₂
    obtain ⟨a, ha, rfl⟩ := hy₁
    obtain ⟨b, hb, hba⟩ := hy₂
    have hbf : b ∈ p ⁻¹' ({p a} : Set Y) := hba
    rw [hsingle a ha] at hbf
    have he : b = a := hbf
    change a ∈ closure U ∧ a ∉ interior U at ha
    rw [hU.interior_eq] at ha
    exact ha.2 (he ▸ hb)
  have hsat : p ⁻¹' (p '' U) = U :=
    invariant_trapping_mark_saturated p id id (fun _ => rfl) hf U U hU
      Subset.rfl (fun _ hx => hx) (fun x hx => by simpa using hx 0) hsep
  refine ⟨hsat, ?_⟩
  intro P
  let A : Set X := {x | ∀ n : ℕ, ((F^[P])^[n]) x ∈ U}
  let B : Set Y := {y | ∀ n : ℕ, ((G^[P])^[n]) y ∈ p '' U}
  have hsp : Semiconj p (F^[P]) (G^[P]) := hs.iterate_right P
  have hpre : p ⁻¹' B = A := by
    ext x
    constructor
    · intro hx
      change ∀ n : ℕ, ((G^[P])^[n]) (p x) ∈ p '' U at hx
      change ∀ n : ℕ, ((F^[P])^[n]) x ∈ U
      intro n
      have hh : p (((F^[P])^[n]) x) ∈ p '' U := by
        rw [hsp.iterate_right n x]
        exact hx n
      have he : ((F^[P])^[n]) x ∈ p ⁻¹' (p '' U) := hh
      rwa [hsat] at he
    · intro hx
      change ∀ n : ℕ, ((F^[P])^[n]) x ∈ U at hx
      change ∀ n : ℕ, ((G^[P])^[n]) (p x) ∈ p '' U
      intro n
      rw [← hsp.iterate_right n x]
      exact ⟨((F^[P])^[n]) x, hx n, rfl⟩
  refine ⟨hpre, ?_⟩
  change p '' A = B
  rw [← hpre]
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, hxy⟩ := hsurj y
    refine ⟨x, ?_, hxy⟩
    change p x ∈ B
    rwa [hxy]

/-- Specialization to the actual quadratic: the finite physical
point-fiber condition follows from its polynomial equation. -/
theorem quadratic_return_preperiodic_frontier
    (c : ℂ) (K : Set ℂ) (F : K → K)
    (hF : ∀ z : K, (F z : ℂ) = (z : ℂ)^2+c)
    (p : K → Y) (G : Y → Y) (hsurj : Surjective p)
    (hs : Semiconj p F G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (U : Set K) (hU : IsOpen U)
    (hfront : ∀ z ∈ frontier U, ∃ a : K, ∃ k : ℕ,
      p ⁻¹' ({p a} : Set Y) = {a} ∧ (F^[k]) z = a) :
    p ⁻¹' (p '' U) = U ∧
      ∀ P : ℕ,
        p ⁻¹' {y : Y | ∀ n : ℕ, ((G^[P])^[n]) y ∈ p '' U} =
          {x : K | ∀ n : ℕ, ((F^[P])^[n]) x ∈ U} ∧
        p '' {x : K | ∀ n : ℕ, ((F^[P])^[n]) x ∈ U} =
          {y : Y | ∀ n : ℕ, ((G^[P])^[n]) y ∈ p '' U} := by
  exact preperiodic_frontier_trapping_correspondence p F G hsurj hs hf
    (quadratic_restricted_fiber_finite c K F hF) U hU hfront


/-- Removing any set of singleton-fiber anchors is compatible with
the exact geometric component lift. Neither the anchor set nor the
component needs to be open, finite, or closed. -/
theorem singleton_cut_set_full_lift [CompactSpace X] [T2Space Y]
    (p : X → Y) (hp : Continuous p) (hsurj : Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (A : Set X) (hA : ∀ a ∈ A, p ⁻¹' ({p a} : Set Y) = {a})
    (x : X) (hx : x ∉ A) :
    connectedComponentIn Aᶜ x =
      p ⁻¹' connectedComponentIn (p '' A)ᶜ (p x) := by
  have hsat : p ⁻¹' (p '' A) = A := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨a, ha, haz⟩ := hz
      have hm : z ∈ p ⁻¹' ({p a} : Set Y) := haz.symm
      rw [hA a ha] at hm
      have he : z = a := hm
      exact he.symm ▸ ha
    · intro z hz
      exact ⟨z, hz, rfl⟩
  have he : p ⁻¹' (p '' A)ᶜ = Aᶜ := by rw [preimage_compl, hsat]
  have hx' : p x ∈ (p '' A)ᶜ := by
    change x ∈ p ⁻¹' (p '' A)ᶜ
    rw [he]
    exact hx
  rw [← he]
  exact component_preimage_closed_fibers p hp.isClosedMap hp hsurj hf
    (p '' A)ᶜ x hx'

section ModelComparison

variable {Z : Type*} [TopologicalSpace Z]

private theorem singleton_anchor_eq (p : X → Y) (a x : X)
    (ha : p ⁻¹' ({p a} : Set Y) = {a}) :
    p x = p a ↔ x = a := by
  constructor
  · intro h
    have hm : x ∈ p ⁻¹' ({p a} : Set Y) := h
    rw [ha] at hm
    exact hm
  · intro h
    rw [h]

/-- The first quotient refines the second if shared singleton-fiber
anchors separate points of the second by their punctured components.
This is a one-sided test on only the target of the second quotient,
not an assumption that the two fiber equivalences coincide. -/
theorem quotient_fiber_refinement_of_cut_separation
    (p : X → Y) (q : X → Z) (hq : Continuous q)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (A : Set X)
    (hpa : ∀ a ∈ A, p ⁻¹' ({p a} : Set Y) = {a})
    (hqa : ∀ a ∈ A, q ⁻¹' ({q a} : Set Z) = {a})
    (hsep : ∀ y z : Z, (∀ a ∈ A,
      (y = q a ↔ z = q a) ∧
      (y ≠ q a → z ∈ connectedComponentIn ({q a} : Set Z)ᶜ y)) → y = z) :
    ∀ x z : X, p x = p z → q x = q z := by
  intro x z h
  apply hsep
  intro a ha
  have hpxa := singleton_anchor_eq p a x (hpa a ha)
  have hpza := singleton_anchor_eq p a z (hpa a ha)
  have hqxa := singleton_anchor_eq q a x (hqa a ha)
  have hqza := singleton_anchor_eq q a z (hqa a ha)
  have hxa : x = a ↔ z = a := by
    constructor
    · intro hx
      exact hpza.mp (h.symm.trans (hpxa.mpr hx))
    · intro hz
      exact hpxa.mp (h.trans (hpza.mpr hz))
  constructor
  · exact hqxa.trans (hxa.trans hqza.symm)
  · intro hxq
    have hxne : x ≠ a := fun he => hxq (hqxa.mpr he)
    let C : Set X := p ⁻¹' {p x}
    have hC : IsPreconnected (q '' C) := (hf (p x)).image q hq.continuousOn
    have hsub : q '' C ⊆ ({q a} : Set Z)ᶜ := by
      rintro _ ⟨u, hu, rfl⟩ huq
      have hua : u = a := (singleton_anchor_eq q a u (hqa a ha)).mp huq
      change p u = p x at hu
      rw [hua] at hu
      exact hxne (hpxa.mp hu.symm)
    exact hC.subset_connectedComponentIn
      ⟨x, rfl, rfl⟩ hsub ⟨z, h.symm, rfl⟩

/-- Equal full fiber equivalences on a compact physical space
construct a dynamical homeomorphism of the Hausdorff targets.
Every geometric mark that is the image of a physical set is
carried to its corresponding image, without a separate marking axiom. -/
theorem quotient_dynamical_homeomorphism_of_equal_fibers
    [CompactSpace X] [T2Space Y] [T2Space Z]
    (p : X → Y) (q : X → Z) (hp : Continuous p) (hq : Continuous q)
    (hps : Surjective p) (hqs : Surjective q)
    (heq : ∀ x z : X, p x = p z ↔ q x = q z)
    (F : X → X) (G : Y → Y) (H : Z → Z)
    (hP : Semiconj p F G) (hQ : Semiconj q F H) :
    ∃ e : Y ≃ₜ Z, (∀ x : X, e (p x) = q x) ∧
      (∀ y : Y, e (G y) = H (e y)) ∧
      ∀ S : Set X, e '' (p '' S) = q '' S := by
  classical
  let j : Y → Z := fun y => q (Classical.choose (hps y))
  let k : Z → Y := fun z => p (Classical.choose (hqs z))
  have hj (x : X) : j (p x) = q x :=
    (heq _ _).mp (Classical.choose_spec (hps (p x)))
  have hk (x : X) : k (q x) = p x :=
    (heq _ _).mpr (Classical.choose_spec (hqs (q x)))
  have hleft : LeftInverse k j := by
    intro y
    obtain ⟨x, rfl⟩ := hps y
    rw [hj, hk]
  have hright : RightInverse k j := by
    intro z
    obtain ⟨x, rfl⟩ := hqs z
    rw [hk, hj]
  have hjc : Continuous j := by
    apply continuous_iff_isClosed.mpr
    intro S hS
    have hset : j ⁻¹' S = p '' (q ⁻¹' S) := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := hps y
        change j (p x) ∈ S at hy
        rw [hj] at hy
        exact ⟨x, hy, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        change j (p x) ∈ S
        rw [hj]
        exact hx
    rw [hset]
    exact hp.isClosedMap _ (hS.preimage hq)
  have hkc : Continuous k := by
    apply continuous_iff_isClosed.mpr
    intro S hS
    have hset : k ⁻¹' S = q '' (p ⁻¹' S) := by
      ext z
      constructor
      · intro hz
        obtain ⟨x, rfl⟩ := hqs z
        change k (q x) ∈ S at hz
        rw [hk] at hz
        exact ⟨x, hz, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        change k (q x) ∈ S
        rw [hk]
        exact hx
    rw [hset]
    exact hq.isClosedMap _ (hS.preimage hp)
  let e : Y ≃ₜ Z := ⟨⟨j, k, hleft, hright⟩, hjc, hkc⟩
  refine ⟨e, hj, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hps y
    change j (G (p x)) = H (j (p x))
    rw [← hP x, hj (F x), hQ x, hj x]
  · intro S
    apply Subset.antisymm
    · rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hj x).symm⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨p x, ⟨x, hx, rfl⟩, hj x⟩

/-- Two monotone geometric models admitting a common family of
singleton anchors that separates points in both punctured-component
systems are canonically dynamically homeomorphic. This turns
model identification into two explicit geometric separation tests. -/
theorem quotient_dynamical_homeomorphism_of_common_cuts
    [CompactSpace X] [T2Space Y] [T2Space Z]
    (p : X → Y) (q : X → Z) (hp : Continuous p) (hq : Continuous q)
    (hps : Surjective p) (hqs : Surjective q)
    (hpf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hqf : ∀ z : Z, IsPreconnected (q ⁻¹' {z}))
    (A : Set X)
    (hpa : ∀ a ∈ A, p ⁻¹' ({p a} : Set Y) = {a})
    (hqa : ∀ a ∈ A, q ⁻¹' ({q a} : Set Z) = {a})
    (hsepP : ∀ y z : Y, (∀ a ∈ A,
      (y = p a ↔ z = p a) ∧
      (y ≠ p a → z ∈ connectedComponentIn ({p a} : Set Y)ᶜ y)) → y = z)
    (hsepQ : ∀ y z : Z, (∀ a ∈ A,
      (y = q a ↔ z = q a) ∧
      (y ≠ q a → z ∈ connectedComponentIn ({q a} : Set Z)ᶜ y)) → y = z)
    (F : X → X) (G : Y → Y) (H : Z → Z)
    (hP : Semiconj p F G) (hQ : Semiconj q F H) :
    ∃ e : Y ≃ₜ Z, (∀ x : X, e (p x) = q x) ∧
      (∀ y : Y, e (G y) = H (e y)) ∧
      ∀ S : Set X, e '' (p '' S) = q '' S := by
  apply quotient_dynamical_homeomorphism_of_equal_fibers p q hp hq hps hqs
    _ F G H hP hQ
  intro x z
  exact ⟨quotient_fiber_refinement_of_cut_separation p q hq hpf A hpa hqa hsepQ x z,
    quotient_fiber_refinement_of_cut_separation q p hp hqf A hqa hpa hsepP x z⟩

end ModelComparison


/-- The genuine filled Julia set of the quadratic polynomial, defined
through the already constructed escape potential. The next theorem
identifies this set with the bounded-orbit locus for every parameter. -/
noncomputable def quadraticFilled (c : ℂ) : Set ℂ :=
  {z | QuadraticEscape.escape c z = 0}

theorem quadratic_filled_iff_bounded (c z : ℂ) :
    z ∈ quadraticFilled c ↔
      ∃ B : ℝ, ∀ n : ℕ, ‖QuadraticEscape.orbit c n z‖ ≤ B :=
  QuadraticEscape.escape_zero_iff_bounded c z

/-- Compactness is a proved property of the actual bounded-orbit set,
not an additional hypothesis on an arbitrary physical carrier. -/
theorem quadratic_filled_compact (c : ℂ) : IsCompact (quadraticFilled c) := by
  have hpair : Continuous (fun z : ℂ => (c, z)) :=
    continuous_const.prodMk continuous_id
  have hc : Continuous (fun z : ℂ => QuadraticEscape.escape c z) := by
    change Continuous ((fun x : ℂ × ℂ => QuadraticEscape.escape x.1 x.2) ∘
      (fun z : ℂ => (c, z)))
    exact QuadraticEscape.escape_continuous.comp hpair
  have hclosed : IsClosed (quadraticFilled c) :=
    isClosed_singleton.preimage hc
  apply (isCompact_closedBall (0 : ℂ) (1+‖c‖)).of_isClosed_subset hclosed
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact QuadraticEscape.escape_zero_orbit_bound c z hz 0

/-- Both directions of complete invariance of the genuine filled set
follow from the proved quadratic escape functional equation. -/
theorem quadratic_filled_complete_invariant (c z : ℂ) :
    z^2+c ∈ quadraticFilled c ↔ z ∈ quadraticFilled c := by
  change QuadraticEscape.escape c (z^2+c) = 0 ↔ QuadraticEscape.escape c z = 0
  rw [QuadraticEscape.escape_step]
  constructor <;> intro h <;> linarith

/-- The actual self-map on the filled Julia set. -/
noncomputable def quadraticFilledMap (c : ℂ) : quadraticFilled c → quadraticFilled c :=
  fun z => ⟨(z : ℂ)^2+c, (quadratic_filled_complete_invariant c z).mpr z.property⟩

/-- The full geometric fiber transport theorem on the genuine
filled Julia set at every parameter. No compactness, complete
invariance or restriction equation for an unspecified physical
carrier is a premise. The finite-to-one monotone model still is. -/
theorem quadratic_filled_fiber_image [T1Space Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hfinite : ∀ y : Y, (G ⁻¹' {y}).Finite) (y : Y) :
    quadraticFilledMap c '' (p ⁻¹' {y}) = p ⁻¹' {G y} := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  exact quadratic_restriction_fiber_image c (quadraticFilled c)
    (quadraticFilledMap c) (fun _ => rfl)
    (fun z hz => (quadratic_filled_complete_invariant c z).mp hz)
    p G hp hsurj hs hf hfinite y

end LoopsStationaryFiberDynamics
