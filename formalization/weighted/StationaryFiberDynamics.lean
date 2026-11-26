import StationaryGeometricFibers
import QuadraticCylinderCensus

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
  have hD : IsClosed D := ((hfinite (G y)).subset diff_subset).isClosed
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

end LoopsStationaryFiberDynamics
