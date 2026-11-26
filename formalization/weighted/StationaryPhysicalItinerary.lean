import StationaryLightModel
import SaturatedTelescope

/-!
# Actual critical-limb predecessor recognition

The input is the native limb geometry in the filled Julia set, not an
assumed address for the proof-used endpoint. The base may be disconnected.
-/

namespace LoopsStationaryPhysicalItinerary

open Set Function
open LoopsStationaryFiberDynamics LoopsStationaryLightModel

variable {X : Type*} [TopologicalSpace X]

/-- The other limb consumes one of the two actual quadratic roots.
Consequently the critical-limb inverse of its own points is unique. -/
theorem quadratic_critical_limb_injective (c : ℂ)
    (D E : Set (quadraticFilled c)) (hDE : Disjoint D E)
    (hother : D ⊆ quadraticFilledMap c '' E) :
    InjOn (quadraticFilledMap c) (D ∩ quadraticFilledMap c ⁻¹' D) := by
  intro x hx y hy hxy
  obtain ⟨z, hz, hzx⟩ := hother hx.2
  have hxz : x ≠ z := by
    intro h
    exact Set.disjoint_left.mp hDE hx.1 (by simpa only [h] using hz)
  have hyz : y ≠ z := by
    intro h
    exact Set.disjoint_left.mp hDE hy.1 (by simpa only [h] using hz)
  rcases quadratic_filled_no_three_predecessors c x y z hxy hzx.symm with h | h | h
  · exact h
  · exact (hxz h).elim
  · exact (hyz h).elim

/-- Pulling a preconnected target through the selected limb preserves
preconnectedness by openness and uniqueness of the selected inverse.
This proof needs no local connectivity of the filled set. -/
theorem limb_inverse_preconnected (F : X → X) (D B : Set X)
    (hopen : IsOpenMap F) (hD : IsOpen D)
    (hcover : D ⊆ F '' D) (hinj : InjOn F (D ∩ F ⁻¹' D))
    (hBD : B ⊆ D) (hB : IsPreconnected B) :
    IsPreconnected (D ∩ F ⁻¹' B) := by
  intro U V hU hV hUV hleft hright
  have hcov : B ⊆ F '' (D ∩ U) ∪ F '' (D ∩ V) := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := hcover (hBD hw)
    have hzB : z ∈ D ∩ F ⁻¹' B := ⟨hz, hzw.symm ▸ hw⟩
    rcases hUV hzB with hu | hv
    · exact Or.inl ⟨z, ⟨hz, hu⟩, hzw⟩
    · exact Or.inr ⟨z, ⟨hz, hv⟩, hzw⟩
  obtain ⟨x, hx, hxU⟩ := hleft
  obtain ⟨y, hy, hyV⟩ := hright
  obtain ⟨w, hw, hwU, hwV⟩ :=
    hB (F '' (D ∩ U)) (F '' (D ∩ V))
      (hopen _ (hD.inter hU)) (hopen _ (hD.inter hV)) hcov
      ⟨F x, hx.2, ⟨x, ⟨hx.1, hxU⟩, rfl⟩⟩
      ⟨F y, hy.2, ⟨y, ⟨hy.1, hyV⟩, rfl⟩⟩
  obtain ⟨u, hu, huw⟩ := hwU
  obtain ⟨v, hv, hvw⟩ := hwV
  have huB : F u ∈ B := huw.symm ▸ hw
  have hvB : F v ∈ B := hvw.symm ▸ hw
  have huv : u = v := hinj ⟨hu.1, hBD huB⟩ ⟨hv.1, hBD hvB⟩
    (huw.trans hvw.symm)
  exact ⟨u, ⟨hu.1, huB⟩, hu.2, huv.symm ▸ hv.2⟩

/-- The selected inverse has exactly the prescribed target image. -/
theorem limb_inverse_image (F : X → X) (D B : Set X)
    (hcover : D ⊆ F '' D) (hBD : B ⊆ D) :
    F '' (D ∩ F ⁻¹' B) = B := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := hcover (hBD hw)
    exact ⟨z, ⟨hz, hzw.symm ▸ hw⟩, hzw⟩

/-- The selected inverse is a whole component of the full inverse,
not merely a connected piece inside the chosen sheet. The fixed
cutpoint excludes excursions through the other limbs. -/
theorem limb_inverse_component (F : X → X) (D B : Set X)
    (a d x : X) (hfix : F a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set X)ᶜ d)
    (hopen : IsOpenMap F) (hD : IsOpen D)
    (hcover : D ⊆ F '' D) (hinj : InjOn F (D ∩ F ⁻¹' D))
    (hBD : B ⊆ D) (hB : IsPreconnected B)
    (hx : x ∈ D ∩ F ⁻¹' B) :
    D ∩ F ⁻¹' B = connectedComponentIn (F ⁻¹' B) x := by
  have hDavoid : D ⊆ ({a} : Set X)ᶜ := by
    rw [hDcomp]
    exact connectedComponentIn_subset _ _
  apply Subset.antisymm
  · have hc := limb_inverse_preconnected F D B hopen hD hcover hinj hBD hB
    exact hc.subset_connectedComponentIn hx (fun _ hz => hz.2)
  · have havoid : F ⁻¹' B ⊆ ({a} : Set X)ᶜ := by
      intro z hz
      change z ∉ ({a} : Set X)
      intro hza
      have he : z = a := Set.mem_singleton_iff.mp hza
      subst z
      change F a ∈ B at hz
      rw [hfix] at hz
      exact hDavoid (hBD hz) (Set.mem_singleton a)
    have hsub := connectedComponentIn_mono x havoid
    have hxd : x ∈ connectedComponentIn ({a} : Set X)ᶜ d := by
      rw [← hDcomp]
      exact hx.1
    have heq : connectedComponentIn ({a} : Set X)ᶜ x = D :=
      (connectedComponentIn_eq hxd).symm.trans hDcomp.symm
    intro z hz
    exact ⟨heq ▸ hsub hz, connectedComponentIn_subset _ _ hz⟩

/-- The itinerary is defined without supplying any component labels. -/
def limbItinerary (F : X → X) (D B : Set X) : ℕ → Set X
  | 0 => B
  | n+1 => D ∩ F ⁻¹' limbItinerary F D B n

/-- Exact pointwise recognition from the ordinary forward orbit:
every intermediate time is in the physical critical limb and the
terminal point is in the selected base. -/
theorem mem_limbItinerary (F : X → X) (D B : Set X) (n : ℕ) (x : X) :
    x ∈ limbItinerary F D B n ↔
      (∀ k < n, (F^[k]) x ∈ D) ∧ (F^[n]) x ∈ B := by
  induction n generalizing x with
  | zero => simp [limbItinerary]
  | succ n ih =>
    change (x ∈ D ∧ F x ∈ limbItinerary F D B n) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hx, hs, ht⟩
      refine ⟨?_, ?_⟩
      · intro k hk
        cases k with
        | zero => simpa using hx
        | succ k =>
          rw [Function.iterate_succ_apply]
          exact hs k (by omega)
      · rw [Function.iterate_succ_apply]
        exact ht
    · rintro ⟨hs, ht⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa using hs 0 (Nat.zero_lt_succ n)
      · intro k hk
        have h := hs (k+1) (by omega)
        rwa [Function.iterate_succ_apply] at h
      · rw [Function.iterate_succ_apply] at ht
        exact ht

/-- All depths remain in the critical limb, even when the selected
base is a proper connected component of the original base. -/
theorem limbItinerary_subset (F : X → X) (D B : Set X)
    (hBD : B ⊆ D) (n : ℕ) : limbItinerary F D B n ⊆ D := by
  cases n with
  | zero => exact hBD
  | succ n => exact fun _ hz => hz.1

/-- The forward itinerary is a whole connected component of the full
iterate preimage, at every finite depth and for every anchor in it. -/
theorem limbItinerary_component (F : X → X) (D B : Set X)
    (a d : X) (hfix : F a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set X)ᶜ d)
    (hF : Continuous F) (hopen : IsOpenMap F) (hD : IsOpen D)
    (hcover : D ⊆ F '' D) (hinj : InjOn F (D ∩ F ⁻¹' D))
    (hBD : B ⊆ D) (hB : IsPreconnected B) (n : ℕ) :
    IsPreconnected (limbItinerary F D B n) ∧
      ∀ x ∈ limbItinerary F D B n,
        limbItinerary F D B n = connectedComponentIn ((F^[n]) ⁻¹' B) x := by
  induction n with
  | zero =>
    refine ⟨hB, ?_⟩
    intro x hx
    simpa [limbItinerary] using (hB.connectedComponentIn hx).symm
  | succ n ih =>
    have hsub := limbItinerary_subset F D B hBD n
    refine ⟨limb_inverse_preconnected F D _ hopen hD hcover hinj hsub ih.1, ?_⟩
    intro x hx
    change x ∈ D ∩ F ⁻¹' limbItinerary F D B n at hx
    change D ∩ F ⁻¹' limbItinerary F D B n = _
    have hstep := limb_inverse_component F D (limbItinerary F D B n)
      a d x hfix hDcomp hopen hD hcover hinj hsub ih.1 hx
    have hterminal : (F^[n]) (F x) ∈ B :=
      ((mem_limbItinerary F D B n (F x)).mp hx.2).2
    rw [hstep, ih.2 (F x) hx.2]
    rw [LoopsSaturatedTelescope.component_pullback_comp F (F^[n]) B x hF hterminal]
    rw [Function.iterate_succ]

/-- The genuine filled-set map is continuous and open. This uses
the archive's proved complete invariance, including the critical point. -/
theorem quadratic_filled_continuous_open (c : ℂ) :
    Continuous (quadraticFilledMap c) ∧ IsOpenMap (quadraticFilledMap c) := by
  constructor
  · exact ((continuous_subtype_val.pow 2).add continuous_const).subtype_mk _
  · exact quadratic_restriction_open c (quadraticFilled c) (quadraticFilledMap c)
      (fun _ => rfl) (fun z hz => (quadratic_filled_complete_invariant c z).mp hz)

/-- If the base is disconnected, the terminal point need only be in
the base component anchored by the marked central point. The actual
orbit itinerary then recovers the full selected component of the
original base's iterate preimage. No selected endpoint address is
assumed. -/
theorem quadratic_selected_itinerary_component (c : ℂ)
    (D E B : Set (quadraticFilled c)) (a d q x : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hBD : B ⊆ D) (n : ℕ)
    (hstay : ∀ k < n, ((quadraticFilledMap c)^[k]) x ∈ D)
    (hterminal : ((quadraticFilledMap c)^[n]) x ∈ connectedComponentIn B q) :
    limbItinerary (quadraticFilledMap c) D (connectedComponentIn B q) n =
      connectedComponentIn (((quadraticFilledMap c)^[n]) ⁻¹' B) x := by
  let F := quadraticFilledMap c
  have hcont : Continuous F := (quadratic_filled_continuous_open c).1
  have hopen : IsOpenMap F := (quadratic_filled_continuous_open c).2
  have hBsub : connectedComponentIn B q ⊆ B := connectedComponentIn_subset B q
  have hx : x ∈ limbItinerary F D (connectedComponentIn B q) n :=
    (mem_limbItinerary F D _ n x).mpr ⟨hstay, hterminal⟩
  have hcomponent := (limbItinerary_component F D (connectedComponentIn B q)
    a d hfix hDcomp hcont hopen hD hcover
    (quadratic_critical_limb_injective c D E hDE hother)
    (hBsub.trans hBD) isPreconnected_connectedComponentIn n).2 x hx
  change limbItinerary F D (connectedComponentIn B q) n = _
  rw [hcomponent]
  apply Subset.antisymm
  · exact connectedComponentIn_mono x (fun _ hz => hBsub hz)
  · let C := connectedComponentIn ((F^[n]) ⁻¹' B) x
    have hxC : x ∈ C := mem_connectedComponentIn (hBsub hterminal)
    have hC : IsPreconnected C := isPreconnected_connectedComponentIn
    have hImg : IsPreconnected ((F^[n]) '' C) :=
      hC.image _ (hcont.iterate n).continuousOn
    have hImgSub : (F^[n]) '' C ⊆ B := by
      rintro _ ⟨z, hz, rfl⟩
      exact connectedComponentIn_subset _ _ hz
    have hImgMem : (F^[n]) x ∈ (F^[n]) '' C := ⟨x, hxC, rfl⟩
    have hImgComp := hImg.subset_connectedComponentIn hImgMem hImgSub
    have heq : connectedComponentIn B ((F^[n]) x) = connectedComponentIn B q :=
      (connectedComponentIn_eq hterminal).symm
    rw [heq] at hImgComp
    exact hC.subset_connectedComponentIn hxC (fun z hz => hImgComp ⟨z, hz, rfl⟩)

/-- A connected independently supplied physical restriction cannot
carry a different component address once one endpoint satisfies the
critical-limb itinerary and terminal anchored-component condition. -/
theorem quadratic_restriction_itinerary_contained (c : ℂ)
    (D E B R : Set (quadraticFilled c)) (a d q x : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hBD : B ⊆ D) (n : ℕ)
    (hstay : ∀ k < n, ((quadraticFilledMap c)^[k]) x ∈ D)
    (hterminal : ((quadraticFilledMap c)^[n]) x ∈ connectedComponentIn B q)
    (hR : IsPreconnected R) (hx : x ∈ R)
    (hRsub : R ⊆ ((quadraticFilledMap c)^[n]) ⁻¹' B) :
    R ⊆ limbItinerary (quadraticFilledMap c) D (connectedComponentIn B q) n := by
  rw [quadratic_selected_itinerary_component c D E B a d q x hfix hDcomp hD
    hDE hcover hother hBD n hstay hterminal]
  exact hR.subset_connectedComponentIn hx hRsub

end LoopsStationaryPhysicalItinerary
