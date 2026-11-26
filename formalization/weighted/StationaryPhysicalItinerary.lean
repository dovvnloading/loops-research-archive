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
    have hpre : F z ∈ B := by rwa [hzw]
    have hzB : z ∈ D ∩ F ⁻¹' B := ⟨hz, hpre⟩
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
    have hpre : F z ∈ B := by rwa [hzw]
    exact ⟨z, ⟨hz, hpre⟩, hzw⟩

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
    exact LoopsSaturatedTelescope.component_pullback_comp F (F^[n]) B x hF hterminal

/-- The genuine filled-set map is continuous and open. This uses
the archive's proved complete invariance, including the critical point. -/
theorem quadratic_filled_continuous_open (c : ℂ) :
    Continuous (quadraticFilledMap c) ∧ IsOpenMap (quadraticFilledMap c) := by
  constructor
  · have h : Continuous (fun z : quadraticFilled c => (z : ℂ)^2+c) :=
      ((continuous_subtype_val : Continuous (Subtype.val : quadraticFilled c → ℂ)).pow 2).add
        continuous_const
    exact h.subtype_mk (fun z => (quadratic_filled_complete_invariant c z).mpr z.property)
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
      change z ∈ (F^[n]) ⁻¹' B
      exact connectedComponentIn_subset ((F^[n]) ⁻¹' B) x hz
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

/-- The selected inverse at every depth has the entire prescribed
base as image. This also guarantees nonemptiness when the base is
nonempty, without choosing an endpoint in advance. -/
theorem limbItinerary_image (F : X → X) (D B : Set X)
    (hcover : D ⊆ F '' D) (hBD : B ⊆ D) (n : ℕ) :
    (F^[n]) '' limbItinerary F D B n = B := by
  induction n with
  | zero => simp [limbItinerary]
  | succ n ih =>
    change (F^[n+1]) '' (D ∩ F ⁻¹' limbItinerary F D B n) = B
    rw [Function.iterate_succ, Set.image_comp,
      limb_inverse_image F D _ hcover (limbItinerary_subset F D B hBD n), ih]

/-- No two points of the same selected itinerary can have the same
terminal point, at any depth, even for disconnected base sets. -/
theorem limbItinerary_injective (F : X → X) (D B : Set X)
    (hinj : InjOn F (D ∩ F ⁻¹' D)) (hBD : B ⊆ D) (n : ℕ) :
    InjOn (F^[n]) (limbItinerary F D B n) := by
  induction n with
  | zero =>
    intro x hx y hy hxy
    exact hxy
  | succ n ih =>
    intro x hx y hy hxy
    change x ∈ D ∩ F ⁻¹' limbItinerary F D B n at hx
    change y ∈ D ∩ F ⁻¹' limbItinerary F D B n at hy
    have hs := limbItinerary_subset F D B hBD n
    have hxy' : (F^[n]) (F x) = (F^[n]) (F y) := hxy
    exact hinj ⟨hx.1, hs hx.2⟩ ⟨hy.1, hs hy.2⟩ (ih hx.2 hy.2 hxy')

/-- The physical itinerary has exactly one inverse point of every
terminal point in the critical limb. This is an existence and
uniqueness theorem on the genuine filled set; an endpoint need not
be supplied to construct the inverse orbit. -/
theorem quadratic_critical_limb_unique_inverse (c : ℂ)
    (D E : Set (quadraticFilled c)) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (n : ℕ) (y : quadraticFilled c) (hy : y ∈ D) :
    ∃! x : quadraticFilled c,
      (∀ k < n, ((quadraticFilledMap c)^[k]) x ∈ D) ∧
        ((quadraticFilledMap c)^[n]) x = y := by
  let F := quadraticFilledMap c
  have himage := limbItinerary_image F D D hcover Subset.rfl n
  have hinj := limbItinerary_injective F D D
    (quadratic_critical_limb_injective c D E hDE hother) Subset.rfl n
  have hy' : y ∈ (F^[n]) '' limbItinerary F D D n := by
    rw [himage]
    exact hy
  obtain ⟨x, hx, hxy⟩ := hy'
  refine ⟨x, ⟨((mem_limbItinerary F D D n x).mp hx).1, hxy⟩, ?_⟩
  intro z hz
  have hzD : (F^[n]) z ∈ D := by
    rw [hz.2]
    exact hy
  have hz' : z ∈ limbItinerary F D D n :=
    (mem_limbItinerary F D D n z).mpr ⟨hz.1, hzD⟩
  exact hinj hz' hx (hz.2.trans hxy.symm)

/-- The terminal base-component test can be discharged by actual
contact with a connected central mark, with no model vertex or
assumed component label. -/
theorem quadratic_mark_itinerary_component (c : ℂ)
    (D E B Q : Set (quadraticFilled c)) (a d q x : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hBD : B ⊆ D) (hQ : IsPreconnected Q) (hQB : Q ⊆ B) (hq : q ∈ Q)
    (n : ℕ)
    (hstay : ∀ k < n, ((quadraticFilledMap c)^[k]) x ∈ D)
    (hterminal : ((quadraticFilledMap c)^[n]) x ∈ Q) :
    limbItinerary (quadraticFilledMap c) D (connectedComponentIn B q) n =
      connectedComponentIn (((quadraticFilledMap c)^[n]) ⁻¹' B) x :=
  quadratic_selected_itinerary_component c D E B a d q x hfix hDcomp hD
    hDE hcover hother hBD n hstay
    (hQ.subset_connectedComponentIn hq hQB hterminal)


/-- The actual inverse itinerary composes, with no relabeling of
intermediate components. -/
theorem limbItinerary_add (F : X → X) (D B : Set X) (m k : ℕ) :
    limbItinerary F D (limbItinerary F D B m) k =
      limbItinerary F D B (m+k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change D ∩ F ⁻¹' limbItinerary F D (limbItinerary F D B m) k =
      D ∩ F ⁻¹' limbItinerary F D B (m+k)
    rw [ih]

/-- Every parent of a full selected address is recovered as its exact
forward image. This holds also for disconnected bases. -/
theorem limbItinerary_prefix_image (F : X → X) (D B : Set X)
    (hcover : D ⊆ F '' D) (hBD : B ⊆ D) (m k : ℕ) :
    (F^[k]) '' limbItinerary F D B (m+k) = limbItinerary F D B m := by
  rw [← limbItinerary_add F D B m k]
  exact limbItinerary_image F D _ hcover (limbItinerary_subset F D B hBD m) k

/-- Recognition from actual intersection with the pulled-back central
mark, without an assumed address for any endpoint of the supplied
restriction. If the restriction covers the entire anchored base,
uniqueness of the inverse point forces equality, not only inclusion. -/
theorem quadratic_marked_restriction_selection (c : ℂ)
    (D E B Q R : Set (quadraticFilled c)) (a d q : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hBD : B ⊆ D) (hQ : IsPreconnected Q) (hQB : Q ⊆ B) (hq : q ∈ Q)
    (n : ℕ) (hR : IsPreconnected R)
    (hRpre : R ⊆ ((quadraticFilledMap c)^[n]) ⁻¹' B)
    (hcontact : (R ∩ limbItinerary (quadraticFilledMap c) D Q n).Nonempty) :
    R ⊆ limbItinerary (quadraticFilledMap c) D (connectedComponentIn B q) n ∧
      (R = limbItinerary (quadraticFilledMap c) D (connectedComponentIn B q) n ↔
        ((quadraticFilledMap c)^[n]) '' R = connectedComponentIn B q) := by
  let F := quadraticFilledMap c
  let L := limbItinerary F D (connectedComponentIn B q) n
  change R ⊆ L ∧ (R = L ↔ (F^[n]) '' R = connectedComponentIn B q)
  obtain ⟨x, hxR, hxQ⟩ := hcontact
  have hroute := (mem_limbItinerary F D Q n x).mp hxQ
  have hselect : L = connectedComponentIn ((F^[n]) ⁻¹' B) x :=
    quadratic_mark_itinerary_component c D E B Q a d q x hfix hDcomp hD
      hDE hcover hother hBD hQ hQB hq n hroute.1 hroute.2
  have hsub : R ⊆ L := by
    rw [hselect]
    exact hR.subset_connectedComponentIn hxR hRpre
  refine ⟨hsub, ?_⟩
  have hBsub : connectedComponentIn B q ⊆ D :=
    (connectedComponentIn_subset B q).trans hBD
  have hImg : (F^[n]) '' L = connectedComponentIn B q :=
    limbItinerary_image F D _ hcover hBsub n
  constructor
  · intro heq
    rw [heq, hImg]
  · intro himage
    apply Subset.antisymm hsub
    intro z hz
    have hzimg : (F^[n]) z ∈ connectedComponentIn B q :=
      ((mem_limbItinerary F D (connectedComponentIn B q) n z).mp hz).2
    rw [← himage] at hzimg
    obtain ⟨w, hw, hweq⟩ := hzimg
    have hwz : w = z := limbItinerary_injective F D _
      (quadratic_critical_limb_injective c D E hDE hother) hBsub n
      (hsub hw) hz hweq
    exact hwz ▸ hw

/-- Monotone-model orbit data recognize the actual selected component
even when the closed connected physical carrier is not saturated for
the quotient. Singleton cut fiber, hereditary unicoherence, and a
path-connected model limb are explicit hypotheses. The full base
becomes preconnected; no terminal anchored-component hypothesis is
needed, only membership in the physical carrier at the terminal time. -/
theorem quadratic_model_carrier_itinerary_component
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyConnectedSpace Y]
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hs : Semiconj p (quadraticFilledMap c) G)
    (D E T : Set (quadraticFilled c)) (a d x : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a) (hda : d ≠ a)
    (hsingleton : p ⁻¹' ({p a} : Set Y) = {a})
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hpath : IsPathConnected (connectedComponentIn ({p a} : Set Y)ᶜ (p d)))
    (hu : ∀ U V : Set (quadraticFilled c), IsClosed U → IsClosed V →
      IsConnected U → IsConnected V → IsPreconnected (U ∩ V))
    (hTc : IsClosed T) (hT : IsConnected T)
    (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (n : ℕ)
    (hmodel : ∀ k ≤ n, (G^[k]) (p x) ∈
      connectedComponentIn ({p a} : Set Y)ᶜ (p d))
    (hterminal : ((quadraticFilledMap c)^[n]) x ∈ T) :
    IsPreconnected (T ∩ D) ∧
      limbItinerary (quadraticFilledMap c) D (T ∩ D) n =
        connectedComponentIn (((quadraticFilledMap c)^[n]) ⁻¹' (T ∩ D)) x := by
  letI : CompactSpace (quadraticFilled c) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact c)
  let F := quadraticFilledMap c
  let V := connectedComponentIn ({p a} : Set Y)ᶜ (p d)
  have hlift : D = p ⁻¹' V :=
    hDcomp.trans (LoopsStationaryMonotoneGeometry.punctured_component_full_lift
      p hp hsurj hf a d hsingleton hda)
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isClosed_singleton.isOpen_compl.connectedComponentIn
  have hDopen : IsOpen D := by
    rw [hlift]
    exact hVopen.preimage hp
  have hbase : IsPreconnected (T ∩ D) := by
    rw [hlift]
    exact LoopsStationaryMonotoneGeometry.preconnected_inter_preimage_path_connected
      p hp hsurj hf hu T V hTc hT hpath
  have hstay : ∀ k ≤ n, (F^[k]) x ∈ D := by
    intro k hk
    rw [hlift]
    change p ((F^[k]) x) ∈ V
    rw [hs.iterate_right k x]
    exact hmodel k hk
  have hx : x ∈ limbItinerary F D (T ∩ D) n :=
    (mem_limbItinerary F D _ n x).mpr
      ⟨fun k hk => hstay k (Nat.le_of_lt hk), hterminal, hstay n le_rfl⟩
  exact ⟨hbase, (limbItinerary_component F D (T ∩ D) a d hfix hDcomp
    (quadratic_filled_continuous_open c).1 (quadratic_filled_continuous_open c).2
    hDopen hcover (quadratic_critical_limb_injective c D E hDE hother)
    inter_subset_right hbase n).2 x hx⟩


/-- The selected-limb inverse is unique for any genuine degree-two
map, not only a polynomial representative. The disjoint second limb
uses the other available inverse point. -/
theorem degree_two_limb_injective (F : X → X) (D E : Set X)
    (hdegree : ∀ x y z : X, F x = F y → F x = F z →
      x = y ∨ x = z ∨ y = z)
    (hDE : Disjoint D E) (hother : D ⊆ F '' E) :
    InjOn F (D ∩ F ⁻¹' D) := by
  intro x hx y hy hxy
  obtain ⟨z, hz, hzx⟩ := hother hx.2
  have hxz : x ≠ z := by
    intro h
    exact Set.disjoint_left.mp hDE hx.1 (by simpa only [h] using hz)
  have hyz : y ≠ z := by
    intro h
    exact Set.disjoint_left.mp hDE hy.1 (by simpa only [h] using hz)
  rcases hdegree x y z hxy hzx.symm with h | h | h
  · exact h
  · exact (hxz h).elim
  · exact (hyz h).elim

/-- The inverse itinerary is not merely a pointwise relation: it
admits a genuine continuous inverse section on the entire limb.
No connectedness or local connectivity of the ambient space is used. -/
theorem limbItinerary_continuous_inverse (F : X → X) (D : Set X)
    (hF : Continuous F) (hopen : IsOpenMap F) (hD : IsOpen D)
    (hcover : D ⊆ F '' D) (hinj : InjOn F (D ∩ F ⁻¹' D))
    (n : ℕ) :
    ∃ g : D → X, Continuous g ∧
      ∀ y : D, g y ∈ limbItinerary F D D n ∧ (F^[n]) (g y) = (y : X) := by
  have hLopen : IsOpen (limbItinerary F D D n) := by
    induction n with
    | zero => exact hD
    | succ k ih =>
      change IsOpen (D ∩ F ⁻¹' limbItinerary F D D k)
      exact hD.inter (ih.preimage hF)
  have hOpenIterAll : ∀ k : ℕ, IsOpenMap (F^[k]) := by
    intro k
    induction k with
    | zero =>
      intro U hU
      simpa using hU
    | succ k ih =>
      rw [Function.iterate_succ]
      exact IsOpenMap.comp ih hopen
  have hOpenIter : IsOpenMap (F^[n]) := hOpenIterAll n
  let L := limbItinerary F D D n
  have hImage : (F^[n]) '' L = D :=
    limbItinerary_image F D D hcover Subset.rfl n
  have hInj : InjOn (F^[n]) L :=
    limbItinerary_injective F D D hinj Subset.rfl n
  have hex : ∀ y : D, ∃ x : X, x ∈ L ∧ (F^[n]) x = (y : X) := by
    intro y
    have hy : (y : X) ∈ (F^[n]) '' L := by
      rw [hImage]
      exact y.property
    exact hy
  choose g hg using hex
  refine ⟨g, ?_, hg⟩
  apply continuous_def.mpr
  intro U hU
  have heq : g ⁻¹' U = (Subtype.val : D → X) ⁻¹' ((F^[n]) '' (L ∩ U)) := by
    ext y
    constructor
    · intro hy
      exact ⟨g y, ⟨(hg y).1, hy⟩, (hg y).2⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hy
      have he : x = g y := hInj hx.1 (hg y).1 (hxy.trans (hg y).2.symm)
      change g y ∈ U
      rw [← he]
      exact hx.2
  rw [heq]
  exact (hOpenIter _ (hLopen.inter hU)).preimage continuous_subtype_val

/-- Source-facing universal compatibility for independently supplied
continuous inverse restrictions of a native degree-two map. One
physical anchor with the selected orbit itinerary determines the
entire inverse section on any preconnected target in the limb.
The target need not be open or compact, and no global local
connectivity or polynomial conjugacy is required. The inverse image
is the entire selected itinerary of that target, not just a subset;
its values agree pointwise with the constructed canonical section. -/
theorem degree_two_independent_inverse_agreement (F : X → X)
    (D E : Set X) (a d : X) (hfix : F a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set X)ᶜ d)
    (hF : Continuous F) (hopen : IsOpenMap F) (hD : IsOpen D)
    (hdegree : ∀ x y z : X, F x = F y → F x = F z →
      x = y ∨ x = z ∨ y = z)
    (hDE : Disjoint D E) (hcover : D ⊆ F '' D) (hother : D ⊆ F '' E)
    (n : ℕ) :
    ∃ φ : D → X, Continuous φ ∧
      (∀ y : D, φ y ∈ limbItinerary F D D n ∧ (F^[n]) (φ y) = (y : X)) ∧
      ∀ (S : Set X) (hSD : S ⊆ D) (q : X), q ∈ S →
        IsPreconnected S → ∀ g : X → X, ContinuousOn g S →
        (∀ y ∈ S, (F^[n]) (g y) = y) →
        (∀ k < n, (F^[k]) (g q) ∈ D) →
        g '' S = limbItinerary F D S n ∧
          ∀ (y : X) (hy : y ∈ S), g y = φ ⟨y, hSD hy⟩ := by
  have hinj := degree_two_limb_injective F D E hdegree hDE hother
  obtain ⟨φ, hφc, hφ⟩ :=
    limbItinerary_continuous_inverse F D hF hopen hD hcover hinj n
  refine ⟨φ, hφc, hφ, ?_⟩
  intro S hSD q hq hS g hg hsection hstay
  have hterminal : (F^[n]) (g q) ∈ S := by
    rw [hsection q hq]
    exact hq
  have hroute : g q ∈ limbItinerary F D S n :=
    (mem_limbItinerary F D S n (g q)).mpr ⟨hstay, hterminal⟩
  have hcomp := (limbItinerary_component F D S a d hfix hDcomp
    hF hopen hD hcover hinj hSD hS n).2 (g q) hroute
  have hR : IsPreconnected (g '' S) := hS.image _ hg
  have hpre : g '' S ⊆ (F^[n]) ⁻¹' S := by
    rintro _ ⟨y, hy, rfl⟩
    change (F^[n]) (g y) ∈ S
    rw [hsection y hy]
    exact hy
  have hsub : g '' S ⊆ limbItinerary F D S n := by
    rw [hcomp]
    exact hR.subset_connectedComponentIn ⟨q, hq, rfl⟩ hpre
  have hinjS := limbItinerary_injective F D S hinj hSD n
  have hEq : g '' S = limbItinerary F D S n := by
    apply Subset.antisymm hsub
    intro z hz
    have hterm := ((mem_limbItinerary F D S n z).mp hz).2
    have hgz : g ((F^[n]) z) ∈ limbItinerary F D S n :=
      hsub ⟨(F^[n]) z, hterm, rfl⟩
    have heq : g ((F^[n]) z) = z := hinjS hgz hz (hsection _ hterm)
    exact ⟨(F^[n]) z, hterm, heq⟩
  refine ⟨hEq, ?_⟩
  intro y hy
  have hgy : g y ∈ limbItinerary F D S n := hsub ⟨y, hy, rfl⟩
  have horbit := (mem_limbItinerary F D S n (g y)).mp hgy
  have hgyD : g y ∈ limbItinerary F D D n :=
    (mem_limbItinerary F D D n (g y)).mpr ⟨horbit.1, hSD horbit.2⟩
  exact (limbItinerary_injective F D D hinj Subset.rfl n) hgyD
    (hφ ⟨y, hSD hy⟩).1 ((hsection y hy).trans (hφ ⟨y, hSD hy⟩).2.symm)

end LoopsStationaryPhysicalItinerary
