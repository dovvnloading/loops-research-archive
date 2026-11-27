import StationaryPhysicalItinerary
import TelescopeUnivalentCollars
import StationaryAmbientLanding

/-!
# Ambient analytic collars of the canonical physical limb itinerary

The central mark is compact and connected in the actual filled Julia set.
The selected core, its planar component identity, its injectivity and all
preterminal critical exclusions are conclusions of the limb geometry.
-/

namespace LoopsStationaryLimbCollar

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsStationaryFiberDynamics LoopsStationaryLightModel
open LoopsStationaryPhysicalItinerary LoopsSaturatedTelescope
open LoopsTelescopeRamification LoopsTelescopeCollar LoopsTelescopeUnivalentCollars

noncomputable section

/-- The restricted physical iterate and the ambient polynomial iterate
have exactly the same values. -/
theorem filled_iterate_val (c : ℂ) (n : ℕ) (z : quadraticFilled c) :
    (((quadraticFilledMap c)^[n]) z : ℂ) = orbit c n z := by
  have hs : Semiconj (Subtype.val : quadraticFilled c → ℂ)
      (quadraticFilledMap c) (fun w : ℂ => w^2+c) := fun _ => rfl
  rw [orbit_map_eq_iterate]
  exact hs.iterate_right n z

private theorem subtype_component_image (K B : Set ℂ) (hBK : B ⊆ K)
    (x : K) (hx : (x : ℂ) ∈ B) :
    (Subtype.val : K → ℂ) '' connectedComponentIn
        ((Subtype.val : K → ℂ) ⁻¹' B) x =
      connectedComponentIn B (x : ℂ) := by
  apply Subset.antisymm
  · apply (isPreconnected_connectedComponentIn.image _
      continuous_subtype_val.continuousOn).subset_connectedComponentIn
    · exact ⟨x, mem_connectedComponentIn hx, rfl⟩
    · rintro z ⟨w, hw, rfl⟩
      exact connectedComponentIn_subset ((Subtype.val : K → ℂ) ⁻¹' B) x hw
  · let C := connectedComponentIn B (x : ℂ)
    have hCK : C ⊆ K := (connectedComponentIn_subset B (x : ℂ)).trans hBK
    have hconn : IsPreconnected ((Subtype.val : K → ℂ) ⁻¹' C) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hCK]
      exact isPreconnected_connectedComponentIn
    have hsub : (Subtype.val : K → ℂ) ⁻¹' C ⊆
        connectedComponentIn ((Subtype.val : K → ℂ) ⁻¹' B) x :=
      hconn.subset_connectedComponentIn (mem_connectedComponentIn hx)
        (fun _ hz => connectedComponentIn_subset B (x : ℂ) hz)
    intro z hz
    exact ⟨⟨z, hCK hz⟩, hsub hz, rfl⟩

/-- A component computed in the genuine filled Julia set is the whole
ambient polynomial pullback component. Complete invariance excludes
additional inverse points outside the filled set. -/
theorem filled_preimage_component_image (c : ℂ)
    (Q : Set (quadraticFilled c)) (n : ℕ) (x : quadraticFilled c)
    (hx : ((quadraticFilledMap c)^[n]) x ∈ Q) :
    (Subtype.val : quadraticFilled c → ℂ) ''
        connectedComponentIn (((quadraticFilledMap c)^[n]) ⁻¹' Q) x =
      connectedComponentIn
        (orbit c n ⁻¹' ((Subtype.val : quadraticFilled c → ℂ) '' Q)) (x : ℂ) := by
  let B : Set ℂ := orbit c n ⁻¹' ((Subtype.val : quadraticFilled c → ℂ) '' Q)
  have hBK : B ⊆ quadraticFilled c := by
    rintro z ⟨y, hy, he⟩
    have hz : orbit c n z ∈ quadraticFilled c := he ▸ y.property
    rw [orbit_map_eq_iterate] at hz
    exact (quadratic_filled_iterate_mem_iff c z n).mp hz
  have hpre : (Subtype.val : quadraticFilled c → ℂ) ⁻¹' B =
      ((quadraticFilledMap c)^[n]) ⁻¹' Q := by
    ext z
    change orbit c n z ∈ (Subtype.val : quadraticFilled c → ℂ) '' Q ↔
      ((quadraticFilledMap c)^[n]) z ∈ Q
    constructor
    · rintro ⟨y, hy, he⟩
      have heq : y = ((quadraticFilledMap c)^[n]) z :=
        Subtype.ext (he.trans (filled_iterate_val c n z).symm)
      exact heq ▸ hy
    · intro hz
      exact ⟨((quadraticFilledMap c)^[n]) z, hz, filled_iterate_val c n z⟩
  have hxB : (x : ℂ) ∈ B :=
    ⟨((quadraticFilledMap c)^[n]) x, hx, filled_iterate_val c n x⟩
  have h := subtype_component_image (quadraticFilled c) B hBK x hxB
  rw [hpre] at h
  exact h

/-- The canonical limb itinerary is a whole connected component in the
ambient plane, even when the filled Julia set is not locally connected. -/
theorem limb_itinerary_planar_component (c : ℂ)
    (D E Q : Set (quadraticFilled c)) (a d x : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hQD : Q ⊆ D) (hQconn : IsPreconnected Q) (n : ℕ)
    (hx : x ∈ limbItinerary (quadraticFilledMap c) D Q n) :
    (Subtype.val : quadraticFilled c → ℂ) ''
        limbItinerary (quadraticFilledMap c) D Q n =
      connectedComponentIn
        (orbit c n ⁻¹' ((Subtype.val : quadraticFilled c → ℂ) '' Q)) (x : ℂ) := by
  have hcomponent := (limbItinerary_component (quadraticFilledMap c) D Q
    a d hfix hDcomp (quadratic_filled_continuous_open c).1
    (quadratic_filled_continuous_open c).2 hD hcover
    (quadratic_critical_limb_injective c D E hDE hother) hQD hQconn n).2 x hx
  rw [hcomponent]
  exact filled_preimage_component_image c Q n x
    ((mem_limbItinerary (quadraticFilledMap c) D Q n x).mp hx).2

/-- A disjoint alternative inverse limb excludes every critical visit
strictly before the terminal time. The central target itself may contain
zero; that terminal encounter is not excluded. -/
theorem limb_itinerary_critical_free (c : ℂ)
    (D E Q : Set (quadraticFilled c)) (hDE : Disjoint D E)
    (hother : D ⊆ quadraticFilledMap c '' E) (hQD : Q ⊆ D)
    (n : ℕ) (x : quadraticFilled c)
    (hx : x ∈ limbItinerary (quadraticFilledMap c) D Q n) :
    ∀ j < n, orbit c j x ≠ 0 := by
  let F := quadraticFilledMap c
  have hroute := (mem_limbItinerary F D Q n x).mp hx
  intro j hj hz
  have hcurrent : (F^[j]) x ∈ D := hroute.1 j hj
  have hnext : F ((F^[j]) x) ∈ D := by
    by_cases hlt : j+1 < n
    · simpa only [Function.iterate_succ_apply'] using hroute.1 (j+1) hlt
    · have he : j+1 = n := by omega
      have ht : (F^[j+1]) x ∈ D := by
        rw [he]
        exact hQD hroute.2
      simpa only [Function.iterate_succ_apply'] using ht
  obtain ⟨w, hw, hew⟩ := hother hnext
  have hval : ((F^[j]) x : ℂ) = 0 := (filled_iterate_val c j x).trans hz
  have hewc : (w : ℂ)^2+c = (0 : ℂ)^2+c := by
    have h := congrArg (fun v : quadraticFilled c => (v : ℂ)) hew
    change (w : ℂ)^2+c = ((F^[j]) x : ℂ)^2+c at h
    simpa only [hval] using h
  have hsq : (w : ℂ)^2 = 0 := by
    simpa using add_right_cancel hewc
  have hmul : (w : ℂ) * (w : ℂ) = 0 := by
    simpa only [pow_two] using hsq
  have hwzero : (w : ℂ) = 0 := (mul_eq_zero.mp hmul).elim id id
  have heq : w = (F^[j]) x := Subtype.ext (hwzero.trans hval.symm)
  exact Set.disjoint_left.mp hDE hcurrent (heq ▸ hw)

/-- All compact-core hypotheses needed for an ambient univalent collar
follow from the physical limb data and compactness of the central mark. -/
theorem limb_itinerary_planar_geometry (c : ℂ)
    (D E Q : Set (quadraticFilled c)) (a d x : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hQD : Q ⊆ D) (hQ : IsCompact Q) (hQconn : IsPreconnected Q)
    (n : ℕ) (hx : x ∈ limbItinerary (quadraticFilledMap c) D Q n) :
    let C := (Subtype.val : quadraticFilled c → ℂ) ''
      limbItinerary (quadraticFilledMap c) D Q n
    IsCompact C ∧ IsPreconnected C ∧ InjOn (orbit c n) C ∧
      ∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0 := by
  let C := (Subtype.val : quadraticFilled c → ℂ) ''
    limbItinerary (quadraticFilledMap c) D Q n
  change IsCompact C ∧ IsPreconnected C ∧ InjOn (orbit c n) C ∧ _
  have hc := limb_itinerary_planar_component c D E Q a d x
    hfix hDcomp hD hDE hcover hother hQD hQconn n hx
  have hxQ : orbit c n x ∈ (Subtype.val : quadraticFilled c → ℂ) '' Q :=
    ⟨((quadraticFilledMap c)^[n]) x,
      ((mem_limbItinerary (quadraticFilledMap c) D Q n x).mp hx).2,
      filled_iterate_val c n x⟩
  have hcompact : IsCompact C := by
    rw [show C = connectedComponentIn
      (orbit c n ⁻¹' ((Subtype.val : quadraticFilled c → ℂ) '' Q)) (x : ℂ) from hc]
    exact proper_component_compact (orbit c n) (orbit_proper c n)
      _ (hQ.image continuous_subtype_val) (x : ℂ) hxQ
  have hconn : IsPreconnected C := by
    rw [show C = connectedComponentIn
      (orbit c n ⁻¹' ((Subtype.val : quadraticFilled c → ℂ) '' Q)) (x : ℂ) from hc]
    exact isPreconnected_connectedComponentIn
  have hinj : InjOn (orbit c n) C := by
    rintro z ⟨u, hu, rfl⟩ w ⟨v, hv, rfl⟩ he
    have heq : ((quadraticFilledMap c)^[n]) u =
        ((quadraticFilledMap c)^[n]) v := by
      apply Subtype.ext
      rw [filled_iterate_val, filled_iterate_val]
      exact he
    exact congrArg (fun y : quadraticFilled c => (y : ℂ))
      (limbItinerary_injective (quadraticFilledMap c) D Q
        (quadratic_critical_limb_injective c D E hDE hother) hQD n hu hv heq)
  refine ⟨hcompact, hconn, hinj, ?_⟩
  rintro z ⟨u, hu, rfl⟩ j hj
  exact limb_itinerary_critical_free c D E Q hDE hother hQD n u hu j hj

/-- The canonical physical predecessor admits an actual analytic collar
inside any prescribed open neighborhood. The anchor, whole planar
component, critical exclusions and injectivity are constructed, not
supplied as extra collar hypotheses. -/
theorem limb_itinerary_analytic_collar (c : ℂ)
    (D E Q : Set (quadraticFilled c)) (a d : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hQD : Q ⊆ D) (hQ : IsCompact Q) (hQconn : IsPreconnected Q)
    (hQne : Q.Nonempty) (n : ℕ) (W : Set ℂ) (hW : IsOpen W)
    (hCW : (Subtype.val : quadraticFilled c → ℂ) ''
      limbItinerary (quadraticFilledMap c) D Q n ⊆ W) :
    ∃ (x : quadraticFilled c) (V : Set ℂ) (g : ℂ → ℂ),
      x ∈ limbItinerary (quadraticFilledMap c) D Q n ∧
      IsOpen V ∧ IsPreconnected V ∧
      (Subtype.val : quadraticFilled c → ℂ) '' Q ⊆ V ∧
      let U := connectedComponentIn (orbit c n ⁻¹' V) (x : ℂ)
      IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ W ∧
        InjOn (orbit c n) (closure U) ∧ orbit c n '' U = V ∧
        MapsTo g V U ∧ LeftInvOn g (orbit c n) U ∧
        RightInvOn g (orbit c n) V ∧ AnalyticOnNhd ℂ g V ∧
        g '' ((Subtype.val : quadraticFilled c → ℂ) '' Q) =
          (Subtype.val : quadraticFilled c → ℂ) ''
            limbItinerary (quadraticFilledMap c) D Q n ∧
        ∀ y ∈ V, HasDerivAt g (deriv (orbit c n) (g y))⁻¹ y ∧ ConformalAt g y := by
  obtain ⟨q, hq⟩ := hQne
  have hqimage : q ∈ ((quadraticFilledMap c)^[n]) ''
      limbItinerary (quadraticFilledMap c) D Q n := by
    rw [limbItinerary_image (quadraticFilledMap c) D Q hcover hQD n]
    exact hq
  obtain ⟨x, hx, _⟩ := hqimage
  have hcomponent := limb_itinerary_planar_component c D E Q a d x
    hfix hDcomp hD hDE hcover hother hQD hQconn n hx
  obtain ⟨_, _, hinj, hcrit⟩ := limb_itinerary_planar_geometry c D E Q a d x
    hfix hDcomp hD hDE hcover hother hQD hQ hQconn n hx
  have hxQ : orbit c n x ∈ (Subtype.val : quadraticFilled c → ℂ) '' Q :=
    ⟨((quadraticFilledMap c)^[n]) x,
      ((mem_limbItinerary (quadraticFilledMap c) D Q n x).mp hx).2,
      filled_iterate_val c n x⟩
  rw [hcomponent] at hCW hinj hcrit
  obtain ⟨V, g, hVo, hVc, hQV, hUo, hUc, hUW, hUI, honto,
      hmap, hleft, hright, hana, hcore, hder⟩ :=
    selected_univalent_analytic_collar c n
      ((Subtype.val : quadraticFilled c → ℂ) '' Q) W (x : ℂ)
      (hQ.image continuous_subtype_val)
      (hQconn.image _ continuous_subtype_val.continuousOn)
      hxQ hW hCW hinj hcrit
  refine ⟨x, V, g, hx, hVo, hVc, hQV, hUo, hUc, hUW, hUI,
    honto, hmap, hleft, hright, hana, ?_, hder⟩
  exact hcore.trans hcomponent.symm

/-- A collar built solely from native limb data forces landing of every
connected anchored ambient restriction, and recovers the complete canonical
parent itinerary. The supplied restriction need not lie in the filled set
and its endpoint is not assumed to exist. -/
theorem limb_collar_ambient_landing {T : Type*} [TopologicalSpace T]
    (c : ℂ) (D E Q : Set (quadraticFilled c)) (a d : quadraticFilled c)
    (hfix : quadraticFilledMap c a = a)
    (hDcomp : D = connectedComponentIn ({a} : Set (quadraticFilled c))ᶜ d)
    (hD : IsOpen D) (hDE : Disjoint D E)
    (hcover : D ⊆ quadraticFilledMap c '' D)
    (hother : D ⊆ quadraticFilledMap c '' E)
    (hQD : Q ⊆ D) (hQ : IsCompact Q) (hQconn : IsPreconnected Q)
    (hQne : Q.Nonempty) (n : ℕ) (W : Set ℂ) (hW : IsOpen W)
    (hCW : (Subtype.val : quadraticFilled c → ℂ) ''
      limbItinerary (quadraticFilledMap c) D Q n ⊆ W) :
    ∃ (x : quadraticFilled c) (V : Set ℂ) (g : ℂ → ℂ),
      x ∈ limbItinerary (quadraticFilledMap c) D Q n ∧
      IsOpen V ∧ IsPreconnected V ∧
      (Subtype.val : quadraticFilled c → ℂ) '' Q ⊆ V ∧
      let U := connectedComponentIn (orbit c n ⁻¹' V) (x : ℂ)
      IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ W ∧
        InjOn (orbit c n) (closure U) ∧
        AnalyticOnNhd ℂ g V ∧
        g '' ((Subtype.val : quadraticFilled c → ℂ) '' Q) =
          (Subtype.val : quadraticFilled c → ℂ) ''
            limbItinerary (quadraticFilledMap c) D Q n ∧
        ∀ (S : Set T) (t₀ : T) (γ : T → ℂ),
          IsPreconnected S → t₀ ∈ S → ContinuousOn γ S →
          MapsTo (fun t => orbit c n (γ t)) S V → γ t₀ ∈ U →
          (∀ t ∈ S, γ t = g (orbit c n (γ t))) ∧
          γ '' S = g '' (orbit c n '' (γ '' S)) ∧
          ∀ (l : Filter T) (y : quadraticFilled c),
            (∀ᶠ t in l, t ∈ S) → y ∈ Q →
            Filter.Tendsto (fun t => orbit c n (γ t)) l (𝓝 (y : ℂ)) →
            Filter.Tendsto γ l (𝓝 (g y)) ∧
              orbit c n (g y) = y ∧
              g y ∈ (Subtype.val : quadraticFilled c → ℂ) ''
                limbItinerary (quadraticFilledMap c) D Q n ∧
              ∀ m k : ℕ, m+k=n →
                orbit c k (g y) ∈ (Subtype.val : quadraticFilled c → ℂ) ''
                  limbItinerary (quadraticFilledMap c) D Q m := by
  obtain ⟨x, V, g, hx, hVo, hVc, hQV, hUo, hUc, hUW, hUI,
      _, _, hleft, hright, hana, hcore, _⟩ :=
    limb_itinerary_analytic_collar c D E Q a d hfix hDcomp hD hDE
      hcover hother hQD hQ hQconn hQne n W hW hCW
  refine ⟨x, V, g, hx, hVo, hVc, hQV, hUo, hUc, hUW, hUI, hana, hcore, ?_⟩
  intro S t₀ γ hS ht₀ hγ hproject hanchor
  refine ⟨LoopsStationaryAmbientLanding.anchored_lift_agrees
      (orbit c n) V (x : ℂ) g hleft S t₀ γ hS ht₀ hγ hproject hanchor,
    LoopsStationaryAmbientLanding.anchored_lift_image
      (orbit c n) V (x : ℂ) g hleft S t₀ γ hS ht₀ hγ hproject hanchor, ?_⟩
  intro l y hmem hy hlimit
  have hyV : (y : ℂ) ∈ V := hQV ⟨y, hy, rfl⟩
  have hland := LoopsStationaryAmbientLanding.anchored_lift_tendsto
    (orbit c n) V (x : ℂ) g hleft S t₀ γ hS ht₀ hγ hproject hanchor
    l hmem (y : ℂ) (hana y hyV).continuousAt hlimit
  have hgy : g y ∈ (Subtype.val : quadraticFilled c → ℂ) ''
      limbItinerary (quadraticFilledMap c) D Q n := by
    rw [← hcore]
    exact ⟨y, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨hland, hright hyV, hgy, ?_⟩
  intro m k hmk
  obtain ⟨z, hz, hzg⟩ := hgy
  have hp : ((quadraticFilledMap c)^[k]) z ∈
      limbItinerary (quadraticFilledMap c) D Q m := by
    rw [← limbItinerary_prefix_image (quadraticFilledMap c) D Q hcover hQD m k]
    exact ⟨z, by simpa only [hmk] using hz, rfl⟩
  refine ⟨((quadraticFilledMap c)^[k]) z, hp, ?_⟩
  rw [filled_iterate_val c k z, hzg]

end

end LoopsStationaryLimbCollar
