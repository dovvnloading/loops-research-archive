import StationaryLimbCollar
import StationaryBoundaryExtension
import PrimeEndSectorImpressions

/-!
# Exact inverse impressions of canonical ambient limb collars

The supplied tails live in a connected ambient restriction, not in the
filled Julia set. Compactness of the constructed source collar and its
injectivity identify the entire source impression from the target
impression, including a nondegenerate target continuum.
-/

namespace LoopsStationaryAmbientImpressions

open Set Function
open QuadraticEscape LoopsStationaryFiberDynamics
open LoopsStationaryPhysicalItinerary LoopsStationaryLimbCollar
open LoopsStationaryAmbientLanding LoopsStationaryBoundaryExtension PrimeEndSectorFilters

/-- Exact inverse covariance for nested ambient traces. Neither impression
is assumed to be a point, and the inverse function need only be a right
inverse on the target collar. Compactness and injectivity come from the
whole closed source collar. -/
theorem quadratic_nested_inverse_impression (c : ℂ) (n : ℕ)
    (U V : Set ℂ) (g : ℂ → ℂ)
    (hUc : IsCompact (closure U)) (hinj : InjOn (orbit c n) (closure U))
    (hmap : MapsTo g V U) (hright : RightInvOn g (orbit c n) V)
    (S : ℕ → Set ℂ) (ha : Antitone S) (hSU : ∀ m, S m ⊆ U)
    (htarget : (⋂ m, closure (orbit c n '' S m)) ⊆ V) :
    (⋂ m, closure (S m)) = g '' (⋂ m, closure (orbit c n '' S m)) := by
  let F := orbit c n
  let J : Set ℂ := ⋂ m, closure (S m)
  let I : Set ℂ := ⋂ m, closure (F '' S m)
  have hcompact (m : ℕ) : IsCompact (closure (S m)) :=
    hUc.of_isClosed_subset isClosed_closure (closure_mono (hSU m))
  have hcov : F '' J = I :=
    quadratic_cofinal_impression_covariance c n S (fun m => F '' S m)
      ha hcompact (fun j => ⟨j, Subset.rfl⟩) (fun i => ⟨i, Subset.rfl⟩)
  have hsub : J ⊆ closure U := fun z hz =>
    closure_mono (hSU 0) (mem_iInter.mp hz 0)
  change J = g '' I
  apply Subset.antisymm
  · intro z hz
    have hpz : F z ∈ I := by
      rw [← hcov]
      exact ⟨z, hz, rfl⟩
    have he : g (F z) = z :=
      hinj (subset_closure (hmap (htarget hpz))) (hsub hz)
        (hright (htarget hpz))
    exact ⟨F z, hpz, he⟩
  · rintro z ⟨y, hy, rfl⟩
    have hy' : y ∈ F '' J := by
      rw [hcov]
      exact hy
    obtain ⟨w, hw, hwy⟩ := hy'
    have he : g y = w :=
      hinj (subset_closure (hmap (htarget hy))) (hsub hw)
        ((hright (htarget hy)).trans hwy.symm)
    rw [he]
    exact hw

/-- A single anchor on the same connected projected trace confines all
of its nested tails. Their full impressions are nonempty and connected,
and exact inverse covariance requires no source landing hypothesis. -/
theorem anchored_trace_inverse_impression {T : Type*} [TopologicalSpace T]
    (c : ℂ) (n : ℕ) (V : Set ℂ) (x : ℂ) (g : ℂ → ℂ)
    (hUc : IsCompact (closure (connectedComponentIn (orbit c n ⁻¹' V) x)))
    (hinj : InjOn (orbit c n)
      (closure (connectedComponentIn (orbit c n ⁻¹' V) x)))
    (hmap : MapsTo g V (connectedComponentIn (orbit c n ⁻¹' V) x))
    (hright : RightInvOn g (orbit c n) V)
    (A : Set T) (t₀ : T) (γ : T → ℂ)
    (hA : IsPreconnected A) (ht₀ : t₀ ∈ A) (hγ : ContinuousOn γ A)
    (hproject : MapsTo (fun t => orbit c n (γ t)) A V)
    (hanchor : γ t₀ ∈ connectedComponentIn (orbit c n ⁻¹' V) x)
    (tail : ℕ → Set T) (ha : Antitone tail)
    (htail : ∀ m, tail m ⊆ A)
    (hne : ∀ m, (tail m).Nonempty) (hp : ∀ m, IsPreconnected (tail m))
    (htarget : (⋂ m, closure (orbit c n '' (γ '' tail m))) ⊆ V) :
    (⋂ m, closure (γ '' tail m)) =
        g '' (⋂ m, closure (orbit c n '' (γ '' tail m))) ∧
      (⋂ m, closure (γ '' tail m)).Nonempty ∧
      IsPreconnected (⋂ m, closure (γ '' tail m)) := by
  let U := connectedComponentIn (orbit c n ⁻¹' V) x
  let S : ℕ → Set ℂ := fun m => γ '' tail m
  have hconf : γ '' A ⊆ U :=
    anchored_component_confinement (orbit c n) V x A t₀ γ
      hA ht₀ hγ hproject hanchor
  have hSU (m : ℕ) : S m ⊆ U := (image_mono (htail m)).trans hconf
  have hmono : Antitone S := fun _ _ hij => image_mono (ha hij)
  have hcompact (m : ℕ) : IsCompact (closure (S m)) :=
    hUc.of_isClosed_subset isClosed_closure (closure_mono (hSU m))
  have hSne (m : ℕ) : (S m).Nonempty := (hne m).image γ
  have hSconn (m : ℕ) : IsPreconnected (S m) :=
    (hp m).image γ (hγ.mono (htail m))
  have hconnected := nested_impression_connected S hmono hcompact hSne hSconn
  exact ⟨quadratic_nested_inverse_impression c n U V g hUc hinj
    hmap hright S hmono hSU htarget, hconnected.1, hconnected.2⟩

/-- Native critical-limb data construct a collar that selects the entire
physical impression of every anchored ambient restriction. The target
impression may be a nondegenerate continuum inside the central mark.
Every source impression point has the full canonical parent address. -/
theorem limb_collar_ambient_impressions {T : Type*} [TopologicalSpace T]
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
        InjOn (orbit c n) (closure U) ∧ AnalyticOnNhd ℂ g V ∧
        g '' ((Subtype.val : quadraticFilled c → ℂ) '' Q) =
          (Subtype.val : quadraticFilled c → ℂ) ''
            limbItinerary (quadraticFilledMap c) D Q n ∧
        ∀ (A : Set T) (t₀ : T) (γ : T → ℂ),
          IsPreconnected A → t₀ ∈ A → ContinuousOn γ A →
          MapsTo (fun t => orbit c n (γ t)) A V → γ t₀ ∈ U →
          ∀ tail : ℕ → Set T, Antitone tail →
            (∀ m, tail m ⊆ A) →
            (∀ m, (tail m).Nonempty) → (∀ m, IsPreconnected (tail m)) →
            (⋂ m, closure (orbit c n '' (γ '' tail m))) ⊆
              (Subtype.val : quadraticFilled c → ℂ) '' Q →
            (⋂ m, closure (γ '' tail m)) =
                g '' (⋂ m, closure (orbit c n '' (γ '' tail m))) ∧
              (⋂ m, closure (γ '' tail m)).Nonempty ∧
              IsPreconnected (⋂ m, closure (γ '' tail m)) ∧
              (⋂ m, closure (γ '' tail m)) ⊆
                (Subtype.val : quadraticFilled c → ℂ) ''
                  limbItinerary (quadraticFilledMap c) D Q n ∧
              ∀ m k : ℕ, m+k=n →
                orbit c k '' (⋂ j, closure (γ '' tail j)) ⊆
                  (Subtype.val : quadraticFilled c → ℂ) ''
                    limbItinerary (quadraticFilledMap c) D Q m := by
  obtain ⟨x, V, g, hx, hVo, hVc, hQV, hUo, hUc, hUW, hUI,
      _, hmap, _, hright, hana, hcore, _⟩ :=
    limb_itinerary_analytic_collar c D E Q a d hfix hDcomp hD hDE
      hcover hother hQD hQ hQconn hQne n W hW hCW
  refine ⟨x, V, g, hx, hVo, hVc, hQV, hUo, hUc, hUW, hUI, hana, hcore, ?_⟩
  intro A t₀ γ hA ht₀ hγ hproject hanchor tail ha htail hne hp htarget
  obtain ⟨heq, hnonempty, hconnected⟩ :=
    anchored_trace_inverse_impression c n V (x : ℂ) g hUc hUI hmap hright
      A t₀ γ hA ht₀ hγ hproject hanchor tail ha htail hne hp (htarget.trans hQV)
  have hsub : (⋂ j, closure (γ '' tail j)) ⊆
      (Subtype.val : quadraticFilled c → ℂ) ''
        limbItinerary (quadraticFilledMap c) D Q n := by
    rw [heq, ← hcore]
    exact image_mono htarget
  refine ⟨heq, hnonempty, hconnected, hsub, ?_⟩
  intro m k hmk z hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨u, hu, huw⟩ := hsub hw
  have hparent : ((quadraticFilledMap c)^[k]) u ∈
      limbItinerary (quadraticFilledMap c) D Q m := by
    rw [← limbItinerary_prefix_image (quadraticFilledMap c) D Q hcover hQD m k]
    exact ⟨u, by simpa only [hmk] using hu, rfl⟩
  refine ⟨((quadraticFilledMap c)^[k]) u, hparent, ?_⟩
  rw [filled_iterate_val c k u, huw]

/-- The same exact inverse-impression theorem on the whole closed critical
limb, including its dividing attachment. The target impression may be any
nonempty continuum retained by the nested traces; no point landing or
local connectivity is required. Every closed parent is recovered. -/
theorem closed_limb_collar_ambient_impressions {T : Type*} [TopologicalSpace T]
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
        ∀ (A : Set T) (t₀ : T) (γ : T → ℂ),
          IsPreconnected A → t₀ ∈ A → ContinuousOn γ A →
          MapsTo (fun t => orbit c n (γ t)) A V → γ t₀ ∈ U →
          ∀ tail : ℕ → Set T, Antitone tail →
            (∀ m, tail m ⊆ A) →
            (∀ m, (tail m).Nonempty) → (∀ m, IsPreconnected (tail m)) →
            (⋂ m, closure (orbit c n '' (γ '' tail m))) ⊆
              (Subtype.val : quadraticFilled c → ℂ) '' closure D →
            (⋂ m, closure (γ '' tail m)) =
                g '' (⋂ m, closure (orbit c n '' (γ '' tail m))) ∧
              (⋂ m, closure (γ '' tail m)).Nonempty ∧
              IsPreconnected (⋂ m, closure (γ '' tail m)) ∧
              (⋂ m, closure (γ '' tail m)) ⊆
                (Subtype.val : quadraticFilled c → ℂ) ''
                  closure (limbItinerary (quadraticFilledMap c) D D n) ∧
              ∀ m k : ℕ, m+k=n →
                orbit c k '' (⋂ j, closure (γ '' tail j)) ⊆
                  (Subtype.val : quadraticFilled c → ℂ) ''
                    closure (limbItinerary (quadraticFilledMap c) D D m) := by
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
      _, hmap, _, hright, hana, hcore, _⟩ :=
    quadratic_closed_limb_analytic_collar c D E a d hfix ha0 hDcomp hD hDE
      hcover hother hzero n W hW hCW
  refine ⟨x, V, g, hx, hVo, hVc, hBV, hUo, hUc, hUW, hUI, hana, hcore, ?_⟩
  intro A t₀ γ hA ht₀ hγ hproject hanchor tail ha htail hne hp htarget
  obtain ⟨heq, hnonempty, hconnected⟩ :=
    anchored_trace_inverse_impression c n V x g hUc hUI hmap hright
      A t₀ γ hA ht₀ hγ hproject hanchor tail ha htail hne hp (htarget.trans hBV)
  have hsub : (⋂ j, closure (γ '' tail j)) ⊆
      (Subtype.val : quadraticFilled c → ℂ) ''
        closure (limbItinerary (quadraticFilledMap c) D D n) := by
    rw [heq, ← hcore]
    exact image_mono htarget
  refine ⟨heq, hnonempty, hconnected, hsub, ?_⟩
  intro m k hmk z hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨u, hu, huw⟩ := hsub hw
  have hparent : ((quadraticFilledMap c)^[k]) u ∈
      closure (limbItinerary (quadraticFilledMap c) D D m) := by
    rw [← limbItinerary_closed_prefix_image (quadraticFilledMap c) D
      (quadratic_filled_continuous_open c).1 hcover m k]
    exact ⟨u, by simpa only [hmk] using hu, rfl⟩
  refine ⟨((quadraticFilledMap c)^[k]) u, hparent, ?_⟩
  rw [filled_iterate_val c k u, huw]

end LoopsStationaryAmbientImpressions
